// calls/string_ops.rs
//
// String operation codegen: string literals, interpolation, value-to-string conversion.

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{DataDescription, Linkage, Module};

use vole_frontend::ast::StringPart;
use vole_sema::StringConversion;
use vole_sema::type_arena::TypeId;

use crate::errors::{CodegenError, CodegenResult};
use crate::function_registry::FunctionRegistry;
use crate::types::{CompiledValue, type_id_to_cranelift};
use crate::union_layout;

use super::super::RuntimeKey;
use super::super::context::Cg;
use crate::ops::sextend_const;

/// Compile a string literal as a static RcString baked into the JIT data section.
/// Returns the raw Cranelift Value (pointer to the static RcString) - caller should
/// wrap with string_value() for CompiledValue.
///
/// The RcString is built at compile time with RC_PINNED refcount so rc_inc/rc_dec
/// are no-ops, making string literals zero-allocation at runtime.
pub(crate) fn compile_string_literal(
    builder: &mut FunctionBuilder,
    s: &str,
    pointer_type: Type,
    module: &mut JITModule,
    func_registry: &mut FunctionRegistry,
) -> CodegenResult<Value> {
    use vole_runtime::{RC_PINNED, RuntimeTypeId, fnv1a_hash};

    // Build complete RcString struct as bytes:
    //   RcHeader { ref_count: u32, type_id: u32, drop_fn: Option<fn> }  = 16 bytes
    //   len: usize                                                       =  8 bytes
    //   char_count: usize                                                =  8 bytes
    //   hash: u64                                                        =  8 bytes
    //   data: [u8; s.len()]                                              =  N bytes
    let mut data = Vec::with_capacity(40 + s.len());
    // RcHeader
    data.extend_from_slice(&RC_PINNED.to_ne_bytes()); // ref_count = pinned (no-op inc/dec)
    data.extend_from_slice(&(RuntimeTypeId::String as u32).to_ne_bytes()); // type_id
    data.extend_from_slice(&0u64.to_ne_bytes()); // drop_fn = null (no cleanup needed)
    // RcString fields
    data.extend_from_slice(&s.len().to_ne_bytes()); // len (byte length)
    data.extend_from_slice(&s.chars().count().to_ne_bytes()); // char_count
    data.extend_from_slice(&fnv1a_hash(s.as_bytes()).to_ne_bytes()); // hash
    data.extend_from_slice(s.as_bytes()); // inline string data

    // Embed in JIT data section
    let data_name = func_registry.next_string_data_name();
    let data_id = module
        .declare_data(&data_name, Linkage::Local, false, false)
        .map_err(CodegenError::cranelift)?;

    let mut data_desc = DataDescription::new();
    data_desc.define(data.into_boxed_slice());
    data_desc.set_align(8);
    module
        .define_data(data_id, &data_desc)
        .map_err(CodegenError::cranelift)?;

    // The data section pointer IS the RcString pointer
    let data_gv = module.declare_data_in_func(data_id, builder.func);
    Ok(builder.ins().global_value(pointer_type, data_gv))
}

impl Cg<'_, '_, '_> {
    /// Compile a string literal
    pub fn string_literal(&mut self, s: &str) -> CodegenResult<CompiledValue> {
        let value = compile_string_literal(
            self.builder,
            s,
            self.ptr_type(),
            self.codegen_ctx.module,
            self.codegen_ctx.func_registry,
        )?;
        Ok(self.string_temp(value))
    }

    /// Compile an interpolated string using StringBuilder for efficient single-allocation
    pub fn interpolated_string(&mut self, parts: &[StringPart]) -> CodegenResult<CompiledValue> {
        if parts.is_empty() {
            return self.string_literal("");
        }

        // Collect all string values, tracking which need cleanup after the build.
        // - Literals: static (pinned RC), rc_dec is a no-op
        // - Expr already string: borrowed or owned from expression
        // - Expr converted via to_string: owned, needs rc_dec
        let mut string_values: Vec<Value> = Vec::new();
        let mut owned_flags: Vec<bool> = Vec::new();
        for part in parts {
            let (str_val, is_owned) = match part {
                StringPart::Literal(s) => (self.string_literal(s)?.value, true),
                StringPart::Expr(expr) => {
                    let compiled = self.expr(expr)?;
                    // Read the sema-annotated conversion for this expression part
                    let conversion = self
                        .get_string_conversion(expr.id)
                        .cloned()
                        .unwrap_or(StringConversion::Identity);
                    match conversion {
                        StringConversion::Identity => (compiled.value, compiled.is_owned()),
                        _ => (self.apply_string_conversion(compiled, &conversion)?, true),
                    }
                }
            };
            string_values.push(str_val);
            owned_flags.push(is_owned);
        }

        // Single part -- return directly, no builder needed.
        // Preserve the original lifecycle: if the value is borrowed (e.g. a
        // variable read like `"{local0}"`), return it as borrowed so the
        // caller emits rc_inc when binding.  Returning a borrowed value as
        // Owned would skip the inc while still registering a dec on scope
        // exit, causing a double-free.
        if string_values.len() == 1 {
            let mut cv = self.string_temp(string_values[0]);
            if !owned_flags[0] {
                cv.mark_borrowed();
            }
            return Ok(cv);
        }

        // Multi-part: use StringBuilder -- one allocation instead of N concats
        let sb = self.call_runtime(RuntimeKey::SbNew, &[])?;

        for &sv in &string_values {
            self.call_runtime_void(RuntimeKey::SbPushString, &[sb, sv])?;
        }

        let result = self.call_runtime(RuntimeKey::SbFinish, &[sb])?;

        // Free all owned input parts -- builder has copied the bytes
        for (val, is_owned) in string_values.iter().zip(owned_flags.iter()) {
            if *is_owned {
                self.emit_rc_dec(*val)?;
            }
        }

        Ok(self.string_temp(result))
    }

    /// Apply a sema-annotated string conversion to a compiled value.
    ///
    /// Reads the `StringConversion` annotation (set by sema) and applies the
    /// corresponding runtime call or branching logic. No type inspection needed.
    fn apply_string_conversion(
        &mut self,
        val: CompiledValue,
        conversion: &StringConversion,
    ) -> CodegenResult<Value> {
        match conversion {
            StringConversion::Identity => Ok(val.value),
            StringConversion::I64ToString => {
                let extended = if val.ty.is_int() && val.ty != types::I64 {
                    sextend_const(self.builder, types::I64, val.value)
                } else {
                    val.value
                };
                self.call_runtime(RuntimeKey::I64ToString, &[extended])
            }
            StringConversion::I128ToString => {
                self.call_runtime(RuntimeKey::I128ToString, &[val.value])
            }
            StringConversion::F32ToString => {
                self.call_runtime(RuntimeKey::F32ToString, &[val.value])
            }
            StringConversion::F64ToString => {
                self.call_runtime(RuntimeKey::F64ToString, &[val.value])
            }
            StringConversion::F128ToString => {
                let bits = self
                    .builder
                    .ins()
                    .bitcast(types::I128, MemFlags::new(), val.value);
                self.call_runtime(RuntimeKey::F128ToString, &[bits])
            }
            StringConversion::BoolToString => {
                self.call_runtime(RuntimeKey::BoolToString, &[val.value])
            }
            StringConversion::NilToString => self.call_runtime(RuntimeKey::NilToString, &[]),
            StringConversion::ArrayToString => {
                self.call_runtime(RuntimeKey::ArrayI64ToString, &[val.value])
            }
            StringConversion::OptionalToString {
                nil_index,
                variants,
                inner_conversion,
            } => self.optional_to_string(val.value, variants, *nil_index, inner_conversion),
            StringConversion::UnionToString { variants } => {
                self.union_to_string(val.value, variants)
            }
        }
    }

    /// Convert an optional (union with nil) to string.
    ///
    /// Branches on the tag: nil -> "nil", otherwise extracts the inner value
    /// and applies the sema-annotated inner conversion.
    fn optional_to_string(
        &mut self,
        ptr: Value,
        variants: &[TypeId],
        nil_idx: usize,
        inner_conversion: &StringConversion,
    ) -> CodegenResult<Value> {
        let is_nil = self.tag_eq(ptr, nil_idx as i64);

        let nil_block = self.builder.create_block();
        let some_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, self.ptr_type());

        self.emit_brif(is_nil, nil_block, some_block);

        // Nil case: return "nil"
        self.switch_to_block(nil_block);
        let nil_str = self.call_runtime(RuntimeKey::NilToString, &[])?;
        self.builder.ins().jump(merge_block, &[nil_str.into()]);

        // Some case: extract inner value and apply annotated conversion
        self.switch_to_block(some_block);
        let inner_type_id = variants
            .iter()
            .find(|v| !v.is_nil())
            .copied()
            .expect("INTERNAL: optional must have non-nil variant");
        let inner_cr_type = type_id_to_cranelift(inner_type_id, self.arena(), self.ptr_type());

        let inner_size = self.type_size(inner_type_id);
        let inner_val = if inner_size > 0 {
            self.builder.ins().load(
                inner_cr_type,
                MemFlags::new(),
                ptr,
                union_layout::PAYLOAD_OFFSET,
            )
        } else {
            self.iconst_cached(inner_cr_type, 0)
        };

        let inner_compiled = CompiledValue::new(inner_val, inner_cr_type, inner_type_id);
        let some_str = self.apply_string_conversion(inner_compiled, inner_conversion)?;
        self.builder.ins().jump(merge_block, &[some_str.into()]);

        self.switch_to_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Convert a general union value to string.
    ///
    /// Branches on the tag for each variant, applies the sema-annotated
    /// conversion for each, then merges results.
    fn union_to_string(
        &mut self,
        ptr: Value,
        variants: &[(TypeId, StringConversion)],
    ) -> CodegenResult<Value> {
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, self.ptr_type());

        let variant_blocks: Vec<_> = (0..variants.len())
            .map(|_| self.builder.create_block())
            .collect();

        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);

        // Chain of brif checks for each variant
        for (i, &block) in variant_blocks.iter().enumerate() {
            if i == variants.len() - 1 {
                self.builder.ins().jump(block, &[]);
            } else {
                let expected = self.iconst_cached(types::I8, i as i64);
                let is_match = self.builder.ins().icmp(IntCC::Equal, tag, expected);
                let next_check = self.builder.create_block();
                self.emit_brif(is_match, block, next_check);
                self.switch_to_block(next_check);
            }
        }

        // For each variant block, extract payload and apply annotated conversion
        for (i, &block) in variant_blocks.iter().enumerate() {
            self.switch_to_block(block);
            let (variant_type_id, ref conv) = variants[i];
            let inner_cr_type =
                type_id_to_cranelift(variant_type_id, self.arena(), self.ptr_type());
            let inner_size = self.type_size(variant_type_id);

            let inner_val = if inner_size > 0 {
                self.builder.ins().load(
                    inner_cr_type,
                    MemFlags::new(),
                    ptr,
                    union_layout::PAYLOAD_OFFSET,
                )
            } else {
                self.iconst_cached(inner_cr_type, 0)
            };

            let inner_compiled = CompiledValue::new(inner_val, inner_cr_type, variant_type_id);
            let str_val = self.apply_string_conversion(inner_compiled, conv)?;
            self.builder.ins().jump(merge_block, &[str_val.into()]);
        }

        self.switch_to_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }
}
