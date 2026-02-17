// calls/string_ops.rs
//
// String operation codegen: string literals, interpolation, value-to-string conversion.

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{DataDescription, Linkage, Module};

use vole_frontend::ast::StringPart;
use vole_sema::type_arena::TypeId;

use crate::errors::{CodegenError, CodegenResult};
use crate::function_registry::FunctionRegistry;
use crate::types::{CompiledValue, type_id_to_cranelift};
use crate::union_layout;

use super::super::RuntimeKey;
use super::super::context::Cg;

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
                    if compiled.type_id == TypeId::STRING {
                        (compiled.value, compiled.is_owned())
                    } else {
                        (self.value_to_string(compiled)?, true)
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

    /// Convert a value to a string
    pub(super) fn value_to_string(&mut self, val: CompiledValue) -> CodegenResult<Value> {
        if val.type_id == TypeId::STRING {
            return Ok(val.value);
        }

        // Handle arrays
        if self.arena().is_array(val.type_id) {
            return self.call_runtime(RuntimeKey::ArrayI64ToString, &[val.value]);
        }

        // Handle nil type directly
        if val.type_id.is_nil() {
            return self.call_runtime(RuntimeKey::NilToString, &[]);
        }

        // Handle optionals (unions with nil variant)
        if let Some(nil_idx) = self.find_nil_variant(val.type_id) {
            let arena = self.arena();
            if let Some(variants) = arena.unwrap_union(val.type_id) {
                let variants_vec: Vec<TypeId> = variants.to_vec();
                return self.optional_to_string_by_id(val.value, &variants_vec, nil_idx);
            }
        }

        // Handle general union types (non-optional, e.g. bool | i64)
        {
            let arena = self.arena();
            if let Some(variants) = arena.unwrap_union(val.type_id) {
                let variants_vec: Vec<TypeId> = variants.to_vec();
                return self.union_to_string(val.value, &variants_vec);
            }
        }

        let (runtime, call_val) = if val.ty == types::F64 {
            (RuntimeKey::F64ToString, val.value)
        } else if val.ty == types::F32 {
            (RuntimeKey::F32ToString, val.value)
        } else if val.ty == types::F128 {
            let bits = self
                .builder
                .ins()
                .bitcast(types::I128, MemFlags::new(), val.value);
            (RuntimeKey::F128ToString, bits)
        } else if val.ty == types::I128 {
            (RuntimeKey::I128ToString, val.value)
        } else if val.ty == types::I8 {
            (RuntimeKey::BoolToString, val.value)
        } else {
            let extended = if val.ty.is_int() && val.ty != types::I64 {
                self.builder.ins().sextend(types::I64, val.value)
            } else {
                val.value
            };
            (RuntimeKey::I64ToString, extended)
        };

        self.call_runtime(runtime, &[call_val])
    }

    /// Convert an optional (union with nil) to string using TypeId variants
    fn optional_to_string_by_id(
        &mut self,
        ptr: Value,
        variants: &[TypeId],
        nil_idx: usize,
    ) -> CodegenResult<Value> {
        // Check if the tag equals nil
        let is_nil = self.tag_eq(ptr, nil_idx as i64);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let some_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Add block param for the result string
        self.builder
            .append_block_param(merge_block, self.ptr_type());

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], some_block, &[]);

        // Nil case: return "nil"
        self.builder.switch_to_block(nil_block);
        let nil_str = self.call_runtime(RuntimeKey::NilToString, &[])?;
        self.builder.ins().jump(merge_block, &[nil_str.into()]);

        // Some case: extract inner value and convert to string
        self.builder.switch_to_block(some_block);
        // Find the non-nil variant using arena
        let arena = self.arena();
        let inner_type_id = variants
            .iter()
            .find(|&&v| !arena.is_nil(v))
            .copied()
            .expect("INTERNAL: non-sentinel union must have non-nil variant");
        let inner_cr_type = type_id_to_cranelift(inner_type_id, arena, self.ptr_type());

        // Only load payload if inner type has data (non-zero size).
        // Sentinel-only unions have no payload bytes allocated at offset 8.
        let inner_size = self.type_size(inner_type_id);
        let inner_val = if inner_size > 0 {
            self.builder.ins().load(
                inner_cr_type,
                MemFlags::new(),
                ptr,
                union_layout::PAYLOAD_OFFSET,
            )
        } else {
            self.builder.ins().iconst(inner_cr_type, 0)
        };

        let inner_compiled = CompiledValue::new(inner_val, inner_cr_type, inner_type_id);
        let some_str = self.value_to_string(inner_compiled)?;
        self.builder.ins().jump(merge_block, &[some_str.into()]);

        // Merge and return result
        self.builder.switch_to_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Convert a general (non-optional) union value to string.
    /// Loads the tag, branches on each variant, converts each to string, then merges.
    fn union_to_string(&mut self, ptr: Value, variants: &[TypeId]) -> CodegenResult<Value> {
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, self.ptr_type());

        // For each variant, create a block that extracts and converts
        let mut variant_blocks: Vec<_> = Vec::new();
        for _ in variants {
            variant_blocks.push(self.builder.create_block());
        }
        // Load the tag
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);

        // Chain of brif checks for each variant
        for (i, &block) in variant_blocks.iter().enumerate() {
            if i == variants.len() - 1 {
                // Last variant: unconditional jump
                self.builder.ins().jump(block, &[]);
            } else {
                let expected = self.builder.ins().iconst(types::I8, i as i64);
                let is_match = self.builder.ins().icmp(IntCC::Equal, tag, expected);
                let next_check = self.builder.create_block();
                self.builder
                    .ins()
                    .brif(is_match, block, &[], next_check, &[]);
                self.builder.switch_to_block(next_check);
            }
        }

        // For each variant block, extract the payload and convert to string
        for (i, &block) in variant_blocks.iter().enumerate() {
            self.builder.switch_to_block(block);
            let variant_type_id = variants[i];
            let arena = self.arena();
            let inner_cr_type = type_id_to_cranelift(variant_type_id, arena, self.ptr_type());
            let inner_size = self.type_size(variant_type_id);

            let inner_val = if inner_size > 0 {
                self.builder.ins().load(
                    inner_cr_type,
                    MemFlags::new(),
                    ptr,
                    union_layout::PAYLOAD_OFFSET,
                )
            } else {
                self.builder.ins().iconst(inner_cr_type, 0)
            };

            let inner_compiled = CompiledValue::new(inner_val, inner_cr_type, variant_type_id);
            let str_val = self.value_to_string(inner_compiled)?;
            self.builder.ins().jump(merge_block, &[str_val.into()]);
        }

        self.builder.switch_to_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }
}
