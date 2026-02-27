// src/codegen/expr/mod.rs
//
// Expression compilation - impl Cg methods.
// The main expr() router lives here; specific expression categories are in sub-modules.

mod as_cast;
mod control_flow;
mod error_patterns;
mod field_ops;
mod indexing;
mod literal;
mod null_ops;
mod pattern_match;
mod unary_assign;
mod vir_calls;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};
use smallvec::smallvec;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;

use vole_frontend::{BinaryOp, Symbol};
use vole_identity::{ModuleId, TypeDefId, VirTypeId};
use vole_sema::type_arena::TypeId;
use vole_vir::{
    AsCastKind, CoerceKind, IsCheckResult, VirBinOp, VirExpr, VirMetaKind, VirStringPart, VirUnOp,
};

use super::context::Cg;
use super::types::{CompiledValue, RcLifecycle, type_id_to_cranelift};

impl Cg<'_, '_, '_> {
    /// Best-effort VIR type extraction for an expression node.
    ///
    /// Used by VIR `is` checks when sema `TypeId` mapping is lossy.
    fn vir_expr_type_id(expr: &VirExpr) -> Option<VirTypeId> {
        match expr {
            VirExpr::IntLiteral { vir_ty, .. }
            | VirExpr::WideLiteral { vir_ty, .. }
            | VirExpr::FloatLiteral { vir_ty, .. }
            | VirExpr::Import { vir_ty, .. }
            | VirExpr::ArrayLiteral { vir_ty, .. }
            | VirExpr::RepeatLiteral { vir_ty, .. }
            | VirExpr::StructLiteral { vir_ty, .. }
            | VirExpr::ClassInstance { vir_ty, .. }
            | VirExpr::BinaryOp { vir_ty, .. }
            | VirExpr::UnaryOp { vir_ty, .. }
            | VirExpr::Call { vir_ty, .. }
            | VirExpr::MethodCall { vir_ty, .. }
            | VirExpr::FieldLoad { vir_ty, .. }
            | VirExpr::Index { vir_ty, .. }
            | VirExpr::If { vir_ty, .. }
            | VirExpr::Block { vir_ty, .. }
            | VirExpr::Match { vir_ty, .. }
            | VirExpr::IsCheck { vir_ty, .. }
            | VirExpr::MetaAccess { vir_ty, .. }
            | VirExpr::LocalLoad { vir_ty, .. }
            | VirExpr::NullCoalesce { vir_ty, .. }
            | VirExpr::OptionalChain { vir_ty, .. }
            | VirExpr::OptionalMethodCall { vir_ty, .. }
            | VirExpr::Lambda { vir_ty, .. } => Some(*vir_ty),
            VirExpr::AsCast { vir_target_ty, .. } => Some(*vir_target_ty),
            VirExpr::Try {
                vir_success_type, ..
            } => Some(*vir_success_type),
            VirExpr::Coerce { vir_to, .. } => Some(*vir_to),
            VirExpr::BoolLiteral(_) => Some(VirTypeId::BOOL),
            VirExpr::StringLiteral(_) => Some(VirTypeId::STRING),
            VirExpr::NilLiteral => Some(VirTypeId::NIL),
            VirExpr::Range { .. } => Some(VirTypeId::RANGE),
            VirExpr::TypeLiteral => Some(VirTypeId::METATYPE),
            VirExpr::Unreachable { .. } => Some(VirTypeId::NEVER),
            VirExpr::RcInc { value } | VirExpr::RcDec { value } | VirExpr::RcMove { value } => {
                Self::vir_expr_type_id(value)
            }
            VirExpr::StringConcat { .. }
            | VirExpr::InterpolatedString { .. }
            | VirExpr::FieldStore { .. }
            | VirExpr::IndexStore { .. }
            | VirExpr::LocalStore { .. }
            | VirExpr::Yield { .. } => None,
        }
    }

    /// Compile a module binding value (from destructuring import).
    /// Returns the constant value for constants, or an error for functions.
    fn module_binding_value(
        &mut self,
        module_id: ModuleId,
        export_name: Symbol,
        export_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let export_name_str = self.interner().resolve(export_name);
        let module_path = self.name_table().module_path(module_id).to_string();

        // Get the name_id for this export
        let name_id = crate::types::module_name_id(self.analyzed(), module_id, export_name_str);

        // Look up constant value in module metadata
        let const_val = {
            let arena = self.arena();
            name_id.and_then(|nid| {
                arena
                    .module_metadata(module_id)
                    .and_then(|meta| meta.constants.get(&nid).cloned())
            })
        };

        if let Some(const_val) = const_val {
            let arena = self.arena();
            let f64_id = arena.f64();
            let i64_id = arena.i64();
            let bool_id = arena.bool();
            match const_val {
                vole_sema::types::ConstantValue::F64(v) => {
                    let val = self.builder.ins().f64const(v);
                    Ok(CompiledValue::new(val, types::F64, f64_id))
                }
                vole_sema::types::ConstantValue::I64(v) => {
                    let val = self.iconst_cached(types::I64, v);
                    Ok(CompiledValue::new(val, types::I64, i64_id))
                }
                vole_sema::types::ConstantValue::Bool(v) => {
                    let val = self.iconst_cached(types::I8, if v { 1 } else { 0 });
                    Ok(CompiledValue::new(val, types::I8, bool_id))
                }
                vole_sema::types::ConstantValue::String(s) => self.string_literal(&s),
            }
        } else if self.arena().is_function(export_type_id) {
            // Functions cannot be used as values directly - must be called
            Err(CodegenError::unsupported_with_context(
                "function as value",
                format!("use {}() to call the function", export_name_str),
            ))
        } else if self.arena().is_sentinel(export_type_id) {
            // Sentinel exports are zero-field structs - emit i8(0)
            let value = self.iconst_cached(types::I8, 0);
            Ok(CompiledValue::new(value, types::I8, export_type_id))
        } else {
            Err(CodegenError::not_found(
                "module export constant",
                format!("{}.{}", module_path, export_name_str),
            ))
        }
    }

    // =========================================================================
    // Function reference / closure wrapper
    // =========================================================================

    /// Create a closure wrapper function that adapts a regular function to closure
    /// calling convention. The wrapper takes (closure_ptr, params...) and calls
    /// the original function with just (params...).
    fn create_closure_wrapper(
        &mut self,
        orig_func_id: FuncId,
        param_ids: &[TypeId],
        return_type_id: TypeId,
    ) -> CodegenResult<FuncId> {
        use cranelift::prelude::FunctionBuilderContext;

        let wrapper_index = self.next_lambda_id();

        // Build wrapper signature: (closure_ptr, params...) -> return_type
        let param_types = self.cranelift_types(param_ids);
        let return_cr_type = self.cranelift_type(return_type_id);
        let is_void_return = self.arena().is_void(return_type_id);

        let mut wrapper_sig = self.jit_module().make_signature();
        wrapper_sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr (ignored)
        for &param_ty in &param_types {
            wrapper_sig.params.push(AbiParam::new(param_ty));
        }
        if !is_void_return {
            wrapper_sig.returns.push(AbiParam::new(return_cr_type));
        }

        // Create wrapper function
        let wrapper_func_key = self.funcs().intern_lambda(wrapper_index);
        let wrapper_name = self.funcs().display(wrapper_func_key);
        let wrapper_func_id = self
            .jit_module()
            .declare_function(
                &wrapper_name,
                cranelift_module::Linkage::Local,
                &wrapper_sig,
            )
            .map_err(CodegenError::cranelift)?;

        self.funcs().set_func_id(wrapper_func_key, wrapper_func_id);
        self.funcs()
            .set_return_type(wrapper_func_key, return_type_id);

        // Build the wrapper function body
        let mut wrapper_ctx = self.jit_module().make_context();
        wrapper_ctx.func.signature = wrapper_sig.clone();

        {
            let mut wrapper_builder_ctx = FunctionBuilderContext::new();
            let mut wrapper_builder =
                FunctionBuilder::new(&mut wrapper_ctx.func, &mut wrapper_builder_ctx);

            let entry_block = wrapper_builder.create_block();
            wrapper_builder.append_block_params_for_function_params(entry_block);
            wrapper_builder.switch_to_block(entry_block);

            let block_params = wrapper_builder.block_params(entry_block).to_vec();
            // block_params[0] is closure_ptr (ignored), block_params[1..] are the actual arguments

            // Get reference to original function
            let orig_func_ref = self
                .jit_module()
                .declare_func_in_func(orig_func_id, wrapper_builder.func);

            // Call original function with just the arguments (skip closure_ptr)
            let call_args: Vec<Value> = block_params[1..].to_vec();
            let call_inst = wrapper_builder.ins().call(orig_func_ref, &call_args);
            let results = wrapper_builder.inst_results(call_inst).to_vec();

            if results.is_empty() {
                wrapper_builder.ins().return_(&[]);
            } else {
                wrapper_builder.ins().return_(&[results[0]]);
            }

            wrapper_builder.seal_all_blocks();
            wrapper_builder.finalize();
        }

        self.jit_module()
            .define_function(wrapper_func_id, &mut wrapper_ctx)
            .map_err(CodegenError::cranelift)?;

        Ok(wrapper_func_id)
    }

    /// Compile a reference to a named function, wrapping it in a closure struct.
    /// Creates a wrapper function that adapts the function to the closure calling convention.
    fn function_reference(
        &mut self,
        sym: Symbol,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Look up the original function's FuncId using the name table
        let module_id = self
            .current_module_id()
            .unwrap_or(self.env.analyzed.module_id());
        let name_id = self.analyzed().function_name_id(module_id, sym);

        let orig_func_key = self.funcs().intern_name_id(name_id);
        let orig_func_id = self.funcs().func_id(orig_func_key).ok_or_else(|| {
            CodegenError::not_found("function id for", self.interner().resolve(sym))
        })?;

        // Unwrap function type to get params and return type
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _is_closure) =
                arena.unwrap_function(func_type_id).ok_or_else(|| {
                    CodegenError::type_mismatch("closure wrapper", "function type", "non-function")
                })?;
            (params.clone(), ret)
        };

        let wrapper_func_id =
            self.create_closure_wrapper(orig_func_id, &param_ids, return_type_id)?;

        // Get the wrapper function address
        let wrapper_func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let ptr_type = self.ptr_type();
        let wrapper_func_addr = self.builder.ins().func_addr(ptr_type, wrapper_func_ref);

        // Wrap in a closure struct with zero captures
        let alloc_ref = self.runtime_func_ref(RuntimeKey::ClosureAlloc)?;
        let zero_captures = self.iconst_cached(types::I64, 0);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[wrapper_func_addr, zero_captures]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        // Use closure type from sema (already has is_closure: true).
        // Mark as Owned: the closure allocation is a fresh +1 reference that
        // must be rc_dec'd when it goes out of scope or is consumed as an arg.
        let cv = CompiledValue::new(closure_ptr, self.ptr_type(), func_type_id);
        Ok(self.mark_rc_owned(cv))
    }

    // =========================================================================
    // Generator yield
    // =========================================================================

    /// Compile a VIR yield expression inside a generator body.
    fn compile_vir_yield(&mut self, value: &VirExpr) -> CodegenResult<CompiledValue> {
        let yielder_var = self.yielder_var.ok_or_else(|| {
            CodegenError::unsupported("yield expression outside generator context")
        })?;

        // Compile the yielded value
        let compiled = self.compile_vir_expr(value)?;

        // Load the yielder pointer
        let yielder_ptr = self.builder.use_var(yielder_var);

        // Call vole_generator_yield(yielder_ptr, value)
        self.call_runtime_void(RuntimeKey::GeneratorYield, &[yielder_ptr, compiled.value])?;

        // Yield is a statement-like expression; return a void/zero value.
        Ok(CompiledValue::new(
            self.iconst_cached(types::I64, 0),
            types::I64,
            TypeId::I64,
        ))
    }

    /// Compile a VIR expression with an expected target type hint.
    ///
    /// Used by typed binding/field contexts to keep array/repeat literal
    /// element lowering aligned with the destination type when VIR expression
    /// type metadata degrades during migration.
    pub(crate) fn compile_vir_expr_with_expected_type(
        &mut self,
        expr: &VirExpr,
        expected_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        if (self.arena().is_array(expected_type_id)
            || self.arena().unwrap_tuple(expected_type_id).is_some()
            || self.arena().unwrap_fixed_array(expected_type_id).is_some())
            && let VirExpr::ArrayLiteral { elements, .. } = expr
        {
            let result = self.compile_vir_array_literal(elements, expected_type_id)?;
            return Ok(self.mark_rc_owned(result));
        }
        if self.arena().unwrap_fixed_array(expected_type_id).is_some()
            && let VirExpr::RepeatLiteral { element, count, .. } = expr
        {
            let result = self.compile_vir_repeat_literal(element, *count, expected_type_id)?;
            return Ok(self.mark_rc_owned(result));
        }
        self.compile_vir_expr(expr)
    }

    // =========================================================================
    // VIR expression compilation
    // =========================================================================

    /// Compile a VIR expression node.
    ///
    /// All VIR variants are handled directly.  A few (`MethodCall`,
    /// `OptionalMethodCall`) delegate to existing AST-based methods for
    /// dispatch logic that has not yet been fully migrated.
    #[deny(clippy::wildcard_enum_match_arm)]
    pub fn compile_vir_expr(&mut self, vir_expr: &VirExpr) -> CodegenResult<CompiledValue> {
        let result = match vir_expr {
            // -- Lowered literals -----------------------------------------
            VirExpr::IntLiteral { value, vir_ty, .. } => Ok(self.vir_int_const(*value, *vir_ty)),
            VirExpr::WideLiteral {
                low, high, vir_ty, ..
            } => Ok(self.vir_wide_literal_const(*low, *high, *vir_ty)),
            VirExpr::FloatLiteral { value, vir_ty, .. } => {
                Ok(self.vir_float_const(*value, *vir_ty))
            }
            VirExpr::BoolLiteral(b) => Ok(self.bool_const(*b)),
            VirExpr::StringLiteral(sym) => {
                let s = self.interner().resolve(*sym).to_string();
                self.string_literal(&s)
            }
            VirExpr::NilLiteral => {
                let value = self.iconst_cached(types::I8, 0);
                Ok(CompiledValue::new(value, types::I8, TypeId::NIL))
            }

            // -- Simple expressions -----------------------------------------
            VirExpr::Unreachable { line } => self.unreachable_expr(*line),
            VirExpr::Import { ty, vir_ty } => {
                // Module types don't round-trip through vir_to_sema losslessly,
                // so read the sema-encoded `ty` for backward compat.
                let type_id = if *ty == VirTypeId::UNKNOWN {
                    TypeId::I64
                } else {
                    self.sema_type_from_vir(*ty)
                };
                Ok(
                    CompiledValue::new(self.iconst_cached(types::I64, 0), types::I64, type_id)
                        .with_vir_type(*vir_ty),
                )
            }
            VirExpr::TypeLiteral => Err(CodegenError::unsupported(
                "type expressions as runtime values",
            )),
            VirExpr::Range {
                start,
                end,
                inclusive,
            } => self.compile_vir_range(start, end, *inclusive),

            // -- Operators ------------------------------------------------
            VirExpr::BinaryOp {
                op, lhs, rhs, line, ..
            } => self.compile_vir_binary_op(*op, lhs, rhs, *line),
            VirExpr::UnaryOp { op, operand, .. } => self.compile_vir_unary_op(*op, operand),
            VirExpr::StringConcat { parts } => self.compile_vir_string_concat(parts),
            VirExpr::InterpolatedString { parts } => self.compile_vir_interpolated_string(parts),

            // -- Coercion -------------------------------------------------
            VirExpr::Coerce {
                value,
                to,
                kind,
                vir_from,
                vir_to,
                ..
            } => {
                let compiled = self.compile_vir_expr(value)?;
                self.compile_vir_coerce(
                    compiled,
                    self.sema_type_from_vir(*to),
                    *vir_from,
                    *vir_to,
                    *kind,
                )
            }

            // -- Calls ----------------------------------------------------
            VirExpr::Call {
                target, args, ty, ..
            } => self.compile_vir_call(target, args, self.sema_type_from_vir(*ty)),
            VirExpr::MethodCall {
                receiver,
                method,
                args,
                dispatch,
                node_id,
                ty: _,
                ..
            } => {
                use crate::structs::methods::MethodCallSource;
                let src = MethodCallSource {
                    receiver,
                    method: *method,
                    args,
                };
                let result = self.method_call(&src, *node_id, dispatch)?;
                Ok(self.mark_rc_owned(result))
            }

            // -- Control flow ---------------------------------------------
            VirExpr::If {
                cond,
                then_body,
                else_body,
                ty,
                ..
            } => self.compile_vir_if(
                cond,
                then_body,
                else_body.as_ref(),
                self.sema_type_from_vir(*ty),
            ),

            VirExpr::Block {
                stmts,
                trailing,
                ty: _,
                ..
            } => self.compile_vir_block(stmts, trailing.as_deref()),

            // -- Pattern match ------------------------------------------------
            VirExpr::Match {
                scrutinee,
                arms,
                ty,
                ..
            } => self.compile_vir_match(scrutinee, arms, self.sema_type_from_vir(*ty)),

            // -- Construction -------------------------------------------------
            VirExpr::ArrayLiteral { elements, ty, .. } => {
                let result =
                    self.compile_vir_array_literal(elements, self.sema_type_from_vir(*ty))?;
                Ok(self.mark_rc_owned(result))
            }
            VirExpr::RepeatLiteral {
                element, count, ty, ..
            } => {
                let result =
                    self.compile_vir_repeat_literal(element, *count, self.sema_type_from_vir(*ty))?;
                Ok(self.mark_rc_owned(result))
            }
            VirExpr::StructLiteral {
                type_def,
                fields,
                ty,
                ..
            } => {
                let result = self.compile_vir_struct_literal(
                    *type_def,
                    fields,
                    self.sema_type_from_vir(*ty),
                )?;
                Ok(self.mark_rc_owned(result))
            }
            VirExpr::ClassInstance {
                type_def,
                fields,
                ty,
                ..
            } => {
                let result = self.compile_vir_class_instance(
                    *type_def,
                    fields,
                    self.sema_type_from_vir(*ty),
                )?;
                Ok(self.mark_rc_owned(result))
            }

            // -- Field access -------------------------------------------------
            VirExpr::FieldLoad { object, field, .. } => self.compile_vir_field_load(object, *field),
            VirExpr::FieldStore {
                object,
                field,
                storage: _,
                value,
            } => self.compile_vir_field_store(object, *field, value),

            // -- Indexing ------------------------------------------------------
            VirExpr::Index {
                object,
                index,
                ty,
                union_storage,
                ..
            } => {
                self.compile_vir_index(object, index, self.sema_type_from_vir(*ty), *union_storage)
            }
            VirExpr::IndexStore {
                object,
                index,
                value,
                union_storage,
            } => self.compile_vir_index_store(object, index, value, *union_storage),

            // -- RC operations ------------------------------------------------
            VirExpr::RcInc { value } => {
                let compiled = self.compile_vir_expr(value)?;
                self.emit_rc_inc(compiled.value)?;
                Ok(compiled)
            }
            VirExpr::RcDec { value } => {
                let compiled = self.compile_vir_expr(value)?;
                self.emit_rc_dec(compiled.value)?;
                Ok(compiled)
            }
            VirExpr::RcMove { value } => {
                // Ownership transfer marker — no runtime effect, just pass through.
                self.compile_vir_expr(value)
            }

            // -- Type operations ------------------------------------------
            VirExpr::IsCheck {
                value,
                result,
                ty: _,
                ..
            } => self.compile_vir_is_check(value, *result),
            VirExpr::AsCast {
                value,
                target_ty,
                kind,
                result,
                ..
            } => {
                self.compile_vir_as_cast(value, self.sema_type_from_vir(*target_ty), *kind, *result)
            }

            // -- Reflection ---------------------------------------------------
            VirExpr::MetaAccess { kind, ty, .. } => {
                self.compile_vir_meta_access(kind, self.sema_type_from_vir(*ty))
            }

            // -- Variables ------------------------------------------------
            VirExpr::LocalLoad { name, ty, .. } => {
                self.compile_local_load(*name, self.sema_type_from_vir(*ty))
            }
            VirExpr::LocalStore { name, value } => self.compile_local_store(*name, value),

            // -- Null / optional operations --------------------------------
            VirExpr::NullCoalesce {
                value,
                default,
                inner_type,
                ..
            } => {
                self.compile_vir_null_coalesce(value, default, self.sema_type_from_vir(*inner_type))
            }
            VirExpr::OptionalChain {
                object,
                field,
                inner_type,
                ty,
                ..
            } => self.compile_vir_optional_chain(
                object,
                *field,
                self.sema_type_from_vir(*inner_type),
                self.sema_type_from_vir(*ty),
            ),
            VirExpr::OptionalMethodCall {
                object,
                method,
                method_args,
                dispatch,
                call_node_id,
                inner_type,
                ty,
                ..
            } => self.compile_vir_optional_method_call(null_ops::VirOptionalMethodCallArgs {
                object_expr: object,
                method: *method,
                method_args,
                dispatch,
                call_node_id: *call_node_id,
                inner_type_id: self.sema_type_from_vir(*inner_type),
                result_type_id: self.sema_type_from_vir(*ty),
            }),
            VirExpr::Try {
                value,
                success_type,
                ..
            } => self.compile_vir_try(value, self.sema_type_from_vir(*success_type)),

            // -- Lambda / closure ------------------------------------------
            VirExpr::Lambda {
                params,
                body,
                captures,
                ty,
                ..
            } => {
                let result =
                    self.compile_vir_lambda(params, body, captures, self.sema_type_from_vir(*ty))?;
                Ok(self.mark_rc_owned(result))
            }

            // -- Generator ------------------------------------------------
            VirExpr::Yield { value } => self.compile_vir_yield(value),
        };
        // Annotate the result with the proper VIR type ID from the expression
        // node so downstream consumers can use VirTypeTable instead of arena.
        result.map(|mut cv| {
            if let Some(vir_ty) = Self::vir_expr_type_id(vir_expr) {
                cv.vir_type_id = vir_ty;
            }
            cv
        })
    }

    /// Compile a VIR binary operation by delegating to `binary_op()`.
    ///
    /// Converts `VirBinOp` back to the AST `BinaryOp` and calls the existing
    /// `binary_op()` method which handles type promotion and Cranelift emission.
    fn compile_vir_binary_op(
        &mut self,
        op: VirBinOp,
        lhs: &VirExpr,
        rhs: &VirExpr,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let left = self.compile_vir_expr(lhs)?;
        let right = self.compile_vir_expr(rhs)?;
        let ast_op = vir_binop_to_ast(op);
        if ast_op == BinaryOp::Add && left.type_id == TypeId::STRING {
            return self.string_concat(left, right);
        }
        self.binary_op(left, right, ast_op, line)
    }

    /// Compile a VIR unary operation.
    ///
    /// Compiles the operand via `compile_vir_expr`, then delegates to
    /// `emit_unary_op` which handles the Cranelift emission directly.
    fn compile_vir_unary_op(
        &mut self,
        op: VirUnOp,
        operand: &VirExpr,
    ) -> CodegenResult<CompiledValue> {
        let compiled = self.compile_vir_expr(operand)?;
        let ast_op = vir_unop_to_ast(op);
        self.emit_unary_op(ast_op, compiled)
    }

    /// Emit a unary operation on an already-compiled value.
    fn emit_unary_op(
        &mut self,
        op: vole_frontend::UnaryOp,
        operand: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        use crate::ops::try_constant_value;
        use vole_frontend::UnaryOp;

        let result = match op {
            UnaryOp::Neg => {
                if operand.ty == types::F128 {
                    let bits = self.call_runtime(RuntimeKey::F128Neg, &[operand.value])?;
                    self.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), bits)
                } else if operand.ty.is_float() {
                    self.builder.ins().fneg(operand.value)
                } else if let Some(c) = try_constant_value(self.builder.func, operand.value) {
                    self.iconst_cached(operand.ty, -c)
                } else {
                    self.builder.ins().ineg(operand.value)
                }
            }
            UnaryOp::Not => {
                let op_val = if operand.ty != types::I8 {
                    self.builder.ins().ireduce(types::I8, operand.value)
                } else {
                    operand.value
                };
                if let Some(c) = try_constant_value(self.builder.func, op_val) {
                    self.iconst_cached(types::I8, if c == 0 { 1 } else { 0 })
                } else {
                    let one = self.iconst_cached(types::I8, 1);
                    self.builder.ins().isub(one, op_val)
                }
            }
            UnaryOp::BitNot => self.builder.ins().bnot(operand.value),
        };
        Ok(operand.with_value(result))
    }

    /// Compile a VIR `StringConcat` by delegating to the existing
    /// `string_concat()` method.
    fn compile_vir_string_concat(
        &mut self,
        parts: &[vole_vir::VirRef],
    ) -> CodegenResult<CompiledValue> {
        debug_assert!(
            parts.len() >= 2,
            "StringConcat should have at least 2 parts"
        );
        let left = self.compile_vir_expr(&parts[0])?;
        let right = self.compile_vir_expr(&parts[1])?;
        self.string_concat(left, right)
    }

    /// Compile a VIR `InterpolatedString`.
    ///
    /// Each part is either a literal (compiled as a static string) or an
    /// expression with a `StringConversion` annotation.  Single-part
    /// interpolations preserve the borrowed/owned lifecycle of the original
    /// expression.  Multi-part interpolations use StringBuilder for a
    /// single allocation.
    fn compile_vir_interpolated_string(
        &mut self,
        parts: &[VirStringPart],
    ) -> CodegenResult<CompiledValue> {
        if parts.is_empty() {
            return self.string_literal("");
        }

        // Collect all string values and track which are owned for cleanup.
        let mut string_values: Vec<Value> = Vec::new();
        let mut owned_flags: Vec<bool> = Vec::new();
        for part in parts {
            let (str_val, is_owned) = match part {
                VirStringPart::Literal(sym) => {
                    let s = self.interner().resolve(*sym).to_string();
                    (self.string_literal(&s)?.value, true)
                }
                VirStringPart::Expr { value, conversion } => {
                    let compiled = self.compile_vir_expr(value)?;
                    #[allow(clippy::wildcard_enum_match_arm)] // sema enum, not VIR dispatch
                    match conversion {
                        vole_sema::StringConversion::Identity => {
                            (compiled.value, compiled.is_owned())
                        }
                        _ => (self.apply_string_conversion(compiled, conversion)?, true),
                    }
                }
            };
            string_values.push(str_val);
            owned_flags.push(is_owned);
        }

        // Single part: return directly, preserving borrowed/owned lifecycle.
        if string_values.len() == 1 {
            let mut cv = self.string_temp(string_values[0]);
            if !owned_flags[0] {
                cv.mark_borrowed();
            }
            return Ok(cv);
        }

        // Multi-part: use StringBuilder for a single allocation.
        let sb = self.call_runtime(RuntimeKey::SbNew, &[])?;
        for &sv in &string_values {
            self.call_runtime_void(RuntimeKey::SbPushString, &[sb, sv])?;
        }
        let result = self.call_runtime(RuntimeKey::SbFinish, &[sb])?;

        // Free owned input parts — builder has copied the bytes.
        for (val, is_owned) in string_values.iter().zip(owned_flags.iter()) {
            if *is_owned {
                self.emit_rc_dec(*val)?;
            }
        }

        Ok(self.string_temp(result))
    }

    /// Compile a VIR type coercion.
    ///
    /// Dispatches on `CoerceKind` to emit the appropriate Cranelift
    /// instructions for numeric conversions, interface boxing/unboxing,
    /// and iterator wrapping.
    fn compile_vir_coerce(
        &mut self,
        value: CompiledValue,
        to: TypeId,
        vir_from: VirTypeId,
        vir_to: VirTypeId,
        kind: CoerceKind,
    ) -> CodegenResult<CompiledValue> {
        use crate::ops::{sextend_const, uextend_const};
        use crate::types::vir_conversions::{vir_is_unsigned, vir_type_to_cranelift};

        let table = self.vir_type_table();
        let ptr = self.ptr_type();
        let target_ty = vir_type_to_cranelift(vir_to, table, ptr);
        match kind {
            CoerceKind::IntExtend => {
                let result = if vir_is_unsigned(vir_from, table) {
                    uextend_const(self.builder, target_ty, value.value)
                } else {
                    sextend_const(self.builder, target_ty, value.value)
                };
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::IntTruncate => {
                let result = self.builder.ins().ireduce(target_ty, value.value);
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::IntToFloat => {
                let result = if vir_is_unsigned(vir_from, table) {
                    self.builder.ins().fcvt_from_uint(target_ty, value.value)
                } else {
                    self.builder.ins().fcvt_from_sint(target_ty, value.value)
                };
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::FloatToInt => {
                let result = if vir_is_unsigned(vir_to, table) {
                    self.builder.ins().fcvt_to_uint(target_ty, value.value)
                } else {
                    self.builder.ins().fcvt_to_sint(target_ty, value.value)
                };
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::FloatExtend => {
                let result = self.builder.ins().fpromote(target_ty, value.value);
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::FloatTruncate => {
                let result = self.builder.ins().fdemote(target_ty, value.value);
                Ok(CompiledValue::new(result, target_ty, to))
            }
            // Box/Unbox/IteratorWrap still use TypeId (migrated in later tickets)
            CoerceKind::Box => self.compile_coerce_box(value, to),
            CoerceKind::Unbox => self.compile_coerce_unbox(value, to),
            CoerceKind::IteratorWrap => self.compile_coerce_iterator_wrap(value, to),
        }
    }

    /// Box a concrete value as an interface type.
    ///
    /// Allocates `[data_ptr, vtable_ptr]` on the heap and generates the
    /// vtable for the concrete type implementing the interface.  Delegates
    /// to the existing `box_interface_value` infrastructure.
    fn compile_coerce_box(
        &mut self,
        value: CompiledValue,
        interface_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.box_interface_value(value, interface_type_id)
    }

    /// Unbox an interface pointer back to the concrete value.
    ///
    /// Loads the data word at offset 0 from the interface box `[data, vtable]`
    /// and converts it back to the concrete Cranelift type.
    fn compile_coerce_unbox(
        &mut self,
        value: CompiledValue,
        concrete_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let ptr_ty = self.ptr_type();
        let data_word = self
            .builder
            .ins()
            .load(ptr_ty, MemFlags::new(), value.value, 0);
        let concrete_val = self.convert_from_i64_storage(data_word, concrete_type_id);
        let concrete_ty = self.cranelift_type(concrete_type_id);
        Ok(CompiledValue::new(
            concrete_val,
            concrete_ty,
            concrete_type_id,
        ))
    }

    /// Wrap a concrete iterator as a `RuntimeIterator`.
    ///
    /// 1. Extracts the element type from the target `RuntimeIterator(elem)`.
    /// 2. Looks up the `Iterator<elem>` interface type.
    /// 3. Boxes the value as that interface.
    /// 4. Wraps via `InterfaceIter` runtime call.
    /// 5. Consumes the intermediate boxed interface.
    fn compile_coerce_iterator_wrap(
        &mut self,
        value: CompiledValue,
        runtime_iter_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // NOTE: arena() retained — lookup_interface and box_interface_value
        // require sema TypeId.  Remove when iterator boxing uses VirTypeId.
        let elem_type_id = self
            .arena()
            .unwrap_runtime_iterator(runtime_iter_type_id)
            .ok_or_else(|| {
                CodegenError::internal("IteratorWrap target is not a RuntimeIterator type")
            })?;

        // Look up Iterator<elem> interface type
        let iterator_type_def = self
            .name_table()
            .well_known
            .iterator_type_def
            .ok_or_else(|| CodegenError::internal("Iterator type_def not found"))?;
        let interface_type_id = self
            .arena()
            .lookup_interface(iterator_type_def, smallvec![elem_type_id])
            .ok_or_else(|| {
                CodegenError::internal("Iterator<T> interface type not found in arena")
            })?;

        // Box as Iterator<elem> interface
        let mut boxed = self.box_interface_value(value, interface_type_id)?;

        // Wrap via InterfaceIter runtime call
        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[boxed.value])?;

        // Release the intermediate boxed interface (InterfaceIter took its own ref)
        self.consume_rc_value(&mut boxed)?;

        Ok(CompiledValue::owned(
            wrapped,
            types::I64,
            runtime_iter_type_id,
        ))
    }

    /// Compile a VIR `LocalLoad` — variable/identifier lookup.
    ///
    /// Handles four cases in priority order:
    /// 1. **Sentinel types** — if `ty` is a sentinel, emit `i8(0)`.
    /// 2. **Local variables** — look up in `self.vars`, with union narrowing
    ///    and unknown extraction when `ty` differs from the declared type.
    /// 3. **Non-local identifiers** — module bindings, globals, function refs,
    ///    and sentinel fallback are delegated to the full `identifier()` path
    ///    (these will migrate to dedicated VIR nodes later).
    fn compile_local_load(&mut self, sym: Symbol, ty: TypeId) -> CodegenResult<CompiledValue> {
        // 1. Sentinel types — always i8(0).
        // NOTE: arena() retained — no vir_is_sentinel helper yet.
        if self.arena().is_sentinel(ty) {
            let value = self.iconst_cached(types::I8, 0);
            return Ok(CompiledValue::new(value, types::I8, ty));
        }

        // 2. Captured variable — load from closure environment.
        if self.has_captures()
            && let Some(binding) = self.get_capture(&sym).copied()
        {
            return self.load_capture(&binding);
        }

        // 3. Local variable — vars map lookup with narrowing.
        if let Some((var, var_type_id)) = self.vars.get(&sym) {
            return self.compile_local_var_load(*var, *var_type_id, ty);
        }

        // 4. Non-local fallback: module bindings, globals, function refs.
        self.compile_non_local_load(sym, ty)
    }

    /// Load a local variable from the vars map, handling union narrowing,
    /// unknown extraction, and RC lifecycle marking.
    fn compile_local_var_load(
        &mut self,
        var: Variable,
        var_type_id: TypeId,
        narrowed_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let val = self.builder.use_var(var);
        let cl_ty = self.builder.func.dfg.value_type(val);

        // Union narrowing: if VIR type differs from declared type, extract
        // the payload from the tagged union.
        let resolved_union_type_id = self.try_substitute_type(var_type_id);
        let narrowed_type_id = self.try_substitute_type(narrowed_ty);
        if self.vir_query_is_union(resolved_union_type_id)
            && !self.vir_query_is_union(narrowed_type_id)
            && narrowed_type_id != resolved_union_type_id
            && let Some(narrowed_variant) =
                self.find_union_variant(resolved_union_type_id, narrowed_type_id)
        {
            // NOTE: arena() retained for type_id_to_cranelift — needs sema TypeId.
            let payload_ty = type_id_to_cranelift(narrowed_variant, self.arena(), self.ptr_type());
            let payload = self.load_union_payload(val, resolved_union_type_id, payload_ty);
            let mut cv = CompiledValue::new(payload, payload_ty, narrowed_variant);
            self.mark_borrowed_if_rc(&mut cv);
            return Ok(cv);
        }

        // Unknown extraction: if declared type is unknown but VIR type is
        // concrete, extract the value from the TaggedValue.
        if self.vir_query_is_unknown(var_type_id) && !self.vir_query_is_unknown(narrowed_type_id) {
            let raw_value = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                val,
                union_layout::PAYLOAD_OFFSET,
            );
            let extracted = self.extract_unknown_value(raw_value, narrowed_type_id);
            return Ok(extracted);
        }

        // Simple local: no narrowing needed.
        let mut cv = CompiledValue::new(val, cl_ty, var_type_id);
        self.mark_borrowed_if_rc(&mut cv);
        if cv.rc_lifecycle == RcLifecycle::Untracked
            && self.rc_state(var_type_id).union_variants().is_some()
        {
            cv.mark_borrowed();
        }
        Ok(cv)
    }

    /// Find a union variant matching the narrowed type, with integer fallback.
    /// NOTE: arena() retained — unwrap_union returns sema TypeId variants which
    /// are used by load_union_payload and extract_union_payload_typed.
    fn find_union_variant(
        &self,
        union_type_id: TypeId,
        narrowed_type_id: TypeId,
    ) -> Option<TypeId> {
        self.arena()
            .unwrap_union(union_type_id)
            .and_then(|variants| {
                variants
                    .iter()
                    .copied()
                    .find(|&v| v == narrowed_type_id)
                    .or_else(|| {
                        if self.arena().is_integer(narrowed_type_id) {
                            variants
                                .iter()
                                .copied()
                                .find(|&v| self.arena().is_integer(v))
                        } else {
                            None
                        }
                    })
            })
    }

    /// Handle non-local identifier resolution: module bindings, globals,
    /// function references, and sentinel fallback.
    fn compile_non_local_load(&mut self, sym: Symbol, ty: TypeId) -> CodegenResult<CompiledValue> {
        // Module binding
        if let Some(&(module_id, export_name, export_type_id)) = self.lookup_module_binding(&sym) {
            return self.module_binding_value(module_id, export_name, export_type_id);
        }

        if let Some(vir_init) = self.global_vir_init(sym).cloned() {
            let mut value = self.compile_vir_expr(&vir_init)?;
            return self
                .coerce_global_to_declared_type(sym, &mut value)
                .map(|()| value);
        }
        if self.has_global_init(sym) {
            return Err(CodegenError::internal_with_context(
                "missing VIR global initializer",
                self.interner().resolve(sym),
            ));
        }

        // Function reference
        // NOTE: arena() retained — no vir_is_function helper yet.
        if self.arena().is_function(ty) {
            return self.function_reference(sym, ty);
        }

        // Sentinel fallback (name-based resolution)
        let name = self.interner().resolve(sym);
        let module_id = self.current_module.unwrap_or(self.env.analyzed.module_id());
        if let Some(type_def_id) = self.analyzed().resolve_type_def_by_str(module_id, name)
            && self.analyzed().is_sentinel_type(type_def_id)
            && let Some(sentinel_type_id) = self.analyzed().sentinel_base_type(type_def_id)
        {
            let value = self.iconst_cached(types::I8, 0);
            return Ok(CompiledValue::new(value, types::I8, sentinel_type_id));
        }

        Err(CodegenError::not_found(
            "variable",
            self.interner().resolve(sym),
        ))
    }

    /// Coerce a global initializer value to its declared type (if any).
    ///
    /// Looks up the `GlobalDef` via the name table and, when the declared
    /// type differs from the compiled value's type, inserts a coercion
    /// (e.g. boxing to an interface type).
    fn coerce_global_to_declared_type(
        &mut self,
        sym: Symbol,
        value: &mut CompiledValue,
    ) -> CodegenResult<()> {
        let name_table = self.name_table();
        let module_id = self
            .current_module()
            .unwrap_or(self.env.analyzed.module_id());
        if let Some(name_id) = name_table.name_id(module_id, &[sym], self.interner())
            && let Some(global_type_id) = self.analyzed().global_type_id(name_id)
        {
            *value = self.coerce_to_type(*value, global_type_id)?;
        }
        Ok(())
    }

    /// Compile a VIR `LocalStore` — variable assignment.
    ///
    /// Handles simple variable assignment with RC bookkeeping, captured
    /// variable stores, and type coercion.  Field and index assignment
    /// targets are handled by `VirExpr::FieldStore` and `VirExpr::IndexStore`.
    pub(crate) fn compile_local_store(
        &mut self,
        sym: Symbol,
        value_expr: &VirExpr,
    ) -> CodegenResult<CompiledValue> {
        // Snapshot RC state before evaluating the new value.
        let (rc_old, composite_rc_old, union_rc_old) = self.snapshot_rc_for_reassignment(&sym);

        let mut value = self.compile_vir_expr(value_expr)?;

        // Captured variable — store through closure environment.
        if let Some(binding) = self.get_capture(&sym).copied() {
            return self.store_capture(&binding, value);
        }

        let (var, var_type_id) = self
            .vars
            .get(&sym)
            .ok_or_else(|| CodegenError::not_found("variable", self.interner().resolve(sym)))?;
        let var = *var;
        let var_type_id = *var_type_id;

        value = self.coerce_to_type(value, var_type_id)?;

        // RC bookkeeping: inc new if borrowed, store, dec old.
        if rc_old.is_some() && value.is_borrowed() {
            self.emit_rc_inc_for_type(value.value, var_type_id)?;
        }
        self.builder.def_var(var, value.value);
        if let Some(old_val) = rc_old {
            self.emit_rc_dec_for_type(old_val, var_type_id)?;
        }

        // Composite RC: dec each RC field of the old struct.
        if let Some((old_ptr, offsets)) = composite_rc_old {
            for off in &offsets {
                let field_ptr = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), old_ptr, *off);
                self.emit_rc_dec(field_ptr)?;
            }
            self.rc_scopes.update_composite_offsets(var, offsets);
        }

        // Union RC: dec the RC payload of the old union value.
        if let Some((old_ptr, rc_tags)) = union_rc_old {
            self.emit_union_rc_dec(old_ptr, &rc_tags)?;
        }

        value.mark_consumed();
        value.debug_assert_rc_handled("assign to variable");
        Ok(value)
    }

    // =========================================================================
    // VIR MetaAccess
    // =========================================================================

    /// Compile a VIR `MetaAccess` expression (`.@meta`).
    ///
    /// Dispatches on `VirMetaKind`:
    /// - `Static`: builds a cached TypeMeta for the compile-time-known type.
    ///   In monomorphized contexts, re-derives the TypeDefId from the object's
    ///   concrete type to handle stale sema annotations.
    /// - `Dynamic`: loads the meta getter from the interface vtable and calls it.
    /// - `TypeParam`: resolves the type parameter via substitutions, then
    ///   dispatches to the static or dynamic path.
    fn compile_vir_meta_access(
        &mut self,
        kind: &VirMetaKind,
        ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        use crate::reflection::{
            compile_dynamic_meta_from_value, compile_static_meta_with_type,
            resolve_reflection_types,
        };

        let result_ty = if ty == TypeId::UNKNOWN {
            resolve_reflection_types(self)
                .ok()
                .map(|i| i.type_meta_type_id)
                .unwrap_or(TypeId::UNKNOWN)
        } else {
            ty
        };

        match kind {
            VirMetaKind::Static { type_def, object } => {
                let effective_type_def = if self.substitutions.is_some() {
                    self.resolve_vir_static_meta_type_def(object.as_deref())
                        .unwrap_or(*type_def)
                } else {
                    *type_def
                };
                compile_static_meta_with_type(self, effective_type_def, result_ty)
            }
            VirMetaKind::Dynamic { value } => {
                let obj = self.compile_vir_expr(value)?;
                compile_dynamic_meta_from_value(self, obj, result_ty)
            }
            VirMetaKind::TypeParam { name_id, value } => {
                self.compile_vir_type_param_meta(*name_id, value, result_ty)
            }
        }
    }

    /// Re-derive the TypeDefId for a static meta access in a monomorphized context.
    ///
    /// When codegen compiles multiple monomorphizations of a generic function,
    /// sema's `MetaAccessKind::Static` annotation may refer to the wrong TypeDefId
    /// because all monomorphizations share the same NodeId and the last re-analysis
    /// overwrites earlier ones.  This function re-derives the correct TypeDefId
    /// from the object's concrete type in the current codegen scope.
    fn resolve_vir_static_meta_type_def(&self, object: Option<&VirExpr>) -> Option<TypeDefId> {
        let object = object?;
        #[allow(clippy::wildcard_enum_match_arm)] // predicate query, not dispatch
        let object_type_id = match object {
            VirExpr::LocalLoad { name, .. } => self.vars.get(name).map(|(_, ty)| *ty)?,
            _ => return None,
        };
        let type_def_id = self.vir_query_unwrap_nominal(object_type_id)?;
        Some(type_def_id)
    }

    /// Resolve a `TypeParam` meta access by looking up the concrete type from
    /// the current monomorphization substitutions.
    fn compile_vir_type_param_meta(
        &mut self,
        name_id: vole_identity::NameId,
        value: &VirExpr,
        result_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        use crate::reflection::{compile_dynamic_meta_from_value, compile_static_meta_with_type};

        let substitutions = self.substitutions.ok_or_else(|| {
            CodegenError::unsupported(
                "T.@meta requires concrete type (not in a monomorphized context)",
            )
        })?;

        let concrete_type_id = substitutions.get(&name_id).copied().ok_or_else(|| {
            let param_name = self
                .analyzed()
                .last_segment(name_id)
                .unwrap_or_else(|| "?".to_string());
            CodegenError::unsupported_with_context(
                "T.@meta: no substitution for type parameter",
                param_name,
            )
        })?;

        // Interface types require dynamic dispatch via vtable.
        if self.vir_query_is_interface(concrete_type_id) {
            let obj = self.compile_vir_expr(value)?;
            return compile_dynamic_meta_from_value(self, obj, result_ty);
        }

        // Concrete nominal types (class/struct) are resolved statically.
        if let Some(type_def_id) = self.vir_query_unwrap_nominal(concrete_type_id) {
            return compile_static_meta_with_type(self, type_def_id, result_ty);
        }

        // Unsupported concrete type (primitive, array, function, etc.)
        let display = self.vir_query_display_basic(concrete_type_id);
        Err(CodegenError::unsupported_with_context(
            "T.@meta: concrete type does not support reflection",
            display,
        ))
    }

    // =========================================================================
    // VIR IsCheck / AsCast
    // =========================================================================

    /// Compile a VIR `IsCheck` expression.
    ///
    /// The `result` field carries the sema-computed decision so codegen is
    /// purely mechanical: static true/false or a runtime tag/unknown check.
    fn compile_vir_is_check(
        &mut self,
        value: &VirExpr,
        result: IsCheckResult,
    ) -> CodegenResult<CompiledValue> {
        match result {
            IsCheckResult::AlwaysTrue => {
                // Compile value for side-effects, then return true.
                let _value = self.compile_vir_expr(value)?;
                Ok(self.bool_const(true))
            }
            IsCheckResult::AlwaysFalse => {
                let _value = self.compile_vir_expr(value)?;
                Ok(self.bool_const(false))
            }
            IsCheckResult::CheckTag(tag_index) => {
                let compiled = self.compile_vir_expr(value)?;
                if self.vir_query_is_unknown(compiled.type_id)
                    && let Some(source_vir_ty) = Self::vir_expr_type_id(value)
                    && let Some(variants) = crate::types::vir_conversions::vir_unwrap_union(
                        source_vir_ty,
                        self.vir_type_table(),
                    )
                    && let Some(&tested_vir_ty) = variants.get(tag_index as usize)
                {
                    let cmp = self.compile_unknown_is_check_vir(compiled.value, tested_vir_ty);
                    return Ok(self.bool_value(cmp));
                }
                let cmp = self.tag_eq(compiled.value, tag_index as i64);
                Ok(self.bool_value(cmp))
            }
            IsCheckResult::CheckUnknown(tested_type_id, tested_vir_type_id) => {
                let compiled = self.compile_vir_expr(value)?;
                let tested_type_id = self.sema_type_from_vir(tested_type_id);

                // Generic union checks are lowered as CheckUnknown so we can
                // re-derive the concrete union tag after substitutions.
                if tested_type_id != TypeId::UNKNOWN {
                    let concrete_value_ty = self.try_substitute_type(compiled.type_id);
                    let concrete_tested_ty = self.try_substitute_type(tested_type_id);
                    if let Some(variants) = self.arena().unwrap_union(concrete_value_ty)
                        && let Some(tag_index) =
                            variants.iter().position(|&ty| ty == concrete_tested_ty)
                    {
                        let cmp = self.tag_eq(compiled.value, tag_index as i64);
                        return Ok(self.bool_value(cmp));
                    }
                }

                let cmp = if tested_type_id != TypeId::UNKNOWN {
                    self.compile_unknown_is_check(compiled.value, tested_type_id)
                } else {
                    self.compile_unknown_is_check_vir(compiled.value, tested_vir_type_id)
                };
                Ok(self.bool_value(cmp))
            }
        }
    }

    /// Compile a VIR `AsCast` expression (`as?` or `as!`).
    ///
    /// Dispatches on the sema-computed `IsCheckResult` embedded in the VIR
    /// node.  `kind` distinguishes checked (as?) from unchecked (as!) casts.
    ///
    /// `target_ty` is the sema expression type:
    ///   - For `as?`: `T | nil` (nullable result)
    ///   - For `as!`: `T` (the tested type directly)
    fn compile_vir_as_cast(
        &mut self,
        value_expr: &VirExpr,
        target_ty: TypeId,
        kind: AsCastKind,
        result: IsCheckResult,
    ) -> CodegenResult<CompiledValue> {
        let value = self.compile_vir_expr(value_expr)?;
        match result {
            IsCheckResult::AlwaysTrue => self.vir_as_cast_always_true(kind, value, target_ty),
            IsCheckResult::AlwaysFalse => self.vir_as_cast_always_false(kind, target_ty),
            IsCheckResult::CheckTag(tag_index) => {
                self.vir_as_cast_check_tag(kind, value, tag_index, target_ty)
            }
            IsCheckResult::CheckUnknown(tested_type_id, tested_vir_type_id) => {
                let tested_type_id = self.sema_type_from_vir(tested_type_id);
                let tested_type_id = if tested_type_id != TypeId::UNKNOWN {
                    tested_type_id
                } else {
                    self.sema_type_from_vir(tested_vir_type_id)
                };
                self.vir_as_cast_check_unknown(kind, value, tested_type_id, target_ty)
            }
        }
    }

    /// Handle `as` cast when sema determined it always succeeds.
    fn vir_as_cast_always_true(
        &mut self,
        kind: AsCastKind,
        value: CompiledValue,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil — wrap the value.
                self.coerce_to_type(value, target_ty)
            }
            AsCastKind::Unchecked => {
                // Value is already T — pass through.
                Ok(value)
            }
        }
    }

    /// Handle `as` cast when sema determined it always fails.
    fn vir_as_cast_always_false(
        &mut self,
        kind: AsCastKind,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil — always returns nil.
                self.compile_nil_for_optional(target_ty)
            }
            AsCastKind::Unchecked => {
                // Always panics.
                self.emit_panic_static("as! cast failed: value is not the expected type", 0)?;
                Ok(CompiledValue::new(
                    self.iconst_cached(types::I64, 0),
                    types::I64,
                    TypeId::NEVER,
                ))
            }
        }
    }

    /// Handle union tag check for `as` cast: branch on tag, extract payload.
    fn vir_as_cast_check_tag(
        &mut self,
        kind: AsCastKind,
        value: CompiledValue,
        tag_index: u32,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Derive the tested type from the union variants.
        // NOTE: arena() retained — extract_union_payload_typed requires sema TypeId.
        // Remove when CompiledValue carries VirTypeId (Phase D).
        let tested_type_id = self
            .arena()
            .unwrap_union(value.type_id)
            .and_then(|variants| variants.get(tag_index as usize).copied())
            .ok_or_else(|| {
                CodegenError::internal("as cast CheckTag: cannot derive tested type from union")
            })?;
        let is_match = self.tag_eq(value.value, tag_index as i64);
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil
                self.as_cast_safe_branch_with_type(is_match, target_ty, |cg| {
                    cg.extract_union_payload_typed(value, tested_type_id)
                })
            }
            AsCastKind::Unchecked => {
                // target_ty is T
                self.as_cast_unsafe_branch_with_type(is_match, tested_type_id, 0, |cg| {
                    cg.extract_union_payload_typed(value, tested_type_id)
                })
            }
        }
    }

    /// Handle unknown type check for `as` cast: branch on runtime tag.
    fn vir_as_cast_check_unknown(
        &mut self,
        kind: AsCastKind,
        value: CompiledValue,
        tested_type_id: TypeId,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let tag = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), value.value, 0);
        let expected_tag = self.vir_query_unknown_type_tag(tested_type_id);
        let expected_val = self.iconst_cached(types::I64, expected_tag as i64);
        let is_match = self.builder.ins().icmp(IntCC::Equal, tag, expected_val);
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil
                self.as_cast_safe_branch_with_type(is_match, target_ty, |cg| {
                    let raw_value = cg.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        value.value,
                        union_layout::PAYLOAD_OFFSET,
                    );
                    Ok(cg.extract_unknown_value(raw_value, tested_type_id))
                })
            }
            AsCastKind::Unchecked => {
                self.as_cast_unsafe_branch_with_type(is_match, tested_type_id, 0, |cg| {
                    let raw_value = cg.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        value.value,
                        union_layout::PAYLOAD_OFFSET,
                    );
                    Ok(cg.extract_unknown_value(raw_value, tested_type_id))
                })
            }
        }
    }

    // VIR call dispatch is in the `vir_calls` submodule.
}

/// Convert a VIR binary operator to its AST equivalent.
fn vir_binop_to_ast(op: VirBinOp) -> BinaryOp {
    match op {
        VirBinOp::Add => BinaryOp::Add,
        VirBinOp::Sub => BinaryOp::Sub,
        VirBinOp::Mul => BinaryOp::Mul,
        VirBinOp::Div => BinaryOp::Div,
        VirBinOp::Mod => BinaryOp::Mod,
        VirBinOp::Eq => BinaryOp::Eq,
        VirBinOp::Ne => BinaryOp::Ne,
        VirBinOp::Lt => BinaryOp::Lt,
        VirBinOp::Le => BinaryOp::Le,
        VirBinOp::Gt => BinaryOp::Gt,
        VirBinOp::Ge => BinaryOp::Ge,
        VirBinOp::And => BinaryOp::And,
        VirBinOp::Or => BinaryOp::Or,
        VirBinOp::BitAnd => BinaryOp::BitAnd,
        VirBinOp::BitOr => BinaryOp::BitOr,
        VirBinOp::BitXor => BinaryOp::BitXor,
        VirBinOp::Shl => BinaryOp::Shl,
        VirBinOp::Shr => BinaryOp::Shr,
    }
}

/// Convert a VIR unary operator to its AST equivalent.
fn vir_unop_to_ast(op: VirUnOp) -> vole_frontend::UnaryOp {
    match op {
        VirUnOp::Neg => vole_frontend::UnaryOp::Neg,
        VirUnOp::Not => vole_frontend::UnaryOp::Not,
        VirUnOp::BitNot => vole_frontend::UnaryOp::BitNot,
    }
}
