// src/codegen/expr.rs
//
// Expression compilation - impl Cg methods.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::Module;

use crate::frontend::{AssignTarget, BinaryOp, Expr, ExprKind, MatchExpr, Pattern, UnaryOp};
use crate::sema::Type;

use super::context::Cg;
use super::types::{convert_to_type, resolve_type_expr, type_to_cranelift, CompiledValue};

impl Cg<'_, '_, '_> {
    /// Compile an expression.
    pub fn expr(&mut self, expr: &Expr) -> Result<CompiledValue, String> {
        // Check for captures first if in closure context
        if self.has_captures() {
            if let ExprKind::Identifier(sym) = &expr.kind {
                if let Some(binding) = self.get_capture(sym).cloned() {
                    return self.load_capture(&binding);
                }
            }
        }

        match &expr.kind {
            ExprKind::IntLiteral(n) => {
                let val = self.builder.ins().iconst(types::I64, *n);
                Ok(CompiledValue {
                    value: val,
                    ty: types::I64,
                    vole_type: Type::I64,
                })
            }
            ExprKind::FloatLiteral(n) => {
                let val = self.builder.ins().f64const(*n);
                Ok(CompiledValue {
                    value: val,
                    ty: types::F64,
                    vole_type: Type::F64,
                })
            }
            ExprKind::BoolLiteral(b) => {
                let val = self.builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
                Ok(CompiledValue {
                    value: val,
                    ty: types::I8,
                    vole_type: Type::Bool,
                })
            }
            ExprKind::Identifier(sym) => self.identifier(*sym, expr),
            ExprKind::Binary(bin) => self.binary(bin),
            ExprKind::Unary(un) => self.unary(un),
            ExprKind::Assign(assign) => self.assign(assign),
            ExprKind::CompoundAssign(compound) => self.compound_assign(compound),
            ExprKind::Grouping(inner) => self.expr(inner),
            ExprKind::StringLiteral(s) => self.string_literal(s),
            ExprKind::Call(call) => self.call(call, expr.span.line),
            ExprKind::InterpolatedString(parts) => self.interpolated_string(parts),
            ExprKind::Range(_) => {
                Err("Range expressions only supported in for-in context".to_string())
            }
            ExprKind::ArrayLiteral(elements) => self.array_literal(elements),
            ExprKind::Index(idx) => self.index(&idx.object, &idx.index),
            ExprKind::Match(match_expr) => self.match_expr(match_expr),
            ExprKind::Nil => {
                let zero = self.builder.ins().iconst(types::I8, 0);
                Ok(CompiledValue {
                    value: zero,
                    ty: types::I8,
                    vole_type: Type::Nil,
                })
            }
            ExprKind::Is(is_expr) => self.is_expr(is_expr),
            ExprKind::NullCoalesce(nc) => self.null_coalesce(nc),
            ExprKind::Lambda(lambda) => self.lambda(lambda),
            ExprKind::TypeLiteral(_) => {
                Err("type expressions cannot be used as runtime values".to_string())
            }
            ExprKind::StructLiteral(sl) => self.struct_literal(sl),
            ExprKind::FieldAccess(fa) => self.field_access(fa),
            ExprKind::MethodCall(mc) => self.method_call(mc),
        }
    }

    /// Compile an identifier lookup
    fn identifier(
        &mut self,
        sym: crate::frontend::Symbol,
        expr: &Expr,
    ) -> Result<CompiledValue, String> {
        if let Some((var, vole_type)) = self.vars.get(&sym) {
            let val = self.builder.use_var(*var);
            let ty = self.builder.func.dfg.value_type(val);

            // Check for narrowed type from semantic analysis
            if let Some(narrowed_type) = self.ctx.expr_types.get(&expr.id) {
                if matches!(vole_type, Type::Union(_)) && !matches!(narrowed_type, Type::Union(_)) {
                    // Union layout: [tag:1][padding:7][payload]
                    let payload_ty = type_to_cranelift(narrowed_type, self.ctx.pointer_type);
                    let payload = self.builder.ins().load(payload_ty, MemFlags::new(), val, 8);
                    return Ok(CompiledValue {
                        value: payload,
                        ty: payload_ty,
                        vole_type: narrowed_type.clone(),
                    });
                }
            }

            Ok(CompiledValue {
                value: val,
                ty,
                vole_type: vole_type.clone(),
            })
        } else if let Some(global) = self.ctx.globals.iter().find(|g| g.name == sym) {
            // Compile global's initializer inline
            let global_init = global.init.clone();
            self.expr(&global_init)
        } else {
            Err(format!(
                "undefined variable: {}",
                self.ctx.interner.resolve(sym)
            ))
        }
    }

    /// Compile a unary expression
    fn unary(&mut self, un: &crate::frontend::UnaryExpr) -> Result<CompiledValue, String> {
        let operand = self.expr(&un.operand)?;
        let result = match un.op {
            UnaryOp::Neg => {
                if operand.ty == types::F64 {
                    self.builder.ins().fneg(operand.value)
                } else {
                    self.builder.ins().ineg(operand.value)
                }
            }
            UnaryOp::Not => {
                let one = self.builder.ins().iconst(types::I8, 1);
                self.builder.ins().isub(one, operand.value)
            }
            UnaryOp::BitNot => self.builder.ins().bnot(operand.value),
        };
        Ok(CompiledValue {
            value: result,
            ty: operand.ty,
            vole_type: operand.vole_type,
        })
    }

    /// Compile an assignment expression
    fn assign(&mut self, assign: &crate::frontend::AssignExpr) -> Result<CompiledValue, String> {
        match &assign.target {
            AssignTarget::Variable(sym) => {
                let value = self.expr(&assign.value)?;

                // Check for captured variable assignment
                if let Some(binding) = self.get_capture(sym).cloned() {
                    return self.store_capture(&binding, value);
                }

                let (var, var_type) = self
                    .vars
                    .get(sym)
                    .ok_or_else(|| {
                        format!(
                            "undefined variable: {}",
                            self.ctx.interner.resolve(*sym)
                        )
                    })?;
                let var = *var;
                let var_type = var_type.clone();

                let final_value = if matches!(&var_type, Type::Union(_))
                    && !matches!(&value.vole_type, Type::Union(_))
                {
                    let wrapped = self.construct_union(value.clone(), &var_type)?;
                    wrapped.value
                } else {
                    value.value
                };
                self.builder.def_var(var, final_value);
                Ok(value)
            }
            AssignTarget::Field { object, field, .. } => {
                self.field_assign(object, *field, &assign.value)
            }
            AssignTarget::Index { object, index } => {
                self.index_assign(object, index, &assign.value)
            }
        }
    }

    /// Compile an array literal
    fn array_literal(&mut self, elements: &[Expr]) -> Result<CompiledValue, String> {
        let array_new_id = self
            .ctx
            .func_ids
            .get("vole_array_new")
            .ok_or_else(|| "vole_array_new not found".to_string())?;
        let array_new_ref = self
            .ctx
            .module
            .declare_func_in_func(*array_new_id, self.builder.func);

        let call = self.builder.ins().call(array_new_ref, &[]);
        let arr_ptr = self.builder.inst_results(call)[0];

        let array_push_id = self
            .ctx
            .func_ids
            .get("vole_array_push")
            .ok_or_else(|| "vole_array_push not found".to_string())?;
        let array_push_ref = self
            .ctx
            .module
            .declare_func_in_func(*array_push_id, self.builder.func);

        let mut elem_type = Type::Unknown;

        for (i, elem) in elements.iter().enumerate() {
            let compiled = self.expr(elem)?;

            if i == 0 {
                elem_type = compiled.vole_type.clone();
            }

            let tag = match &compiled.vole_type {
                Type::I64 | Type::I32 => 2i64,
                Type::F64 => 3i64,
                Type::Bool => 4i64,
                Type::String => 1i64,
                Type::Array(_) => 5i64,
                _ => 2i64,
            };

            let tag_val = self.builder.ins().iconst(types::I64, tag);

            let value_bits = if compiled.ty == types::F64 {
                self.builder
                    .ins()
                    .bitcast(types::I64, MemFlags::new(), compiled.value)
            } else if compiled.ty == types::I8 {
                self.builder.ins().uextend(types::I64, compiled.value)
            } else {
                compiled.value
            };

            self.builder
                .ins()
                .call(array_push_ref, &[arr_ptr, tag_val, value_bits]);
        }

        Ok(CompiledValue {
            value: arr_ptr,
            ty: self.ctx.pointer_type,
            vole_type: Type::Array(Box::new(elem_type)),
        })
    }

    /// Compile an index expression
    fn index(&mut self, object: &Expr, index: &Expr) -> Result<CompiledValue, String> {
        let arr = self.expr(object)?;
        let idx = self.expr(index)?;

        let elem_type = match &arr.vole_type {
            Type::Array(elem) => elem.as_ref().clone(),
            _ => Type::I64,
        };

        let get_value_id = self
            .ctx
            .func_ids
            .get("vole_array_get_value")
            .ok_or_else(|| "vole_array_get_value not found".to_string())?;
        let get_value_ref = self
            .ctx
            .module
            .declare_func_in_func(*get_value_id, self.builder.func);

        let call = self
            .builder
            .ins()
            .call(get_value_ref, &[arr.value, idx.value]);
        let value = self.builder.inst_results(call)[0];

        let (result_value, result_ty) = match &elem_type {
            Type::F64 => {
                let fval = self
                    .builder
                    .ins()
                    .bitcast(types::F64, MemFlags::new(), value);
                (fval, types::F64)
            }
            Type::Bool => {
                let bval = self.builder.ins().ireduce(types::I8, value);
                (bval, types::I8)
            }
            _ => (value, types::I64),
        };

        Ok(CompiledValue {
            value: result_value,
            ty: result_ty,
            vole_type: elem_type,
        })
    }

    /// Compile an index assignment
    fn index_assign(
        &mut self,
        object: &Expr,
        index: &Expr,
        value: &Expr,
    ) -> Result<CompiledValue, String> {
        let arr = self.expr(object)?;
        let idx = self.expr(index)?;
        let val = self.expr(value)?;

        let set_value_id = self
            .ctx
            .func_ids
            .get("vole_array_set_value")
            .ok_or_else(|| "vole_array_set_value not found".to_string())?;
        let set_value_ref = self
            .ctx
            .module
            .declare_func_in_func(*set_value_id, self.builder.func);

        let tag = match &val.vole_type {
            Type::I64 | Type::I32 => 2i64,
            Type::F64 => 3i64,
            Type::Bool => 4i64,
            Type::String => 1i64,
            Type::Array(_) => 5i64,
            _ => 2i64,
        };

        let tag_val = self.builder.ins().iconst(types::I64, tag);

        let value_bits = if val.ty == types::F64 {
            self.builder
                .ins()
                .bitcast(types::I64, MemFlags::new(), val.value)
        } else if val.ty == types::I8 {
            self.builder.ins().uextend(types::I64, val.value)
        } else {
            val.value
        };

        self.builder
            .ins()
            .call(set_value_ref, &[arr.value, idx.value, tag_val, value_bits]);

        Ok(val)
    }

    /// Compile an `is` type check expression
    fn is_expr(&mut self, is_expr: &crate::frontend::IsExpr) -> Result<CompiledValue, String> {
        let value = self.expr(&is_expr.value)?;
        let tested_type = resolve_type_expr(&is_expr.type_expr, self.ctx.type_aliases);

        if let Type::Union(variants) = &value.vole_type {
            let expected_tag = variants
                .iter()
                .position(|v| v == &tested_type)
                .unwrap_or(usize::MAX);

            let tag = self
                .builder
                .ins()
                .load(types::I8, MemFlags::new(), value.value, 0);
            let expected = self.builder.ins().iconst(types::I8, expected_tag as i64);
            let result = self.builder.ins().icmp(IntCC::Equal, tag, expected);

            Ok(CompiledValue {
                value: result,
                ty: types::I8,
                vole_type: Type::Bool,
            })
        } else {
            let result = if value.vole_type == tested_type { 1i64 } else { 0i64 };
            let result_val = self.builder.ins().iconst(types::I8, result);
            Ok(CompiledValue {
                value: result_val,
                ty: types::I8,
                vole_type: Type::Bool,
            })
        }
    }

    /// Compile a null coalesce expression (??)
    fn null_coalesce(
        &mut self,
        nc: &crate::frontend::NullCoalesceExpr,
    ) -> Result<CompiledValue, String> {
        let value = self.expr(&nc.value)?;

        let Type::Union(variants) = &value.vole_type else {
            return Err("Expected union for ??".to_string());
        };
        let nil_tag = variants
            .iter()
            .position(|v| v == &Type::Nil)
            .unwrap_or(usize::MAX);

        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), value.value, 0);
        let nil_tag_val = self.builder.ins().iconst(types::I8, nil_tag as i64);
        let is_nil = self.builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let result_vole_type = value.vole_type.unwrap_optional().unwrap_or(Type::Error);
        let cranelift_type = type_to_cranelift(&result_vole_type, self.ctx.pointer_type);
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        self.builder.switch_to_block(nil_block);
        self.builder.seal_block(nil_block);
        let default_val = self.expr(&nc.default)?;
        let default_coerced = if default_val.ty != cranelift_type {
            if default_val.ty.is_int() && cranelift_type.is_int() {
                if cranelift_type.bytes() < default_val.ty.bytes() {
                    self.builder.ins().ireduce(cranelift_type, default_val.value)
                } else {
                    self.builder
                        .ins()
                        .sextend(cranelift_type, default_val.value)
                }
            } else {
                default_val.value
            }
        } else {
            default_val.value
        };
        let default_arg = BlockArg::from(default_coerced);
        self.builder.ins().jump(merge_block, &[default_arg]);

        self.builder.switch_to_block(not_nil_block);
        self.builder.seal_block(not_nil_block);
        let payload = self
            .builder
            .ins()
            .load(cranelift_type, MemFlags::new(), value.value, 8);
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue {
            value: result,
            ty: cranelift_type,
            vole_type: result_vole_type,
        })
    }

    /// Load a captured variable from closure
    fn load_capture(
        &mut self,
        binding: &super::lambda::CaptureBinding,
    ) -> Result<CompiledValue, String> {
        let closure_var = self
            .closure_var()
            .ok_or_else(|| "Closure variable not available for capture access".to_string())?;
        let closure_ptr = self.builder.use_var(closure_var);

        let get_capture_id = self
            .ctx
            .func_ids
            .get("vole_closure_get_capture")
            .ok_or_else(|| "vole_closure_get_capture not found".to_string())?;
        let get_capture_ref = self
            .ctx
            .module
            .declare_func_in_func(*get_capture_id, self.builder.func);
        let index_val = self.builder.ins().iconst(types::I64, binding.index as i64);
        let call = self
            .builder
            .ins()
            .call(get_capture_ref, &[closure_ptr, index_val]);
        let heap_ptr = self.builder.inst_results(call)[0];

        let cranelift_ty = type_to_cranelift(&binding.vole_type, self.ctx.pointer_type);
        let value = self
            .builder
            .ins()
            .load(cranelift_ty, MemFlags::new(), heap_ptr, 0);

        Ok(CompiledValue {
            value,
            ty: cranelift_ty,
            vole_type: binding.vole_type.clone(),
        })
    }

    /// Store a value to a captured variable in closure
    fn store_capture(
        &mut self,
        binding: &super::lambda::CaptureBinding,
        value: CompiledValue,
    ) -> Result<CompiledValue, String> {
        let closure_var = self
            .closure_var()
            .ok_or_else(|| "Closure variable not available for capture access".to_string())?;
        let closure_ptr = self.builder.use_var(closure_var);

        let get_capture_id = self
            .ctx
            .func_ids
            .get("vole_closure_get_capture")
            .ok_or_else(|| "vole_closure_get_capture not found".to_string())?;
        let get_capture_ref = self
            .ctx
            .module
            .declare_func_in_func(*get_capture_id, self.builder.func);
        let index_val = self.builder.ins().iconst(types::I64, binding.index as i64);
        let call = self
            .builder
            .ins()
            .call(get_capture_ref, &[closure_ptr, index_val]);
        let heap_ptr = self.builder.inst_results(call)[0];

        let cranelift_ty = type_to_cranelift(&binding.vole_type, self.ctx.pointer_type);
        self.builder
            .ins()
            .store(MemFlags::new(), value.value, heap_ptr, 0);

        Ok(CompiledValue {
            value: value.value,
            ty: cranelift_ty,
            vole_type: binding.vole_type.clone(),
        })
    }

    /// Compile a match expression
    pub fn match_expr(&mut self, match_expr: &MatchExpr) -> Result<CompiledValue, String> {
        let scrutinee = self.expr(&match_expr.scrutinee)?;

        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        let arm_blocks: Vec<Block> = match_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        if !arm_blocks.is_empty() {
            self.builder.ins().jump(arm_blocks[0], &[]);
        } else {
            let default_val = self.builder.ins().iconst(types::I64, 0);
            let default_arg = BlockArg::from(default_val);
            self.builder.ins().jump(merge_block, &[default_arg]);
        }

        let mut result_vole_type = Type::Void;

        for (i, arm) in match_expr.arms.iter().enumerate() {
            let arm_block = arm_blocks[i];
            let next_block = arm_blocks.get(i + 1).copied().unwrap_or(merge_block);

            self.builder.switch_to_block(arm_block);

            let mut arm_variables = self.vars.clone();

            let pattern_matches = match &arm.pattern {
                Pattern::Wildcard(_) => None,
                Pattern::Identifier { name, .. } => {
                    let var = self.builder.declare_var(scrutinee.ty);
                    self.builder.def_var(var, scrutinee.value);
                    arm_variables.insert(*name, (var, scrutinee.vole_type.clone()));
                    None
                }
                Pattern::Literal(lit_expr) => {
                    // Save and restore vars for pattern matching
                    let saved_vars = std::mem::replace(&mut *self.vars, arm_variables.clone());
                    let lit_val = self.expr(lit_expr)?;
                    arm_variables = std::mem::replace(&mut *self.vars, saved_vars);

                    let cmp = match scrutinee.ty {
                        types::I64 | types::I32 | types::I8 => self
                            .builder
                            .ins()
                            .icmp(IntCC::Equal, scrutinee.value, lit_val.value),
                        types::F64 => self
                            .builder
                            .ins()
                            .fcmp(FloatCC::Equal, scrutinee.value, lit_val.value),
                        _ => {
                            if let Some(cmp_id) = self.ctx.func_ids.get("vole_string_eq") {
                                let cmp_ref = self
                                    .ctx
                                    .module
                                    .declare_func_in_func(*cmp_id, self.builder.func);
                                let call = self
                                    .builder
                                    .ins()
                                    .call(cmp_ref, &[scrutinee.value, lit_val.value]);
                                self.builder.inst_results(call)[0]
                            } else {
                                self.builder
                                    .ins()
                                    .icmp(IntCC::Equal, scrutinee.value, lit_val.value)
                            }
                        }
                    };
                    Some(cmp)
                }
            };

            // Save and restore vars for guard evaluation
            let guard_result = if let Some(guard) = &arm.guard {
                let saved_vars = std::mem::replace(&mut *self.vars, arm_variables.clone());
                let guard_val = self.expr(guard)?;
                arm_variables = std::mem::replace(&mut *self.vars, saved_vars);
                Some(guard_val.value)
            } else {
                None
            };

            let should_execute = match (pattern_matches, guard_result) {
                (None, None) => None,
                (Some(p), None) => Some(p),
                (None, Some(g)) => Some(g),
                (Some(p), Some(g)) => Some(self.builder.ins().band(p, g)),
            };

            let body_block = self.builder.create_block();

            if let Some(cond) = should_execute {
                let cond_i32 = self.builder.ins().uextend(types::I32, cond);
                self.builder
                    .ins()
                    .brif(cond_i32, body_block, &[], next_block, &[]);
            } else {
                self.builder.ins().jump(body_block, &[]);
            }

            self.builder.seal_block(arm_block);

            self.builder.switch_to_block(body_block);

            // Compile body with the arm's variables
            let saved_vars = std::mem::replace(&mut *self.vars, arm_variables);
            let body_val = self.expr(&arm.body)?;
            let _ = std::mem::replace(&mut *self.vars, saved_vars);

            if i == 0 {
                result_vole_type = body_val.vole_type.clone();
            }

            let result_val = if body_val.ty != types::I64 {
                match body_val.ty {
                    types::I8 => self.builder.ins().sextend(types::I64, body_val.value),
                    types::I32 => self.builder.ins().sextend(types::I64, body_val.value),
                    _ => body_val.value,
                }
            } else {
                body_val.value
            };

            let result_arg = BlockArg::from(result_val);
            self.builder.ins().jump(merge_block, &[result_arg]);
            self.builder.seal_block(body_block);
        }

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue {
            value: result,
            ty: types::I64,
            vole_type: result_vole_type,
        })
    }
}
