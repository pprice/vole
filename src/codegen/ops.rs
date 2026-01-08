// src/codegen/ops.rs
//
// Binary and compound assignment operations - impl Cg methods.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use crate::codegen::RuntimeFn;
use crate::frontend::{AssignTarget, BinaryExpr, BinaryOp, CompoundAssignExpr};
use crate::sema::Type;

use super::context::Cg;
use super::structs::{convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type};
use super::types::{CompiledValue, array_element_tag, convert_to_type};

impl Cg<'_, '_, '_> {
    /// Compile a binary expression
    pub fn binary(&mut self, bin: &BinaryExpr) -> Result<CompiledValue, String> {
        // Handle short-circuit evaluation for And/Or
        match bin.op {
            BinaryOp::And => return self.binary_and(bin),
            BinaryOp::Or => return self.binary_or(bin),
            _ => {}
        }

        let left = self.expr(&bin.left)?;
        let right = self.expr(&bin.right)?;

        self.binary_op(left, right, bin.op)
    }

    /// Short-circuit AND evaluation
    fn binary_and(&mut self, bin: &BinaryExpr) -> Result<CompiledValue, String> {
        let left = self.expr(&bin.left)?;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I8);

        self.builder
            .ins()
            .brif(left.value, then_block, &[], else_block, &[]);

        // Then block: left was true, evaluate right
        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        let right = self.expr(&bin.right)?;
        let right_arg = BlockArg::from(right.value);
        self.builder.ins().jump(merge_block, &[right_arg]);

        // Else block: left was false, short-circuit with false
        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        let false_val = self.builder.ins().iconst(types::I8, 0);
        let false_arg = BlockArg::from(false_val);
        self.builder.ins().jump(merge_block, &[false_arg]);

        // Merge block
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        let result = self.builder.block_params(merge_block)[0];

        Ok(self.bool_value(result))
    }

    /// Short-circuit OR evaluation
    fn binary_or(&mut self, bin: &BinaryExpr) -> Result<CompiledValue, String> {
        let left = self.expr(&bin.left)?;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I8);

        self.builder
            .ins()
            .brif(left.value, then_block, &[], else_block, &[]);

        // Then block: left was true, short-circuit with true
        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        let true_val = self.builder.ins().iconst(types::I8, 1);
        let true_arg = BlockArg::from(true_val);
        self.builder.ins().jump(merge_block, &[true_arg]);

        // Else block: left was false, evaluate right
        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        let right = self.expr(&bin.right)?;
        let right_arg = BlockArg::from(right.value);
        self.builder.ins().jump(merge_block, &[right_arg]);

        // Merge block
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        let result = self.builder.block_params(merge_block)[0];

        Ok(self.bool_value(result))
    }

    /// Compile a binary operation on two values
    pub fn binary_op(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
        op: BinaryOp,
    ) -> Result<CompiledValue, String> {
        // Handle optional/nil comparisons specially
        // When comparing optional == nil or optional != nil, we need to check the tag
        if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
            // Check if left is optional and right is nil
            if left.vole_type.is_optional() && matches!(right.vole_type, Type::Nil) {
                return self.optional_nil_compare(left, op);
            }
            // Check if right is optional and left is nil
            if right.vole_type.is_optional() && matches!(left.vole_type, Type::Nil) {
                return self.optional_nil_compare(right, op);
            }
        }

        // Determine result type - original behavior: use left's type for integers
        // This matches the original compiler.rs behavior
        let result_ty = if left.ty == types::F64 || right.ty == types::F64 {
            types::F64
        } else if left.ty == types::F32 || right.ty == types::F32 {
            types::F32
        } else {
            left.ty
        };

        let left_vole_type = left.vole_type.clone();

        // Convert operands
        let left_val = convert_to_type(self.builder, left, result_ty);
        let right_val = convert_to_type(self.builder, right, result_ty);

        let result = match op {
            BinaryOp::Add => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fadd(left_val, right_val)
                } else {
                    self.builder.ins().iadd(left_val, right_val)
                }
            }
            BinaryOp::Sub => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fsub(left_val, right_val)
                } else {
                    self.builder.ins().isub(left_val, right_val)
                }
            }
            BinaryOp::Mul => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fmul(left_val, right_val)
                } else {
                    self.builder.ins().imul(left_val, right_val)
                }
            }
            BinaryOp::Div => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fdiv(left_val, right_val)
                } else if left_vole_type.is_unsigned() {
                    self.builder.ins().udiv(left_val, right_val)
                } else {
                    self.builder.ins().sdiv(left_val, right_val)
                }
            }
            BinaryOp::Mod => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    let div = self.builder.ins().fdiv(left_val, right_val);
                    let floor = self.builder.ins().floor(div);
                    let mul = self.builder.ins().fmul(floor, right_val);
                    self.builder.ins().fsub(left_val, mul)
                } else if left_vole_type.is_unsigned() {
                    self.builder.ins().urem(left_val, right_val)
                } else {
                    self.builder.ins().srem(left_val, right_val)
                }
            }
            BinaryOp::Eq => {
                if matches!(left_vole_type, Type::String) {
                    self.string_eq(left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
                } else {
                    self.builder.ins().icmp(IntCC::Equal, left_val, right_val)
                }
            }
            BinaryOp::Ne => {
                if matches!(left_vole_type, Type::String) {
                    let eq = self.string_eq(left_val, right_val)?;
                    let one = self.builder.ins().iconst(types::I8, 1);
                    self.builder.ins().isub(one, eq)
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder
                        .ins()
                        .fcmp(FloatCC::NotEqual, left_val, right_val)
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::NotEqual, left_val, right_val)
                }
            }
            BinaryOp::Lt => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder
                        .ins()
                        .fcmp(FloatCC::LessThan, left_val, right_val)
                } else if left_vole_type.is_unsigned() {
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedLessThan, left_val, right_val)
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::SignedLessThan, left_val, right_val)
                }
            }
            BinaryOp::Gt => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder
                        .ins()
                        .fcmp(FloatCC::GreaterThan, left_val, right_val)
                } else if left_vole_type.is_unsigned() {
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThan, left_val, right_val)
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::SignedGreaterThan, left_val, right_val)
                }
            }
            BinaryOp::Le => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder
                        .ins()
                        .fcmp(FloatCC::LessThanOrEqual, left_val, right_val)
                } else if left_vole_type.is_unsigned() {
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedLessThanOrEqual, left_val, right_val)
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
                }
            }
            BinaryOp::Ge => {
                if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder
                        .ins()
                        .fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val)
                } else if left_vole_type.is_unsigned() {
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, left_val, right_val)
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
                }
            }
            BinaryOp::And | BinaryOp::Or => unreachable!("handled above"),
            BinaryOp::BitAnd => self.builder.ins().band(left_val, right_val),
            BinaryOp::BitOr => self.builder.ins().bor(left_val, right_val),
            BinaryOp::BitXor => self.builder.ins().bxor(left_val, right_val),
            BinaryOp::Shl => self.builder.ins().ishl(left_val, right_val),
            BinaryOp::Shr => {
                if left_vole_type.is_unsigned() {
                    self.builder.ins().ushr(left_val, right_val)
                } else {
                    self.builder.ins().sshr(left_val, right_val)
                }
            }
        };

        let final_ty = match op {
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::Le
            | BinaryOp::Ge => types::I8,
            BinaryOp::And | BinaryOp::Or => unreachable!(),
            _ => result_ty,
        };

        let vole_type = match op {
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::Le
            | BinaryOp::Ge => Type::Bool,
            BinaryOp::And | BinaryOp::Or => unreachable!(),
            _ => left_vole_type,
        };

        Ok(CompiledValue {
            value: result,
            ty: final_ty,
            vole_type,
        })
    }

    /// String equality comparison
    fn string_eq(&mut self, left: Value, right: Value) -> Result<Value, String> {
        if self
            .ctx
            .func_registry
            .runtime_key(RuntimeFn::StringEq)
            .and_then(|key| self.ctx.func_registry.func_id(key))
            .is_some()
        {
            self.call_runtime(RuntimeFn::StringEq, &[left, right])
        } else {
            Ok(self.builder.ins().icmp(IntCC::Equal, left, right))
        }
    }

    /// Compare an optional value with nil
    /// Returns true if the optional's tag matches the nil tag
    fn optional_nil_compare(
        &mut self,
        optional: CompiledValue,
        op: BinaryOp,
    ) -> Result<CompiledValue, String> {
        let Type::Union(variants) = &optional.vole_type else {
            return Err("optional_nil_compare called on non-union type".into());
        };

        // Find the position of nil in the variants (this is the nil tag value)
        let nil_tag = variants
            .iter()
            .position(|v| v == &Type::Nil)
            .unwrap_or(usize::MAX);

        // Load the tag from the optional (first byte)
        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), optional.value, 0);

        // Compare tag with nil_tag
        let nil_tag_val = self.builder.ins().iconst(types::I8, nil_tag as i64);
        let is_nil = self.builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

        // For != nil, we need to invert the result
        let result = match op {
            BinaryOp::Eq => is_nil,
            BinaryOp::Ne => {
                let one = self.builder.ins().iconst(types::I8, 1);
                self.builder.ins().isub(one, is_nil)
            }
            _ => unreachable!("optional_nil_compare only handles Eq and Ne"),
        };

        Ok(self.bool_value(result))
    }

    /// Compile compound assignment (+=, -=, etc.)
    pub fn compound_assign(
        &mut self,
        compound: &CompoundAssignExpr,
    ) -> Result<CompiledValue, String> {
        match &compound.target {
            AssignTarget::Variable(sym) => self.compound_assign_var(*sym, compound),
            AssignTarget::Index { object, index } => {
                self.compound_assign_index(object, index, compound)
            }
            AssignTarget::Field { object, field, .. } => {
                self.compound_assign_field(object, *field, compound)
            }
        }
    }

    /// Compound assignment to variable
    fn compound_assign_var(
        &mut self,
        sym: crate::frontend::Symbol,
        compound: &CompoundAssignExpr,
    ) -> Result<CompiledValue, String> {
        let (var, var_type) = self
            .vars
            .get(&sym)
            .ok_or_else(|| format!("undefined variable: {}", self.ctx.interner.resolve(sym)))?;
        let var = *var;
        let var_type = var_type.clone();
        let current_val = self.builder.use_var(var);

        let current = self.typed_value(current_val, var_type);

        let rhs = self.expr(&compound.value)?;
        let binary_op = compound.op.to_binary_op();
        let result = self.binary_op(current, rhs, binary_op)?;

        self.builder.def_var(var, result.value);
        Ok(result)
    }

    /// Compound assignment to array index
    fn compound_assign_index(
        &mut self,
        object: &crate::frontend::Expr,
        index: &crate::frontend::Expr,
        compound: &CompoundAssignExpr,
    ) -> Result<CompiledValue, String> {
        let arr = self.expr(object)?;
        let idx = self.expr(index)?;

        let elem_type = match &arr.vole_type {
            Type::Array(elem) => elem.as_ref().clone(),
            _ => Type::I64,
        };

        // Load current element
        let raw_value = self.call_runtime(RuntimeFn::ArrayGetValue, &[arr.value, idx.value])?;
        let (current_val, current_ty) = convert_field_value(self.builder, raw_value, &elem_type);

        let current = CompiledValue {
            value: current_val,
            ty: current_ty,
            vole_type: elem_type.clone(),
        };

        let rhs = self.expr(&compound.value)?;
        let binary_op = compound.op.to_binary_op();
        let result = self.binary_op(current, rhs, binary_op)?;

        // Store back
        let array_set_key = self
            .ctx
            .func_registry
            .runtime_key(RuntimeFn::ArraySet)
            .ok_or_else(|| "vole_array_set not found".to_string())?;
        let array_set_ref = self.func_ref(array_set_key)?;
        let store_value = convert_to_i64_for_storage(self.builder, &result);
        let tag_val = self
            .builder
            .ins()
            .iconst(types::I64, array_element_tag(&elem_type));

        self.builder
            .ins()
            .call(array_set_ref, &[arr.value, idx.value, tag_val, store_value]);

        Ok(result)
    }

    /// Compound assignment to field
    fn compound_assign_field(
        &mut self,
        object: &crate::frontend::Expr,
        field: crate::frontend::Symbol,
        compound: &CompoundAssignExpr,
    ) -> Result<CompiledValue, String> {
        let obj = self.expr(object)?;

        let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, field, self.ctx)?;

        // Load current field
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let current_raw = self.call_runtime(RuntimeFn::InstanceGetField, &[obj.value, slot_val])?;

        let (current_val, cranelift_ty) =
            convert_field_value(self.builder, current_raw, &field_type);

        let current = CompiledValue {
            value: current_val,
            ty: cranelift_ty,
            vole_type: field_type,
        };

        let rhs = self.expr(&compound.value)?;
        let binary_op = compound.op.to_binary_op();
        let result = self.binary_op(current, rhs, binary_op)?;

        // Store back
        let store_value = convert_to_i64_for_storage(self.builder, &result);

        self.call_runtime_void(
            RuntimeFn::InstanceSetField,
            &[obj.value, slot_val, store_value],
        )?;

        Ok(result)
    }
}
