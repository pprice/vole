// src/codegen/ops.rs
//
// Binary and compound assignment operations - impl Cg methods.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;

use crate::RuntimeFn;
use vole_frontend::{AssignTarget, BinaryExpr, BinaryOp, CompoundAssignExpr};
use vole_sema::implement_registry::ImplTypeId;
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::structs::{
    convert_field_value_id, convert_to_i64_for_storage, get_field_slot_and_type_id,
};
use super::types::{CompiledValue, array_element_tag_id, convert_to_type, type_id_to_cranelift};

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

        // Handle string concatenation: string + Stringable
        if bin.op == BinaryOp::Add && left.type_id == TypeId::STRING {
            let right = self.expr(&bin.right)?;
            return self.string_concat(left, right);
        }

        let right = self.expr(&bin.right)?;

        self.binary_op(left, right, bin.op)
    }

    /// Concatenate two values as strings.
    /// Left must be a string, right will be converted via to_string() if not already string.
    fn string_concat(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
    ) -> Result<CompiledValue, String> {
        // Get the right operand as a string
        let right_string = if right.type_id == TypeId::STRING {
            // Right is already a string, use it directly
            right.value
        } else {
            // Right is not a string, call to_string() on it
            self.call_to_string(&right)?
        };

        // Call vole_string_concat(left, right_string)
        let concat_result =
            self.call_runtime(RuntimeFn::StringConcat, &[left.value, right_string])?;

        Ok(self.string_value(concat_result))
    }

    /// Call to_string() on a value via the Stringable interface.
    /// Returns the resulting string value.
    fn call_to_string(&mut self, val: &CompiledValue) -> Result<Value, String> {
        let arena = self.ctx.arena.borrow();
        let impl_type_id =
            ImplTypeId::from_type_id(val.type_id, &arena, &self.ctx.analyzed.entity_registry)
                .ok_or_else(|| format!("Cannot find ImplTypeId for type_id {:?}", val.type_id))?;
        drop(arena);

        // Look up to_string method via query
        let method_id = self.ctx.analyzed.query().method_name_id_by_str("to_string");

        let method_impl = self
            .ctx
            .analyzed
            .implement_registry
            .get_method(&impl_type_id, method_id)
            .ok_or_else(|| {
                format!(
                    "to_string method not implemented for type_id {:?}",
                    val.type_id
                )
            })?;

        // Check if it's an external (native) method
        if let Some(ref external_info) = method_impl.external_info {
            // Call the external function directly
            let string_type_id = self.ctx.arena.borrow().primitives.string;
            let result = self.call_external_id(external_info, &[val.value], string_type_id)?;
            return Ok(result.value);
        }

        // Otherwise, it's a Vole method - look up the compiled function
        // Get the method key from impl_method_infos
        let method_info = self
            .ctx
            .impl_method_infos
            .get(&(impl_type_id, method_id))
            .ok_or_else(|| "to_string method info not found in impl_method_infos".to_string())?;

        let func_ref = self.func_ref(method_info.func_key)?;

        // Call the method with `self` (the value) as the only argument
        let call = self.builder.ins().call(func_ref, &[val.value]);
        let results = self.builder.inst_results(call);

        results
            .first()
            .copied()
            .ok_or_else(|| "to_string method did not return a value".to_string())
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
            if self.ctx.arena.borrow().is_optional(left.type_id) && right.type_id.is_nil() {
                return self.optional_nil_compare(left, op);
            }
            // Check if right is optional and left is nil
            if self.ctx.arena.borrow().is_optional(right.type_id) && left.type_id.is_nil() {
                return self.optional_nil_compare(right, op);
            }
            // Check if left is optional and right is a compatible value type (using TypeId)
            let arena = self.ctx.arena.borrow();
            if let Some(inner_type_id) = arena.unwrap_optional(left.type_id)
                && (inner_type_id == right.type_id
                    || (arena.is_integer(inner_type_id) && arena.is_integer(right.type_id)))
            {
                drop(arena);
                return self.optional_value_compare(left, right, op);
            }
            // Check if right is optional and left is a compatible value type (using TypeId)
            if let Some(inner_type_id) = arena.unwrap_optional(right.type_id)
                && (inner_type_id == left.type_id
                    || (arena.is_integer(inner_type_id) && arena.is_integer(left.type_id)))
            {
                drop(arena);
                return self.optional_value_compare(right, left, op);
            }
            drop(arena);
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

        let left_type_id = left.type_id;
        let left_is_string = left_type_id == TypeId::STRING;

        // Convert operands
        let left_val = convert_to_type(self.builder, left, result_ty, self.ctx.arena);
        let right_val = convert_to_type(self.builder, right, result_ty, self.ctx.arena);

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
                } else if left_type_id.is_unsigned_int() {
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
                } else if left_type_id.is_unsigned_int() {
                    self.builder.ins().urem(left_val, right_val)
                } else {
                    self.builder.ins().srem(left_val, right_val)
                }
            }
            BinaryOp::Eq => {
                if left_is_string {
                    self.string_eq(left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
                } else {
                    self.builder.ins().icmp(IntCC::Equal, left_val, right_val)
                }
            }
            BinaryOp::Ne => {
                if left_is_string {
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
                } else if left_type_id.is_unsigned_int() {
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
                } else if left_type_id.is_unsigned_int() {
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
                } else if left_type_id.is_unsigned_int() {
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
                } else if left_type_id.is_unsigned_int() {
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
                if left_type_id.is_unsigned_int() {
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

        let result_type_id = match op {
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::Le
            | BinaryOp::Ge => TypeId::BOOL,
            BinaryOp::And | BinaryOp::Or => unreachable!(),
            _ => left_type_id,
        };

        Ok(CompiledValue {
            value: result,
            ty: final_ty,
            type_id: result_type_id,
        })
    }

    /// String equality comparison
    fn string_eq(&mut self, left: Value, right: Value) -> Result<Value, String> {
        if self.ctx.func_registry.has_runtime(RuntimeFn::StringEq) {
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
        // Find the position of nil in the variants (this is the nil tag value)
        let nil_tag = self
            .find_nil_variant(optional.type_id)
            .ok_or("optional_nil_compare called on non-optional type")?;

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

    /// Compare an optional value with a non-nil value (e.g., optional == 42)
    /// Returns false if the optional is nil, otherwise compares the payload
    fn optional_value_compare(
        &mut self,
        optional: CompiledValue,
        value: CompiledValue,
        op: BinaryOp,
    ) -> Result<CompiledValue, String> {
        // Find the position of nil in the variants (this is the nil tag value)
        let nil_tag = self
            .find_nil_variant(optional.type_id)
            .ok_or("optional_value_compare called on non-optional type")?;

        // Load the tag from the optional (first byte)
        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), optional.value, 0);

        // Check if not nil (tag != nil_tag)
        let nil_tag_val = self.builder.ins().iconst(types::I8, nil_tag as i64);
        let is_not_nil = self.builder.ins().icmp(IntCC::NotEqual, tag, nil_tag_val);

        // Load the payload (at offset 8) with the correct type
        // The payload type matches the inner (non-nil) type of the optional (using TypeId)
        let arena = self.ctx.arena.borrow();
        let inner_type_id = arena
            .unwrap_optional(optional.type_id)
            .unwrap_or_else(|| arena.i64());
        let payload_cranelift_type =
            type_id_to_cranelift(inner_type_id, &arena, self.ctx.pointer_type);
        drop(arena);
        let payload =
            self.builder
                .ins()
                .load(payload_cranelift_type, MemFlags::new(), optional.value, 8);

        // Compare payload with value (extend if necessary to match types)
        let values_equal = if value.ty == types::F64 {
            self.builder
                .ins()
                .fcmp(FloatCC::Equal, payload, value.value)
        } else {
            // Ensure both values have the same type for comparison
            let (cmp_payload, cmp_value) = if payload_cranelift_type.bytes() < value.ty.bytes() {
                // Extend payload to match value's type
                let extended = self.builder.ins().sextend(value.ty, payload);
                (extended, value.value)
            } else if payload_cranelift_type.bytes() > value.ty.bytes() {
                // Extend value to match payload's type
                let extended = self
                    .builder
                    .ins()
                    .sextend(payload_cranelift_type, value.value);
                (payload, extended)
            } else {
                (payload, value.value)
            };
            self.builder
                .ins()
                .icmp(IntCC::Equal, cmp_payload, cmp_value)
        };

        // Result is: is_not_nil AND values_equal
        let result = match op {
            BinaryOp::Eq => {
                // (not nil) AND (values equal)
                self.builder.ins().band(is_not_nil, values_equal)
            }
            BinaryOp::Ne => {
                // NOT ((not nil) AND (values equal)) = is_nil OR (values not equal)
                let equal = self.builder.ins().band(is_not_nil, values_equal);
                let one = self.builder.ins().iconst(types::I8, 1);
                self.builder.ins().isub(one, equal)
            }
            _ => unreachable!("optional_value_compare only handles Eq and Ne"),
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
        sym: vole_frontend::Symbol,
        compound: &CompoundAssignExpr,
    ) -> Result<CompiledValue, String> {
        let (var, var_type_id) = self
            .vars
            .get(&sym)
            .ok_or_else(|| format!("undefined variable: {}", self.ctx.interner.resolve(sym)))?;
        let var = *var;
        let var_type_id = *var_type_id;
        let current_val = self.builder.use_var(var);

        let current = self.typed_value_interned(current_val, var_type_id);

        let rhs = self.expr(&compound.value)?;
        let binary_op = compound.op.to_binary_op();
        let result = self.binary_op(current, rhs, binary_op)?;

        self.builder.def_var(var, result.value);
        Ok(result)
    }

    /// Compound assignment to array index
    fn compound_assign_index(
        &mut self,
        object: &vole_frontend::Expr,
        index: &vole_frontend::Expr,
        compound: &CompoundAssignExpr,
    ) -> Result<CompiledValue, String> {
        let arr = self.expr(object)?;
        let idx = self.expr(index)?;

        let arena = self.ctx.arena.borrow();
        let elem_type_id = arena
            .unwrap_array(arr.type_id)
            .unwrap_or_else(|| arena.i64());

        // Load current element
        let raw_value = self.call_runtime(RuntimeFn::ArrayGetValue, &[arr.value, idx.value])?;
        let (current_val, current_ty) =
            convert_field_value_id(self.builder, raw_value, elem_type_id, &arena);
        drop(arena);

        let current = CompiledValue {
            value: current_val,
            ty: current_ty,
            type_id: elem_type_id,
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
        let tag_val = self.builder.ins().iconst(
            types::I64,
            array_element_tag_id(elem_type_id, &self.ctx.arena.borrow()),
        );

        self.builder
            .ins()
            .call(array_set_ref, &[arr.value, idx.value, tag_val, store_value]);

        Ok(result)
    }

    /// Compound assignment to field
    fn compound_assign_field(
        &mut self,
        object: &vole_frontend::Expr,
        field: vole_frontend::Symbol,
        compound: &CompoundAssignExpr,
    ) -> Result<CompiledValue, String> {
        let obj = self.expr(object)?;

        let field_name = self.ctx.interner.resolve(field);
        let (slot, field_type_id) = get_field_slot_and_type_id(obj.type_id, field_name, self.ctx)?;

        // Load current field
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let current_raw = self.call_runtime(RuntimeFn::InstanceGetField, &[obj.value, slot_val])?;

        let arena = self.ctx.arena.borrow();
        let (current_val, cranelift_ty) =
            convert_field_value_id(self.builder, current_raw, field_type_id, &arena);
        drop(arena);

        let current = CompiledValue {
            value: current_val,
            ty: cranelift_ty,
            type_id: field_type_id,
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
        self.field_cache.clear(); // Invalidate cached field reads

        Ok(result)
    }
}
