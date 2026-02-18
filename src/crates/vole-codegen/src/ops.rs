// src/codegen/ops.rs
//
// Binary and compound assignment operations - impl Cg methods.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_codegen::ir::{Function, InstructionData};

use crate::RuntimeKey;
use vole_frontend::{BinaryExpr, BinaryOp, ExprKind};
use vole_sema::implement_registry::ImplTypeId;
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::types::{CompiledValue, convert_to_type};
use crate::errors::{CodegenError, CodegenResult};

/// If `val` is defined by an `iconst` instruction, return its immediate value.
///
/// Used for constant folding boolean NOT, AND, and OR at codegen time so that
/// compile-time-constant operands avoid emitting unnecessary control-flow blocks.
pub(crate) fn try_constant_value(func: &Function, val: Value) -> Option<i64> {
    let inst = func.dfg.value_def(val).inst()?;
    if let InstructionData::UnaryImm { imm, .. } = func.dfg.insts[inst] {
        Some(imm.bits())
    } else {
        None
    }
}

/// Convert a numeric TypeId to its corresponding Cranelift type.
/// Only handles numeric types; other types will default to I64.
fn type_id_to_cranelift_type(type_id: TypeId) -> Type {
    match type_id {
        TypeId::I8 | TypeId::U8 => types::I8,
        TypeId::I16 | TypeId::U16 => types::I16,
        TypeId::I32 | TypeId::U32 => types::I32,
        TypeId::I64 | TypeId::U64 => types::I64,
        TypeId::I128 => types::I128,
        TypeId::F32 => types::F32,
        TypeId::F64 => types::F64,
        TypeId::F128 => types::F128,
        _ => types::I64, // Default for other types
    }
}

/// Compute the result TypeId for numeric binary operations.
/// Mirrors sema's numeric_result_type/integer_result_type logic to ensure consistency.
fn numeric_result_type_id(left: TypeId, right: TypeId) -> TypeId {
    // Float types take precedence, wider float wins
    if left == TypeId::F128 || right == TypeId::F128 {
        TypeId::F128
    } else if left == TypeId::F64 || right == TypeId::F64 {
        TypeId::F64
    } else if left == TypeId::F32 || right == TypeId::F32 {
        TypeId::F32
    } else {
        // Both are integers - use integer promotion rules (wider type wins)
        integer_result_type_id(left, right)
    }
}

/// Compute the result TypeId for integer binary operations.
/// Follows sema's integer promotion: wider type wins.
fn integer_result_type_id(left: TypeId, right: TypeId) -> TypeId {
    // i128 is widest
    if left == TypeId::I128 || right == TypeId::I128 {
        TypeId::I128
    }
    // 64-bit types
    else if left == TypeId::I64
        || right == TypeId::I64
        || left == TypeId::U64
        || right == TypeId::U64
    {
        // If mixing signed/unsigned 64-bit, result is i64
        TypeId::I64
    }
    // 32-bit types
    else if left == TypeId::I32
        || right == TypeId::I32
        || left == TypeId::U32
        || right == TypeId::U32
    {
        if left == TypeId::U32 && right == TypeId::U32 {
            TypeId::U32
        } else {
            TypeId::I32
        }
    }
    // 16-bit types
    else if left == TypeId::I16
        || right == TypeId::I16
        || left == TypeId::U16
        || right == TypeId::U16
    {
        if left == TypeId::U16 && right == TypeId::U16 {
            TypeId::U16
        } else {
            TypeId::I16
        }
    }
    // 8-bit types
    else if left == TypeId::U8 && right == TypeId::U8 {
        TypeId::U8
    } else {
        // Default: i8 or mixed 8-bit
        TypeId::I8
    }
}

/// Comparison condition codes for float, unsigned int, and signed int operations.
struct CmpCodes {
    float: FloatCC,
    unsigned: IntCC,
    signed: IntCC,
}

impl Cg<'_, '_, '_> {
    /// Compile a binary expression
    pub fn binary(&mut self, bin: &BinaryExpr, line: u32) -> CodegenResult<CompiledValue> {
        // Handle short-circuit evaluation for And/Or
        match bin.op {
            BinaryOp::And => return self.binary_and(bin),
            BinaryOp::Or => return self.binary_or(bin),
            _ => {}
        }

        // Try to emit FMA for floating-point add/sub with multiplication
        if let Some(result) = self.try_emit_fma(bin)? {
            return Ok(result);
        }

        // Try to optimize multiply/divide/mod by power of 2 to shifts
        if let Some(result) = self.try_emit_power_of_two(bin)? {
            return Ok(result);
        }

        let left = self.expr(&bin.left)?;

        // Handle string concatenation: string + Stringable
        if bin.op == BinaryOp::Add && left.type_id == TypeId::STRING {
            let right = self.expr(&bin.right)?;
            return self.string_concat(left, right);
        }

        let right = self.expr(&bin.right)?;

        self.binary_op(left, right, bin.op, line)
    }

    /// Try to emit FMA instruction for patterns like (x * y) + z or z + (x * y)
    /// Returns Some(result) if FMA was emitted, None otherwise
    fn try_emit_fma(&mut self, bin: &BinaryExpr) -> CodegenResult<Option<CompiledValue>> {
        // Only handle Add and Sub for FMA patterns
        if !matches!(bin.op, BinaryOp::Add | BinaryOp::Sub) {
            return Ok(None);
        }

        // Helper to unwrap Grouping expressions
        fn unwrap_grouping(expr: &vole_frontend::Expr) -> &vole_frontend::Expr {
            match &expr.kind {
                ExprKind::Grouping(inner) => unwrap_grouping(inner),
                _ => expr,
            }
        }

        let left_unwrapped = unwrap_grouping(&bin.left);
        let right_unwrapped = unwrap_grouping(&bin.right);

        // Check if left is a multiplication: (x * y) + z or (x * y) - z
        if let ExprKind::Binary(ref left_bin) = left_unwrapped.kind
            && left_bin.op == BinaryOp::Mul
        {
            // Check if this is a floating-point operation by looking at operand types
            let x = self.expr(&left_bin.left)?;
            if x.ty == types::F64 || x.ty == types::F32 {
                let y = self.expr(&left_bin.right)?;
                let z = self.expr(&bin.right)?;

                // Promote operands to the target float type (e.g. i64 → f64)
                let arena = self.env.analyzed.type_arena();
                let x_val = convert_to_type(self.builder, x, x.ty, arena);
                let y_val = convert_to_type(self.builder, y, x.ty, arena);
                let z_val = convert_to_type(self.builder, z, x.ty, arena);

                let result = if bin.op == BinaryOp::Add {
                    // (x * y) + z → fma(x, y, z)
                    self.builder.ins().fma(x_val, y_val, z_val)
                } else {
                    // (x * y) - z → fma(x, y, -z)
                    let neg_z = self.builder.ins().fneg(z_val);
                    self.builder.ins().fma(x_val, y_val, neg_z)
                };

                return Ok(Some(CompiledValue::new(result, x.ty, x.type_id)));
            }
        }

        // Check if right is a multiplication: z + (x * y)
        if bin.op == BinaryOp::Add
            && let ExprKind::Binary(ref right_bin) = right_unwrapped.kind
            && right_bin.op == BinaryOp::Mul
        {
            let z = self.expr(&bin.left)?;
            if z.ty == types::F64 || z.ty == types::F32 {
                let x = self.expr(&right_bin.left)?;
                let y = self.expr(&right_bin.right)?;

                // Promote operands to the target float type (e.g. i64 → f64)
                let arena = self.env.analyzed.type_arena();
                let x_val = convert_to_type(self.builder, x, z.ty, arena);
                let y_val = convert_to_type(self.builder, y, z.ty, arena);
                let z_val = convert_to_type(self.builder, z, z.ty, arena);

                // z + (x * y) → fma(x, y, z)
                let result = self.builder.ins().fma(x_val, y_val, z_val);

                return Ok(Some(CompiledValue::new(result, z.ty, z.type_id)));
            }
        }

        // Check for z - (x * y) pattern (FNMA)
        if bin.op == BinaryOp::Sub
            && let ExprKind::Binary(ref right_bin) = right_unwrapped.kind
            && right_bin.op == BinaryOp::Mul
        {
            let z = self.expr(&bin.left)?;
            if z.ty == types::F64 || z.ty == types::F32 {
                let x = self.expr(&right_bin.left)?;
                let y = self.expr(&right_bin.right)?;

                // Promote operands to the target float type (e.g. i64 → f64)
                let arena = self.env.analyzed.type_arena();
                let x_val = convert_to_type(self.builder, x, z.ty, arena);
                let y_val = convert_to_type(self.builder, y, z.ty, arena);
                let z_val = convert_to_type(self.builder, z, z.ty, arena);

                // z - (x * y) → fma(-x, y, z)
                let neg_x = self.builder.ins().fneg(x_val);
                let result = self.builder.ins().fma(neg_x, y_val, z_val);

                return Ok(Some(CompiledValue::new(result, z.ty, z.type_id)));
            }
        }

        Ok(None)
    }

    /// Try to optimize integer multiply/divide/mod by power of 2 to shifts/masks
    /// Returns Some(result) if optimization was applied, None otherwise
    fn try_emit_power_of_two(&mut self, bin: &BinaryExpr) -> CodegenResult<Option<CompiledValue>> {
        // Only handle Mul, Div, Mod for power-of-2 optimization
        if !matches!(bin.op, BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod) {
            return Ok(None);
        }

        /// Check if n is a positive power of 2, return the shift amount (log2)
        fn power_of_two_shift(n: i64) -> Option<i64> {
            if n > 0 && (n & (n - 1)) == 0 {
                Some(n.trailing_zeros() as i64)
            } else {
                None
            }
        }

        /// Helper to unwrap Grouping expressions
        fn unwrap_grouping(expr: &vole_frontend::Expr) -> &vole_frontend::Expr {
            match &expr.kind {
                ExprKind::Grouping(inner) => unwrap_grouping(inner),
                _ => expr,
            }
        }

        let left_unwrapped = unwrap_grouping(&bin.left);
        let right_unwrapped = unwrap_grouping(&bin.right);

        // Check if right operand is a power-of-2 integer literal
        if let ExprKind::IntLiteral(value, _) = right_unwrapped.kind
            && let Some(shift_amount) = power_of_two_shift(value)
        {
            let left = self.expr(&bin.left)?;

            // Only optimize integer types, not floats
            if left.ty == types::F64 || left.ty == types::F32 {
                return Ok(None);
            }

            // Get the literal's type from sema (or default to i64)
            let literal_type_id = self
                .get_expr_type(&right_unwrapped.id)
                .unwrap_or(TypeId::I64);

            // Apply type promotion to match sema's behavior
            let result_type_id = numeric_result_type_id(left.type_id, literal_type_id);
            let result_ty = type_id_to_cranelift_type(result_type_id);

            // Convert left operand to result type if needed
            let arena = self.env.analyzed.type_arena();
            let left_val = convert_to_type(self.builder, left, result_ty, arena);

            let shift_val = self.builder.ins().iconst(result_ty, shift_amount);

            let result = match bin.op {
                BinaryOp::Mul => {
                    // x * 2^n → x << n
                    self.builder.ins().ishl(left_val, shift_val)
                }
                BinaryOp::Div => {
                    // Only safe for unsigned: x / 2^n → x >> n
                    // Signed division rounds toward zero, but arithmetic shift rounds toward -infinity
                    if result_type_id.is_unsigned_int() {
                        self.builder.ins().ushr(left_val, shift_val)
                    } else {
                        return Ok(None); // Don't optimize signed division
                    }
                }
                BinaryOp::Mod => {
                    // Only safe for unsigned: x % 2^n → x & (2^n - 1)
                    if result_type_id.is_unsigned_int() {
                        let mask = self.builder.ins().iconst(result_ty, value - 1);
                        self.builder.ins().band(left_val, mask)
                    } else {
                        return Ok(None); // Don't optimize signed modulo
                    }
                }
                _ => return Ok(None),
            };

            return Ok(Some(CompiledValue::new(result, result_ty, result_type_id)));
        }

        // For multiplication, also check if LEFT operand is power of 2 (commutative)
        if bin.op == BinaryOp::Mul
            && let ExprKind::IntLiteral(value, _) = left_unwrapped.kind
            && let Some(shift_amount) = power_of_two_shift(value)
        {
            let right = self.expr(&bin.right)?;

            // Only optimize integer types
            if right.ty == types::F64 || right.ty == types::F32 {
                return Ok(None);
            }

            // Get the literal's type from sema (or default to i64)
            let literal_type_id = self
                .get_expr_type(&left_unwrapped.id)
                .unwrap_or(TypeId::I64);

            // Apply type promotion to match sema's behavior
            let result_type_id = numeric_result_type_id(literal_type_id, right.type_id);
            let result_ty = type_id_to_cranelift_type(result_type_id);

            // Convert right operand to result type if needed
            let arena = self.env.analyzed.type_arena();
            let right_val = convert_to_type(self.builder, right, result_ty, arena);

            let shift_val = self.builder.ins().iconst(result_ty, shift_amount);
            // 2^n * x → x << n
            let result = self.builder.ins().ishl(right_val, shift_val);

            return Ok(Some(CompiledValue::new(result, result_ty, result_type_id)));
        }

        Ok(None)
    }

    /// Concatenate two values as strings.
    /// Left must be a string, right will be converted via to_string() if not already string.
    fn string_concat(
        &mut self,
        mut left: CompiledValue,
        mut right: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        // Get the right operand as a string
        let right_converted = if right.type_id == TypeId::STRING {
            // Right is already a string, use it directly
            None
        } else {
            // Right is not a string, call to_string() on it (allocates a new string)
            Some(self.call_to_string(&right)?)
        };
        let right_string = right_converted.unwrap_or(right.value);

        // Call vole_string_concat(left, right_string)
        let concat_result =
            self.call_runtime(RuntimeKey::StringConcat, &[left.value, right_string])?;

        // Consume RC operands used by string concat
        self.consume_rc_value(&mut left)?;
        self.consume_rc_value(&mut right)?;

        // Dec the to_string intermediate if we created one (it's a fresh allocation
        // that was only needed for the concat call)
        if let Some(to_string_val) = right_converted {
            self.emit_rc_dec(to_string_val)?;
        }

        Ok(self.string_temp(concat_result))
    }

    /// Call to_string() on a value via the Stringable interface.
    /// Returns the resulting string value.
    fn call_to_string(&mut self, val: &CompiledValue) -> CodegenResult<Value> {
        let arena = self.arena();
        let impl_type_id = ImplTypeId::from_type_id(val.type_id, arena, self.registry())
            .ok_or_else(|| {
                CodegenError::not_found("ImplTypeId for type_id", format!("{:?}", val.type_id))
            })?;

        // Look up to_string method via query
        let method_id = self.query().method_name_id_by_str("to_string");

        let method_impl = self
            .analyzed()
            .implement_registry()
            .get_method(&impl_type_id, method_id)
            .ok_or_else(|| {
                CodegenError::not_found("to_string method", format!("{:?}", val.type_id))
            })?;

        // Check if it's an external (native) method
        if let Some(ref external_info) = method_impl.external_info {
            // Call the external function directly
            let string_type_id = self.arena().primitives.string;
            let result = self.call_external_id(external_info, &[val.value], string_type_id)?;
            return Ok(result.value);
        }

        // Otherwise, it's a Vole method - look up via unified method_func_keys
        // Use type's NameId directly for stable lookup across analyzer instances
        let type_name_id = impl_type_id.name_id();
        let func_key = *self
            .method_func_keys()
            .get(&(type_name_id, method_id))
            .ok_or_else(|| {
                CodegenError::not_found("method info", "to_string in method_func_keys")
            })?;

        let func_ref = self.func_ref(func_key)?;

        // Call the method with `self` (the value) as the only argument
        let coerced = self.coerce_call_args(func_ref, &[val.value]);
        let call = self.builder.ins().call(func_ref, &coerced);
        let results = self.builder.inst_results(call);

        results
            .first()
            .copied()
            .ok_or_else(|| CodegenError::internal("to_string method did not return a value"))
    }

    /// Short-circuit AND evaluation
    fn binary_and(&mut self, bin: &BinaryExpr) -> CodegenResult<CompiledValue> {
        let left = self.expr(&bin.left)?;

        // Constant-fold: if left is a known constant, skip control flow.
        if let Some(c) = try_constant_value(self.builder.func, left.value) {
            if c == 0 {
                // false && _ => false (skip evaluating right)
                return Ok(self.bool_const(false));
            }
            // true && right => right
            let right = self.expr(&bin.right)?;
            let right_val = if self.builder.func.dfg.value_type(right.value) != types::I8 {
                self.builder.ins().ireduce(types::I8, right.value)
            } else {
                right.value
            };
            return Ok(self.bool_value(right_val));
        }

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I8);

        self.builder
            .ins()
            .brif(left.value, then_block, &[], else_block, &[]);

        // Then block: left was true, evaluate right
        self.switch_and_seal(then_block);
        let right = self.expr(&bin.right)?;
        // Right operand may be wider than i8 (e.g. from nested boolean
        // expressions that flow through i64 block parameters), narrow it.
        let right_val = if self.builder.func.dfg.value_type(right.value) != types::I8 {
            self.builder.ins().ireduce(types::I8, right.value)
        } else {
            right.value
        };
        let right_arg = BlockArg::from(right_val);
        self.builder.ins().jump(merge_block, &[right_arg]);

        // Else block: left was false, short-circuit with false
        self.switch_and_seal(else_block);
        let false_val = self.builder.ins().iconst(types::I8, 0);
        let false_arg = BlockArg::from(false_val);
        self.builder.ins().jump(merge_block, &[false_arg]);

        // Merge block — values cached in either branch do not dominate here
        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();
        let result = self.builder.block_params(merge_block)[0];

        Ok(self.bool_value(result))
    }

    /// Short-circuit OR evaluation
    fn binary_or(&mut self, bin: &BinaryExpr) -> CodegenResult<CompiledValue> {
        let left = self.expr(&bin.left)?;

        // Constant-fold: if left is a known constant, skip control flow.
        if let Some(c) = try_constant_value(self.builder.func, left.value) {
            if c != 0 {
                // true || _ => true (skip evaluating right)
                return Ok(self.bool_const(true));
            }
            // false || right => right
            let right = self.expr(&bin.right)?;
            let right_val = if self.builder.func.dfg.value_type(right.value) != types::I8 {
                self.builder.ins().ireduce(types::I8, right.value)
            } else {
                right.value
            };
            return Ok(self.bool_value(right_val));
        }

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I8);

        self.builder
            .ins()
            .brif(left.value, then_block, &[], else_block, &[]);

        // Then block: left was true, short-circuit with true
        self.switch_and_seal(then_block);
        let true_val = self.builder.ins().iconst(types::I8, 1);
        let true_arg = BlockArg::from(true_val);
        self.builder.ins().jump(merge_block, &[true_arg]);

        // Else block: left was false, evaluate right
        self.switch_and_seal(else_block);
        let right = self.expr(&bin.right)?;
        // Right operand may be wider than i8 (e.g. from nested boolean
        // expressions that flow through i64 block parameters), narrow it.
        let right_val = if self.builder.func.dfg.value_type(right.value) != types::I8 {
            self.builder.ins().ireduce(types::I8, right.value)
        } else {
            right.value
        };
        let right_arg = BlockArg::from(right_val);
        self.builder.ins().jump(merge_block, &[right_arg]);

        // Merge block — values cached in either branch do not dominate here
        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();
        let result = self.builder.block_params(merge_block)[0];

        Ok(self.bool_value(result))
    }

    /// Compile a binary operation on two values
    pub fn binary_op(
        &mut self,
        mut left: CompiledValue,
        mut right: CompiledValue,
        op: BinaryOp,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        // Handle optional/nil comparisons specially
        // When comparing optional == nil or optional != nil, we need to check the tag
        if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
            // Check if left is optional and right is nil
            if self.arena().is_optional(left.type_id) && right.type_id.is_nil() {
                return self.optional_nil_compare(left, op);
            }
            // Check if right is optional and left is nil
            if self.arena().is_optional(right.type_id) && left.type_id.is_nil() {
                return self.optional_nil_compare(right, op);
            }
            // Check if left is optional and right is a compatible value type (using TypeId)
            let arena = self.arena();
            if let Some(inner_type_id) = arena.unwrap_optional(left.type_id)
                && (inner_type_id == right.type_id
                    || (arena.is_integer(inner_type_id) && arena.is_integer(right.type_id)))
            {
                return self.optional_value_compare(left, right, op);
            }
            // Check if right is optional and left is a compatible value type (using TypeId)
            if let Some(inner_type_id) = arena.unwrap_optional(right.type_id)
                && (inner_type_id == left.type_id
                    || (arena.is_integer(inner_type_id) && arena.is_integer(left.type_id)))
            {
                return self.optional_value_compare(right, left, op);
            }
            // Check if both operands are structs
            if self.arena().is_struct(left.type_id) && self.arena().is_struct(right.type_id) {
                return self.struct_equality(left, right, op);
            }
        }

        let left_type_id = left.type_id;
        let left_is_string = left_type_id == TypeId::STRING;

        // Determine result type using type promotion rules.
        // For numeric types, use sema's numeric_result_type logic.
        // For non-numeric types (like strings), use left's type directly.
        let (result_type_id, result_ty) = if left_type_id.is_numeric() && right.type_id.is_numeric()
        {
            let promoted = numeric_result_type_id(left_type_id, right.type_id);
            (promoted, type_id_to_cranelift_type(promoted))
        } else {
            (left_type_id, left.ty)
        };

        let (left_val, right_val) = if result_ty == types::F128 {
            (
                self.coerce_value_to_f128(left)?,
                self.coerce_value_to_f128(right)?,
            )
        } else {
            // Convert operands - access arena via env to avoid borrow conflict
            let arena = self.env.analyzed.type_arena();
            (
                convert_to_type(self.builder, left, result_ty, arena),
                convert_to_type(self.builder, right, result_ty, arena),
            )
        };

        let result = match op {
            BinaryOp::Add => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Add, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fadd(left_val, right_val)
                } else {
                    self.builder.ins().iadd(left_val, right_val)
                }
            }
            BinaryOp::Sub => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Sub, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fsub(left_val, right_val)
                } else {
                    self.builder.ins().isub(left_val, right_val)
                }
            }
            BinaryOp::Mul => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Mul, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fmul(left_val, right_val)
                } else {
                    self.builder.ins().imul(left_val, right_val)
                }
            }
            BinaryOp::Div => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Div, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fdiv(left_val, right_val)
                } else if result_ty == types::I128 {
                    // Cranelift x64 doesn't support sdiv.i128; use runtime helper
                    self.call_runtime(RuntimeKey::I128Sdiv, &[left_val, right_val])?
                } else if left_type_id.is_unsigned_int() {
                    // Unsigned division: check for division by zero
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.builder.ins().udiv(left_val, right_val)
                } else {
                    // Signed division: check for division by zero and MIN/-1 overflow
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.emit_signed_div_overflow_check(left_val, right_val, result_ty, line)?;
                    self.builder.ins().sdiv(left_val, right_val)
                }
            }
            BinaryOp::Mod => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Rem, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    let div = self.builder.ins().fdiv(left_val, right_val);
                    let floor = self.builder.ins().floor(div);
                    let mul = self.builder.ins().fmul(floor, right_val);
                    self.builder.ins().fsub(left_val, mul)
                } else if result_ty == types::I128 {
                    // Cranelift x64 doesn't support srem.i128; use runtime helper
                    self.call_runtime(RuntimeKey::I128Srem, &[left_val, right_val])?
                } else if left_type_id.is_unsigned_int() {
                    // Unsigned remainder: check for division by zero
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.builder.ins().urem(left_val, right_val)
                } else {
                    // Signed remainder: check for division by zero and MIN/-1 overflow
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.emit_signed_div_overflow_check(left_val, right_val, result_ty, line)?;
                    self.builder.ins().srem(left_val, right_val)
                }
            }
            BinaryOp::Eq => {
                if left_is_string {
                    self.string_eq(left_val, right_val)?
                } else if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Eq, left_val, right_val)?
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
                } else if result_ty == types::F128 {
                    let eq = self.call_f128_cmp(RuntimeKey::F128Eq, left_val, right_val)?;
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
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Lt, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_type_id,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::LessThan,
                            unsigned: IntCC::UnsignedLessThan,
                            signed: IntCC::SignedLessThan,
                        },
                    )
                }
            }
            BinaryOp::Gt => {
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Gt, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_type_id,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::GreaterThan,
                            unsigned: IntCC::UnsignedGreaterThan,
                            signed: IntCC::SignedGreaterThan,
                        },
                    )
                }
            }
            BinaryOp::Le => {
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Le, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_type_id,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::LessThanOrEqual,
                            unsigned: IntCC::UnsignedLessThanOrEqual,
                            signed: IntCC::SignedLessThanOrEqual,
                        },
                    )
                }
            }
            BinaryOp::Ge => {
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Ge, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_type_id,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::GreaterThanOrEqual,
                            unsigned: IntCC::UnsignedGreaterThanOrEqual,
                            signed: IntCC::SignedGreaterThanOrEqual,
                        },
                    )
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

        // Consume RC operands used by string comparison
        if left_is_string && matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
            self.consume_rc_value(&mut left)?;
            self.consume_rc_value(&mut right)?;
        }

        // For comparison ops, result is bool; otherwise use the promoted type
        let (final_ty, final_type_id) = match op {
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::Le
            | BinaryOp::Ge => (types::I8, TypeId::BOOL),
            BinaryOp::And | BinaryOp::Or => unreachable!(),
            _ => (result_ty, result_type_id),
        };

        Ok(CompiledValue::new(result, final_ty, final_type_id))
    }

    fn coerce_value_to_f128(&mut self, value: CompiledValue) -> CodegenResult<Value> {
        match value.ty {
            ty if ty == types::F128 => Ok(value.value),
            ty if ty == types::F64 => {
                let bits = self.call_runtime(RuntimeKey::F64ToF128, &[value.value])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            ty if ty == types::F32 => {
                let bits = self.call_runtime(RuntimeKey::F32ToF128, &[value.value])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            ty if ty == types::I128 => {
                let bits = self.call_runtime(RuntimeKey::I128ToF128, &[value.value])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            ty if ty.is_int() => {
                let v = if ty == types::I64 {
                    value.value
                } else {
                    self.builder.ins().sextend(types::I64, value.value)
                };
                let bits = self.call_runtime(RuntimeKey::I64ToF128, &[v])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            _ => Err(CodegenError::type_mismatch(
                "f128 coercion",
                "numeric type",
                format!("{:?}", value.ty),
            )),
        }
    }

    fn call_f128_binary_op(
        &mut self,
        key: RuntimeKey,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        let left_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), left);
        let right_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), right);
        let result_bits = self.call_runtime(key, &[left_bits, right_bits])?;
        Ok(self
            .builder
            .ins()
            .bitcast(types::F128, MemFlags::new(), result_bits))
    }

    fn call_f128_cmp(
        &mut self,
        key: RuntimeKey,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        let left_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), left);
        let right_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), right);
        self.call_runtime(key, &[left_bits, right_bits])
    }

    /// String equality comparison
    fn string_eq(&mut self, left: Value, right: Value) -> CodegenResult<Value> {
        if self.funcs().has_runtime(RuntimeKey::StringEq) {
            self.call_runtime(RuntimeKey::StringEq, &[left, right])
        } else {
            Ok(self.builder.ins().icmp(IntCC::Equal, left, right))
        }
    }

    /// Struct equality: compare all flat slots field-by-field.
    /// For Eq, returns true iff all slots are equal; for Ne, returns true iff any slot differs.
    fn struct_equality(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
        op: BinaryOp,
    ) -> CodegenResult<CompiledValue> {
        let flat_count = self.struct_flat_slot_count(left.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("struct_equality", "struct type", "non-struct")
        })?;

        // Start with true (1) - all fields equal so far
        let mut result = self.builder.ins().iconst(types::I8, 1);

        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let left_slot =
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), left.value, offset);
            let right_slot =
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), right.value, offset);
            let eq = self.builder.ins().icmp(IntCC::Equal, left_slot, right_slot);
            result = self.builder.ins().band(result, eq);
        }

        // For NotEq, negate the result
        if op == BinaryOp::Ne {
            let one = self.builder.ins().iconst(types::I8, 1);
            result = self.builder.ins().bxor(result, one);
        }

        Ok(self.bool_value(result))
    }

    /// Compare an optional value with nil
    /// Returns true if the optional's tag matches the nil tag
    fn optional_nil_compare(
        &mut self,
        optional: CompiledValue,
        op: BinaryOp,
    ) -> CodegenResult<CompiledValue> {
        // Find the position of nil in the variants (this is the nil tag value)
        let nil_tag = self.find_nil_variant(optional.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("optional_nil_compare", "optional type", "non-optional")
        })?;

        // Compare tag with nil_tag
        let result = match op {
            BinaryOp::Eq => self.tag_eq(optional.value, nil_tag as i64),
            BinaryOp::Ne => self.tag_ne(optional.value, nil_tag as i64),
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
    ) -> CodegenResult<CompiledValue> {
        // Find the position of nil in the variants (this is the nil tag value)
        let nil_tag = self.find_nil_variant(optional.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("optional_value_compare", "optional type", "non-optional")
        })?;

        // Check if not nil (tag != nil_tag)
        let is_not_nil = self.tag_ne(optional.value, nil_tag as i64);

        // Load the payload (at offset 8) with the correct type
        // The payload type matches the inner (non-nil) type of the optional (using TypeId)
        let inner_type_id = {
            let arena = self.arena();
            arena
                .unwrap_optional(optional.type_id)
                .unwrap_or_else(|| arena.i64())
        };
        let payload_cranelift_type = self.cranelift_type(inner_type_id);
        let payload =
            self.load_union_payload(optional.value, optional.type_id, payload_cranelift_type);

        // Compare payload with value (extend if necessary to match types)
        let values_equal = if value.ty.is_float() {
            self.builder
                .ins()
                .fcmp(FloatCC::Equal, payload, value.value)
        } else if value.ty.is_int() {
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
        } else {
            panic!(
                "optional_eq: unexpected Cranelift type {:?} for equality comparison",
                value.ty
            )
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

    /// Emit a comparison instruction, dispatching based on type (float vs int, signed vs unsigned).
    fn emit_cmp(
        &mut self,
        result_ty: Type,
        left_type_id: TypeId,
        left_val: Value,
        right_val: Value,
        codes: CmpCodes,
    ) -> Value {
        if result_ty == types::F64 || result_ty == types::F32 {
            self.builder.ins().fcmp(codes.float, left_val, right_val)
        } else if left_type_id.is_unsigned_int() {
            self.builder.ins().icmp(codes.unsigned, left_val, right_val)
        } else {
            self.builder.ins().icmp(codes.signed, left_val, right_val)
        }
    }

    /// Emit division by zero check for integer division/remainder.
    /// Creates a branch: if divisor == 0, panic; else continue.
    /// Returns the continue block that should be used for subsequent code.
    fn emit_div_by_zero_check(&mut self, divisor: Value, line: u32) -> CodegenResult<Block> {
        let is_zero = self.builder.ins().icmp_imm(IntCC::Equal, divisor, 0);

        let panic_block = self.builder.create_block();
        let continue_block = self.builder.create_block();

        self.builder
            .ins()
            .brif(is_zero, panic_block, &[], continue_block, &[]);

        // Panic block
        self.switch_and_seal(panic_block);
        self.emit_panic_static("division by zero", line)?;

        // Continue block
        self.switch_and_seal(continue_block);

        Ok(continue_block)
    }

    /// Emit signed division overflow check for MIN / -1 case.
    /// For signed division, INT_MIN / -1 causes overflow.
    /// Creates a branch: if (dividend == MIN && divisor == -1), panic; else continue.
    fn emit_signed_div_overflow_check(
        &mut self,
        dividend: Value,
        divisor: Value,
        result_ty: Type,
        line: u32,
    ) -> CodegenResult<()> {
        // Get MIN value for the integer type
        let min_val = match result_ty {
            types::I8 => i8::MIN as i64,
            types::I16 => i16::MIN as i64,
            types::I32 => i32::MIN as i64,
            types::I64 => i64::MIN,
            _ => return Ok(()), // Not a standard signed integer type
        };

        // Check if dividend == MIN
        let is_min = self.builder.ins().icmp_imm(IntCC::Equal, dividend, min_val);

        // Check if divisor == -1
        let is_neg_one = self.builder.ins().icmp_imm(IntCC::Equal, divisor, -1);

        // Combine: both must be true for overflow
        let would_overflow = self.builder.ins().band(is_min, is_neg_one);

        let panic_block = self.builder.create_block();
        let continue_block = self.builder.create_block();

        self.builder
            .ins()
            .brif(would_overflow, panic_block, &[], continue_block, &[]);

        // Panic block
        self.switch_and_seal(panic_block);
        self.emit_panic_static("integer overflow in division", line)?;

        // Continue block
        self.switch_and_seal(continue_block);

        Ok(())
    }
}
