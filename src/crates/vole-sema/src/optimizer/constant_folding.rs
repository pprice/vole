//! Constant folding optimization pass.
//!
//! This pass evaluates constant expressions at compile time, replacing them
//! with literal values. It also applies algebraic optimizations:
//!
//! - Division by constant: `x / 4.0` -> `x * 0.25` (3x faster on x86)
//! - Division by power-of-2: `x / 8` -> `x >> 3` (for unsigned integers)
//! - Constant binary operations: `2 + 3` -> `5`
//!
//! # Example
//!
//! Before optimization:
//! ```vole
//! let x = 2.0 * y / 4000.0
//! ```
//!
//! After optimization:
//! ```vole
//! let x = 2.0 * y * 0.00025  // 1/4000
//! ```

use crate::ExpressionData;
use std::collections::HashMap;
use vole_frontend::{
    BinaryExpr, BinaryOp, Block, Decl, Expr, ExprKind, FuncBody, FuncDecl, Interner, NumericSuffix,
    Program, Stmt, Symbol,
};

/// Statistics from constant folding.
#[derive(Debug, Clone, Default)]
pub struct FoldingStats {
    /// Number of constant expressions folded to literals
    pub constants_folded: usize,
    /// Number of divisions replaced with multiplication
    pub div_to_mul: usize,
    /// Number of divisions replaced with bit shifts
    pub div_to_shift: usize,
    /// Number of constant propagations (variable references replaced with literals)
    pub constants_propagated: usize,
}

/// A constant value that can be computed at compile time.
#[derive(Debug, Clone)]
enum ConstValue {
    Int(i64, Option<NumericSuffix>),
    Float(f64, Option<NumericSuffix>),
    Bool(bool),
}

impl ConstValue {
    /// Convert to an expression kind
    fn to_expr_kind(&self) -> ExprKind {
        match self {
            ConstValue::Int(v, suffix) => ExprKind::IntLiteral(*v, *suffix),
            ConstValue::Float(v, suffix) => ExprKind::FloatLiteral(*v, *suffix),
            ConstValue::Bool(v) => ExprKind::BoolLiteral(*v),
        }
    }
}

/// Run constant folding on the program.
pub fn fold_constants(
    program: &mut Program,
    interner: &Interner,
    expr_data: &mut ExpressionData,
) -> FoldingStats {
    let mut folder = ConstantFolder::new(interner, expr_data);
    folder.fold_program(program);
    folder.stats
}

/// The constant folder visitor.
struct ConstantFolder<'a> {
    #[allow(dead_code)] // Will be used for more complex folding later
    interner: &'a Interner,
    expr_data: &'a mut ExpressionData,
    stats: FoldingStats,
    /// Map from immutable variable symbols to their constant values.
    /// Used for constant propagation.
    constant_bindings: HashMap<Symbol, ConstValue>,
}

impl<'a> ConstantFolder<'a> {
    fn new(interner: &'a Interner, expr_data: &'a mut ExpressionData) -> Self {
        Self {
            interner,
            expr_data,
            stats: FoldingStats::default(),
            constant_bindings: HashMap::new(),
        }
    }

    /// Fold constants in the entire program.
    fn fold_program(&mut self, program: &mut Program) {
        for decl in &mut program.declarations {
            self.fold_decl(decl);
        }
    }

    /// Fold constants in a declaration.
    fn fold_decl(&mut self, decl: &mut Decl) {
        match decl {
            Decl::Function(func) => self.fold_func(func),
            Decl::Tests(tests) => {
                for inner_decl in &mut tests.decls {
                    self.fold_decl(inner_decl);
                }
                for test in &mut tests.tests {
                    // Each test has its own fresh scope
                    let saved_bindings = std::mem::take(&mut self.constant_bindings);
                    self.fold_func_body(&mut test.body);
                    self.constant_bindings = saved_bindings;
                }
            }
            Decl::Let(let_stmt) => {
                if let vole_frontend::LetInit::Expr(ref mut expr) = let_stmt.init {
                    self.fold_expr(expr);

                    // For immutable bindings (not `let mut`), record constant values
                    // for later propagation in subsequent declarations.
                    // Only propagate if there's no explicit type annotation (see
                    // comment in fold_stmt for rationale).
                    if !let_stmt.mutable
                        && let_stmt.ty.is_none()
                        && let Some(const_val) = self.get_const_value(expr)
                    {
                        self.constant_bindings.insert(let_stmt.name, const_val);
                    }
                }
            }
            Decl::LetTuple(let_tuple) => {
                self.fold_expr(&mut let_tuple.init);
            }
            Decl::Class(class) => {
                for field in &mut class.fields {
                    if let Some(ref mut default) = field.default_value {
                        self.fold_expr(default);
                    }
                }
                for method in &mut class.methods {
                    self.fold_func(method);
                }
            }
            Decl::Struct(_)
            | Decl::Interface(_)
            | Decl::Implement(_)
            | Decl::Error(_)
            | Decl::Sentinel(_)
            | Decl::External(_) => {}
        }
    }

    /// Fold constants in a function declaration.
    fn fold_func(&mut self, func: &mut FuncDecl) {
        // Fold default parameter values (using outer scope's constants)
        for param in &mut func.params {
            if let Some(ref mut default) = param.default_value {
                self.fold_expr(default);
            }
        }
        // Save current constant bindings and start fresh for this function
        let saved_bindings = std::mem::take(&mut self.constant_bindings);
        self.fold_func_body(&mut func.body);
        // Restore outer scope's constant bindings
        self.constant_bindings = saved_bindings;
    }

    /// Fold constants in a function body.
    fn fold_func_body(&mut self, body: &mut FuncBody) {
        match body {
            FuncBody::Block(block) => self.fold_block(block),
            FuncBody::Expr(expr) => self.fold_expr(expr),
        }
    }

    /// Fold constants in a block.
    fn fold_block(&mut self, block: &mut Block) {
        for stmt in &mut block.stmts {
            self.fold_stmt(stmt);
        }
    }

    /// Fold constants in a statement.
    fn fold_stmt(&mut self, stmt: &mut Stmt) {
        match stmt {
            Stmt::Let(let_stmt) => {
                if let vole_frontend::LetInit::Expr(ref mut expr) = let_stmt.init {
                    self.fold_expr(expr);

                    // For immutable bindings (not `let mut`), record constant values
                    // for later propagation.
                    // IMPORTANT: Only propagate if there's no explicit type annotation.
                    // If there's a type annotation, the variable might be stored as a
                    // union/optional (e.g., `let x: i32? = 42`), and propagating the
                    // literal would change the semantics (x is a tagged union pointer,
                    // not just the value 42).
                    if !let_stmt.mutable
                        && let_stmt.ty.is_none()
                        && let Some(const_val) = self.get_const_value(expr)
                    {
                        self.constant_bindings.insert(let_stmt.name, const_val);
                    }
                }
            }
            Stmt::LetTuple(let_tuple) => {
                self.fold_expr(&mut let_tuple.init);
            }
            Stmt::Expr(expr_stmt) => {
                self.fold_expr(&mut expr_stmt.expr);
            }
            Stmt::While(while_stmt) => {
                self.fold_expr(&mut while_stmt.condition);
                self.fold_block(&mut while_stmt.body);
            }
            Stmt::For(for_stmt) => {
                self.fold_expr(&mut for_stmt.iterable);
                self.fold_block(&mut for_stmt.body);
            }
            Stmt::If(if_stmt) => {
                self.fold_expr(&mut if_stmt.condition);
                self.fold_block(&mut if_stmt.then_branch);
                if let Some(ref mut else_branch) = if_stmt.else_branch {
                    self.fold_block(else_branch);
                }
            }
            Stmt::Return(ret) => {
                if let Some(ref mut expr) = ret.value {
                    self.fold_expr(expr);
                }
            }
            Stmt::Raise(raise) => {
                for field in &mut raise.fields {
                    self.fold_expr(&mut field.value);
                }
            }
            Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    /// Fold constants in an expression (main entry point).
    ///
    /// This recursively visits all sub-expressions and applies folding
    /// transformations. The expression is modified in place.
    fn fold_expr(&mut self, expr: &mut Expr) {
        // First, try constant propagation for identifiers
        if let ExprKind::Identifier(sym) = &expr.kind
            && let Some(const_val) = self.constant_bindings.get(sym).cloned()
        {
            expr.kind = const_val.to_expr_kind();
            self.stats.constants_propagated += 1;
            return;
        }

        // Then, recursively fold sub-expressions
        self.fold_expr_children(expr);

        // Then try to fold this expression
        if let Some(folded) = self.try_fold_expr(expr) {
            // Update the expression in place
            expr.kind = folded.to_expr_kind();
            self.stats.constants_folded += 1;
        } else {
            // Try algebraic optimizations (division -> multiplication)
            self.try_optimize_division(expr);
        }
    }

    /// Recursively fold children of an expression.
    fn fold_expr_children(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Binary(bin) => {
                self.fold_expr(&mut bin.left);
                self.fold_expr(&mut bin.right);
            }
            ExprKind::Unary(unary) => {
                self.fold_expr(&mut unary.operand);
            }
            ExprKind::Grouping(inner) => {
                self.fold_expr(inner);
            }
            ExprKind::Call(call) => {
                self.fold_expr(&mut call.callee);
                for arg in &mut call.args {
                    self.fold_expr(arg);
                }
            }
            ExprKind::ArrayLiteral(elements) => {
                for elem in elements {
                    self.fold_expr(elem);
                }
            }
            ExprKind::RepeatLiteral { element, .. } => {
                self.fold_expr(element);
            }
            ExprKind::Index(idx) => {
                self.fold_expr(&mut idx.object);
                self.fold_expr(&mut idx.index);
            }
            ExprKind::Match(m) => {
                self.fold_expr(&mut m.scrutinee);
                for arm in &mut m.arms {
                    if let Some(ref mut guard) = arm.guard {
                        self.fold_expr(guard);
                    }
                    self.fold_expr(&mut arm.body);
                }
            }
            ExprKind::NullCoalesce(nc) => {
                self.fold_expr(&mut nc.value);
                self.fold_expr(&mut nc.default);
            }
            ExprKind::Is(is) => {
                self.fold_expr(&mut is.value);
            }
            ExprKind::Lambda(lambda) => {
                for param in &mut lambda.params {
                    if let Some(ref mut default) = param.default_value {
                        self.fold_expr(default);
                    }
                }
                // Lambdas capture their enclosing scope, so they inherit constant bindings
                // But we need to save/restore so any new bindings inside don't leak out
                let saved_bindings = self.constant_bindings.clone();
                self.fold_func_body(&mut lambda.body);
                self.constant_bindings = saved_bindings;
            }
            ExprKind::StructLiteral(lit) => {
                for field in &mut lit.fields {
                    self.fold_expr(&mut field.value);
                }
            }
            ExprKind::FieldAccess(fa) => {
                self.fold_expr(&mut fa.object);
            }
            ExprKind::OptionalChain(oc) => {
                self.fold_expr(&mut oc.object);
            }
            ExprKind::MethodCall(mc) => {
                self.fold_expr(&mut mc.object);
                for arg in &mut mc.args {
                    self.fold_expr(arg);
                }
            }
            ExprKind::Try(inner) => {
                self.fold_expr(inner);
            }
            ExprKind::Yield(y) => {
                self.fold_expr(&mut y.value);
            }
            ExprKind::Block(block) => {
                for stmt in &mut block.stmts {
                    self.fold_stmt(stmt);
                }
                if let Some(ref mut trailing) = block.trailing_expr {
                    self.fold_expr(trailing);
                }
            }
            ExprKind::If(if_expr) => {
                self.fold_expr(&mut if_expr.condition);
                self.fold_expr(&mut if_expr.then_branch);
                if let Some(ref mut else_branch) = if_expr.else_branch {
                    self.fold_expr(else_branch);
                }
            }
            ExprKind::When(when) => {
                for arm in &mut when.arms {
                    if let Some(ref mut cond) = arm.condition {
                        self.fold_expr(cond);
                    }
                    self.fold_expr(&mut arm.body);
                }
            }
            ExprKind::Assign(assign) => {
                self.fold_expr(&mut assign.value);
            }
            ExprKind::CompoundAssign(compound) => {
                self.fold_expr(&mut compound.value);
            }
            ExprKind::Range(range) => {
                self.fold_expr(&mut range.start);
                self.fold_expr(&mut range.end);
            }
            ExprKind::InterpolatedString(parts) => {
                for part in parts {
                    if let vole_frontend::StringPart::Expr(e) = part {
                        self.fold_expr(e);
                    }
                }
            }
            // Literals and identifiers have no children
            ExprKind::IntLiteral(_, _)
            | ExprKind::FloatLiteral(_, _)
            | ExprKind::BoolLiteral(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::Identifier(_)
            | ExprKind::Nil
            | ExprKind::Done
            | ExprKind::Unreachable
            | ExprKind::TypeLiteral(_)
            | ExprKind::Import(_) => {}
        }
    }

    /// Try to evaluate a constant expression.
    fn try_fold_expr(&self, expr: &Expr) -> Option<ConstValue> {
        match &expr.kind {
            ExprKind::Binary(bin) => self.try_fold_binary(bin),
            ExprKind::Unary(unary) => self.try_fold_unary(unary),
            ExprKind::Grouping(inner) => self.try_fold_expr(inner),
            _ => None,
        }
    }

    /// Try to fold a binary expression.
    fn try_fold_binary(&self, bin: &BinaryExpr) -> Option<ConstValue> {
        let left = self.get_const_value(&bin.left)?;
        let right = self.get_const_value(&bin.right)?;

        match (left, right) {
            // Integer operations
            (ConstValue::Int(l, l_suffix), ConstValue::Int(r, r_suffix)) => {
                let result_suffix = l_suffix.or(r_suffix);
                match bin.op {
                    BinaryOp::Add => Some(ConstValue::Int(l.wrapping_add(r), result_suffix)),
                    BinaryOp::Sub => Some(ConstValue::Int(l.wrapping_sub(r), result_suffix)),
                    BinaryOp::Mul => Some(ConstValue::Int(l.wrapping_mul(r), result_suffix)),
                    BinaryOp::Div if r != 0 => Some(ConstValue::Int(l / r, result_suffix)),
                    BinaryOp::Mod if r != 0 => Some(ConstValue::Int(l % r, result_suffix)),
                    BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
                    BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
                    BinaryOp::Lt => Some(ConstValue::Bool(l < r)),
                    BinaryOp::Gt => Some(ConstValue::Bool(l > r)),
                    BinaryOp::Le => Some(ConstValue::Bool(l <= r)),
                    BinaryOp::Ge => Some(ConstValue::Bool(l >= r)),
                    BinaryOp::BitAnd => Some(ConstValue::Int(l & r, result_suffix)),
                    BinaryOp::BitOr => Some(ConstValue::Int(l | r, result_suffix)),
                    BinaryOp::BitXor => Some(ConstValue::Int(l ^ r, result_suffix)),
                    BinaryOp::Shl => Some(ConstValue::Int(l << (r & 63), result_suffix)),
                    BinaryOp::Shr => Some(ConstValue::Int(l >> (r & 63), result_suffix)),
                    _ => None,
                }
            }
            // Float operations
            (ConstValue::Float(l, l_suffix), ConstValue::Float(r, r_suffix)) => {
                let result_suffix = l_suffix.or(r_suffix);
                match bin.op {
                    BinaryOp::Add => Some(ConstValue::Float(l + r, result_suffix)),
                    BinaryOp::Sub => Some(ConstValue::Float(l - r, result_suffix)),
                    BinaryOp::Mul => Some(ConstValue::Float(l * r, result_suffix)),
                    BinaryOp::Div => Some(ConstValue::Float(l / r, result_suffix)),
                    BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
                    BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
                    BinaryOp::Lt => Some(ConstValue::Bool(l < r)),
                    BinaryOp::Gt => Some(ConstValue::Bool(l > r)),
                    BinaryOp::Le => Some(ConstValue::Bool(l <= r)),
                    BinaryOp::Ge => Some(ConstValue::Bool(l >= r)),
                    _ => None,
                }
            }
            // Mixed int/float (promote to float)
            (ConstValue::Int(l, _), ConstValue::Float(r, suffix)) => {
                let l = l as f64;
                match bin.op {
                    BinaryOp::Add => Some(ConstValue::Float(l + r, suffix)),
                    BinaryOp::Sub => Some(ConstValue::Float(l - r, suffix)),
                    BinaryOp::Mul => Some(ConstValue::Float(l * r, suffix)),
                    BinaryOp::Div => Some(ConstValue::Float(l / r, suffix)),
                    BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
                    BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
                    BinaryOp::Lt => Some(ConstValue::Bool(l < r)),
                    BinaryOp::Gt => Some(ConstValue::Bool(l > r)),
                    BinaryOp::Le => Some(ConstValue::Bool(l <= r)),
                    BinaryOp::Ge => Some(ConstValue::Bool(l >= r)),
                    _ => None,
                }
            }
            (ConstValue::Float(l, suffix), ConstValue::Int(r, _)) => {
                let r = r as f64;
                match bin.op {
                    BinaryOp::Add => Some(ConstValue::Float(l + r, suffix)),
                    BinaryOp::Sub => Some(ConstValue::Float(l - r, suffix)),
                    BinaryOp::Mul => Some(ConstValue::Float(l * r, suffix)),
                    BinaryOp::Div => Some(ConstValue::Float(l / r, suffix)),
                    BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
                    BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
                    BinaryOp::Lt => Some(ConstValue::Bool(l < r)),
                    BinaryOp::Gt => Some(ConstValue::Bool(l > r)),
                    BinaryOp::Le => Some(ConstValue::Bool(l <= r)),
                    BinaryOp::Ge => Some(ConstValue::Bool(l >= r)),
                    _ => None,
                }
            }
            // Boolean operations
            (ConstValue::Bool(l), ConstValue::Bool(r)) => match bin.op {
                BinaryOp::And => Some(ConstValue::Bool(l && r)),
                BinaryOp::Or => Some(ConstValue::Bool(l || r)),
                BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
                BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
                _ => None,
            },
            // Mismatched types
            _ => None,
        }
    }

    /// Try to fold a unary expression.
    fn try_fold_unary(&self, unary: &vole_frontend::UnaryExpr) -> Option<ConstValue> {
        let operand = self.get_const_value(&unary.operand)?;

        match (unary.op, operand) {
            (vole_frontend::UnaryOp::Neg, ConstValue::Int(v, suffix)) => {
                Some(ConstValue::Int(-v, suffix))
            }
            (vole_frontend::UnaryOp::Neg, ConstValue::Float(v, suffix)) => {
                Some(ConstValue::Float(-v, suffix))
            }
            (vole_frontend::UnaryOp::Not, ConstValue::Bool(v)) => Some(ConstValue::Bool(!v)),
            (vole_frontend::UnaryOp::BitNot, ConstValue::Int(v, suffix)) => {
                Some(ConstValue::Int(!v, suffix))
            }
            _ => None,
        }
    }

    /// Get the constant value of an expression if it's a literal or a known constant variable.
    fn get_const_value(&self, expr: &Expr) -> Option<ConstValue> {
        match &expr.kind {
            ExprKind::IntLiteral(v, suffix) => Some(ConstValue::Int(*v, *suffix)),
            ExprKind::FloatLiteral(v, suffix) => Some(ConstValue::Float(*v, *suffix)),
            ExprKind::BoolLiteral(v) => Some(ConstValue::Bool(*v)),
            ExprKind::Grouping(inner) => self.get_const_value(inner),
            // Recurse into binary/unary for nested constant expressions
            ExprKind::Binary(bin) => self.try_fold_binary(bin),
            ExprKind::Unary(unary) => self.try_fold_unary(unary),
            // Look up constant bindings for identifiers (constant propagation)
            ExprKind::Identifier(sym) => self.constant_bindings.get(sym).cloned(),
            _ => None,
        }
    }

    /// Try to optimize division operations.
    ///
    /// Transforms:
    /// - `x / const` -> `x * (1/const)` for floating-point
    /// - `x / 2^n` -> `x >> n` for unsigned integers (done in codegen for signed)
    fn try_optimize_division(&mut self, expr: &mut Expr) {
        let ExprKind::Binary(ref mut bin) = expr.kind else {
            return;
        };

        if bin.op != BinaryOp::Div {
            return;
        }

        // Get the type of the expression to determine if it's floating-point
        let type_id = self.expr_data.get_type(expr.id);

        // Check if the divisor is a constant
        let Some(divisor) = self.get_const_value(&bin.right) else {
            return;
        };

        match divisor {
            ConstValue::Float(divisor_val, suffix) if divisor_val != 0.0 => {
                // Replace x / const with x * (1/const)
                let reciprocal = 1.0 / divisor_val;

                // Create the new multiplication expression
                let reciprocal_expr = Expr {
                    id: bin.right.id, // Reuse the node ID
                    kind: ExprKind::FloatLiteral(reciprocal, suffix),
                    span: bin.right.span,
                };

                bin.op = BinaryOp::Mul;
                bin.right = reciprocal_expr;
                self.stats.div_to_mul += 1;
            }
            ConstValue::Int(divisor_val, _suffix) if divisor_val > 0 => {
                // Check if the result type is floating-point (float / int -> float)
                let is_float_result = type_id.map(|t| t.is_float()).unwrap_or(false);

                if is_float_result && divisor_val != 0 {
                    // For float results, convert integer divisor to float reciprocal
                    // x / 4000 -> x * 0.00025 (when result type is float)
                    let reciprocal = 1.0 / (divisor_val as f64);

                    // Create the new multiplication expression with float reciprocal
                    let reciprocal_expr = Expr {
                        id: bin.right.id,
                        kind: ExprKind::FloatLiteral(reciprocal, None),
                        span: bin.right.span,
                    };

                    bin.op = BinaryOp::Mul;
                    bin.right = reciprocal_expr;
                    self.stats.div_to_mul += 1;
                } else if let Some(shift) = power_of_two_shift(divisor_val) {
                    // Check if it's a power of 2 and if type is unsigned
                    // Only optimize unsigned integers here; signed division
                    // has different semantics (rounds toward zero vs toward -infinity)
                    // The codegen already handles this optimization for unsigned
                    let is_unsigned = type_id.map(|t| t.is_unsigned_int()).unwrap_or(false);

                    if is_unsigned {
                        // Replace x / 2^n with x >> n
                        let shift_expr = Expr {
                            id: bin.right.id,
                            kind: ExprKind::IntLiteral(shift, None),
                            span: bin.right.span,
                        };

                        bin.op = BinaryOp::Shr;
                        bin.right = shift_expr;
                        self.stats.div_to_shift += 1;
                    }
                }
            }
            _ => {}
        }
    }
}

/// Check if n is a positive power of 2 and return the shift amount (log2).
fn power_of_two_shift(n: i64) -> Option<i64> {
    if n > 0 && (n & (n - 1)) == 0 {
        Some(n.trailing_zeros() as i64)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_power_of_two_shift() {
        assert_eq!(power_of_two_shift(1), Some(0));
        assert_eq!(power_of_two_shift(2), Some(1));
        assert_eq!(power_of_two_shift(4), Some(2));
        assert_eq!(power_of_two_shift(8), Some(3));
        assert_eq!(power_of_two_shift(16), Some(4));
        assert_eq!(power_of_two_shift(1024), Some(10));
        assert_eq!(power_of_two_shift(3), None);
        assert_eq!(power_of_two_shift(0), None);
        assert_eq!(power_of_two_shift(-1), None);
    }
}
