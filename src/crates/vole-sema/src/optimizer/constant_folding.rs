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

use crate::node_map::NodeMap;
use crate::types::ConstantValue;
use std::collections::HashMap;
use vole_frontend::ast::{BlockExpr, MethodCallExpr, NumericSuffix, StringPart, UnaryExpr};
use vole_frontend::{
    BinaryExpr, BinaryOp, Block, Decl, Expr, ExprKind, FuncBody, FuncDecl, Program, Stmt, Symbol,
};

/// Statistics from constant folding.
#[derive(Debug, Clone, Default)]
pub(crate) struct FoldingStats {
    /// Number of constant expressions folded to literals
    pub(crate) constants_folded: usize,
    /// Number of divisions replaced with multiplication
    pub(crate) div_to_mul: usize,
    /// Number of divisions replaced with bit shifts
    pub(crate) div_to_shift: usize,
    /// Number of constant propagations (variable references replaced with literals)
    pub(crate) constants_propagated: usize,
    /// Number of dead branches eliminated (if/when with constant conditions)
    pub(crate) branches_eliminated: usize,
    /// Number of pure intrinsic calls folded (e.g., f64.sqrt(4.0) -> 2.0)
    pub(crate) intrinsics_folded: usize,
}

/// A constant value computed at compile time, with optional numeric suffix metadata.
///
/// This is the optimizer-internal counterpart to [`ConstantValue`]. The extra
/// `Option<NumericSuffix>` on `Int` and `Float` preserves type annotations through
/// constant folds (e.g., `1u8 + 2u8` folds to `3u8`, not just `3`).
///
/// `From` conversions exist between this type and `ConstantValue`:
/// - `ConstantValue::from(&ConstValue)` — drops the suffix (for module exports)
/// - `ConstValue::from(&ConstantValue)` — sets suffix to `None`
#[derive(Debug, Clone)]
enum ConstValue {
    Int(i64, Option<NumericSuffix>),
    Float(f64, Option<NumericSuffix>),
    Bool(bool),
    String(String),
}

impl ConstValue {
    /// Convert to an expression kind.
    fn to_expr_kind(&self) -> ExprKind {
        match self {
            ConstValue::Int(v, suffix) => ExprKind::IntLiteral(*v, *suffix),
            ConstValue::Float(v, suffix) => ExprKind::FloatLiteral(*v, *suffix),
            ConstValue::Bool(v) => ExprKind::BoolLiteral(*v),
            ConstValue::String(s) => ExprKind::StringLiteral(s.clone()),
        }
    }
}

/// Convert from optimizer's ConstValue to module-level ConstantValue.
///
/// Drops the numeric suffix metadata since module constants don't need it.
impl From<&ConstValue> for ConstantValue {
    fn from(cv: &ConstValue) -> Self {
        match cv {
            ConstValue::Int(v, _) => ConstantValue::I64(*v),
            ConstValue::Float(v, _) => ConstantValue::F64(*v),
            ConstValue::Bool(v) => ConstantValue::Bool(*v),
            ConstValue::String(s) => ConstantValue::String(s.clone()),
        }
    }
}

/// Convert from module-level ConstantValue to optimizer's ConstValue.
///
/// The numeric suffix is set to `None` since module constants don't carry suffix info.
impl From<&ConstantValue> for ConstValue {
    fn from(cv: &ConstantValue) -> Self {
        match cv {
            ConstantValue::I64(v) => ConstValue::Int(*v, None),
            ConstantValue::F64(v) => ConstValue::Float(*v, None),
            ConstantValue::Bool(v) => ConstValue::Bool(*v),
            ConstantValue::String(s) => ConstValue::String(s.clone()),
        }
    }
}

/// Run constant folding on the program.
pub(crate) fn fold_constants(program: &mut Program, node_map: &mut NodeMap) -> FoldingStats {
    let mut folder = ConstantFolder::new(node_map);
    folder.fold_program(program);
    folder.stats
}

/// Evaluate a constant expression without mutating the AST.
///
/// This is a lightweight evaluator for use during module scanning (before
/// the optimizer runs). It handles:
/// - Literals (int, float, bool, string)
/// - Unary operations on constants (negation, not, bitwise not)
/// - Binary operations on constants (arithmetic, comparison, logic)
/// - References to already-known constants via the `known_constants` map
///
/// Returns `None` if the expression cannot be evaluated at compile time.
pub(crate) fn eval_const_expr(
    expr: &Expr,
    known_constants: &HashMap<Symbol, ConstantValue>,
) -> Option<ConstantValue> {
    eval_const_value(expr, known_constants).map(|cv| ConstantValue::from(&cv))
}

/// Internal: evaluate an expression to ConstValue (preserves suffix info).
fn eval_const_value(
    expr: &Expr,
    known_constants: &HashMap<Symbol, ConstantValue>,
) -> Option<ConstValue> {
    match &expr.kind {
        ExprKind::IntLiteral(v, suffix) => Some(ConstValue::Int(*v, *suffix)),
        ExprKind::FloatLiteral(v, suffix) => Some(ConstValue::Float(*v, *suffix)),
        ExprKind::BoolLiteral(v) => Some(ConstValue::Bool(*v)),
        ExprKind::StringLiteral(s) => Some(ConstValue::String(s.clone())),
        ExprKind::Grouping(inner) => eval_const_value(inner, known_constants),
        ExprKind::Identifier(sym) => known_constants.get(sym).map(ConstValue::from),
        ExprKind::Binary(bin) => eval_binary(bin, known_constants),
        ExprKind::Unary(unary) => eval_unary(unary, known_constants),
        _ => None,
    }
}

/// Evaluate a binary expression on two constant operands.
fn eval_binary(
    bin: &BinaryExpr,
    known_constants: &HashMap<Symbol, ConstantValue>,
) -> Option<ConstValue> {
    let left = eval_const_value(&bin.left, known_constants)?;
    let right = eval_const_value(&bin.right, known_constants)?;
    fold_binary_values(left, right, bin.op)
}

/// Evaluate a unary expression on a constant operand.
fn eval_unary(
    unary: &UnaryExpr,
    known_constants: &HashMap<Symbol, ConstantValue>,
) -> Option<ConstValue> {
    let operand = eval_const_value(&unary.operand, known_constants)?;
    fold_unary_value(unary.op, operand)
}

/// Fold a binary operation on two pre-resolved constant values.
///
/// This is the shared core logic used by both `eval_binary` (module-scanning path)
/// and `ConstantFolder::try_fold_binary` (optimizer path).
fn fold_binary_values(left: ConstValue, right: ConstValue, op: BinaryOp) -> Option<ConstValue> {
    match (left, right) {
        (ConstValue::Int(l, l_suffix), ConstValue::Int(r, r_suffix)) => {
            let s = l_suffix.or(r_suffix);
            match op {
                BinaryOp::Add => Some(ConstValue::Int(l.wrapping_add(r), s)),
                BinaryOp::Sub => Some(ConstValue::Int(l.wrapping_sub(r), s)),
                BinaryOp::Mul => Some(ConstValue::Int(l.wrapping_mul(r), s)),
                BinaryOp::Div if r != 0 => Some(ConstValue::Int(l / r, s)),
                BinaryOp::Mod if r != 0 => Some(ConstValue::Int(l % r, s)),
                BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
                BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
                BinaryOp::Lt => Some(ConstValue::Bool(l < r)),
                BinaryOp::Gt => Some(ConstValue::Bool(l > r)),
                BinaryOp::Le => Some(ConstValue::Bool(l <= r)),
                BinaryOp::Ge => Some(ConstValue::Bool(l >= r)),
                BinaryOp::BitAnd => Some(ConstValue::Int(l & r, s)),
                BinaryOp::BitOr => Some(ConstValue::Int(l | r, s)),
                BinaryOp::BitXor => Some(ConstValue::Int(l ^ r, s)),
                BinaryOp::Shl if shift_in_range(r, s) => Some(ConstValue::Int(l << r, s)),
                BinaryOp::Shr if shift_in_range(r, s) => Some(ConstValue::Int(l >> r, s)),
                _ => None,
            }
        }
        (ConstValue::Float(l, l_suffix), ConstValue::Float(r, r_suffix)) => {
            fold_float_binary(l, r, l_suffix.or(r_suffix), op)
        }
        (ConstValue::Int(l, _), ConstValue::Float(r, suffix)) => {
            fold_float_binary(l as f64, r, suffix, op)
        }
        (ConstValue::Float(l, suffix), ConstValue::Int(r, _)) => {
            fold_float_binary(l, r as f64, suffix, op)
        }
        (ConstValue::Bool(l), ConstValue::Bool(r)) => match op {
            BinaryOp::And => Some(ConstValue::Bool(l && r)),
            BinaryOp::Or => Some(ConstValue::Bool(l || r)),
            BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
            BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
            _ => None,
        },
        (ConstValue::String(l), ConstValue::String(r)) => match op {
            BinaryOp::Add => Some(ConstValue::String(l + &r)),
            BinaryOp::Eq => Some(ConstValue::Bool(l == r)),
            BinaryOp::Ne => Some(ConstValue::Bool(l != r)),
            _ => None,
        },
        _ => None,
    }
}

/// Fold a unary operation on a pre-resolved constant value.
///
/// This is the shared core logic used by both `eval_unary` (module-scanning path)
/// and `ConstantFolder::try_fold_unary` (optimizer path).
fn fold_unary_value(op: vole_frontend::UnaryOp, operand: ConstValue) -> Option<ConstValue> {
    match (op, operand) {
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

/// Fold a binary operation on two f64 values at compile time.
fn fold_float_binary(
    l: f64,
    r: f64,
    suffix: Option<NumericSuffix>,
    op: BinaryOp,
) -> Option<ConstValue> {
    match op {
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

/// The constant folder visitor.
struct ConstantFolder<'a> {
    node_map: &'a mut NodeMap,
    stats: FoldingStats,
    /// Map from immutable variable symbols to their constant values.
    /// Used for constant propagation.
    constant_bindings: HashMap<Symbol, ConstValue>,
}

impl<'a> ConstantFolder<'a> {
    fn new(node_map: &'a mut NodeMap) -> Self {
        Self {
            node_map,
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
    ///
    /// After folding each statement, eliminates dead if-branches by inlining
    /// the taken branch's statements or removing the if entirely.
    fn fold_block(&mut self, block: &mut Block) {
        for stmt in &mut block.stmts {
            self.fold_stmt(stmt);
        }

        // Eliminate dead if-statements by replacing them with inlined branches.
        // We collect replacements first, then apply them (since inlining a block
        // may produce multiple statements, changing the Vec length).
        let mut replacements: Vec<(usize, Vec<Stmt>)> = Vec::new();

        for (i, stmt) in block.stmts.iter().enumerate() {
            if let Some(stmts) = self.try_eliminate_if_stmt(stmt) {
                replacements.push((i, stmts));
            }
        }

        // Apply replacements in reverse order to preserve indices
        for (i, replacement) in replacements.into_iter().rev() {
            block.stmts.splice(i..=i, replacement);
        }
    }

    /// Check if a Stmt::If has a constant condition and return the replacement statements.
    ///
    /// Returns `Some(stmts)` if the if-statement should be replaced (may be empty vec
    /// for `if false` with no else branch).
    fn try_eliminate_if_stmt(&mut self, stmt: &Stmt) -> Option<Vec<Stmt>> {
        let Stmt::If(if_stmt) = stmt else {
            return None;
        };
        let Some(ConstValue::Bool(cond)) = self.get_const_value(&if_stmt.condition) else {
            return None;
        };

        self.stats.branches_eliminated += 1;

        if cond {
            // Condition is true: inline the then_branch statements
            Some(if_stmt.then_branch.stmts.clone())
        } else if let Some(else_branch) = &if_stmt.else_branch {
            // Condition is false with else: inline the else_branch statements
            Some(else_branch.stmts.clone())
        } else {
            // Condition is false with no else: remove entirely
            Some(vec![])
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

        // Try dead branch elimination for if/when expressions
        if self.try_eliminate_dead_branch(expr) {
            return;
        }

        // Then try to fold this expression
        if let Some(folded) = self.try_fold_expr(expr) {
            // Track intrinsic folds separately from general constant folds
            let is_intrinsic = matches!(expr.kind, ExprKind::MethodCall(_));
            expr.kind = folded.to_expr_kind();
            if is_intrinsic {
                self.stats.intrinsics_folded += 1;
            } else {
                self.stats.constants_folded += 1;
            }
        } else {
            // Try algebraic optimizations (division -> multiplication)
            self.try_optimize_division(expr);
        }
    }

    /// Try to eliminate dead branches in if/when expressions with constant conditions.
    ///
    /// Returns `true` if the expression was replaced (dead branch eliminated).
    fn try_eliminate_dead_branch(&mut self, expr: &mut Expr) -> bool {
        match &expr.kind {
            ExprKind::If(if_expr) => self.try_eliminate_if(expr, if_expr.span),
            ExprKind::When(_) => self.try_eliminate_when(expr),
            _ => false,
        }
    }

    /// Eliminate dead branches in an if-expression with a constant bool condition.
    ///
    /// - `if true  { a } else { b }` => `a`
    /// - `if false { a } else { b }` => `b`
    /// - `if false { a }` (no else)  => empty block (void)
    fn try_eliminate_if(&mut self, expr: &mut Expr, span: vole_frontend::Span) -> bool {
        let ExprKind::If(ref if_expr) = expr.kind else {
            return false;
        };
        let Some(ConstValue::Bool(cond)) = self.get_const_value(&if_expr.condition) else {
            return false;
        };

        // Take ownership of the if-expression to extract the taken branch
        let ExprKind::If(if_expr) = std::mem::replace(&mut expr.kind, ExprKind::Unreachable) else {
            unreachable!();
        };

        if cond {
            // Condition is true: replace with then_branch
            expr.id = if_expr.then_branch.id;
            expr.kind = if_expr.then_branch.kind;
        } else if let Some(else_branch) = if_expr.else_branch {
            // Condition is false with else branch: replace with else_branch
            expr.id = else_branch.id;
            expr.kind = else_branch.kind;
        } else {
            // Condition is false with no else: replace with empty block (void)
            expr.kind = ExprKind::Block(Box::new(BlockExpr {
                stmts: vec![],
                trailing_expr: None,
                span,
            }));
        }

        self.stats.branches_eliminated += 1;
        true
    }

    /// Eliminate dead arms in when-expressions where the condition is a constant bool.
    ///
    /// If a `true` arm is found, replaces the entire when with that arm's body.
    /// Removes arms with `false` conditions (they're dead code).
    /// Only replaces the wildcard arm if all prior arms are constant-false.
    fn try_eliminate_when(&mut self, expr: &mut Expr) -> bool {
        let ExprKind::When(ref when) = expr.kind else {
            return false;
        };

        // Walk arms in order. Track whether all prior arms are known-false.
        let mut all_prior_dead = true;

        for (i, arm) in when.arms.iter().enumerate() {
            match &arm.condition {
                Some(cond) => match self.get_const_value(cond) {
                    Some(ConstValue::Bool(true)) => {
                        // This arm always matches; replace the whole when
                        let ExprKind::When(mut when) =
                            std::mem::replace(&mut expr.kind, ExprKind::Unreachable)
                        else {
                            unreachable!();
                        };
                        let arm = when.arms.swap_remove(i);
                        expr.id = arm.body.id;
                        expr.kind = arm.body.kind;
                        self.stats.branches_eliminated += 1;
                        return true;
                    }
                    Some(ConstValue::Bool(false)) => {
                        // This arm is dead; continue checking
                    }
                    _ => {
                        // Non-constant condition; can't eliminate
                        all_prior_dead = false;
                    }
                },
                None if all_prior_dead => {
                    // Wildcard arm and all prior arms are dead -- only this fires
                    let ExprKind::When(mut when) =
                        std::mem::replace(&mut expr.kind, ExprKind::Unreachable)
                    else {
                        unreachable!();
                    };
                    let arm = when.arms.swap_remove(i);
                    expr.id = arm.body.id;
                    expr.kind = arm.body.kind;
                    self.stats.branches_eliminated += 1;
                    return true;
                }
                None => {
                    // Wildcard but prior arms have unknown conditions; stop
                    all_prior_dead = false;
                }
            }
        }

        // Remove dead (false-condition) arms even if we can't eliminate the whole when
        let ExprKind::When(ref when) = expr.kind else {
            return false;
        };
        let has_dead_arms = when.arms.iter().any(|arm| {
            arm.condition.as_ref().is_some_and(|cond| {
                matches!(self.get_const_value(cond), Some(ConstValue::Bool(false)))
            })
        });

        if has_dead_arms {
            let ExprKind::When(ref mut when) = expr.kind else {
                unreachable!();
            };
            when.arms.retain(|arm| {
                !arm.condition.as_ref().is_some_and(|cond| {
                    matches!(self.get_const_value(cond), Some(ConstValue::Bool(false)))
                })
            });
            self.stats.branches_eliminated += 1;
        }

        false
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
                    self.fold_expr(arg.expr_mut());
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
            ExprKind::AsCast(as_cast) => {
                self.fold_expr(&mut as_cast.value);
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
            ExprKind::MetaAccess(ma) => {
                self.fold_expr(&mut ma.object);
            }
            ExprKind::OptionalChain(oc) => {
                self.fold_expr(&mut oc.object);
            }
            ExprKind::OptionalMethodCall(omc) => {
                self.fold_expr(&mut omc.object);
                for arg in &mut omc.args {
                    self.fold_expr(arg.expr_mut());
                }
            }
            ExprKind::MethodCall(mc) => {
                self.fold_expr(&mut mc.object);
                for arg in &mut mc.args {
                    self.fold_expr(arg.expr_mut());
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
                    if let StringPart::Expr(e) = part {
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
            ExprKind::MethodCall(mc) => self.try_fold_intrinsic(expr.id, mc),
            _ => None,
        }
    }

    /// Try to fold a binary expression.
    fn try_fold_binary(&self, bin: &BinaryExpr) -> Option<ConstValue> {
        let left = self.get_const_value(&bin.left)?;
        let right = self.get_const_value(&bin.right)?;
        fold_binary_values(left, right, bin.op)
    }

    /// Try to fold a unary expression.
    fn try_fold_unary(&self, unary: &UnaryExpr) -> Option<ConstValue> {
        let operand = self.get_const_value(&unary.operand)?;
        fold_unary_value(unary.op, operand)
    }

    /// Try to fold a pure intrinsic method call with all-constant arguments.
    ///
    /// Uses the intrinsic key resolved by sema (e.g., "f64_sqrt") to identify
    /// the specific intrinsic. Only folds calls that sema has verified are
    /// compiler intrinsics with known type mappings.
    fn try_fold_intrinsic(
        &self,
        expr_id: vole_frontend::NodeId,
        mc: &MethodCallExpr,
    ) -> Option<ConstValue> {
        // Look up the sema-resolved intrinsic key for this call site
        let intrinsic_key = self.node_map.get_intrinsic_key(expr_id)?;

        match mc.args.len() {
            1 => {
                let arg = self.get_const_value(mc.args[0].expr())?;
                fold_intrinsic_unary(intrinsic_key, arg)
            }
            2 => {
                let a = self.get_const_value(mc.args[0].expr())?;
                let b = self.get_const_value(mc.args[1].expr())?;
                fold_intrinsic_binary(intrinsic_key, a, b)
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
            ExprKind::StringLiteral(s) => Some(ConstValue::String(s.clone())),
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
        let type_id = self.node_map.get_type(expr.id);

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

/// Return the bit width of an integer type given its suffix.
///
/// When no suffix is present the expression is an unsized integer literal, which
/// is stored in an i64 context (64 bits), so the Cranelift `& 63` masking is
/// correct — we return 64 so that all shifts [0, 63] are in range.
fn int_bit_width(suffix: Option<NumericSuffix>) -> i64 {
    match suffix {
        Some(NumericSuffix::I8) | Some(NumericSuffix::U8) => 8,
        Some(NumericSuffix::I16) | Some(NumericSuffix::U16) => 16,
        Some(NumericSuffix::I32) | Some(NumericSuffix::U32) => 32,
        Some(NumericSuffix::I64) | Some(NumericSuffix::U64) => 64,
        Some(NumericSuffix::I128) => 128,
        // Float suffixes never reach this code (handled in fold_float_binary).
        // No suffix → treat as 64-bit, consistent with Cranelift's i64 default.
        _ => 64,
    }
}

/// Return true if `r` is a valid shift amount for the type described by `suffix`.
///
/// A shift amount is in range when `0 <= r < bit_width(type)`.  Out-of-range
/// shifts are left unfolded so the runtime (Cranelift) handles them consistently
/// instead of producing a value that disagrees with compile-time evaluation.
///
/// The constant folder stores all integers as `i64`, so the maximum safe shift
/// amount is 63 regardless of the declared type.  For `i128`, where the true
/// bit width is 128, shifts of 64..127 cannot be represented correctly in i64
/// arithmetic and are left unfolded too.
fn shift_in_range(r: i64, suffix: Option<NumericSuffix>) -> bool {
    r >= 0 && r < int_bit_width(suffix).min(64)
}

/// Check if n is a positive power of 2 and return the shift amount (log2).
fn power_of_two_shift(n: i64) -> Option<i64> {
    if n > 0 && (n & (n - 1)) == 0 {
        Some(n.trailing_zeros() as i64)
    } else {
        None
    }
}

/// Fold a unary (single-argument) pure intrinsic by intrinsic key.
///
/// The `key` is a sema-resolved string like "f64_sqrt", "i32_abs", "u64_clz".
/// Only pure, deterministic intrinsics are handled.
fn fold_intrinsic_unary(key: &str, arg: ConstValue) -> Option<ConstValue> {
    match key {
        // Float unary operations (f64)
        "f64_sqrt" => fold_f64_unary(arg, |v| if v >= 0.0 { Some(v.sqrt()) } else { None }),
        "f64_abs" => fold_f64_unary(arg, |v| Some(v.abs())),
        "f64_ceil" => fold_f64_unary(arg, |v| Some(v.ceil())),
        "f64_floor" => fold_f64_unary(arg, |v| Some(v.floor())),
        "f64_trunc" => fold_f64_unary(arg, |v| Some(v.trunc())),
        "f64_round" => fold_f64_unary(arg, |v| Some(v.round())),
        // Float unary operations (f32)
        "f32_sqrt" => fold_f32_unary(arg, |v| if v >= 0.0 { Some(v.sqrt()) } else { None }),
        "f32_abs" => fold_f32_unary(arg, |v| Some(v.abs())),
        "f32_ceil" => fold_f32_unary(arg, |v| Some(v.ceil())),
        "f32_floor" => fold_f32_unary(arg, |v| Some(v.floor())),
        "f32_trunc" => fold_f32_unary(arg, |v| Some(v.trunc())),
        "f32_round" => fold_f32_unary(arg, |v| Some(v.round())),
        // Signed integer abs
        "i8_abs" | "i16_abs" | "i32_abs" | "i64_abs" => {
            fold_int_unary(key, arg, |v, _| v.wrapping_abs())
        }
        // Leading/trailing zeros and popcount (all integer types)
        k if k.ends_with("_clz") => fold_int_unary(key, arg, count_leading_zeros),
        k if k.ends_with("_ctz") => fold_int_unary(key, arg, count_trailing_zeros),
        k if k.ends_with("_popcnt") => fold_int_unary(key, arg, popcount),
        _ => None,
    }
}

/// Fold a binary (two-argument) pure intrinsic by intrinsic key.
fn fold_intrinsic_binary(key: &str, a: ConstValue, b: ConstValue) -> Option<ConstValue> {
    match key {
        "f64_min" => fold_f64_binary(a, b, f64::min),
        "f64_max" => fold_f64_binary(a, b, f64::max),
        "f32_min" => fold_f32_binary(a, b, f32::min),
        "f32_max" => fold_f32_binary(a, b, f32::max),
        k if k.ends_with("_min") => fold_int_binary(key, a, b, |va, vb| va.min(vb)),
        k if k.ends_with("_max") => fold_int_binary(key, a, b, |va, vb| va.max(vb)),
        _ => None,
    }
}

/// Helper: fold a unary f64 intrinsic.
fn fold_f64_unary(arg: ConstValue, f: impl FnOnce(f64) -> Option<f64>) -> Option<ConstValue> {
    let v = match arg {
        ConstValue::Float(v, _) => v,
        ConstValue::Int(v, _) => v as f64,
        _ => return None,
    };
    f(v).map(|r| ConstValue::Float(r, Some(NumericSuffix::F64)))
}

/// Helper: fold a unary f32 intrinsic.
fn fold_f32_unary(arg: ConstValue, f: impl FnOnce(f32) -> Option<f32>) -> Option<ConstValue> {
    let v = match arg {
        ConstValue::Float(v, _) => v as f32,
        ConstValue::Int(v, _) => v as f32,
        _ => return None,
    };
    f(v).map(|r| ConstValue::Float(r as f64, Some(NumericSuffix::F32)))
}

/// Helper: fold a unary integer intrinsic by extracting bit width from the key prefix.
fn fold_int_unary(
    key: &str,
    arg: ConstValue,
    f: impl FnOnce(i64, u32) -> i64,
) -> Option<ConstValue> {
    let ConstValue::Int(v, _) = arg else {
        return None;
    };
    let (suffix, bits) = int_suffix_and_bits_from_key(key)?;
    Some(ConstValue::Int(f(v, bits), suffix))
}

/// Helper: fold a binary f64 intrinsic.
fn fold_f64_binary(
    a: ConstValue,
    b: ConstValue,
    f: impl FnOnce(f64, f64) -> f64,
) -> Option<ConstValue> {
    let va = match &a {
        ConstValue::Float(v, _) => *v,
        ConstValue::Int(v, _) => *v as f64,
        _ => return None,
    };
    let vb = match &b {
        ConstValue::Float(v, _) => *v,
        ConstValue::Int(v, _) => *v as f64,
        _ => return None,
    };
    Some(ConstValue::Float(f(va, vb), Some(NumericSuffix::F64)))
}

/// Helper: fold a binary f32 intrinsic.
fn fold_f32_binary(
    a: ConstValue,
    b: ConstValue,
    f: impl FnOnce(f32, f32) -> f32,
) -> Option<ConstValue> {
    let va = match &a {
        ConstValue::Float(v, _) => *v as f32,
        ConstValue::Int(v, _) => *v as f32,
        _ => return None,
    };
    let vb = match &b {
        ConstValue::Float(v, _) => *v as f32,
        ConstValue::Int(v, _) => *v as f32,
        _ => return None,
    };
    Some(ConstValue::Float(
        f(va, vb) as f64,
        Some(NumericSuffix::F32),
    ))
}

/// Helper: fold a binary integer intrinsic.
fn fold_int_binary(
    key: &str,
    a: ConstValue,
    b: ConstValue,
    f: impl FnOnce(i64, i64) -> i64,
) -> Option<ConstValue> {
    let (ConstValue::Int(va, _), ConstValue::Int(vb, _)) = (&a, &b) else {
        return None;
    };
    let (suffix, _bits) = int_suffix_and_bits_from_key(key)?;
    Some(ConstValue::Int(f(*va, *vb), suffix))
}

/// Extract NumericSuffix and bit width from an intrinsic key prefix (e.g., "i64_clz" -> (I64, 64)).
fn int_suffix_and_bits_from_key(key: &str) -> Option<(Option<NumericSuffix>, u32)> {
    if key.starts_with("i8_") {
        Some((Some(NumericSuffix::I8), 8))
    } else if key.starts_with("i16_") {
        Some((Some(NumericSuffix::I16), 16))
    } else if key.starts_with("i32_") {
        Some((Some(NumericSuffix::I32), 32))
    } else if key.starts_with("i64_") {
        Some((Some(NumericSuffix::I64), 64))
    } else if key.starts_with("u8_") {
        Some((Some(NumericSuffix::U8), 8))
    } else if key.starts_with("u16_") {
        Some((Some(NumericSuffix::U16), 16))
    } else if key.starts_with("u32_") {
        Some((Some(NumericSuffix::U32), 32))
    } else if key.starts_with("u64_") {
        Some((Some(NumericSuffix::U64), 64))
    } else {
        None
    }
}

/// Count leading zeros for a value with the given bit width.
fn count_leading_zeros(v: i64, bits: u32) -> i64 {
    let masked = (v as u64) & ((1u64.wrapping_shl(bits)).wrapping_sub(1));
    let clz_64 = masked.leading_zeros();
    (clz_64 - (64 - bits)) as i64
}

/// Count trailing zeros for a value with the given bit width.
fn count_trailing_zeros(v: i64, bits: u32) -> i64 {
    let masked = (v as u64) & ((1u64.wrapping_shl(bits)).wrapping_sub(1));
    let ctz = masked.trailing_zeros();
    // If value is 0, trailing_zeros returns 64, cap at bit width
    ctz.min(bits) as i64
}

/// Population count (number of set bits) for a value with the given bit width.
fn popcount(v: i64, bits: u32) -> i64 {
    let masked = (v as u64) & ((1u64.wrapping_shl(bits)).wrapping_sub(1));
    masked.count_ones() as i64
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

    #[test]
    fn test_shift_in_range() {
        // u8: valid shifts are 0..7
        assert!(shift_in_range(0, Some(NumericSuffix::U8)));
        assert!(shift_in_range(7, Some(NumericSuffix::U8)));
        assert!(!shift_in_range(8, Some(NumericSuffix::U8)));
        assert!(!shift_in_range(9, Some(NumericSuffix::U8)));
        assert!(!shift_in_range(-1, Some(NumericSuffix::U8)));

        // u16: valid shifts are 0..15
        assert!(shift_in_range(15, Some(NumericSuffix::U16)));
        assert!(!shift_in_range(16, Some(NumericSuffix::U16)));

        // i32/u32: valid shifts are 0..31
        assert!(shift_in_range(31, Some(NumericSuffix::I32)));
        assert!(!shift_in_range(32, Some(NumericSuffix::I32)));
        assert!(shift_in_range(31, Some(NumericSuffix::U32)));
        assert!(!shift_in_range(32, Some(NumericSuffix::U32)));

        // i64/u64: valid shifts are 0..63
        assert!(shift_in_range(63, Some(NumericSuffix::I64)));
        assert!(!shift_in_range(64, Some(NumericSuffix::I64)));

        // No suffix → 64-bit context; shifts 0..63 are valid
        assert!(shift_in_range(63, None));
        assert!(!shift_in_range(64, None));

        // i128: true bit width is 128, but the folder uses i64 arithmetic,
        // so we can only fold shifts 0..63 (r < 64).
        assert!(shift_in_range(63, Some(NumericSuffix::I128)));
        assert!(!shift_in_range(64, Some(NumericSuffix::I128)));
    }

    #[test]
    fn test_fold_shl_out_of_range_not_folded() {
        use vole_frontend::ast::ExprKind;
        use vole_frontend::{BinaryExpr, BinaryOp, Expr, NodeId, Span};

        // Helper to make a literal Expr
        let make_int = |v: i64, suffix: Option<NumericSuffix>| -> Expr {
            Expr {
                id: NodeId::new_for_test(0),
                kind: ExprKind::IntLiteral(v, suffix),
                span: Span::default(),
            }
        };

        let known: HashMap<_, _> = HashMap::new();

        // 1_u8 << 8_u8 — shift amount equals the bit width: must NOT fold
        let bin = BinaryExpr {
            left: make_int(1, Some(NumericSuffix::U8)),
            right: make_int(8, Some(NumericSuffix::U8)),
            op: BinaryOp::Shl,
        };
        assert!(
            eval_binary(&bin, &known).is_none(),
            "1_u8 << 8_u8 must not fold"
        );

        // 1_u8 << 7_u8 — shift amount is in range: must fold to 128_u8
        let bin2 = BinaryExpr {
            left: make_int(1, Some(NumericSuffix::U8)),
            right: make_int(7, Some(NumericSuffix::U8)),
            op: BinaryOp::Shl,
        };
        let folded = eval_binary(&bin2, &known);
        assert!(
            matches!(folded, Some(ConstValue::Int(128, Some(NumericSuffix::U8)))),
            "1_u8 << 7_u8 must fold to 128_u8, got {folded:?}"
        );

        // 1_u16 << 16_u16 — out of range: must NOT fold
        let bin3 = BinaryExpr {
            left: make_int(1, Some(NumericSuffix::U16)),
            right: make_int(16, Some(NumericSuffix::U16)),
            op: BinaryOp::Shl,
        };
        assert!(
            eval_binary(&bin3, &known).is_none(),
            "1_u16 << 16_u16 must not fold"
        );
    }
}
