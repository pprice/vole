// builder.rs
//
// VirBuilder: incremental construction of VIR trees.

use vole_identity::{FunctionId, Symbol, TypeId};

use crate::calls::CallTarget;
use crate::expr::{CoerceKind, FieldStorage, VirBinOp, VirExpr, VirUnOp};
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::{AssignTarget, VirStmt};

/// Builder for constructing VIR function bodies.
///
/// Provides two usage patterns:
///
/// 1. **Incremental**: use [`push`]/[`set_trailing`]/[`build`] to accumulate
///    statements one at a time into a body.
/// 2. **Direct**: use the `build_*` helpers to construct individual nodes, then
///    assemble them with [`build_body`] and [`finish`].
///
/// The builder itself is a thin wrapper — it exists to provide a typed API that
/// future phases can extend with scope tracking, RC validation, etc.
#[derive(Debug, Clone)]
pub struct VirBuilder {
    stmts: Vec<VirStmt>,
    trailing: Option<VirRef>,
}

impl VirBuilder {
    /// Create a new, empty builder.
    pub fn new() -> Self {
        Self {
            stmts: Vec::new(),
            trailing: None,
        }
    }

    // -- Incremental body construction ----------------------------------------

    /// Append a statement to the body under construction.
    pub fn push(&mut self, stmt: VirStmt) {
        self.stmts.push(stmt);
    }

    /// Set the trailing expression that produces the body's value.
    pub fn set_trailing(&mut self, expr: VirRef) {
        self.trailing = Some(expr);
    }

    /// Consume the builder, producing a finished `VirBody` from any
    /// statements accumulated via [`push`] and [`set_trailing`].
    pub fn build(self) -> VirBody {
        VirBody {
            stmts: self.stmts,
            trailing: self.trailing,
        }
    }

    // -- Expression builders --------------------------------------------------

    /// Integer literal that fits in 64 bits.
    pub fn build_int_literal(&mut self, value: i64, ty: TypeId) -> VirRef {
        Box::new(VirExpr::IntLiteral { value, ty })
    }

    /// Wide integer literal (i128) stored as two 64-bit halves.
    pub fn build_wide_literal(&mut self, low: u64, high: u64, ty: TypeId) -> VirRef {
        Box::new(VirExpr::WideLiteral { low, high, ty })
    }

    /// Floating-point literal.
    pub fn build_float_literal(&mut self, value: f64, ty: TypeId) -> VirRef {
        Box::new(VirExpr::FloatLiteral { value, ty })
    }

    /// Boolean literal.
    pub fn build_bool_literal(&mut self, value: bool) -> VirRef {
        Box::new(VirExpr::BoolLiteral(value))
    }

    /// Interned string literal.
    pub fn build_string_literal(&mut self, symbol: Symbol) -> VirRef {
        Box::new(VirExpr::StringLiteral(symbol))
    }

    /// The `nil` literal.
    pub fn build_nil_literal(&mut self) -> VirRef {
        Box::new(VirExpr::NilLiteral)
    }

    /// Binary operation (arithmetic, comparison, logical, bitwise).
    pub fn build_binary_op(
        &mut self,
        op: VirBinOp,
        lhs: VirRef,
        rhs: VirRef,
        ty: TypeId,
        line: u32,
    ) -> VirRef {
        Box::new(VirExpr::BinaryOp {
            op,
            lhs,
            rhs,
            ty,
            line,
        })
    }

    /// Unary operation (negation, logical/bitwise not).
    pub fn build_unary_op(&mut self, op: VirUnOp, operand: VirRef, ty: TypeId) -> VirRef {
        Box::new(VirExpr::UnaryOp { op, operand, ty })
    }

    /// Function or method call.
    pub fn build_call(&mut self, target: CallTarget, args: Vec<VirRef>, ty: TypeId) -> VirRef {
        Box::new(VirExpr::Call { target, args, ty })
    }

    /// Type coercion (numeric widening, boxing, iterator wrapping, etc.).
    pub fn build_coerce(
        &mut self,
        value: VirRef,
        from: TypeId,
        to: TypeId,
        kind: CoerceKind,
    ) -> VirRef {
        Box::new(VirExpr::Coerce {
            value,
            from,
            to,
            kind,
        })
    }

    /// Increment the reference count of a value (expression form — returns
    /// the value).
    pub fn build_rc_inc(&mut self, value: VirRef) -> VirRef {
        Box::new(VirExpr::RcInc { value })
    }

    /// Decrement the reference count of a value (expression form — returns
    /// the value).
    pub fn build_rc_dec(&mut self, value: VirRef) -> VirRef {
        Box::new(VirExpr::RcDec { value })
    }

    /// Transfer ownership of a reference-counted value (consume without
    /// decrement).
    pub fn build_rc_move(&mut self, value: VirRef) -> VirRef {
        Box::new(VirExpr::RcMove { value })
    }

    /// Load a field from a struct or class instance.
    pub fn build_field_load(
        &mut self,
        object: VirRef,
        field: Symbol,
        storage: FieldStorage,
        ty: TypeId,
    ) -> VirRef {
        Box::new(VirExpr::FieldLoad {
            object,
            field,
            storage,
            ty,
        })
    }

    /// Load a local variable.
    pub fn build_local_load(&mut self, name: Symbol, ty: TypeId) -> VirRef {
        Box::new(VirExpr::LocalLoad { name, ty })
    }

    /// Conditional expression (if/else).
    pub fn build_if_expr(
        &mut self,
        cond: VirRef,
        then_body: VirBody,
        else_body: Option<VirBody>,
        ty: TypeId,
    ) -> VirRef {
        Box::new(VirExpr::If {
            cond,
            then_body,
            else_body,
            ty,
        })
    }

    // -- Statement builders ---------------------------------------------------

    /// Local variable binding (`let x = ...`).
    pub fn build_let(&mut self, name: Symbol, value: VirRef, mutable: bool, ty: TypeId) -> VirStmt {
        VirStmt::Let {
            name,
            value,
            mutable,
            ty,
        }
    }

    /// Assignment to a local variable.
    pub fn build_assign_local(&mut self, name: Symbol, value: VirRef) -> VirStmt {
        VirStmt::Assign {
            target: AssignTarget::Local(name),
            value,
        }
    }

    /// Expression used as a statement (value is discarded).
    pub fn build_expr_stmt(&mut self, value: VirRef) -> VirStmt {
        VirStmt::Expr { value }
    }

    /// Return from the enclosing function.
    pub fn build_return(&mut self, value: Option<VirRef>) -> VirStmt {
        VirStmt::Return { value }
    }

    /// Decrement reference count (statement form — fire-and-forget).
    pub fn build_rc_dec_stmt(&mut self, value: VirRef) -> VirStmt {
        VirStmt::RcDec { value }
    }

    // -- Body / function construction -----------------------------------------

    /// Assemble a body from a list of statements and an optional trailing
    /// expression.
    pub fn build_body(&mut self, stmts: Vec<VirStmt>, trailing: Option<VirRef>) -> VirBody {
        VirBody { stmts, trailing }
    }

    /// Consume the builder, producing a complete `VirFunction`.
    pub fn finish(
        self,
        id: FunctionId,
        name: String,
        params: Vec<(Symbol, TypeId)>,
        return_ty: TypeId,
        body: VirBody,
    ) -> VirFunction {
        VirFunction {
            id,
            name,
            params,
            return_type: return_ty,
            body,
            mangled_name_id: None,
            method_id: None,
        }
    }
}

impl Default for VirBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{FieldStorage, VirBinOp, VirExpr};

    fn dummy_type_id() -> TypeId {
        TypeId::from_raw(0)
    }

    fn dummy_function_id() -> FunctionId {
        FunctionId::new(0)
    }

    fn dummy_symbol() -> Symbol {
        Symbol::UNKNOWN
    }

    #[test]
    fn build_let_and_return() {
        let mut b = VirBuilder::new();
        let ty = dummy_type_id();

        // let x = 42
        let lit = b.build_int_literal(42, ty);
        let let_stmt = b.build_let(dummy_symbol(), lit, false, ty);

        // return x
        let load = b.build_local_load(dummy_symbol(), ty);
        let ret = b.build_return(Some(load));

        let body = b.build_body(vec![let_stmt, ret], None);
        let func =
            VirBuilder::new().finish(dummy_function_id(), "test_fn".into(), vec![], ty, body);

        assert_eq!(func.name, "test_fn");
        assert_eq!(func.body.stmts.len(), 2);
        assert!(func.body.trailing.is_none());

        // Verify the let statement
        match &func.body.stmts[0] {
            VirStmt::Let { mutable, .. } => assert!(!mutable),
            other => panic!("expected Let, got {other:?}"),
        }

        // Verify the return
        match &func.body.stmts[1] {
            VirStmt::Return { value } => assert!(value.is_some()),
            other => panic!("expected Return, got {other:?}"),
        }
    }

    #[test]
    fn build_if_expression() {
        let mut b = VirBuilder::new();
        let ty = dummy_type_id();

        // if true { 1 } else { 2 }
        let cond = b.build_bool_literal(true);
        let then_val = b.build_int_literal(1, ty);
        let else_val = b.build_int_literal(2, ty);

        let then_body = b.build_body(vec![], Some(then_val));
        let else_body = b.build_body(vec![], Some(else_val));
        let if_expr = b.build_if_expr(cond, then_body, Some(else_body), ty);

        // Use as trailing expression
        let body = b.build_body(vec![], Some(if_expr));

        assert!(body.trailing.is_some());
        match body.trailing.as_deref() {
            Some(VirExpr::If {
                else_body: Some(_), ..
            }) => {}
            other => panic!("expected If with else, got {other:?}"),
        }
    }

    #[test]
    fn build_incremental_body() {
        let mut b = VirBuilder::new();
        let ty = dummy_type_id();

        // Build the let's value and the statement, then push
        let lit = b.build_int_literal(10, ty);
        let let_stmt = b.build_let(dummy_symbol(), lit, true, ty);
        b.push(let_stmt);

        let load = b.build_local_load(dummy_symbol(), ty);
        b.set_trailing(load);

        let body = b.build();
        assert_eq!(body.stmts.len(), 1);
        assert!(body.trailing.is_some());
    }

    #[test]
    fn build_binary_and_field_load() {
        let mut b = VirBuilder::new();
        let ty = dummy_type_id();

        let lhs = b.build_int_literal(1, ty);
        let rhs = b.build_int_literal(2, ty);
        let sum = b.build_binary_op(VirBinOp::Add, lhs, rhs, ty, 0);

        match sum.as_ref() {
            VirExpr::BinaryOp { op, .. } => assert_eq!(*op, VirBinOp::Add),
            other => panic!("expected BinaryOp, got {other:?}"),
        }

        let obj = b.build_local_load(dummy_symbol(), ty);
        let field = b.build_field_load(obj, dummy_symbol(), FieldStorage::Direct { offset: 8 }, ty);

        match field.as_ref() {
            VirExpr::FieldLoad {
                storage: FieldStorage::Direct { offset: 8 },
                ..
            } => {}
            other => panic!("expected FieldLoad Direct@8, got {other:?}"),
        }
    }

    #[test]
    fn build_rc_operations() {
        let mut b = VirBuilder::new();
        let ty = dummy_type_id();

        let val = b.build_local_load(dummy_symbol(), ty);
        let inc = b.build_rc_inc(val);
        match inc.as_ref() {
            VirExpr::RcInc { .. } => {}
            other => panic!("expected RcInc, got {other:?}"),
        }

        let val2 = b.build_local_load(dummy_symbol(), ty);
        let dec = b.build_rc_dec(val2);
        match dec.as_ref() {
            VirExpr::RcDec { .. } => {}
            other => panic!("expected RcDec, got {other:?}"),
        }

        let val3 = b.build_local_load(dummy_symbol(), ty);
        let mv = b.build_rc_move(val3);
        match mv.as_ref() {
            VirExpr::RcMove { .. } => {}
            other => panic!("expected RcMove, got {other:?}"),
        }
    }

    #[test]
    fn build_nil_bool_string_float_wide() {
        let mut b = VirBuilder::new();
        let ty = dummy_type_id();

        match b.build_nil_literal().as_ref() {
            VirExpr::NilLiteral => {}
            other => panic!("expected NilLiteral, got {other:?}"),
        }

        match b.build_bool_literal(false).as_ref() {
            VirExpr::BoolLiteral(false) => {}
            other => panic!("expected BoolLiteral(false), got {other:?}"),
        }

        match b.build_string_literal(dummy_symbol()).as_ref() {
            VirExpr::StringLiteral(_) => {}
            other => panic!("expected StringLiteral, got {other:?}"),
        }

        match b.build_float_literal(3.14, ty).as_ref() {
            VirExpr::FloatLiteral { value, .. } => {
                assert!((value - 3.14).abs() < f64::EPSILON);
            }
            other => panic!("expected FloatLiteral, got {other:?}"),
        }

        match b.build_wide_literal(0xDEAD, 0xBEEF, ty).as_ref() {
            VirExpr::WideLiteral { low, high, .. } => {
                assert_eq!(*low, 0xDEAD);
                assert_eq!(*high, 0xBEEF);
            }
            other => panic!("expected WideLiteral, got {other:?}"),
        }
    }
}
