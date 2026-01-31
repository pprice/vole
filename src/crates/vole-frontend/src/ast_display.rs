// src/frontend/ast_display.rs
//! Pretty-printing for AST nodes with symbol resolution.

use std::fmt::Write;

use crate::{
    AssignTarget, BinaryOp, Block, CompoundOp, Decl, ErrorDecl, Expr, ExprKind, FuncBody, FuncDecl,
    Interner, LetInit, LetStmt, Param, PrimitiveType, Program, Stmt, StringPart, TestCase,
    TestsDecl, TypeExpr, UnaryOp,
};

/// Pretty-printer for AST nodes that resolves symbols via an Interner.
pub struct AstPrinter<'a> {
    interner: &'a Interner,
    indent: usize,
    no_tests: bool,
}

impl<'a> AstPrinter<'a> {
    /// Create a new AstPrinter.
    pub fn new(interner: &'a Interner, no_tests: bool) -> Self {
        Self {
            interner,
            indent: 0,
            no_tests,
        }
    }

    /// Print an entire program to a String.
    pub fn print_program(&self, program: &Program) -> String {
        let mut out = String::new();
        self.write_program(&mut out, program);
        out
    }

    fn write_indent(&self, out: &mut String) {
        for _ in 0..self.indent {
            out.push_str("  ");
        }
    }

    fn indented(&self) -> Self {
        Self {
            interner: self.interner,
            indent: self.indent + 1,
            no_tests: self.no_tests,
        }
    }

    fn write_program(&self, out: &mut String, program: &Program) {
        out.push_str("Program\n");
        let inner = self.indented();
        for decl in &program.declarations {
            if self.no_tests && matches!(decl, Decl::Tests(_)) {
                continue;
            }
            inner.write_decl(out, decl);
        }
    }

    fn write_decl(&self, out: &mut String, decl: &Decl) {
        match decl {
            Decl::Function(f) => self.write_func_decl(out, f),
            Decl::Tests(t) => self.write_tests_decl(out, t),
            Decl::Let(l) => self.write_let(out, l),
            Decl::LetTuple(_) => {
                // TODO: implement let tuple display
            }
            Decl::Class(_) => {
                // TODO: implement class display
            }
            Decl::Struct(s) => self.write_struct_decl(out, s),
            Decl::Interface(_) | Decl::Implement(_) => {
                // TODO: implement interface/implement display
            }
            Decl::Error(e) => self.write_error_decl(out, e),
            Decl::External(_) => {
                // TODO: implement external decl display
            }
        }
    }

    fn write_func_decl(&self, out: &mut String, func: &FuncDecl) {
        self.write_indent(out);
        let name = self.interner.resolve(func.name);
        writeln!(out, "FunctionDecl \"{}\"", name).unwrap();

        let inner = self.indented();

        // Params
        if !func.params.is_empty() {
            inner.write_indent(out);
            out.push_str("params: [");
            for (i, param) in func.params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                inner.write_param_inline(out, param);
            }
            out.push_str("]\n");
        }

        // Return type
        if let Some(ret) = &func.return_type {
            inner.write_indent(out);
            write!(out, "return_type: ").unwrap();
            inner.write_type_inline(out, ret);
            out.push('\n');
        }

        // Body
        inner.write_indent(out);
        out.push_str("body:\n");
        match &func.body {
            FuncBody::Block(block) => inner.indented().write_block(out, block),
            FuncBody::Expr(expr) => inner.indented().write_expr(out, expr),
        }
    }

    fn write_tests_decl(&self, out: &mut String, tests: &TestsDecl) {
        self.write_indent(out);
        if let Some(label) = &tests.label {
            writeln!(out, "Tests \"{}\"", label).unwrap();
        } else {
            out.push_str("Tests\n");
        }

        let inner = self.indented();
        // Print scoped declarations
        for decl in &tests.decls {
            inner.write_decl(out, decl);
        }
        // Print test cases
        for test in &tests.tests {
            inner.write_test_case(out, test);
        }
    }

    fn write_error_decl(&self, out: &mut String, error_decl: &ErrorDecl) {
        self.write_indent(out);
        let name = self.interner.resolve(error_decl.name);
        writeln!(out, "ErrorDecl \"{}\"", name).unwrap();

        if !error_decl.fields.is_empty() {
            let inner = self.indented();
            inner.write_indent(out);
            out.push_str("fields: [");
            for (i, field) in error_decl.fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let field_name = self.interner.resolve(field.name);
                write!(out, "({}: ", field_name).unwrap();
                self.write_type_inline(out, &field.ty);
                out.push(')');
            }
            out.push_str("]\n");
        }
    }

    fn write_struct_decl(&self, out: &mut String, struct_decl: &crate::StructDecl) {
        self.write_indent(out);
        let name = self.interner.resolve(struct_decl.name);
        writeln!(out, "StructDecl \"{}\"", name).unwrap();

        if !struct_decl.fields.is_empty() {
            let inner = self.indented();
            inner.write_indent(out);
            out.push_str("fields: [");
            for (i, field) in struct_decl.fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let field_name = self.interner.resolve(field.name);
                write!(out, "({}: ", field_name).unwrap();
                self.write_type_inline(out, &field.ty);
                out.push(')');
            }
            out.push_str("]\n");
        }
    }

    fn write_test_case(&self, out: &mut String, test: &TestCase) {
        self.write_indent(out);
        writeln!(out, "Test \"{}\"", test.name).unwrap();
        match &test.body {
            FuncBody::Block(block) => self.indented().write_block(out, block),
            FuncBody::Expr(expr) => self.indented().write_expr(out, expr),
        }
    }

    fn write_param_inline(&self, out: &mut String, param: &Param) {
        let name = self.interner.resolve(param.name);
        write!(out, "({}: ", name).unwrap();
        self.write_type_inline(out, &param.ty);
        out.push(')');
    }

    fn write_type_inline(&self, out: &mut String, ty: &TypeExpr) {
        match ty {
            TypeExpr::Primitive(p) => {
                let s = match p {
                    PrimitiveType::I8 => "i8",
                    PrimitiveType::I16 => "i16",
                    PrimitiveType::I32 => "i32",
                    PrimitiveType::I64 => "i64",
                    PrimitiveType::I128 => "i128",
                    PrimitiveType::U8 => "u8",
                    PrimitiveType::U16 => "u16",
                    PrimitiveType::U32 => "u32",
                    PrimitiveType::U64 => "u64",
                    PrimitiveType::F32 => "f32",
                    PrimitiveType::F64 => "f64",
                    PrimitiveType::Bool => "bool",
                    PrimitiveType::String => "string",
                };
                out.push_str(s);
            }
            TypeExpr::Named(sym) => {
                let name = self.interner.resolve(*sym);
                out.push_str(name);
            }
            TypeExpr::Array(elem_ty) => {
                out.push('[');
                self.write_type_inline(out, elem_ty);
                out.push(']');
            }
            TypeExpr::Optional(inner) => {
                self.write_type_inline(out, inner);
                out.push('?');
            }
            TypeExpr::Union(types) => {
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" | ");
                    }
                    self.write_type_inline(out, ty);
                }
            }
            TypeExpr::Nil => {
                out.push_str("nil");
            }
            TypeExpr::Done => {
                out.push_str("Done");
            }
            TypeExpr::Never => {
                out.push_str("never");
            }
            TypeExpr::Unknown => {
                out.push_str("unknown");
            }
            TypeExpr::Function {
                params,
                return_type,
            } => {
                out.push('(');
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_type_inline(out, param);
                }
                out.push_str(") -> ");
                self.write_type_inline(out, return_type);
            }
            TypeExpr::SelfType => {
                out.push_str("Self");
            }
            TypeExpr::Fallible {
                success_type,
                error_type,
            } => {
                out.push_str("fallible(");
                self.write_type_inline(out, success_type);
                out.push_str(", ");
                self.write_type_inline(out, error_type);
                out.push(')');
            }
            TypeExpr::Generic { name, args } => {
                out.push_str(self.interner.resolve(*name));
                out.push('<');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_type_inline(out, arg);
                }
                out.push('>');
            }
            TypeExpr::Tuple(elements) => {
                out.push('[');
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_type_inline(out, elem);
                }
                out.push(']');
            }
            TypeExpr::FixedArray { element, size } => {
                out.push('[');
                self.write_type_inline(out, element);
                out.push_str("; ");
                out.push_str(&size.to_string());
                out.push(']');
            }
            TypeExpr::Structural { fields, methods } => {
                out.push_str("{ ");
                let mut first = true;
                for field in fields {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    out.push_str(self.interner.resolve(field.name));
                    out.push_str(": ");
                    self.write_type_inline(out, &field.ty);
                }
                for method in methods {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    out.push_str("func ");
                    out.push_str(self.interner.resolve(method.name));
                    out.push('(');
                    for (i, param) in method.params.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.write_type_inline(out, param);
                    }
                    out.push_str(") -> ");
                    self.write_type_inline(out, &method.return_type);
                }
                out.push_str(" }");
            }
            TypeExpr::Combination(parts) => {
                for (i, ty) in parts.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" + ");
                    }
                    self.write_type_inline(out, ty);
                }
            }
            TypeExpr::QualifiedPath { segments, args } => {
                for (i, sym) in segments.iter().enumerate() {
                    if i > 0 {
                        out.push('.');
                    }
                    out.push_str(self.interner.resolve(*sym));
                }
                if !args.is_empty() {
                    out.push('<');
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.write_type_inline(out, arg);
                    }
                    out.push('>');
                }
            }
        }
    }

    fn write_block(&self, out: &mut String, block: &Block) {
        for stmt in &block.stmts {
            self.write_stmt(out, stmt);
        }
    }

    fn write_stmt(&self, out: &mut String, stmt: &Stmt) {
        match stmt {
            Stmt::Let(l) => self.write_let(out, l),
            Stmt::Expr(e) => self.write_expr_stmt(out, &e.expr),
            Stmt::Return(r) => {
                self.write_indent(out);
                out.push_str("Return\n");
                if let Some(val) = &r.value {
                    self.indented().write_expr(out, val);
                }
            }
            Stmt::While(w) => {
                self.write_indent(out);
                out.push_str("While\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("condition:\n");
                inner.indented().write_expr(out, &w.condition);
                inner.write_indent(out);
                out.push_str("body:\n");
                inner.indented().write_block(out, &w.body);
            }
            Stmt::If(i) => {
                self.write_indent(out);
                out.push_str("If\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("condition:\n");
                inner.indented().write_expr(out, &i.condition);
                inner.write_indent(out);
                out.push_str("then:\n");
                inner.indented().write_block(out, &i.then_branch);
                if let Some(else_branch) = &i.else_branch {
                    inner.write_indent(out);
                    out.push_str("else:\n");
                    inner.indented().write_block(out, else_branch);
                }
            }
            Stmt::Break(_) => {
                self.write_indent(out);
                out.push_str("Break\n");
            }
            Stmt::Continue(_) => {
                self.write_indent(out);
                out.push_str("Continue\n");
            }
            Stmt::For(f) => {
                self.write_indent(out);
                let var_name = self.interner.resolve(f.var_name);
                writeln!(out, "For \"{}\"", var_name).unwrap();
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("iterable:\n");
                inner.indented().write_expr(out, &f.iterable);
                inner.write_indent(out);
                out.push_str("body:\n");
                inner.indented().write_block(out, &f.body);
            }
            Stmt::Raise(_) => {
                self.write_indent(out);
                out.push_str("Raise\n");
                // TODO: implement raise statement display
            }
            Stmt::LetTuple(lt) => {
                self.write_indent(out);
                out.push_str("LetTuple\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("pattern: ");
                self.write_pattern_inline(out, &lt.pattern);
                out.push('\n');
                inner.write_indent(out);
                out.push_str("init:\n");
                inner.indented().write_expr(out, &lt.init);
            }
        }
    }

    fn write_let(&self, out: &mut String, l: &LetStmt) {
        self.write_indent(out);
        let name = self.interner.resolve(l.name);
        if l.mutable {
            writeln!(out, "LetMut \"{}\"", name).unwrap();
        } else {
            writeln!(out, "Let \"{}\"", name).unwrap();
        }
        let inner = self.indented();
        if let Some(ty) = &l.ty {
            inner.write_indent(out);
            write!(out, "type: ").unwrap();
            inner.write_type_inline(out, ty);
            out.push('\n');
        }
        inner.write_indent(out);
        out.push_str("init:\n");
        match &l.init {
            LetInit::Expr(e) => inner.indented().write_expr(out, e),
            LetInit::TypeAlias(ty) => {
                inner.indented().write_indent(out);
                write!(out, "TypeAlias: ").unwrap();
                inner.indented().write_type_inline(out, ty);
                out.push('\n');
            }
        }
    }

    fn write_expr_stmt(&self, out: &mut String, expr: &Expr) {
        self.write_expr(out, expr);
    }

    fn write_expr(&self, out: &mut String, expr: &Expr) {
        match &expr.kind {
            ExprKind::IntLiteral(n, suffix) => {
                self.write_indent(out);
                if let Some(s) = suffix {
                    writeln!(out, "Int {}_{}", n, s.as_str()).unwrap();
                } else {
                    writeln!(out, "Int {}", n).unwrap();
                }
            }
            ExprKind::FloatLiteral(n, suffix) => {
                self.write_indent(out);
                if let Some(s) = suffix {
                    writeln!(out, "Float {}_{}", n, s.as_str()).unwrap();
                } else {
                    writeln!(out, "Float {}", n).unwrap();
                }
            }
            ExprKind::BoolLiteral(b) => {
                self.write_indent(out);
                writeln!(out, "Bool {}", b).unwrap();
            }
            ExprKind::StringLiteral(s) => {
                self.write_indent(out);
                writeln!(out, "String {:?}", s).unwrap();
            }
            ExprKind::InterpolatedString(parts) => {
                self.write_indent(out);
                out.push_str("InterpolatedString\n");
                let inner = self.indented();
                for part in parts {
                    match part {
                        StringPart::Literal(s) => {
                            inner.write_indent(out);
                            writeln!(out, "Literal {:?}", s).unwrap();
                        }
                        StringPart::Expr(e) => {
                            inner.write_indent(out);
                            out.push_str("Expr:\n");
                            inner.indented().write_expr(out, e);
                        }
                    }
                }
            }
            ExprKind::Identifier(sym) => {
                self.write_indent(out);
                let name = self.interner.resolve(*sym);
                writeln!(out, "Ident \"{}\"", name).unwrap();
            }
            ExprKind::Binary(b) => {
                self.write_indent(out);
                let op = match b.op {
                    BinaryOp::Add => "Add",
                    BinaryOp::Sub => "Sub",
                    BinaryOp::Mul => "Mul",
                    BinaryOp::Div => "Div",
                    BinaryOp::Mod => "Mod",
                    BinaryOp::Eq => "Eq",
                    BinaryOp::Ne => "Ne",
                    BinaryOp::Lt => "Lt",
                    BinaryOp::Gt => "Gt",
                    BinaryOp::Le => "Le",
                    BinaryOp::Ge => "Ge",
                    BinaryOp::And => "And",
                    BinaryOp::Or => "Or",
                    BinaryOp::BitAnd => "BitAnd",
                    BinaryOp::BitOr => "BitOr",
                    BinaryOp::BitXor => "BitXor",
                    BinaryOp::Shl => "Shl",
                    BinaryOp::Shr => "Shr",
                };
                writeln!(out, "BinaryOp {}", op).unwrap();
                let inner = self.indented();
                inner.write_expr(out, &b.left);
                inner.write_expr(out, &b.right);
            }
            ExprKind::Unary(u) => {
                self.write_indent(out);
                let op = match u.op {
                    UnaryOp::Neg => "Neg",
                    UnaryOp::Not => "Not",
                    UnaryOp::BitNot => "BitNot",
                };
                writeln!(out, "UnaryOp {}", op).unwrap();
                self.indented().write_expr(out, &u.operand);
            }
            ExprKind::Call(c) => {
                self.write_indent(out);
                out.push_str("Call\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("callee:\n");
                inner.indented().write_expr(out, &c.callee);
                if !c.args.is_empty() {
                    inner.write_indent(out);
                    out.push_str("args:\n");
                    let args_inner = inner.indented();
                    for arg in &c.args {
                        args_inner.write_expr(out, arg);
                    }
                }
            }
            ExprKind::Assign(a) => {
                self.write_indent(out);
                let target_str = match &a.target {
                    AssignTarget::Variable(sym) => self.interner.resolve(*sym).to_string(),
                    AssignTarget::Discard => "_".to_string(),
                    AssignTarget::Index { .. } => "<index>".to_string(),
                    AssignTarget::Field { field, .. } => {
                        format!("<field>.{}", self.interner.resolve(*field))
                    }
                };
                writeln!(out, "Assign \"{}\"", target_str).unwrap();
                self.indented().write_expr(out, &a.value);
            }
            ExprKind::CompoundAssign(c) => {
                self.write_indent(out);
                let op_str = match c.op {
                    CompoundOp::Add => "+=",
                    CompoundOp::Sub => "-=",
                    CompoundOp::Mul => "*=",
                    CompoundOp::Div => "/=",
                    CompoundOp::Mod => "%=",
                };
                let target_str = match &c.target {
                    AssignTarget::Variable(sym) => self.interner.resolve(*sym).to_string(),
                    AssignTarget::Discard => "_".to_string(),
                    AssignTarget::Index { .. } => "<index>".to_string(),
                    AssignTarget::Field { field, .. } => {
                        format!("<field>.{}", self.interner.resolve(*field))
                    }
                };
                writeln!(out, "CompoundAssign {} {}", target_str, op_str).unwrap();
                self.indented().write_expr(out, &c.value);
            }
            ExprKind::Grouping(inner) => {
                // Skip grouping node, just print inner
                self.write_expr(out, inner);
            }
            ExprKind::Range(r) => {
                self.write_indent(out);
                if r.inclusive {
                    out.push_str("RangeInclusive\n");
                } else {
                    out.push_str("Range\n");
                }
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("start:\n");
                inner.indented().write_expr(out, &r.start);
                inner.write_indent(out);
                out.push_str("end:\n");
                inner.indented().write_expr(out, &r.end);
            }
            ExprKind::ArrayLiteral(elements) => {
                self.write_indent(out);
                writeln!(out, "ArrayLiteral (len={})", elements.len()).unwrap();
                let inner = self.indented();
                for elem in elements {
                    inner.write_expr(out, elem);
                }
            }
            ExprKind::RepeatLiteral { element, count } => {
                self.write_indent(out);
                writeln!(out, "RepeatLiteral (count={})", count).unwrap();
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("element:\n");
                inner.indented().write_expr(out, element);
            }
            ExprKind::Index(idx) => {
                self.write_indent(out);
                out.push_str("Index\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("object:\n");
                inner.indented().write_expr(out, &idx.object);
                inner.write_indent(out);
                out.push_str("index:\n");
                inner.indented().write_expr(out, &idx.index);
            }
            ExprKind::Match(m) => {
                self.write_indent(out);
                out.push_str("Match\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("scrutinee:\n");
                inner.indented().write_expr(out, &m.scrutinee);
                for (i, arm) in m.arms.iter().enumerate() {
                    inner.write_indent(out);
                    writeln!(out, "arm[{}]:", i).unwrap();
                    let arm_inner = inner.indented();
                    arm_inner.write_indent(out);
                    out.push_str("pattern: ");
                    arm_inner.write_pattern_inline(out, &arm.pattern);
                    out.push('\n');
                    if let Some(guard) = &arm.guard {
                        arm_inner.write_indent(out);
                        out.push_str("guard:\n");
                        arm_inner.indented().write_expr(out, guard);
                    }
                    arm_inner.write_indent(out);
                    out.push_str("body:\n");
                    arm_inner.indented().write_expr(out, &arm.body);
                }
            }

            ExprKind::Nil => {
                self.write_indent(out);
                writeln!(out, "Nil").unwrap();
            }

            ExprKind::Done => {
                self.write_indent(out);
                writeln!(out, "Done").unwrap();
            }

            ExprKind::Unreachable => {
                self.write_indent(out);
                writeln!(out, "Unreachable").unwrap();
            }

            ExprKind::NullCoalesce(nc) => {
                self.write_indent(out);
                writeln!(out, "NullCoalesce").unwrap();
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("value:\n");
                inner.indented().write_expr(out, &nc.value);
                inner.write_indent(out);
                out.push_str("default:\n");
                inner.indented().write_expr(out, &nc.default);
            }

            ExprKind::Is(is_expr) => {
                self.write_indent(out);
                writeln!(out, "Is").unwrap();
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("value:\n");
                inner.indented().write_expr(out, &is_expr.value);
                inner.write_indent(out);
                out.push_str("type: ");
                self.write_type_inline(out, &is_expr.type_expr);
                out.push('\n');
            }

            ExprKind::Lambda(lambda) => {
                self.write_indent(out);
                writeln!(out, "Lambda").unwrap();
                let inner = self.indented();
                for (i, param) in lambda.params.iter().enumerate() {
                    inner.write_indent(out);
                    write!(out, "param[{}]: {}", i, self.interner.resolve(param.name)).unwrap();
                    if let Some(ty) = &param.ty {
                        out.push_str(": ");
                        self.write_type_inline(out, ty);
                    }
                    out.push('\n');
                }
                if let Some(ret_ty) = &lambda.return_type {
                    inner.write_indent(out);
                    out.push_str("return_type: ");
                    self.write_type_inline(out, ret_ty);
                    out.push('\n');
                }
                inner.write_indent(out);
                out.push_str("body:\n");
                match &lambda.body {
                    FuncBody::Expr(e) => {
                        inner.indented().write_expr(out, e);
                    }
                    FuncBody::Block(block) => {
                        inner.indented().write_block(out, block);
                    }
                }
            }

            ExprKind::TypeLiteral(ty) => {
                self.write_indent(out);
                out.push_str("TypeLiteral ");
                self.write_type_inline(out, ty);
                out.push('\n');
            }

            ExprKind::StructLiteral(_) => {
                self.write_indent(out);
                out.push_str("StructLiteral\n");
                // TODO: implement struct literal display
            }

            ExprKind::FieldAccess(_) => {
                self.write_indent(out);
                out.push_str("FieldAccess\n");
                // TODO: implement field access display
            }

            ExprKind::OptionalChain(_) => {
                self.write_indent(out);
                out.push_str("OptionalChain\n");
                // TODO: implement optional chain display
            }

            ExprKind::MethodCall(_) => {
                self.write_indent(out);
                out.push_str("MethodCall\n");
                // TODO: implement method call display
            }

            ExprKind::Try(inner) => {
                self.write_indent(out);
                out.push_str("Try ");
                self.write_expr(out, inner);
            }

            ExprKind::Import(path) => {
                self.write_indent(out);
                out.push_str(&format!("Import \"{}\"\n", path));
            }

            ExprKind::Yield(yield_expr) => {
                self.write_indent(out);
                out.push_str("Yield ");
                self.write_expr(out, &yield_expr.value);
            }

            ExprKind::Block(block) => {
                self.write_indent(out);
                out.push_str("Block\n");
                let inner = self.indented();
                if !block.stmts.is_empty() {
                    inner.write_indent(out);
                    out.push_str("stmts:\n");
                    let stmts_inner = inner.indented();
                    for stmt in &block.stmts {
                        stmts_inner.write_stmt(out, stmt);
                    }
                }
                if let Some(trailing) = &block.trailing_expr {
                    inner.write_indent(out);
                    out.push_str("trailing_expr:\n");
                    inner.indented().write_expr(out, trailing);
                }
            }

            ExprKind::If(if_expr) => {
                self.write_indent(out);
                out.push_str("If\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("condition:\n");
                inner.indented().write_expr(out, &if_expr.condition);
                inner.write_indent(out);
                out.push_str("then_branch:\n");
                inner.indented().write_expr(out, &if_expr.then_branch);
                if let Some(else_branch) = &if_expr.else_branch {
                    inner.write_indent(out);
                    out.push_str("else_branch:\n");
                    inner.indented().write_expr(out, else_branch);
                }
            }

            ExprKind::When(when_expr) => {
                self.write_indent(out);
                out.push_str("When\n");
                let inner = self.indented();
                for (i, arm) in when_expr.arms.iter().enumerate() {
                    inner.write_indent(out);
                    writeln!(out, "arm[{}]:", i).unwrap();
                    let arm_inner = inner.indented();
                    arm_inner.write_indent(out);
                    if let Some(ref cond) = arm.condition {
                        out.push_str("condition:\n");
                        arm_inner.indented().write_expr(out, cond);
                    } else {
                        out.push_str("condition: _ (wildcard)\n");
                    }
                    arm_inner.write_indent(out);
                    out.push_str("body:\n");
                    arm_inner.indented().write_expr(out, &arm.body);
                }
            }
        }
    }

    fn write_pattern_inline(&self, out: &mut String, pattern: &crate::Pattern) {
        use crate::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => out.push('_'),
            PatternKind::Literal(expr) => match &expr.kind {
                ExprKind::IntLiteral(n, _) => write!(out, "{}", n).unwrap(),
                ExprKind::FloatLiteral(n, _) => write!(out, "{}", n).unwrap(),
                ExprKind::BoolLiteral(b) => write!(out, "{}", b).unwrap(),
                ExprKind::StringLiteral(s) => write!(out, "{:?}", s).unwrap(),
                ExprKind::Unary(u) => {
                    out.push('-');
                    if let ExprKind::IntLiteral(n, _) = &u.operand.kind {
                        write!(out, "{}", n).unwrap();
                    } else if let ExprKind::FloatLiteral(n, _) = &u.operand.kind {
                        write!(out, "{}", n).unwrap();
                    }
                }
                _ => out.push_str("<expr>"),
            },
            PatternKind::Identifier { name, .. } => {
                let ident = self.interner.resolve(*name);
                out.push_str(ident);
            }
            PatternKind::Type { type_expr, .. } => {
                self.write_type_expr_inline(out, type_expr);
            }
            PatternKind::Val { name, .. } => {
                out.push_str("val ");
                let ident = self.interner.resolve(*name);
                out.push_str(ident);
            }
            PatternKind::Success { inner, .. } => {
                out.push_str("success");
                if let Some(inner_pattern) = inner {
                    out.push(' ');
                    self.write_pattern_inline(out, inner_pattern);
                }
            }
            PatternKind::Error { inner, .. } => {
                out.push_str("error");
                if let Some(inner_pattern) = inner {
                    out.push(' ');
                    self.write_pattern_inline(out, inner_pattern);
                }
            }
            PatternKind::Tuple { elements, .. } => {
                out.push('[');
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_pattern_inline(out, elem);
                }
                out.push(']');
            }
            PatternKind::Record { fields, .. } => {
                out.push_str("{ ");
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    let field_name = self.interner.resolve(field.field_name);
                    let binding_name = self.interner.resolve(field.binding);
                    if field.field_name == field.binding {
                        out.push_str(field_name);
                    } else {
                        out.push_str(&format!("{}: {}", field_name, binding_name));
                    }
                }
                out.push_str(" }");
            }
        }
    }

    fn write_type_expr_inline(&self, out: &mut String, ty: &TypeExpr) {
        use crate::TypeExpr;
        match ty {
            TypeExpr::Primitive(p) => out.push_str(&format!("{:?}", p).to_lowercase()),
            TypeExpr::Named(sym) => out.push_str(self.interner.resolve(*sym)),
            TypeExpr::Array(inner) => {
                out.push('[');
                self.write_type_expr_inline(out, inner);
                out.push(']');
            }
            TypeExpr::Optional(inner) => {
                self.write_type_expr_inline(out, inner);
                out.push('?');
            }
            TypeExpr::Union(types) => {
                for (i, t) in types.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" | ");
                    }
                    self.write_type_expr_inline(out, t);
                }
            }
            TypeExpr::Nil => out.push_str("nil"),
            TypeExpr::Done => out.push_str("Done"),
            TypeExpr::Never => out.push_str("never"),
            TypeExpr::Unknown => out.push_str("unknown"),
            TypeExpr::Function {
                params,
                return_type,
            } => {
                out.push('(');
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_type_expr_inline(out, p);
                }
                out.push_str(") -> ");
                self.write_type_expr_inline(out, return_type);
            }
            TypeExpr::SelfType => out.push_str("Self"),
            TypeExpr::Fallible {
                success_type,
                error_type,
            } => {
                out.push_str("fallible(");
                self.write_type_expr_inline(out, success_type);
                out.push_str(", ");
                self.write_type_expr_inline(out, error_type);
                out.push(')');
            }
            TypeExpr::Generic { name, args } => {
                out.push_str(self.interner.resolve(*name));
                out.push('<');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_type_expr_inline(out, arg);
                }
                out.push('>');
            }
            TypeExpr::Tuple(elements) => {
                out.push('[');
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_type_expr_inline(out, elem);
                }
                out.push(']');
            }
            TypeExpr::FixedArray { element, size } => {
                out.push('[');
                self.write_type_expr_inline(out, element);
                out.push_str("; ");
                out.push_str(&size.to_string());
                out.push(']');
            }
            TypeExpr::Structural { fields, methods } => {
                out.push_str("{ ");
                let mut first = true;
                for field in fields {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    out.push_str(self.interner.resolve(field.name));
                    out.push_str(": ");
                    self.write_type_expr_inline(out, &field.ty);
                }
                for method in methods {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    out.push_str("func ");
                    out.push_str(self.interner.resolve(method.name));
                    out.push('(');
                    for (i, param) in method.params.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.write_type_expr_inline(out, param);
                    }
                    out.push_str(") -> ");
                    self.write_type_expr_inline(out, &method.return_type);
                }
                out.push_str(" }");
            }
            TypeExpr::Combination(parts) => {
                for (i, ty) in parts.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" + ");
                    }
                    self.write_type_expr_inline(out, ty);
                }
            }
            TypeExpr::QualifiedPath { segments, args } => {
                for (i, sym) in segments.iter().enumerate() {
                    if i > 0 {
                        out.push('.');
                    }
                    out.push_str(self.interner.resolve(*sym));
                }
                if !args.is_empty() {
                    out.push('<');
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.write_type_expr_inline(out, arg);
                    }
                    out.push('>');
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Parser;

    #[test]
    fn print_simple_function() {
        let source = r#"
func add(a: i64, b: i64) -> i64 {
    return a + b
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();

        let printer = AstPrinter::new(&interner, false);
        let output = printer.print_program(&program);

        assert!(output.contains("FunctionDecl \"add\""));
        assert!(output.contains("params: [(a: i64), (b: i64)]"));
        assert!(output.contains("return_type: i64"));
        assert!(output.contains("BinaryOp Add"));
    }

    #[test]
    fn print_filters_tests_when_no_tests() {
        let source = r#"
func main() { }

tests {
    test "example" {
        assert(true)
    }
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();

        let with_tests = AstPrinter::new(&interner, false).print_program(&program);
        let without_tests = AstPrinter::new(&interner, true).print_program(&program);

        assert!(with_tests.contains("Tests"));
        assert!(!without_tests.contains("Tests"));
    }
}
