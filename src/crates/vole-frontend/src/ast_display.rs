// src/frontend/ast_display.rs
//! Pretty-printing for AST nodes with symbol resolution.

use std::fmt::Write;

/// Writes to a String, ignoring the Result since it cannot fail.
/// Writing to a String only fails if the underlying `Write` impl returns an error,
/// which String's implementation never does.
macro_rules! w {
    ($dst:expr, $($arg:tt)*) => {{
        let _ = write!($dst, $($arg)*);
    }};
}

/// Writes a line to a String, ignoring the Result since it cannot fail.
macro_rules! wln {
    ($dst:expr, $($arg:tt)*) => {{
        let _ = writeln!($dst, $($arg)*);
    }};
}

use crate::Interner;
use crate::ast::{
    Annotation, AssignTarget, BinaryOp, Block, CallArg, ClassDecl, CompoundOp, Decl, ErrorDecl,
    Expr, ExprKind, ExternalBlock, FieldAccessExpr, FuncBody, FuncDecl, ImplementBlock,
    InterfaceDecl, LetInit, LetStmt, LetTupleStmt, MethodCallExpr, OptionalChainExpr,
    OptionalMethodCallExpr, Param, Program, RaiseStmt, SentinelDecl, Stmt, StringPart, StructDecl,
    StructLiteralExpr, TestCase, TestsDecl, TypeExpr, UnaryOp,
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
            Decl::LetTuple(lt) => self.write_let_tuple_decl(out, lt),
            Decl::Class(c) => self.write_class_decl(out, c),
            Decl::Struct(s) => self.write_struct_decl(out, s),
            Decl::Interface(i) => self.write_interface_decl(out, i),
            Decl::Implement(i) => self.write_implement_decl(out, i),
            Decl::Error(e) => self.write_error_decl(out, e),
            Decl::Sentinel(s) => self.write_sentinel_decl(out, s),
            Decl::External(e) => self.write_external_decl(out, e),
        }
    }

    fn write_annotations(&self, out: &mut String, annotations: &[Annotation]) {
        for ann in annotations {
            self.write_indent(out);
            let name = self.interner.resolve(ann.name);
            if ann.args.is_empty() {
                wln!(out, "@{}", name);
            } else {
                w!(out, "@{}(", name);
                for (i, arg) in ann.args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    match arg {
                        CallArg::Positional(_) => out.push_str("<expr>"),
                        CallArg::Named { name, .. } => {
                            let arg_name = self.interner.resolve(*name);
                            w!(out, "{}: <expr>", arg_name);
                        }
                    }
                }
                out.push_str(")\n");
            }
        }
    }

    fn write_func_decl(&self, out: &mut String, func: &FuncDecl) {
        self.write_annotations(out, &func.annotations);
        self.write_indent(out);
        let name = self.interner.resolve(func.name);
        wln!(out, "FunctionDecl \"{}\"", name);

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
            w!(out, "return_type: ");
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
            wln!(out, "Tests \"{}\"", label);
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
        wln!(out, "ErrorDecl \"{}\"", name);

        if !error_decl.fields.is_empty() {
            let inner = self.indented();
            inner.write_indent(out);
            out.push_str("fields: [");
            for (i, field) in error_decl.fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let field_name = self.interner.resolve(field.name);
                w!(out, "({}: ", field_name);
                self.write_type_inline(out, &field.ty);
                out.push(')');
            }
            out.push_str("]\n");
        }
    }

    fn write_sentinel_decl(&self, out: &mut String, sentinel_decl: &SentinelDecl) {
        self.write_indent(out);
        let name = self.interner.resolve(sentinel_decl.name);
        wln!(out, "SentinelDecl \"{}\"", name);
    }

    fn write_struct_decl(&self, out: &mut String, struct_decl: &StructDecl) {
        self.write_annotations(out, &struct_decl.annotations);
        self.write_indent(out);
        let name = self.interner.resolve(struct_decl.name);
        wln!(out, "StructDecl \"{}\"", name);

        let inner = self.indented();

        if !struct_decl.fields.is_empty() {
            inner.write_indent(out);
            out.push_str("fields: [");
            for (i, field) in struct_decl.fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let field_name = self.interner.resolve(field.name);
                w!(out, "({}: ", field_name);
                self.write_type_inline(out, &field.ty);
                out.push(')');
            }
            out.push_str("]\n");
        }

        for method in &struct_decl.methods {
            inner.write_func_decl(out, method);
        }

        if let Some(ref statics) = struct_decl.statics {
            inner.write_indent(out);
            out.push_str("statics:\n");
            let statics_inner = inner.indented();
            for method in &statics.methods {
                statics_inner.write_indent(out);
                let method_name = self.interner.resolve(method.name);
                wln!(out, "StaticMethod \"{}\"", method_name);
            }
        }
    }

    fn write_let_tuple_decl(&self, out: &mut String, lt: &LetTupleStmt) {
        self.write_indent(out);
        if lt.mutable {
            out.push_str("LetTupleMut\n");
        } else {
            out.push_str("LetTuple\n");
        }
        let inner = self.indented();
        inner.write_indent(out);
        out.push_str("pattern: ");
        self.write_pattern_inline(out, &lt.pattern);
        out.push('\n');
        inner.write_indent(out);
        out.push_str("init:\n");
        inner.indented().write_expr(out, &lt.init);
    }

    fn write_class_decl(&self, out: &mut String, class_decl: &ClassDecl) {
        self.write_annotations(out, &class_decl.annotations);
        self.write_indent(out);
        let name = self.interner.resolve(class_decl.name);
        wln!(out, "ClassDecl \"{}\"", name);

        let inner = self.indented();

        if !class_decl.type_params.is_empty() {
            inner.write_indent(out);
            out.push_str("type_params: [");
            for (i, tp) in class_decl.type_params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(self.interner.resolve(tp.name));
            }
            out.push_str("]\n");
        }

        if !class_decl.implements.is_empty() {
            inner.write_indent(out);
            out.push_str("implements: [");
            for (i, ty) in class_decl.implements.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                self.write_type_inline(out, ty);
            }
            out.push_str("]\n");
        }

        if !class_decl.fields.is_empty() {
            inner.write_indent(out);
            out.push_str("fields: [");
            for (i, field) in class_decl.fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let field_name = self.interner.resolve(field.name);
                w!(out, "({}: ", field_name);
                self.write_type_inline(out, &field.ty);
                out.push(')');
            }
            out.push_str("]\n");
        }

        if let Some(ref external) = class_decl.external {
            self.write_external_block(&inner, out, external);
        }

        for method in &class_decl.methods {
            inner.write_func_decl(out, method);
        }

        if let Some(ref statics) = class_decl.statics {
            inner.write_indent(out);
            out.push_str("statics:\n");
            let statics_inner = inner.indented();
            for method in &statics.methods {
                statics_inner.write_indent(out);
                let method_name = self.interner.resolve(method.name);
                wln!(out, "StaticMethod \"{}\"", method_name);
            }
        }
    }

    fn write_interface_decl(&self, out: &mut String, iface: &InterfaceDecl) {
        self.write_annotations(out, &iface.annotations);
        self.write_indent(out);
        let name = self.interner.resolve(iface.name);
        wln!(out, "InterfaceDecl \"{}\"", name);

        let inner = self.indented();

        if !iface.type_params.is_empty() {
            inner.write_indent(out);
            out.push_str("type_params: [");
            for (i, tp) in iface.type_params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(self.interner.resolve(tp.name));
            }
            out.push_str("]\n");
        }

        if !iface.extends.is_empty() {
            inner.write_indent(out);
            out.push_str("extends: [");
            for (i, ty) in iface.extends.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                self.write_type_inline(out, ty);
            }
            out.push_str("]\n");
        }

        if !iface.fields.is_empty() {
            inner.write_indent(out);
            out.push_str("fields: [");
            for (i, field) in iface.fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                let field_name = self.interner.resolve(field.name);
                w!(out, "({}: ", field_name);
                self.write_type_inline(out, &field.ty);
                out.push(')');
            }
            out.push_str("]\n");
        }

        for external in &iface.external_blocks {
            self.write_external_block(&inner, out, external);
        }

        for method in &iface.methods {
            inner.write_indent(out);
            let method_name = self.interner.resolve(method.name);
            if method.is_default {
                wln!(out, "DefaultMethod \"{}\"", method_name);
            } else if method.body.is_some() {
                wln!(out, "Method \"{}\"", method_name);
            } else {
                wln!(out, "AbstractMethod \"{}\"", method_name);
            }
        }

        if let Some(ref statics) = iface.statics {
            inner.write_indent(out);
            out.push_str("statics:\n");
            let statics_inner = inner.indented();
            for method in &statics.methods {
                statics_inner.write_indent(out);
                let method_name = self.interner.resolve(method.name);
                wln!(out, "StaticMethod \"{}\"", method_name);
            }
        }
    }

    fn write_implement_decl(&self, out: &mut String, impl_block: &ImplementBlock) {
        self.write_indent(out);
        if let Some(ref trait_type) = impl_block.trait_type {
            out.push_str("Implement ");
            self.write_type_inline(out, trait_type);
            out.push_str(" for ");
            self.write_type_inline(out, &impl_block.target_type);
            out.push('\n');
        } else {
            out.push_str("Implement ");
            self.write_type_inline(out, &impl_block.target_type);
            out.push('\n');
        }

        let inner = self.indented();

        if let Some(ref external) = impl_block.external {
            self.write_external_block(&inner, out, external);
        }

        for method in &impl_block.methods {
            inner.write_func_decl(out, method);
        }

        if let Some(ref statics) = impl_block.statics {
            inner.write_indent(out);
            out.push_str("statics:\n");
            let statics_inner = inner.indented();
            for method in &statics.methods {
                statics_inner.write_indent(out);
                let method_name = self.interner.resolve(method.name);
                wln!(out, "StaticMethod \"{}\"", method_name);
            }
        }
    }

    fn write_external_decl(&self, out: &mut String, external: &ExternalBlock) {
        self.write_external_block(self, out, external);
    }

    fn write_external_block(
        &self,
        printer: &AstPrinter<'_>,
        out: &mut String,
        ext: &ExternalBlock,
    ) {
        printer.write_indent(out);
        wln!(out, "External \"{}\"", ext.module_path);
        let inner = printer.indented();
        for func in &ext.functions {
            inner.write_indent(out);
            let func_name = self.interner.resolve(func.vole_name);
            if let Some(ref native_name) = func.native_name {
                wln!(
                    out,
                    "ExternalFunc \"{}\" (native: \"{}\")",
                    func_name,
                    native_name
                );
            } else {
                wln!(out, "ExternalFunc \"{}\"", func_name);
            }
        }
    }

    fn write_test_case(&self, out: &mut String, test: &TestCase) {
        self.write_indent(out);
        wln!(out, "Test \"{}\"", test.name);
        match &test.body {
            FuncBody::Block(block) => self.indented().write_block(out, block),
            FuncBody::Expr(expr) => self.indented().write_expr(out, expr),
        }
    }

    fn write_param_inline(&self, out: &mut String, param: &Param) {
        let name = self.interner.resolve(param.name);
        w!(out, "({}: ", name);
        self.write_type_inline(out, &param.ty);
        out.push(')');
    }

    fn write_type_inline(&self, out: &mut String, ty: &TypeExpr) {
        use crate::ast::TypeExprKind;
        match &ty.kind {
            TypeExprKind::Primitive(p) => {
                out.push_str(p.as_str());
            }
            TypeExprKind::Named(sym) => {
                let name = self.interner.resolve(*sym);
                out.push_str(name);
            }
            TypeExprKind::Array(elem_ty) => {
                out.push('[');
                self.write_type_inline(out, elem_ty);
                out.push(']');
            }
            TypeExprKind::Optional(inner) => {
                self.write_type_inline(out, inner);
                out.push('?');
            }
            TypeExprKind::Union(types) => {
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" | ");
                    }
                    self.write_type_inline(out, ty);
                }
            }
            TypeExprKind::Handle => {
                out.push_str("handle");
            }
            TypeExprKind::Never => {
                out.push_str("never");
            }
            TypeExprKind::Unknown => {
                out.push_str("unknown");
            }
            TypeExprKind::Function {
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
            TypeExprKind::SelfType => {
                out.push_str("Self");
            }
            TypeExprKind::Fallible {
                success_type,
                error_type,
            } => {
                out.push_str("fallible(");
                self.write_type_inline(out, success_type);
                out.push_str(", ");
                self.write_type_inline(out, error_type);
                out.push(')');
            }
            TypeExprKind::Generic { name, args } => {
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
            TypeExprKind::Tuple(elements) => {
                out.push('[');
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.write_type_inline(out, elem);
                }
                out.push(']');
            }
            TypeExprKind::FixedArray { element, size } => {
                out.push('[');
                self.write_type_inline(out, element);
                out.push_str("; ");
                out.push_str(&size.to_string());
                out.push(']');
            }
            TypeExprKind::Structural { fields, methods } => {
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
            TypeExprKind::Combination(parts) => {
                for (i, ty) in parts.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" + ");
                    }
                    self.write_type_inline(out, ty);
                }
            }
            TypeExprKind::QualifiedPath { segments, args } => {
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
                wln!(out, "For \"{}\"", var_name);
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("iterable:\n");
                inner.indented().write_expr(out, &f.iterable);
                inner.write_indent(out);
                out.push_str("body:\n");
                inner.indented().write_block(out, &f.body);
            }
            Stmt::Raise(r) => self.write_raise_stmt(out, r),
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
            wln!(out, "LetMut \"{}\"", name);
        } else {
            wln!(out, "Let \"{}\"", name);
        }
        let inner = self.indented();
        if let Some(ty) = &l.ty {
            inner.write_indent(out);
            w!(out, "type: ");
            inner.write_type_inline(out, ty);
            out.push('\n');
        }
        inner.write_indent(out);
        out.push_str("init:\n");
        match &l.init {
            LetInit::Expr(e) => inner.indented().write_expr(out, e),
            LetInit::TypeAlias(ty) => {
                inner.indented().write_indent(out);
                w!(out, "TypeAlias: ");
                inner.indented().write_type_inline(out, ty);
                out.push('\n');
            }
        }
    }

    fn write_raise_stmt(&self, out: &mut String, raise: &RaiseStmt) {
        self.write_indent(out);
        let error_name = self.interner.resolve(raise.error_name);
        wln!(out, "Raise \"{}\"", error_name);
        if !raise.fields.is_empty() {
            let inner = self.indented();
            inner.write_indent(out);
            out.push_str("fields:\n");
            let fields_inner = inner.indented();
            for field in &raise.fields {
                fields_inner.write_indent(out);
                let field_name = self.interner.resolve(field.name);
                wln!(out, "{}:", field_name);
                fields_inner.indented().write_expr(out, &field.value);
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
                    wln!(out, "Int {}_{}", n, s.as_str());
                } else {
                    wln!(out, "Int {}", n);
                }
            }
            ExprKind::FloatLiteral(n, suffix) => {
                self.write_indent(out);
                if let Some(s) = suffix {
                    wln!(out, "Float {}_{}", n, s.as_str());
                } else {
                    wln!(out, "Float {}", n);
                }
            }
            ExprKind::BoolLiteral(b) => {
                self.write_indent(out);
                wln!(out, "Bool {}", b);
            }
            ExprKind::StringLiteral(s) => {
                self.write_indent(out);
                wln!(out, "String {:?}", s);
            }
            ExprKind::InterpolatedString(parts) => {
                self.write_indent(out);
                out.push_str("InterpolatedString\n");
                let inner = self.indented();
                for part in parts {
                    match part {
                        StringPart::Literal(s) => {
                            inner.write_indent(out);
                            wln!(out, "Literal {:?}", s);
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
                wln!(out, "Ident \"{}\"", name);
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
                wln!(out, "BinaryOp {}", op);
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
                wln!(out, "UnaryOp {}", op);
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
                        self.write_call_arg(out, &args_inner, arg);
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
                wln!(out, "Assign \"{}\"", target_str);
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
                wln!(out, "CompoundAssign {} {}", target_str, op_str);
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
                wln!(out, "ArrayLiteral (len={})", elements.len());
                let inner = self.indented();
                for elem in elements {
                    inner.write_expr(out, elem);
                }
            }
            ExprKind::RepeatLiteral { element, count } => {
                self.write_indent(out);
                wln!(out, "RepeatLiteral (count={})", count);
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
                    wln!(out, "arm[{}]:", i);
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

            ExprKind::Unreachable => {
                self.write_indent(out);
                wln!(out, "Unreachable");
            }

            ExprKind::NullCoalesce(nc) => {
                self.write_indent(out);
                wln!(out, "NullCoalesce");
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
                wln!(out, "Is");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("value:\n");
                inner.indented().write_expr(out, &is_expr.value);
                inner.write_indent(out);
                out.push_str("type: ");
                self.write_type_inline(out, &is_expr.type_expr);
                out.push('\n');
            }

            ExprKind::AsCast(as_cast) => {
                self.write_indent(out);
                let op = match as_cast.kind {
                    crate::ast::AsCastKind::Safe => "AsCastSafe",
                    crate::ast::AsCastKind::Unsafe => "AsCastUnsafe",
                };
                wln!(out, "{}", op);
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("value:\n");
                inner.indented().write_expr(out, &as_cast.value);
                inner.write_indent(out);
                out.push_str("type: ");
                self.write_type_inline(out, &as_cast.type_expr);
                out.push('\n');
            }

            ExprKind::Lambda(lambda) => {
                self.write_indent(out);
                wln!(out, "Lambda");
                let inner = self.indented();
                for (i, param) in lambda.params.iter().enumerate() {
                    inner.write_indent(out);
                    w!(out, "param[{}]: {}", i, self.interner.resolve(param.name));
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

            ExprKind::StructLiteral(sl) => self.write_struct_literal(out, sl),

            ExprKind::FieldAccess(fa) => self.write_field_access(out, fa),

            ExprKind::OptionalChain(oc) => self.write_optional_chain(out, oc),

            ExprKind::OptionalMethodCall(omc) => self.write_optional_method_call(out, omc),

            ExprKind::MethodCall(mc) => self.write_method_call(out, mc),

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
                    wln!(out, "arm[{}]:", i);
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

    fn write_struct_literal(&self, out: &mut String, sl: &StructLiteralExpr) {
        self.write_indent(out);
        // Format path as module.Type or just Type
        let path_str: String = sl
            .path
            .iter()
            .map(|sym| self.interner.resolve(*sym))
            .collect::<Vec<_>>()
            .join(".");
        wln!(out, "StructLiteral \"{}\"", path_str);
        let inner = self.indented();

        if !sl.type_args.is_empty() {
            inner.write_indent(out);
            out.push_str("type_args: [");
            for (i, ty) in sl.type_args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                self.write_type_inline(out, ty);
            }
            out.push_str("]\n");
        }

        if !sl.fields.is_empty() {
            inner.write_indent(out);
            out.push_str("fields:\n");
            let fields_inner = inner.indented();
            for field in &sl.fields {
                fields_inner.write_indent(out);
                let field_name = self.interner.resolve(field.name);
                if field.shorthand {
                    wln!(out, "{} (shorthand):", field_name);
                } else {
                    wln!(out, "{}:", field_name);
                }
                fields_inner.indented().write_expr(out, &field.value);
            }
        }
    }

    fn write_field_access(&self, out: &mut String, fa: &FieldAccessExpr) {
        self.write_indent(out);
        let field_name = self.interner.resolve(fa.field);
        wln!(out, "FieldAccess \"{}\"", field_name);
        let inner = self.indented();
        inner.write_indent(out);
        out.push_str("object:\n");
        inner.indented().write_expr(out, &fa.object);
    }

    fn write_optional_chain(&self, out: &mut String, oc: &OptionalChainExpr) {
        self.write_indent(out);
        let field_name = self.interner.resolve(oc.field);
        wln!(out, "OptionalChain \"{}\"", field_name);
        let inner = self.indented();
        inner.write_indent(out);
        out.push_str("object:\n");
        inner.indented().write_expr(out, &oc.object);
    }

    fn write_optional_method_call(&self, out: &mut String, omc: &OptionalMethodCallExpr) {
        self.write_indent(out);
        let method_name = self.interner.resolve(omc.method);
        wln!(out, "OptionalMethodCall \"{}\"", method_name);
        let inner = self.indented();

        inner.write_indent(out);
        out.push_str("object:\n");
        inner.indented().write_expr(out, &omc.object);

        if !omc.type_args.is_empty() {
            inner.write_indent(out);
            out.push_str("type_args: [");
            for (i, ty) in omc.type_args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                self.write_type_inline(out, ty);
            }
            out.push_str("]\n");
        }

        if !omc.args.is_empty() {
            inner.write_indent(out);
            out.push_str("args:\n");
            let args_inner = inner.indented();
            for arg in &omc.args {
                self.write_call_arg(out, &args_inner, arg);
            }
        }
    }

    fn write_method_call(&self, out: &mut String, mc: &MethodCallExpr) {
        self.write_indent(out);
        let method_name = self.interner.resolve(mc.method);
        wln!(out, "MethodCall \"{}\"", method_name);
        let inner = self.indented();

        inner.write_indent(out);
        out.push_str("object:\n");
        inner.indented().write_expr(out, &mc.object);

        if !mc.type_args.is_empty() {
            inner.write_indent(out);
            out.push_str("type_args: [");
            for (i, ty) in mc.type_args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                self.write_type_inline(out, ty);
            }
            out.push_str("]\n");
        }

        if !mc.args.is_empty() {
            inner.write_indent(out);
            out.push_str("args:\n");
            let args_inner = inner.indented();
            for arg in &mc.args {
                self.write_call_arg(out, &args_inner, arg);
            }
        }
    }

    /// Display a single call argument, showing the name prefix for named args.
    fn write_call_arg(&self, out: &mut String, printer: &AstPrinter<'_>, arg: &CallArg) {
        match arg {
            CallArg::Positional(expr) => printer.write_expr(out, expr),
            CallArg::Named { name, value, .. } => {
                printer.write_indent(out);
                wln!(out, "named: {}", self.interner.resolve(*name));
                printer.indented().write_expr(out, value);
            }
        }
    }

    fn write_pattern_inline(&self, out: &mut String, pattern: &crate::Pattern) {
        use crate::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => out.push('_'),
            PatternKind::Literal(expr) => match &expr.kind {
                ExprKind::IntLiteral(n, _) => w!(out, "{}", n),
                ExprKind::FloatLiteral(n, _) => w!(out, "{}", n),
                ExprKind::BoolLiteral(b) => w!(out, "{}", b),
                ExprKind::StringLiteral(s) => w!(out, "{:?}", s),
                ExprKind::Unary(u) => {
                    out.push('-');
                    if let ExprKind::IntLiteral(n, _) = &u.operand.kind {
                        w!(out, "{}", n);
                    } else if let ExprKind::FloatLiteral(n, _) = &u.operand.kind {
                        w!(out, "{}", n);
                    }
                }
                _ => out.push_str("<expr>"),
            },
            PatternKind::Identifier { name, .. } => {
                let ident = self.interner.resolve(*name);
                out.push_str(ident);
            }
            PatternKind::Type { type_expr, .. } => {
                self.write_type_inline(out, type_expr);
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
            PatternKind::Record { type_name, fields } => {
                if let Some(type_expr) = type_name {
                    self.write_type_inline(out, type_expr);
                    out.push(' ');
                }
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Parser;
    use crate::ast::ModuleId;

    #[test]
    fn print_simple_function() {
        let source = r#"
func add(a: i64, b: i64) -> i64 {
    return a + b
}
"#;
        let mut parser = Parser::new(source, ModuleId::new(0));
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
        let mut parser = Parser::new(source, ModuleId::new(0));
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();

        let with_tests = AstPrinter::new(&interner, false).print_program(&program);
        let without_tests = AstPrinter::new(&interner, true).print_program(&program);

        assert!(with_tests.contains("Tests"));
        assert!(!without_tests.contains("Tests"));
    }
}
