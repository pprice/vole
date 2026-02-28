// vir_printer.rs
//
// Pretty-printing for VIR functions, statements, and expressions.
//
// The `VirPrinter` turns VIR trees into human-readable text for the
// `vole inspect vir` command.  It resolves `Symbol` -> string via the
// interner and `TypeId` -> type name via `display_type_id`.

use std::fmt::Write;

use vole_identity::{Symbol, VirTypeId};

use vole_vir::calls::{CallTarget, NativeAbi};
use vole_vir::expr::{
    AsCastKind, CoerceKind, FieldStorage, IsCheckResult, VirBinOp, VirExpr, VirMetaKind,
    VirPattern, VirStringPart, VirUnOp,
};
use vole_vir::func::{VirBody, VirFunction};
use vole_vir::refs::VirRef;
use vole_vir::stmt::{AssignTarget, VirIterKind, VirStmt};

/// Writes to a String, ignoring the infallible Result.
macro_rules! w {
    ($dst:expr, $($arg:tt)*) => {{
        let _ = write!($dst, $($arg)*);
    }};
}

/// Writes a line to a String, ignoring the infallible Result.
macro_rules! wln {
    ($dst:expr) => {{
        let _ = writeln!($dst);
    }};
    ($dst:expr, $($arg:tt)*) => {{
        let _ = writeln!($dst, $($arg)*);
    }};
}

/// Pretty-printer for VIR trees.
pub struct VirPrinter<'a> {
    analyzed: &'a crate::analyzed::AnalyzedProgram,
}

impl<'a> VirPrinter<'a> {
    pub fn new(analyzed: &'a crate::analyzed::AnalyzedProgram) -> Self {
        Self { analyzed }
    }

    /// Print a single VIR function to a String.
    pub fn print_function(&self, func: &VirFunction) -> String {
        let mut out = String::new();
        let params = func
            .params
            .iter()
            .map(|(sym, ty, _)| format!("{}: {}", self.sym(*sym), self.ty(*ty)))
            .collect::<Vec<_>>()
            .join(", ");
        wln!(
            out,
            "fn {}({}) -> {} {{",
            func.name,
            params,
            self.ty(func.return_type)
        );
        self.fmt_body(&func.body, &mut out, 1);
        wln!(out, "}}");
        out
    }

    /// Print a VIR body (test or function) to a String.
    pub fn print_body(&self, body: &VirBody) -> String {
        let mut out = String::new();
        self.fmt_body(body, &mut out, 0);
        out
    }

    fn fmt_body(&self, body: &VirBody, out: &mut String, ind: usize) {
        for stmt in &body.stmts {
            self.fmt_stmt(stmt, out, ind);
        }
        if let Some(ref trailing) = body.trailing {
            self.pad(out, ind);
            self.fmt_expr(trailing, out, ind);
            wln!(out);
        }
    }

    // -- Statements ---------------------------------------------------------

    fn fmt_stmt(&self, stmt: &VirStmt, out: &mut String, ind: usize) {
        self.pad(out, ind);
        match stmt {
            VirStmt::Let {
                name,
                value,
                mutable,
                ty,
                storage,
                ..
            } => {
                let kw = if *mutable { "let mut" } else { "let" };
                w!(out, "{} {}: {} = ", kw, self.sym(*name), self.ty(*ty));
                self.fmt_expr(value, out, ind);
                match storage {
                    vole_vir::stmt::LetStorageHint::Scalar => {}
                    hint => w!(out, "  // storage={hint:?}"),
                }
                wln!(out);
            }
            VirStmt::LetTuple {
                pattern,
                value,
                init_ty,
                ..
            } => {
                w!(out, "let ");
                self.fmt_destructure_pattern(pattern, out);
                w!(out, ": {} = ", self.ty(*init_ty));
                self.fmt_expr(value, out, ind);
                wln!(out);
            }
            VirStmt::Assign { target, value } => {
                self.fmt_assign_target(target, out, ind);
                w!(out, " = ");
                self.fmt_expr(value, out, ind);
                wln!(out);
            }
            VirStmt::Expr { value } => {
                self.fmt_expr(value, out, ind);
                wln!(out);
            }
            VirStmt::While { cond, body } => {
                w!(out, "while ");
                self.fmt_expr(cond, out, ind);
                wln!(out, " {{");
                self.fmt_body(body, out, ind + 1);
                self.pad(out, ind);
                wln!(out, "}}");
            }
            VirStmt::For(vir_for) => {
                self.fmt_for(vir_for, out, ind);
            }
            VirStmt::Return { value, .. } => {
                if let Some(val) = value {
                    w!(out, "return ");
                    self.fmt_expr(val, out, ind);
                    wln!(out);
                } else {
                    wln!(out, "return");
                }
            }
            VirStmt::Break => wln!(out, "break"),
            VirStmt::Continue => wln!(out, "continue"),
            VirStmt::Raise { error_name, fields } => {
                w!(out, "raise {}", self.sym(*error_name));
                if !fields.is_empty() {
                    w!(out, " {{ ");
                    for (i, (name, val)) in fields.iter().enumerate() {
                        if i > 0 {
                            w!(out, ", ");
                        }
                        w!(out, "{}: ", self.sym(*name));
                        self.fmt_expr(val, out, ind);
                    }
                    w!(out, " }}");
                }
                wln!(out);
            }
            VirStmt::RcInc { value } => {
                w!(out, "rc_inc ");
                self.fmt_expr(value, out, ind);
                wln!(out);
            }
            VirStmt::RcDec { value } => {
                w!(out, "rc_dec ");
                self.fmt_expr(value, out, ind);
                wln!(out);
            }
            VirStmt::Noop => wln!(out, "noop"),
        }
    }

    fn fmt_for(&self, vir_for: &vole_vir::stmt::VirFor, out: &mut String, ind: usize) {
        let kind_label = match &vir_for.kind {
            VirIterKind::Range => "range".to_string(),
            VirIterKind::Array { elem_type, .. } => format!("array<{}>", self.ty(*elem_type)),
            VirIterKind::String => "string".to_string(),
            VirIterKind::IteratorInterface { elem_type, .. } => {
                format!("iterator<{}>", self.ty(*elem_type))
            }
            VirIterKind::CustomIterator { elem_type, .. } => {
                format!("custom_iterator<{}>", self.ty(*elem_type))
            }
            VirIterKind::CustomIterable { elem_type, .. } => {
                format!("custom_iterable<{}>", self.ty(*elem_type))
            }
            VirIterKind::Generic { elem_type, .. } => {
                format!("generic<{}>", self.ty(*elem_type))
            }
        };
        w!(
            out,
            "for {}: {} in [{}] ",
            self.sym(vir_for.var_name),
            self.ty(vir_for.var_type),
            kind_label,
        );
        self.fmt_expr(&vir_for.iterable, out, ind);
        wln!(out, " {{");
        self.fmt_body(&vir_for.body, out, ind + 1);
        self.pad(out, ind);
        wln!(out, "}}");
    }

    fn fmt_assign_target(&self, target: &AssignTarget, out: &mut String, ind: usize) {
        match target {
            AssignTarget::Local(sym) => w!(out, "{}", self.sym(*sym)),
            AssignTarget::Field {
                object,
                field,
                storage,
            } => {
                self.fmt_expr(object, out, ind);
                w!(out, ".{}", self.sym(*field));
                self.fmt_storage_suffix(*storage, out);
            }
            AssignTarget::Index { array, index } => {
                self.fmt_expr(array, out, ind);
                w!(out, "[");
                self.fmt_expr(index, out, ind);
                w!(out, "]");
            }
        }
    }

    // -- Expressions --------------------------------------------------------

    fn fmt_expr(&self, expr: &VirRef, out: &mut String, ind: usize) {
        match expr.as_ref() {
            VirExpr::IntLiteral { value, ty, .. } => {
                w!(out, "{}: {}", value, self.ty(*ty));
            }
            VirExpr::WideLiteral { low, high, ty, .. } => {
                let val = (*low as i128) | ((*high as i128) << 64);
                w!(out, "{}: {}", val, self.ty(*ty));
            }
            VirExpr::FloatLiteral { value, ty, .. } => {
                w!(out, "{}: {}", value, self.ty(*ty));
            }
            VirExpr::BoolLiteral(b) => w!(out, "{}", b),
            VirExpr::StringLiteral(sym) => {
                w!(out, "\"{}\"", self.sym(*sym));
            }
            VirExpr::NilLiteral => w!(out, "nil"),
            VirExpr::Unreachable { line } => w!(out, "unreachable@{}", line),
            VirExpr::Import { ty, .. } => w!(out, "import: {}", self.ty(*ty)),
            VirExpr::TypeLiteral => w!(out, "type_literal"),
            VirExpr::Range {
                start,
                end,
                inclusive,
            } => {
                self.fmt_expr(start, out, ind);
                w!(out, "{}", if *inclusive { "..=" } else { ".." });
                self.fmt_expr(end, out, ind);
            }
            VirExpr::ArrayLiteral { elements, ty, .. } => {
                w!(out, "[");
                self.fmt_comma_list(elements, out, ind);
                w!(out, "]: {}", self.ty(*ty));
            }
            VirExpr::RepeatLiteral {
                element, count, ty, ..
            } => {
                w!(out, "[");
                self.fmt_expr(element, out, ind);
                w!(out, "; {}]: {}", count, self.ty(*ty));
            }
            VirExpr::StructLiteral {
                type_def,
                fields,
                ty,
                ..
            } => {
                self.fmt_construction("struct", *type_def, fields, *ty, out, ind);
            }
            VirExpr::ClassInstance {
                type_def,
                fields,
                ty,
                ..
            } => {
                self.fmt_construction("class", *type_def, fields, *ty, out, ind);
            }
            VirExpr::BinaryOp {
                op, lhs, rhs, ty, ..
            } => {
                w!(out, "(");
                self.fmt_expr(lhs, out, ind);
                w!(out, " {} ", format_binop(*op));
                self.fmt_expr(rhs, out, ind);
                w!(out, "): {}", self.ty(*ty));
            }
            VirExpr::UnaryOp {
                op, operand, ty, ..
            } => {
                w!(out, "({})", format_unop(*op));
                self.fmt_expr(operand, out, ind);
                w!(out, ": {}", self.ty(*ty));
            }
            VirExpr::StringConcat { parts } => {
                w!(out, "concat(");
                self.fmt_comma_list(parts, out, ind);
                w!(out, ")");
            }
            VirExpr::InterpolatedString { parts } => {
                self.fmt_interpolated(parts, out, ind);
            }
            VirExpr::Call {
                target, args, ty, ..
            } => {
                self.fmt_call(target, args, *ty, out, ind);
            }
            VirExpr::MethodCall {
                receiver,
                method,
                args,
                ty,
                ..
            } => {
                self.fmt_expr(receiver, out, ind);
                w!(out, ".{}(", self.sym(*method));
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    self.fmt_expr(arg, out, ind);
                }
                w!(out, "): {}", self.ty(*ty));
            }
            VirExpr::FieldLoad {
                object,
                field,
                storage,
                ty,
                ..
            } => {
                self.fmt_expr(object, out, ind);
                w!(out, ".{}", self.sym(*field));
                self.fmt_storage_suffix(*storage, out);
                w!(out, ": {}", self.ty(*ty));
            }
            VirExpr::FieldStore {
                object,
                field,
                storage,
                value,
            } => {
                self.fmt_expr(object, out, ind);
                w!(out, ".{}", self.sym(*field));
                self.fmt_storage_suffix(*storage, out);
                w!(out, " = ");
                self.fmt_expr(value, out, ind);
            }
            VirExpr::Index {
                object, index, ty, ..
            } => {
                self.fmt_expr(object, out, ind);
                w!(out, "[");
                self.fmt_expr(index, out, ind);
                w!(out, "]: {}", self.ty(*ty));
            }
            VirExpr::IndexStore {
                object,
                index,
                value,
                ..
            } => {
                self.fmt_expr(object, out, ind);
                w!(out, "[");
                self.fmt_expr(index, out, ind);
                w!(out, "] = ");
                self.fmt_expr(value, out, ind);
            }
            VirExpr::RcInc { value } => {
                w!(out, "rc_inc(");
                self.fmt_expr(value, out, ind);
                w!(out, ")");
            }
            VirExpr::RcDec { value } => {
                w!(out, "rc_dec(");
                self.fmt_expr(value, out, ind);
                w!(out, ")");
            }
            VirExpr::RcMove { value } => {
                w!(out, "rc_move(");
                self.fmt_expr(value, out, ind);
                w!(out, ")");
            }
            VirExpr::Coerce {
                value,
                from,
                to,
                kind,
                ..
            } => {
                w!(
                    out,
                    "coerce[{}]({} -> {}, ",
                    format_coerce(*kind),
                    self.ty(*from),
                    self.ty(*to)
                );
                self.fmt_expr(value, out, ind);
                w!(out, ")");
            }
            VirExpr::If {
                cond,
                then_body,
                else_body,
                ty,
                ..
            } => {
                self.fmt_if(cond, then_body, else_body.as_ref(), *ty, out, ind);
            }
            VirExpr::Match {
                scrutinee,
                arms,
                ty,
                ..
            } => {
                self.fmt_match(scrutinee, arms, *ty, out, ind);
            }
            VirExpr::Block {
                stmts,
                trailing,
                ty,
                ..
            } => {
                self.fmt_block(stmts, trailing.as_ref(), *ty, out, ind);
            }
            VirExpr::IsCheck {
                value, result, ty, ..
            } => {
                w!(out, "is_check[{}](", fmt_is_check(result, self));
                self.fmt_expr(value, out, ind);
                w!(out, "): {}", self.ty(*ty));
            }
            VirExpr::AsCast {
                value,
                target_ty,
                kind,
                result,
                ..
            } => {
                let kw = match kind {
                    AsCastKind::Checked => "as?",
                    AsCastKind::Unchecked => "as!",
                };
                w!(out, "cast[{}, {}](", kw, fmt_is_check(result, self));
                self.fmt_expr(value, out, ind);
                w!(out, "): {}", self.ty(*target_ty));
            }
            VirExpr::MetaAccess { kind, ty, .. } => {
                self.fmt_meta_access(kind, *ty, out, ind);
            }
            VirExpr::LocalLoad { name, ty, .. } => {
                w!(out, "{}: {}", self.sym(*name), self.ty(*ty));
            }
            VirExpr::LocalStore { name, value } => {
                w!(out, "{} = ", self.sym(*name));
                self.fmt_expr(value, out, ind);
            }
            VirExpr::Lambda {
                params,
                body,
                captures,
                ty,
                ..
            } => {
                self.fmt_lambda(params, body, captures, *ty, out, ind);
            }
            VirExpr::NullCoalesce {
                value, default, ty, ..
            } => {
                w!(out, "(");
                self.fmt_expr(value, out, ind);
                w!(out, " ?? ");
                self.fmt_expr(default, out, ind);
                w!(out, "): {}", self.ty(*ty));
            }
            VirExpr::OptionalChain {
                object, field, ty, ..
            } => {
                self.fmt_expr(object, out, ind);
                w!(out, "?.{}: {}", self.sym(*field), self.ty(*ty));
            }
            VirExpr::OptionalMethodCall {
                object,
                method,
                method_args,
                ty,
                ..
            } => {
                self.fmt_expr(object, out, ind);
                w!(out, "?.{}(", self.sym(*method));
                for (i, arg) in method_args.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    self.fmt_expr(arg, out, ind);
                }
                w!(out, "): {}", self.ty(*ty));
            }
            VirExpr::Try {
                value,
                success_type,
                ..
            } => {
                self.fmt_expr(value, out, ind);
                w!(out, "?: {}", self.ty(*success_type));
            }
            VirExpr::Yield { value } => {
                w!(out, "yield ");
                self.fmt_expr(value, out, ind);
            }
        }
    }

    // -- Compound expression helpers ----------------------------------------

    fn fmt_call(
        &self,
        target: &CallTarget,
        args: &[VirRef],
        ty: VirTypeId,
        out: &mut String,
        ind: usize,
    ) {
        match target {
            CallTarget::Direct { function_id } => {
                w!(out, "call({:?}, ", function_id);
            }
            CallTarget::VtableMethod { slot } => {
                w!(out, "vtable_call(slot={}, ", slot);
            }
            CallTarget::BuiltinMethod { method } => {
                w!(out, "builtin({:?}, ", method);
            }
            CallTarget::Intrinsic { key } => {
                w!(out, "intrinsic({:?}, ", key);
            }
            CallTarget::IntrinsicRuntime { key } => {
                w!(out, "rt_intrinsic({:?}, ", key);
            }
            CallTarget::Lambda => {
                w!(out, "lambda_call(");
            }
            CallTarget::Native {
                module_path,
                native_name,
                abi,
            } => {
                let abi_str = match abi {
                    NativeAbi::Simple => String::new(),
                    NativeAbi::StructReturn { field_count } => format!(", sret={}", field_count),
                };
                w!(
                    out,
                    "native({}::{}{}, ",
                    self.sym(*module_path),
                    self.sym(*native_name),
                    abi_str,
                );
            }
            CallTarget::GenericCall {
                function_id,
                type_args,
            } => {
                let targs: Vec<String> = type_args.iter().map(|t| format!("{t:?}")).collect();
                w!(
                    out,
                    "generic_call({:?}<{}>, ",
                    function_id,
                    targs.join(", ")
                );
            }
            CallTarget::VirDirect { function_index } => {
                w!(out, "vir_direct(idx={}, ", function_index);
            }
            CallTarget::Unresolved {
                callee_sym, line, ..
            } => {
                w!(out, "unresolved({}@{})(", self.sym(*callee_sym), line);
            }
        }
        self.fmt_comma_list(args, out, ind);
        w!(out, "): {}", self.ty(ty));
    }

    fn fmt_if(
        &self,
        cond: &VirRef,
        then_body: &VirBody,
        else_body: Option<&VirBody>,
        ty: VirTypeId,
        out: &mut String,
        ind: usize,
    ) {
        w!(out, "if ");
        self.fmt_expr(cond, out, ind);
        wln!(out, " {{");
        self.fmt_body(then_body, out, ind + 1);
        self.pad(out, ind);
        if let Some(else_b) = else_body {
            wln!(out, "}} else {{");
            self.fmt_body(else_b, out, ind + 1);
            self.pad(out, ind);
        }
        w!(out, "}}: {}", self.ty(ty));
    }

    fn fmt_match(
        &self,
        scrutinee: &VirRef,
        arms: &[vole_vir::expr::VirMatchArm],
        ty: VirTypeId,
        out: &mut String,
        ind: usize,
    ) {
        w!(out, "match ");
        self.fmt_expr(scrutinee, out, ind);
        wln!(out, " {{");
        for arm in arms {
            self.pad(out, ind + 1);
            self.fmt_pattern(&arm.pattern, out, ind + 1);
            if let Some(ref guard) = arm.guard {
                w!(out, " when ");
                self.fmt_expr(guard, out, ind + 1);
            }
            wln!(out, " => {{");
            self.fmt_body(&arm.body, out, ind + 2);
            self.pad(out, ind + 1);
            wln!(out, "}}");
        }
        self.pad(out, ind);
        w!(out, "}}: {}", self.ty(ty));
    }

    fn fmt_block(
        &self,
        stmts: &[VirStmt],
        trailing: Option<&VirRef>,
        ty: VirTypeId,
        out: &mut String,
        ind: usize,
    ) {
        wln!(out, "{{");
        for stmt in stmts {
            self.fmt_stmt(stmt, out, ind + 1);
        }
        if let Some(trail) = trailing {
            self.pad(out, ind + 1);
            self.fmt_expr(trail, out, ind + 1);
            wln!(out);
        }
        self.pad(out, ind);
        w!(out, "}}: {}", self.ty(ty));
    }

    fn fmt_lambda(
        &self,
        params: &[Symbol],
        body: &VirBody,
        captures: &[vole_vir::expr::VirCapture],
        ty: VirTypeId,
        out: &mut String,
        ind: usize,
    ) {
        let param_str = params
            .iter()
            .map(|s| self.sym(*s))
            .collect::<Vec<_>>()
            .join(", ");
        w!(out, "lambda({})", param_str);
        if !captures.is_empty() {
            let cap_str = captures
                .iter()
                .map(|c| {
                    let prefix = if c.by_ref { "&" } else { "" };
                    format!("{}{}: {}", prefix, self.sym(c.name), self.ty(c.ty))
                })
                .collect::<Vec<_>>()
                .join(", ");
            w!(out, " [{}]", cap_str);
        }
        wln!(out, " {{");
        self.fmt_body(body, out, ind + 1);
        self.pad(out, ind);
        w!(out, "}}: {}", self.ty(ty));
    }

    fn fmt_meta_access(&self, kind: &VirMetaKind, ty: VirTypeId, out: &mut String, ind: usize) {
        match kind {
            VirMetaKind::Static { type_def, object } => {
                if let Some(obj) = object {
                    self.fmt_expr(obj, out, ind);
                    w!(out, ".@meta[static, def={}]", type_def.index());
                } else {
                    w!(out, "<type def={}>.@meta[static]", type_def.index());
                }
            }
            VirMetaKind::Dynamic { value } => {
                self.fmt_expr(value, out, ind);
                w!(out, ".@meta[dynamic]");
            }
            VirMetaKind::TypeParam { value, .. } => {
                self.fmt_expr(value, out, ind);
                w!(out, ".@meta[type_param]");
            }
        }
        w!(out, ": {}", self.ty(ty));
    }

    fn fmt_interpolated(&self, parts: &[VirStringPart], out: &mut String, ind: usize) {
        w!(out, "interpolate(");
        for (i, part) in parts.iter().enumerate() {
            if i > 0 {
                w!(out, ", ");
            }
            match part {
                VirStringPart::Literal(sym) => w!(out, "\"{}\"", self.sym(*sym)),
                VirStringPart::Expr { value, conversion } => {
                    w!(out, "[{:?}] ", conversion);
                    self.fmt_expr(value, out, ind);
                }
            }
        }
        w!(out, ")");
    }

    fn fmt_construction(
        &self,
        kind: &str,
        type_def: vole_identity::TypeDefId,
        fields: &[(Symbol, VirRef)],
        ty: VirTypeId,
        out: &mut String,
        ind: usize,
    ) {
        w!(out, "{}(def={}", kind, type_def.index());
        for (name, val) in fields {
            w!(out, ", {}: ", self.sym(*name));
            self.fmt_expr(val, out, ind);
        }
        w!(out, "): {}", self.ty(ty));
    }

    // -- Patterns -----------------------------------------------------------

    fn fmt_pattern(&self, pattern: &VirPattern, out: &mut String, ind: usize) {
        match pattern {
            VirPattern::Wildcard => w!(out, "_"),
            VirPattern::Binding { name, ty, .. } => {
                w!(out, "{}: {}", self.sym(*name), self.ty(*ty));
            }
            VirPattern::TypeCheck {
                result,
                tested_type,
                binding,
                ..
            } => {
                w!(out, "is {}", self.ty(*tested_type));
                w!(out, " [{}]", fmt_is_check(result, self));
                if let Some((name, ty, _)) = binding {
                    w!(out, " as {}: {}", self.sym(*name), self.ty(*ty));
                }
            }
            VirPattern::Literal {
                value,
                scrutinee_ty,
                ..
            } => {
                self.fmt_expr(value, out, ind);
                w!(out, " [scrutinee: {}]", self.ty(*scrutinee_ty));
            }
            VirPattern::Val { name } => {
                w!(out, "val {}", self.sym(*name));
            }
            VirPattern::Success {
                inner,
                success_type,
                ..
            } => {
                w!(out, "success");
                if let Some(p) = inner {
                    w!(out, " ");
                    self.fmt_pattern(p, out, ind);
                }
                w!(out, ": {}", self.ty(*success_type));
            }
            VirPattern::Error { kind } => {
                self.fmt_error_pattern(kind, out);
            }
            VirPattern::Tuple { bindings } => {
                w!(out, "[");
                for (i, binding) in bindings.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    self.fmt_pattern(&binding.pattern, out, ind);
                }
                w!(out, "]");
            }
            VirPattern::Record {
                type_check,
                tested_type,
                fields,
                source_ty,
                is_union_payload,
                is_struct,
                ..
            } => {
                if let Some(ty) = tested_type {
                    w!(out, "{}", self.ty(*ty));
                }
                w!(out, " {{ ");
                for (i, f) in fields.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    if f.field_name == f.binding_name {
                        w!(out, "{}: {}", self.sym(f.field_name), self.ty(f.ty));
                    } else {
                        w!(
                            out,
                            "{}: {} as {}",
                            self.sym(f.field_name),
                            self.ty(f.ty),
                            self.sym(f.binding_name)
                        );
                    }
                }
                w!(out, " }}");
                if let Some(check) = type_check {
                    w!(out, " [{}]", fmt_is_check(check, self));
                }
                w!(out, " [src: {}", self.ty(*source_ty));
                if *is_union_payload {
                    w!(out, ", union");
                }
                if *is_struct {
                    w!(out, ", struct");
                }
                w!(out, "]");
            }
        }
    }

    fn fmt_error_pattern(&self, kind: &vole_vir::expr::VirErrorPatternKind, out: &mut String) {
        use vole_vir::expr::VirErrorPatternKind;
        match kind {
            VirErrorPatternKind::Bare => w!(out, "error"),
            VirErrorPatternKind::CatchAll { name, error_ty, .. } => {
                w!(out, "error {}: {}", self.sym(*name), self.ty(*error_ty));
            }
            VirErrorPatternKind::Specific { error_tag } => {
                w!(out, "error[tag={}]", error_tag);
            }
            VirErrorPatternKind::SpecificRecord {
                error_tag, fields, ..
            } => {
                w!(out, "error[tag={}] {{ ", error_tag);
                for (i, binding) in fields.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    w!(
                        out,
                        "{} -> {}",
                        self.sym(binding.field_name),
                        self.sym(binding.binding)
                    );
                }
                w!(out, " }}");
            }
        }
    }

    // -- Destructure patterns -----------------------------------------------

    fn fmt_destructure_pattern(
        &self,
        pattern: &vole_vir::stmt::VirDestructurePattern,
        out: &mut String,
    ) {
        use vole_vir::stmt::VirDestructurePattern;
        match pattern {
            VirDestructurePattern::Bind { name, ty, .. } => {
                w!(out, "{}: {}", self.sym(*name), self.ty(*ty));
            }
            VirDestructurePattern::Wildcard => w!(out, "_"),
            VirDestructurePattern::Tuple { elements, .. } => {
                w!(out, "[");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    self.fmt_destructure_pattern(&elem.pattern, out);
                }
                w!(out, "]");
            }
            VirDestructurePattern::Record {
                fields, is_struct, ..
            } => {
                w!(out, "{{ ");
                for (i, f) in fields.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    if f.field_name == f.binding {
                        w!(out, "{}: {}", self.sym(f.field_name), self.ty(f.ty));
                    } else {
                        w!(
                            out,
                            "{}: {} as {}",
                            self.sym(f.field_name),
                            self.ty(f.ty),
                            self.sym(f.binding)
                        );
                    }
                }
                w!(out, " }}");
                if *is_struct {
                    w!(out, " [struct]");
                }
            }
            VirDestructurePattern::Module { bindings, .. } => {
                w!(out, "module {{ ");
                for (i, b) in bindings.iter().enumerate() {
                    if i > 0 {
                        w!(out, ", ");
                    }
                    if b.export_name == b.binding {
                        w!(out, "{}", self.sym(b.export_name));
                    } else {
                        w!(
                            out,
                            "{} as {}",
                            self.sym(b.export_name),
                            self.sym(b.binding)
                        );
                    }
                }
                w!(out, " }}");
            }
        }
    }

    // -- Helpers ------------------------------------------------------------

    fn fmt_comma_list(&self, refs: &[VirRef], out: &mut String, ind: usize) {
        for (i, r) in refs.iter().enumerate() {
            if i > 0 {
                w!(out, ", ");
            }
            self.fmt_expr(r, out, ind);
        }
    }

    fn fmt_storage_suffix(&self, storage: FieldStorage, out: &mut String) {
        match storage {
            FieldStorage::Direct { offset } => w!(out, "@{}", offset),
            FieldStorage::Heap { offset } => w!(out, "#h{}", offset),
            FieldStorage::ByName => {} // no suffix
        }
    }

    fn pad(&self, out: &mut String, level: usize) {
        for _ in 0..level {
            w!(out, "  ");
        }
    }

    fn sym(&self, s: Symbol) -> String {
        // Module functions may carry Symbols interned in a different interner.
        // Guard against out-of-bounds by falling back to a numeric label.
        let interner = self.analyzed.interner();
        if (s.index() as usize) < interner.len() {
            interner.resolve(s).to_string()
        } else {
            format!("$sym{}", s.index())
        }
    }

    fn ty(&self, id: VirTypeId) -> String {
        let sema_ty = crate::types::vir_conversions::vir_to_sema_type_id_lossy(id);
        self.analyzed.display_type_id_short(sema_ty)
    }
}

// -- Free formatting helpers ------------------------------------------------

fn format_binop(op: VirBinOp) -> &'static str {
    match op {
        VirBinOp::Add => "+",
        VirBinOp::Sub => "-",
        VirBinOp::Mul => "*",
        VirBinOp::Div => "/",
        VirBinOp::Mod => "%",
        VirBinOp::Eq => "==",
        VirBinOp::Ne => "!=",
        VirBinOp::Lt => "<",
        VirBinOp::Le => "<=",
        VirBinOp::Gt => ">",
        VirBinOp::Ge => ">=",
        VirBinOp::And => "&&",
        VirBinOp::Or => "||",
        VirBinOp::BitAnd => "&",
        VirBinOp::BitOr => "|",
        VirBinOp::BitXor => "^",
        VirBinOp::Shl => "<<",
        VirBinOp::Shr => ">>",
    }
}

fn format_unop(op: VirUnOp) -> &'static str {
    match op {
        VirUnOp::Neg => "-",
        VirUnOp::Not => "!",
        VirUnOp::BitNot => "~",
    }
}

fn format_coerce(kind: CoerceKind) -> &'static str {
    match kind {
        CoerceKind::IntExtend => "int_extend",
        CoerceKind::IntTruncate => "int_truncate",
        CoerceKind::IntToFloat => "int_to_float",
        CoerceKind::FloatToInt => "float_to_int",
        CoerceKind::FloatExtend => "float_extend",
        CoerceKind::FloatTruncate => "float_truncate",
        CoerceKind::Box => "box",
        CoerceKind::Unbox => "unbox",
        CoerceKind::IteratorWrap => "iterator_wrap",
    }
}

fn fmt_is_check(result: &IsCheckResult, printer: &VirPrinter<'_>) -> String {
    match result {
        IsCheckResult::AlwaysTrue => "always_true".to_string(),
        IsCheckResult::AlwaysFalse => "always_false".to_string(),
        IsCheckResult::CheckTag(tag) => format!("check_tag={}", tag),
        IsCheckResult::CheckUnknown(ty, _) => format!("check_unknown={}", printer.ty(*ty)),
    }
}
