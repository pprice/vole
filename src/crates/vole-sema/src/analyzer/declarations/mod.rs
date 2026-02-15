//! Declaration signature collection (Pass 1 of semantic analysis).

mod classes;
mod externals;
mod functions;
mod implements;
mod interfaces;
mod methods;
mod structs;
mod type_params;

use super::*;
use crate::entity_defs::{GenericFuncInfo, GenericTypeInfo, TypeDefKind};
use crate::generic::TypeConstraint;
use crate::type_arena::{InternedStructural, TypeId as ArenaTypeId, TypeIdVec};
use vole_frontend::ast::{
    ExprKind, FieldDef as AstFieldDef, LetInit, TypeExpr, TypeExprKind, TypeMapping,
};

/// Data needed for function registration in the entity registry.
struct FuncRegistrationData {
    name_id: NameId,
    required_params: usize,
    param_defaults: Vec<Option<Box<Expr>>>,
}

/// Extract the base interface name from a TypeExpr.
/// For `Iterator` returns `Iterator`, for `Iterator<i64>` returns `Iterator`.
/// For `mod.Interface` returns the last segment `Interface`.
fn interface_base_name(type_expr: &TypeExpr) -> Option<Symbol> {
    match &type_expr.kind {
        TypeExprKind::Named(sym) => Some(*sym),
        TypeExprKind::Generic { name, .. } => Some(*name),
        TypeExprKind::QualifiedPath { segments, .. } => segments.last().copied(),
        _ => None,
    }
}

/// Check if a TypeExpr is a qualified path (mod.Interface).
fn is_qualified_path(type_expr: &TypeExpr) -> bool {
    matches!(type_expr.kind, TypeExprKind::QualifiedPath { .. })
}

/// Format a TypeExpr for error messages.
fn format_type_expr(type_expr: &TypeExpr, interner: &Interner) -> String {
    match &type_expr.kind {
        TypeExprKind::Named(sym) => interner.resolve(*sym).to_string(),
        TypeExprKind::Generic { name, args } => {
            let args_str: Vec<String> =
                args.iter().map(|a| format_type_expr(a, interner)).collect();
            format!("{}<{}>", interner.resolve(*name), args_str.join(", "))
        }
        TypeExprKind::QualifiedPath { segments, args } => {
            let path_str: String = segments
                .iter()
                .map(|s| interner.resolve(*s))
                .collect::<Vec<_>>()
                .join(".");
            if args.is_empty() {
                path_str
            } else {
                let args_str: Vec<String> =
                    args.iter().map(|a| format_type_expr(a, interner)).collect();
                format!("{}<{}>", path_str, args_str.join(", "))
            }
        }
        _ => "unknown".to_string(),
    }
}

impl Analyzer {
    /// Pass 0.5: Register all type shells so forward references work.
    /// Must be called before collect_signatures.
    pub(super) fn register_all_type_shells(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Class(c) => {
                    self.register_type_shell(c.name, TypeDefKind::Class, interner);
                }
                Decl::Struct(s) => {
                    self.register_type_shell(s.name, TypeDefKind::Struct, interner);
                }
                Decl::Interface(i) => {
                    self.register_type_shell(i.name, TypeDefKind::Interface, interner);
                }
                Decl::Sentinel(s) => {
                    self.register_type_shell(s.name, TypeDefKind::Sentinel, interner);
                }
                Decl::Let(l) => {
                    // Handle both new syntax (let T = SomeType) and legacy (let T: type = SomeType)
                    let is_type_alias = match &l.init {
                        LetInit::TypeAlias(_) => true,
                        LetInit::Expr(expr) => {
                            matches!(expr.kind, ExprKind::TypeLiteral(_))
                        }
                    };
                    if is_type_alias {
                        self.register_type_shell(l.name, TypeDefKind::Alias, interner);
                    }
                }
                _ => {}
            }
        }
    }

    /// Pass 1: Collect signatures for functions, classes, records, interfaces, and implement blocks
    pub(super) fn collect_signatures(&mut self, program: &Program, interner: &Interner) {
        self.collect_type_signatures(program, interner);
        self.collect_function_signatures(program, interner);
    }

    /// Collect signatures for type declarations: classes, records, interfaces, implement blocks, errors.
    pub(super) fn collect_type_signatures(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    self.collect_class_signature(class, interner);
                }
                Decl::Struct(struct_decl) => {
                    self.collect_struct_signature(struct_decl, interner);
                }
                Decl::Interface(interface_decl) => {
                    self.collect_interface_def(interface_decl, interner);
                }
                Decl::Implement(impl_block) => {
                    self.collect_implement_block(impl_block, interner);
                }
                Decl::Error(decl) => {
                    self.analyze_error_decl(decl, interner);
                }
                Decl::Sentinel(sentinel_decl) => {
                    self.collect_sentinel_signature(sentinel_decl, interner);
                }
                _ => {}
            }
        }
    }

    /// Collect signatures for functions and external blocks.
    pub(super) fn collect_function_signatures(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.collect_function_signature(func, interner);
                }
                Decl::External(ext_block) => {
                    self.collect_external_block(ext_block, interner);
                }
                _ => {}
            }
        }
    }
}
