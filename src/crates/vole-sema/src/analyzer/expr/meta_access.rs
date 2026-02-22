use super::super::*;
use crate::node_map::MetaAccessKind;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check a `.@meta` access expression and resolve it to `TypeMeta`.
    ///
    /// Two cases:
    /// 1. **Static**: `T.@meta` where T is a type name (struct, class, interface,
    ///    primitive). The reflected type is known at compile time.
    /// 2. **Instance**: `val.@meta` where val is a value expression. If the
    ///    value's type is concrete (class/struct), the access is `Static`;
    ///    if the value is typed as an interface, it is `Dynamic` (resolved at
    ///    runtime via vtable).
    pub(super) fn check_meta_access_expr(
        &mut self,
        expr: &Expr,
        ma: &MetaAccessExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Resolve the TypeMeta struct from the prelude so we can return its TypeId.
        let type_meta_type_id = self.resolve_type_meta_id(interner, expr);
        let Some(type_meta_type_id) = type_meta_type_id else {
            // TypeMeta not found — prelude may not be loaded. Return UNKNOWN
            // and skip annotation (codegen will see UNKNOWN and can handle it).
            return Ok(ArenaTypeId::UNKNOWN);
        };

        // Try to resolve the object as a type name (static meta access).
        if let Some(type_def_id) = self.resolve_meta_access_type_target(&ma.object, interner) {
            self.results
                .node_map
                .set_meta_access(expr.id, MetaAccessKind::Static { type_def_id });
            return Ok(type_meta_type_id);
        }

        // Not a type name — check the object as a value expression.
        let object_type_id = self.check_expr(&ma.object, interner)?;

        if object_type_id.is_invalid() {
            return Ok(ArenaTypeId::INVALID);
        }

        // Determine Static vs Dynamic based on the value's type.
        let meta_kind = self.classify_meta_access(object_type_id);
        self.results.node_map.set_meta_access(expr.id, meta_kind);

        Ok(type_meta_type_id)
    }

    /// Attempt to resolve the object expression as a type name for static
    /// meta access (e.g. `Point.@meta`, `i32.@meta`).
    ///
    /// Returns `Some(TypeDefId)` if the object refers to a type, `None` if
    /// it should be treated as a value expression instead.
    fn resolve_meta_access_type_target(
        &self,
        object: &Expr,
        interner: &Interner,
    ) -> Option<TypeDefId> {
        match &object.kind {
            // Named type: `Point.@meta`, `MyClass.@meta`
            ExprKind::Identifier(sym) => {
                // Only treat as a type if it's not a variable in scope.
                if self.get_variable_type_id(*sym).is_some() {
                    return None;
                }
                self.resolver(interner)
                    .resolve_type_or_interface(*sym, &self.entity_registry())
            }
            // Primitive type keyword: `i32.@meta`, `bool.@meta`
            ExprKind::TypeLiteral(type_expr) => {
                use vole_frontend::ast::TypeExprKind;
                if let TypeExprKind::Primitive(prim) = &type_expr.kind {
                    let name_id = self.name_table().primitives.from_ast(*prim);
                    self.entity_registry().type_by_name(name_id)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Classify a value-expression meta access as Static or Dynamic based
    /// on the value's compile-time type.
    fn classify_meta_access(&self, object_type_id: ArenaTypeId) -> MetaAccessKind {
        let arena = self.type_arena();

        // Interface types are dynamic — the concrete type is only known at runtime.
        if arena.is_interface(object_type_id) {
            return MetaAccessKind::Dynamic;
        }

        // Concrete nominal types (class/struct) are static.
        if let Some((type_def_id, _, _)) = arena.unwrap_nominal(object_type_id) {
            return MetaAccessKind::Static { type_def_id };
        }

        // For everything else (primitives, arrays, functions, etc.) fall back
        // to Dynamic. Codegen can decide how to handle these; sema's job is
        // just to type the expression as TypeMeta.
        MetaAccessKind::Dynamic
    }

    /// Look up the `TypeMeta` struct's TypeId from the prelude.
    ///
    /// TypeMeta is defined in `stdlib/prelude/reflection.vole` as a plain
    /// struct with fields `name`, `fields`, and `construct`.
    fn resolve_type_meta_id(&mut self, interner: &Interner, expr: &Expr) -> Option<ArenaTypeId> {
        // First try the resolver chain (handles direct module-scoped resolution).
        let type_def_id = {
            let resolver = self.resolver(interner);
            resolver.resolve_type_str_or_interface("TypeMeta", &self.entity_registry())
        };
        // Fallback: search all types by short name (TypeMeta is a struct, not
        // a class/interface, so class_by_short_name would miss it).
        let type_def_id = type_def_id.or_else(|| {
            self.entity_registry()
                .type_by_short_name("TypeMeta", &self.name_table())
        });

        if let Some(type_def_id) = type_def_id {
            Some(self.type_arena_mut().struct_type(type_def_id, vec![]))
        } else {
            tracing::warn!(
                line = expr.span.line,
                "TypeMeta struct not found in prelude — @meta will return unknown"
            );
            None
        }
    }
}
