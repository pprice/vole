// src/sema/resolve.rs
//
// Type resolution: converts TypeExpr (AST representation) to Type (semantic representation)

use std::cell::RefCell;

use crate::compilation_db::CompilationDb;
use crate::entity_defs::TypeDefKind;
use crate::entity_registry::EntityRegistry;
use crate::generic::TypeParamScope;
use crate::type_arena::{TypeArena, TypeId, TypeIdVec};
use vole_frontend::{Interner, Symbol, TypeExpr};
use vole_identity::{ModuleId, NameTable, Resolver, TypeDefId};

/// Extension trait for Resolver that adds entity resolution methods.
/// These methods require access to EntityRegistry, so they're defined here in sema
/// rather than in the identity crate.
pub trait ResolverEntityExt {
    /// Resolve a Symbol to a TypeDefId through the resolution chain.
    fn resolve_type(&self, sym: Symbol, registry: &EntityRegistry) -> Option<TypeDefId>;

    /// Resolve a string to a TypeDefId through the resolution chain.
    fn resolve_type_str(&self, name: &str, registry: &EntityRegistry) -> Option<TypeDefId>;

    /// Resolve a type with fallback to interface/class short name search.
    fn resolve_type_or_interface(
        &self,
        sym: Symbol,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId>;

    /// Resolve a type string with fallback to interface/class short name search.
    fn resolve_type_str_or_interface(
        &self,
        name: &str,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId>;
}

impl ResolverEntityExt for Resolver<'_> {
    fn resolve_type(&self, sym: Symbol, registry: &EntityRegistry) -> Option<TypeDefId> {
        self.resolve(sym)
            .and_then(|name_id| registry.type_by_name(name_id))
    }

    fn resolve_type_str(&self, name: &str, registry: &EntityRegistry) -> Option<TypeDefId> {
        self.resolve_str(name)
            .and_then(|name_id| registry.type_by_name(name_id))
    }

    fn resolve_type_or_interface(
        &self,
        sym: Symbol,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId> {
        let name = self.interner().resolve(sym);
        self.resolve_type_str_or_interface(name, registry)
    }

    fn resolve_type_str_or_interface(
        &self,
        name: &str,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId> {
        tracing::trace!(name, "resolve_type_str_or_interface");
        let result = self
            .resolve_str(name)
            .and_then(|name_id| registry.type_by_name(name_id))
            .or_else(|| registry.interface_by_short_name(name, self.table()))
            .or_else(|| registry.class_by_short_name(name, self.table()));
        tracing::trace!(?result, "resolve_type_str_or_interface result");
        result
    }
}

/// Context needed for type resolution
pub struct TypeResolutionContext<'a> {
    /// Shared compilation database
    pub db: &'a RefCell<CompilationDb>,
    pub interner: &'a Interner,
    pub module_id: ModuleId,
    /// Type parameters in scope (for generic contexts)
    pub type_params: Option<&'a TypeParamScope>,
    /// The concrete type that `Self` resolves to (for method signatures), as interned TypeId
    pub self_type: Option<TypeId>,
}

impl<'a> TypeResolutionContext<'a> {
    /// Create a context with type parameters in scope
    pub fn with_type_params(
        db: &'a RefCell<CompilationDb>,
        interner: &'a Interner,
        module_id: ModuleId,
        type_params: &'a TypeParamScope,
    ) -> Self {
        Self {
            db,
            interner,
            module_id,
            type_params: Some(type_params),
            self_type: None,
        }
    }

    /// Create a context without type parameters
    pub fn new(
        db: &'a RefCell<CompilationDb>,
        interner: &'a Interner,
        module_id: ModuleId,
    ) -> Self {
        Self {
            db,
            interner,
            module_id,
            type_params: None,
            self_type: None,
        }
    }

    /// Get the entity registry (read access)
    pub fn entity_registry(&self) -> std::cell::Ref<'_, EntityRegistry> {
        std::cell::Ref::map(self.db.borrow(), |db| &*db.entities)
    }

    /// Get the name table (read access)
    pub fn name_table(&self) -> std::cell::Ref<'_, NameTable> {
        std::cell::Ref::map(self.db.borrow(), |db| &db.names)
    }

    /// Get the name table (write access)
    pub fn name_table_mut(&self) -> std::cell::RefMut<'_, NameTable> {
        std::cell::RefMut::map(self.db.borrow_mut(), |db| &mut db.names)
    }

    /// Get the type arena (read access)
    pub fn type_arena(&self) -> std::cell::Ref<'_, TypeArena> {
        std::cell::Ref::map(self.db.borrow(), |db| &*db.types)
    }

    /// Get the type arena (write access) - uses Rc::make_mut for copy-on-write
    pub fn type_arena_mut(&self) -> std::cell::RefMut<'_, TypeArena> {
        std::cell::RefMut::map(self.db.borrow_mut(), |db| db.types_mut())
    }

    /// Resolve a type or interface by symbol.
    /// This borrows db for the duration of the call.
    pub fn resolve_type_or_interface(&self, sym: Symbol) -> Option<TypeDefId> {
        let db = self.db.borrow();
        let resolver = Resolver::new(self.interner, &db.names, self.module_id, &[]);
        resolver.resolve_type_or_interface(sym, &db.entities)
    }

    /// Resolve a string to a type or interface.
    /// This borrows db for the duration of the call.
    pub fn resolve_type_str_or_interface(&self, name: &str) -> Option<TypeDefId> {
        let db = self.db.borrow();
        let resolver = Resolver::new(self.interner, &db.names, self.module_id, &[]);
        resolver.resolve_type_str_or_interface(name, &db.entities)
    }
}

/// Resolve a TypeExpr directly to a TypeId.
///
/// This is the TypeId-based version of resolve_type. It returns an interned TypeId
/// for O(1) equality and reduced allocations. Uses ctx.type_arena for interning.
pub fn resolve_type_to_id(ty: &TypeExpr, ctx: &mut TypeResolutionContext<'_>) -> TypeId {
    match ty {
        TypeExpr::Primitive(p) => {
            let prim_type = crate::types::PrimitiveType::from_ast(*p);
            ctx.type_arena_mut().primitive(prim_type)
        }
        TypeExpr::Named(sym) => resolve_named_type_to_id(*sym, ctx),
        TypeExpr::Array(elem) => {
            let elem_id = resolve_type_to_id(elem, ctx);
            ctx.type_arena_mut().array(elem_id)
        }
        TypeExpr::Nil => ctx.type_arena_mut().nil(),
        TypeExpr::Done => ctx.type_arena_mut().done(),
        TypeExpr::Optional(inner) => {
            let inner_id = resolve_type_to_id(inner, ctx);
            ctx.type_arena_mut().optional(inner_id)
        }
        TypeExpr::Union(variants) => {
            let variant_ids: TypeIdVec = variants
                .iter()
                .map(|t| resolve_type_to_id(t, ctx))
                .collect();
            ctx.type_arena_mut().union(variant_ids)
        }
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_ids: TypeIdVec = params.iter().map(|p| resolve_type_to_id(p, ctx)).collect();
            let ret_id = resolve_type_to_id(return_type, ctx);
            ctx.type_arena_mut().function(param_ids, ret_id, false)
        }
        TypeExpr::Tuple(elements) => {
            let elem_ids: TypeIdVec = elements
                .iter()
                .map(|e| resolve_type_to_id(e, ctx))
                .collect();
            ctx.type_arena_mut().tuple(elem_ids)
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_id = resolve_type_to_id(element, ctx);
            ctx.type_arena_mut().fixed_array(elem_id, *size)
        }
        TypeExpr::Generic { name, args } => resolve_generic_type_to_id(*name, args, ctx),
        TypeExpr::SelfType => {
            // Self resolves to the implementing type when in a method context
            ctx.self_type.unwrap_or_else(|| {
                // Self in interface signatures - use placeholder for later substitution
                ctx.type_arena_mut()
                    .placeholder(crate::types::PlaceholderKind::SelfType)
            })
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success_id = resolve_type_to_id(success_type, ctx);
            let error_id = resolve_type_to_id(error_type, ctx);
            ctx.type_arena_mut().fallible(success_id, error_id)
        }
        TypeExpr::Structural { fields, methods } => {
            resolve_structural_type_to_id(fields, methods, ctx)
        }
        TypeExpr::Combination(_) => {
            // Type combinations are constraint-only, not resolved to a concrete type
            ctx.type_arena_mut().invalid()
        }
        TypeExpr::QualifiedPath { .. } => {
            // Qualified paths are handled specially in implement block resolution
            // They should not appear in general type positions
            ctx.type_arena_mut().invalid()
        }
    }
}

/// Resolve a named type (non-generic) to TypeId
fn resolve_named_type_to_id(sym: Symbol, ctx: &mut TypeResolutionContext<'_>) -> TypeId {
    // Handle "void" as a special case
    let name_str = ctx.interner.resolve(sym);
    if name_str == "void" {
        return ctx.type_arena_mut().void();
    }

    // Check if it's a type parameter in scope first
    if let Some(type_params) = ctx.type_params
        && let Some(tp_info) = type_params.get(sym)
    {
        return ctx.type_arena_mut().type_param(tp_info.name_id);
    }

    // Look up type via EntityRegistry
    let type_def_id = ctx.resolve_type_or_interface(sym);
    if let Some(type_def_id) = type_def_id {
        // Copy type info to avoid holding borrow during arena operations
        let (kind, aliased_type) = {
            let registry = ctx.entity_registry();
            let type_def = registry.get_type(type_def_id);
            (type_def.kind, type_def.aliased_type)
        };
        match kind {
            TypeDefKind::Alias => {
                // Return aliased type directly
                aliased_type.unwrap_or_else(|| ctx.type_arena_mut().invalid())
            }
            TypeDefKind::Record => ctx.type_arena_mut().record(type_def_id, TypeIdVec::new()),
            TypeDefKind::Class => ctx.type_arena_mut().class(type_def_id, TypeIdVec::new()),
            TypeDefKind::Interface => ctx
                .type_arena_mut()
                .interface(type_def_id, TypeIdVec::new()),
            TypeDefKind::ErrorType => ctx.type_arena_mut().error_type(type_def_id),
            TypeDefKind::Primitive => {
                // Shouldn't reach here - primitives are handled by TypeExpr::Primitive
                ctx.type_arena_mut().invalid()
            }
        }
    } else {
        // Unknown type name
        ctx.type_arena_mut().invalid()
    }
}

/// Resolve a generic type (with type arguments) to TypeId
fn resolve_generic_type_to_id(
    name: Symbol,
    args: &[TypeExpr],
    ctx: &mut TypeResolutionContext<'_>,
) -> TypeId {
    // Resolve all type arguments first
    let type_args_id: TypeIdVec = args.iter().map(|a| resolve_type_to_id(a, ctx)).collect();

    // Look up the type first (borrows db), then get kind (borrows db again)
    let type_def_id = ctx.resolve_type_or_interface(name);
    let lookup_result: Option<(TypeDefId, TypeDefKind)> = type_def_id.map(|id| {
        let kind = ctx.entity_registry().get_type(id).kind;
        (id, kind)
    });

    if let Some((type_def_id, kind)) = lookup_result {
        match kind {
            TypeDefKind::Class => {
                let result = ctx
                    .type_arena_mut()
                    .class(type_def_id, type_args_id.clone());
                // Pre-compute substituted field types so codegen can use lookup_substitute
                precompute_field_substitutions(ctx, type_def_id, &type_args_id);
                result
            }
            TypeDefKind::Record => {
                let result = ctx
                    .type_arena_mut()
                    .record(type_def_id, type_args_id.clone());
                // Pre-compute substituted field types so codegen can use lookup_substitute
                precompute_field_substitutions(ctx, type_def_id, &type_args_id);
                result
            }
            TypeDefKind::Interface => {
                let result = ctx
                    .type_arena_mut()
                    .interface(type_def_id, type_args_id.clone());
                // Pre-compute substituted method signatures so codegen can use lookup_substitute
                precompute_interface_method_substitutions(ctx, type_def_id, &type_args_id);
                result
            }
            TypeDefKind::Alias | TypeDefKind::ErrorType | TypeDefKind::Primitive => {
                // These types don't support type parameters
                ctx.type_arena_mut().invalid()
            }
        }
    } else {
        // Unknown type name
        ctx.type_arena_mut().invalid()
    }
}

/// Pre-compute substituted field types for a generic class/record instantiation.
///
/// When creating a type like Box<String>, this ensures that the substituted field
/// types (e.g., String for a field of type T) exist in the arena. This allows
/// codegen to use lookup_substitute instead of substitute, making it fully read-only.
fn precompute_field_substitutions(
    ctx: &TypeResolutionContext<'_>,
    type_def_id: TypeDefId,
    type_args: &[TypeId],
) {
    // Skip if no type arguments (no substitution needed)
    if type_args.is_empty() {
        return;
    }

    // Get field types and type params from the type definition
    let (field_types, type_params): (Vec<TypeId>, Vec<vole_identity::NameId>) = {
        let registry = ctx.entity_registry();
        let type_def = registry.get_type(type_def_id);
        if let Some(generic_info) = &type_def.generic_info {
            (
                generic_info.field_types.clone(),
                type_def.type_params.clone(),
            )
        } else {
            return;
        }
    };

    // Build substitution map: type param NameId -> concrete TypeId
    let subs: rustc_hash::FxHashMap<vole_identity::NameId, TypeId> = type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect();

    // Pre-compute substituted types for all fields
    // This ensures they exist in the arena for codegen's lookup_substitute
    let mut arena = ctx.type_arena_mut();
    for field_type in field_types {
        arena.substitute(field_type, &subs);
    }
}

/// Pre-compute substituted method signatures for a generic interface instantiation.
///
/// When creating a type like Iterator<i64>, this ensures that the substituted method
/// param/return types (e.g., `i64 | Done` for `T | Done`) exist in the arena. This
/// allows codegen to use lookup_substitute instead of substitute, making it fully read-only.
fn precompute_interface_method_substitutions(
    ctx: &TypeResolutionContext<'_>,
    type_def_id: TypeDefId,
    type_args: &[TypeId],
) {
    // Skip if no type arguments (no substitution needed)
    if type_args.is_empty() {
        return;
    }

    // Get interface type params and method signature IDs upfront
    // to avoid borrow conflicts with the arena
    let (type_params, signature_ids): (Vec<vole_identity::NameId>, Vec<TypeId>) = {
        let registry = ctx.entity_registry();
        let type_def = registry.get_type(type_def_id);
        let type_params = type_def.type_params.clone();
        let method_ids = registry.interface_methods_ordered(type_def_id);
        let signature_ids: Vec<TypeId> = method_ids
            .iter()
            .map(|&mid| registry.get_method(mid).signature_id)
            .collect();
        (type_params, signature_ids)
    };

    // Skip if type params and args don't match (error case handled elsewhere)
    if type_params.len() != type_args.len() {
        return;
    }

    // Build substitution map: type param NameId -> concrete TypeId
    let subs: rustc_hash::FxHashMap<vole_identity::NameId, TypeId> = type_params
        .iter()
        .zip(type_args.iter())
        .map(|(&param, &arg)| (param, arg))
        .collect();

    // Pre-compute substituted types for all method signatures
    // This ensures they exist in the arena for codegen's lookup_substitute
    let mut arena = ctx.type_arena_mut();
    for signature_id in signature_ids {
        // Get method param and return types
        if let Some((params, ret, _)) = arena.unwrap_function(signature_id) {
            // Substitute each param type
            let params = params.to_vec();
            for param in params {
                arena.substitute(param, &subs);
            }
            // Substitute return type
            arena.substitute(ret, &subs);
        }
    }
}

/// Resolve a structural type to TypeId
fn resolve_structural_type_to_id(
    fields: &[vole_frontend::StructuralField],
    methods: &[vole_frontend::StructuralMethod],
    ctx: &mut TypeResolutionContext<'_>,
) -> TypeId {
    use crate::type_arena::InternedStructuralMethod;
    use smallvec::SmallVec;

    let resolved_fields: SmallVec<[(vole_identity::NameId, TypeId); 4]> = fields
        .iter()
        .map(|f| {
            let name_id = ctx
                .name_table_mut()
                .intern(ctx.module_id, &[f.name], ctx.interner);
            let ty_id = resolve_type_to_id(&f.ty, ctx);
            (name_id, ty_id)
        })
        .collect();

    let resolved_methods: SmallVec<[InternedStructuralMethod; 2]> = methods
        .iter()
        .map(|m| {
            let name_id = ctx
                .name_table_mut()
                .intern(ctx.module_id, &[m.name], ctx.interner);
            let params: TypeIdVec = m
                .params
                .iter()
                .map(|p| resolve_type_to_id(p, ctx))
                .collect();
            let return_type = resolve_type_to_id(&m.return_type, ctx);
            InternedStructuralMethod {
                name: name_id,
                params,
                return_type,
            }
        })
        .collect();

    ctx.type_arena_mut()
        .structural(resolved_fields, resolved_methods)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compilation_db::CompilationDb;
    use crate::type_arena::SemaType;
    use vole_frontend::PrimitiveType as FrontendPrimitiveType;

    fn with_empty_context<F, R>(interner: &Interner, f: F) -> R
    where
        F: FnOnce(&mut TypeResolutionContext<'_>) -> R,
    {
        use std::cell::RefCell;

        let db = RefCell::new(CompilationDb::new());
        let module_id = db.borrow_mut().names.main_module();
        let mut ctx = TypeResolutionContext::new(&db, interner, module_id);
        f(&mut ctx)
    }

    #[test]
    fn resolve_primitive_types() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            // Use TypeId constants for comparison
            assert_eq!(
                resolve_type_to_id(&TypeExpr::Primitive(FrontendPrimitiveType::I32), ctx),
                TypeId::I32
            );
            assert_eq!(
                resolve_type_to_id(&TypeExpr::Primitive(FrontendPrimitiveType::Bool), ctx),
                TypeId::BOOL
            );
            assert_eq!(
                resolve_type_to_id(&TypeExpr::Primitive(FrontendPrimitiveType::String), ctx),
                TypeId::STRING
            );
        });
    }

    #[test]
    fn resolve_nil_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            assert_eq!(resolve_type_to_id(&TypeExpr::Nil, ctx), TypeId::NIL);
        });
    }

    #[test]
    fn resolve_array_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let array_expr =
                TypeExpr::Array(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::I64)));
            let type_id = resolve_type_to_id(&array_expr, ctx);
            // Use arena queries to verify structure
            let elem = ctx.type_arena().unwrap_array(type_id);
            assert_eq!(elem, Some(TypeId::I64));
        });
    }

    #[test]
    fn resolve_optional_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let opt_expr =
                TypeExpr::Optional(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::I32)));
            let type_id = resolve_type_to_id(&opt_expr, ctx);
            // Optional should unwrap to inner type
            let inner = ctx.type_arena().unwrap_optional(type_id);
            assert_eq!(inner, Some(TypeId::I32));
        });
    }

    #[test]
    fn resolve_function_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let func_expr = TypeExpr::Function {
                params: vec![
                    TypeExpr::Primitive(FrontendPrimitiveType::I32),
                    TypeExpr::Primitive(FrontendPrimitiveType::I32),
                ],
                return_type: Box::new(TypeExpr::Primitive(FrontendPrimitiveType::Bool)),
            };
            let type_id = resolve_type_to_id(&func_expr, ctx);
            // Use arena queries to verify function structure
            let arena = ctx.type_arena();
            if let Some((params, ret, is_closure)) = arena.unwrap_function(type_id) {
                assert_eq!(params.len(), 2);
                assert_eq!(params[0], TypeId::I32);
                assert_eq!(params[1], TypeId::I32);
                assert_eq!(ret, TypeId::BOOL);
                assert!(!is_closure);
            } else {
                panic!("Expected function type");
            }
        });
    }

    #[test]
    fn resolve_unknown_named_type() {
        // Create a context with an interner that has the symbol
        use std::cell::RefCell;
        use vole_frontend::Interner;

        static TEST_INTERNER: std::sync::LazyLock<Interner> = std::sync::LazyLock::new(|| {
            let mut interner = Interner::new();
            interner.intern("UnknownType"); // Symbol(0) = "UnknownType"
            interner
        });

        let db = RefCell::new(CompilationDb::new());
        let module_id = db.borrow_mut().names.main_module();
        let mut ctx = TypeResolutionContext::new(&db, &TEST_INTERNER, module_id);
        let named = TypeExpr::Named(Symbol(0));
        assert!(resolve_type_to_id(&named, &mut ctx).is_invalid());
    }

    #[test]
    fn resolve_self_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            // Self without context resolves to SelfType placeholder (for interface signatures)
            let self_type_id = resolve_type_to_id(&TypeExpr::SelfType, ctx);
            let arena = ctx.type_arena();
            assert!(
                matches!(
                    arena.get(self_type_id),
                    SemaType::Placeholder(crate::types::PlaceholderKind::SelfType)
                ),
                "Self should resolve to Placeholder(SelfType), got {:?}",
                arena.get(self_type_id)
            );
        });
    }

    // ========================================================================
    // TypeId interning tests
    // ========================================================================

    #[test]
    fn resolve_to_id_interning() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let i32_expr = TypeExpr::Primitive(FrontendPrimitiveType::I32);
            let type_id = resolve_type_to_id(&i32_expr, ctx);

            // Should get the reserved constant
            assert_eq!(type_id, TypeId::I32);

            // Interning should work - same expr gives same TypeId
            let type_id2 = resolve_type_to_id(&i32_expr, ctx);
            assert_eq!(type_id, type_id2);

            // Complex types should also intern
            let array_expr =
                TypeExpr::Array(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::String)));
            let arr_id1 = resolve_type_to_id(&array_expr, ctx);
            let arr_id2 = resolve_type_to_id(&array_expr, ctx);
            assert_eq!(arr_id1, arr_id2);
        });
    }

    #[test]
    fn resolve_to_id_tuple() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let tuple_expr = TypeExpr::Tuple(vec![
                TypeExpr::Primitive(FrontendPrimitiveType::I32),
                TypeExpr::Primitive(FrontendPrimitiveType::String),
            ]);
            let type_id = resolve_type_to_id(&tuple_expr, ctx);

            // Use arena queries to verify tuple structure
            let arena = ctx.type_arena();
            if let Some(elements) = arena.unwrap_tuple(type_id) {
                assert_eq!(elements.len(), 2);
                assert_eq!(elements[0], TypeId::I32);
                assert_eq!(elements[1], TypeId::STRING);
            } else {
                panic!("Expected tuple type");
            }
        });
    }

    // ========================================================================
    // Pre-computation of field substitutions tests
    // ========================================================================

    #[test]
    fn precompute_field_substitutions_creates_types() {
        use crate::entity_defs::{GenericTypeInfo, TypeDefKind};
        use crate::generic::TypeParamInfo;
        use std::cell::RefCell;

        let mut interner = Interner::new();
        let t_sym = interner.intern("T");
        let box_sym = interner.intern("Box");
        let value_sym = interner.intern("value");

        let db = RefCell::new(CompilationDb::new());
        let module_id = db.borrow_mut().names.main_module();

        // Create type param name ID
        let t_name_id = db.borrow_mut().names.intern(module_id, &[t_sym], &interner);
        let box_name_id = db
            .borrow_mut()
            .names
            .intern(module_id, &[box_sym], &interner);
        let value_name_id = db
            .borrow_mut()
            .names
            .intern(module_id, &[value_sym], &interner);

        // Create a type param TypeId (T)
        let t_type_id = db.borrow_mut().types_mut().type_param(t_name_id);

        // Register Box<T> type with a field of type T
        let box_type_def_id = {
            let mut db_mut = db.borrow_mut();
            // First register the type
            let id =
                db_mut
                    .entities_mut()
                    .register_type(box_name_id, TypeDefKind::Class, module_id);
            // Set type params
            db_mut.entities_mut().set_type_params(id, vec![t_name_id]);
            // Set generic info with field of type T
            db_mut.entities_mut().set_generic_info(
                id,
                GenericTypeInfo {
                    type_params: vec![TypeParamInfo {
                        name: t_sym,
                        name_id: t_name_id,
                        constraint: None,
                        type_param_id: None,
                        variance: crate::generic::TypeParamVariance::Invariant,
                    }],
                    field_names: vec![value_name_id],
                    field_types: vec![t_type_id], // Field of type T
                    field_has_default: vec![false],
                },
            );
            id
        };

        // Now resolve Box<String>
        let mut ctx = TypeResolutionContext::new(&db, &interner, module_id);
        let box_string_expr = TypeExpr::Generic {
            name: box_sym,
            args: vec![TypeExpr::Primitive(FrontendPrimitiveType::String)],
        };
        let box_string_id = resolve_type_to_id(&box_string_expr, &mut ctx);

        // Verify Box<String> was created
        let arena = ctx.type_arena();
        assert!(
            arena.unwrap_class(box_string_id).is_some(),
            "Expected class type"
        );

        // The key test: verify that the substituted field type (String) can be looked up
        // using lookup_substitute instead of substitute
        let subs = {
            let registry = ctx.entity_registry();
            registry.substitution_map_id(box_type_def_id, &[TypeId::STRING])
        };

        // lookup_substitute should succeed because precompute_field_substitutions
        // already called substitute for the field type
        let result = arena.lookup_substitute(t_type_id, &subs);
        assert_eq!(
            result,
            Some(TypeId::STRING),
            "Field type substitution should be pre-computed and findable via lookup"
        );
    }
}
