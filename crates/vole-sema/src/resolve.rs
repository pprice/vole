// src/sema/resolve.rs
//
// Type resolution: converts TypeExpr (AST representation) to Type (semantic representation)

use std::cell::RefCell;

use crate::EntityRegistry;
use crate::entity_defs::TypeDefKind;
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
    pub entity_registry: &'a EntityRegistry,
    pub interner: &'a Interner,
    pub name_table: &'a mut NameTable,
    pub module_id: ModuleId,
    /// Type parameters in scope (for generic contexts)
    pub type_params: Option<&'a TypeParamScope>,
    /// The concrete type that `Self` resolves to (for method signatures), as interned TypeId
    pub self_type: Option<TypeId>,
    /// Type arena for interning types (RefCell for interior mutability)
    pub type_arena: &'a RefCell<TypeArena>,
}

impl<'a> TypeResolutionContext<'a> {
    /// Create a context with type parameters and arena in scope
    pub fn with_type_params_and_arena(
        entity_registry: &'a EntityRegistry,
        interner: &'a Interner,
        name_table: &'a mut NameTable,
        module_id: ModuleId,
        type_params: &'a TypeParamScope,
        type_arena: &'a RefCell<TypeArena>,
    ) -> Self {
        Self {
            entity_registry,
            interner,
            name_table,
            module_id,
            type_params: Some(type_params),
            self_type: None,
            type_arena,
        }
    }

    /// Get a resolver for name lookups in the current context.
    /// Uses the resolution chain: primitives -> current module -> builtin module.
    pub fn resolver(&self) -> Resolver<'_> {
        Resolver::new(self.interner, self.name_table, self.module_id, &[])
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
            ctx.type_arena.borrow_mut().primitive(prim_type)
        }
        TypeExpr::Named(sym) => resolve_named_type_to_id(*sym, ctx),
        TypeExpr::Array(elem) => {
            let elem_id = resolve_type_to_id(elem, ctx);
            ctx.type_arena.borrow_mut().array(elem_id)
        }
        TypeExpr::Nil => ctx.type_arena.borrow_mut().nil(),
        TypeExpr::Done => ctx.type_arena.borrow_mut().done(),
        TypeExpr::Optional(inner) => {
            let inner_id = resolve_type_to_id(inner, ctx);
            ctx.type_arena.borrow_mut().optional(inner_id)
        }
        TypeExpr::Union(variants) => {
            let variant_ids: TypeIdVec = variants
                .iter()
                .map(|t| resolve_type_to_id(t, ctx))
                .collect();
            ctx.type_arena.borrow_mut().union(variant_ids)
        }
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_ids: TypeIdVec = params.iter().map(|p| resolve_type_to_id(p, ctx)).collect();
            let ret_id = resolve_type_to_id(return_type, ctx);
            ctx.type_arena
                .borrow_mut()
                .function(param_ids, ret_id, false)
        }
        TypeExpr::Tuple(elements) => {
            let elem_ids: TypeIdVec = elements
                .iter()
                .map(|e| resolve_type_to_id(e, ctx))
                .collect();
            ctx.type_arena.borrow_mut().tuple(elem_ids)
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_id = resolve_type_to_id(element, ctx);
            ctx.type_arena.borrow_mut().fixed_array(elem_id, *size)
        }
        TypeExpr::Generic { name, args } => resolve_generic_type_to_id(*name, args, ctx),
        TypeExpr::SelfType => {
            // Self resolves to the implementing type when in a method context
            ctx.self_type.unwrap_or_else(|| {
                // Self can't be used outside method context - return invalid
                ctx.type_arena.borrow_mut().invalid()
            })
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success_id = resolve_type_to_id(success_type, ctx);
            let error_id = resolve_type_to_id(error_type, ctx);
            ctx.type_arena.borrow_mut().fallible(success_id, error_id)
        }
        TypeExpr::Structural { fields, methods } => {
            resolve_structural_type_to_id(fields, methods, ctx)
        }
        TypeExpr::Combination(_) => {
            // Type combinations are constraint-only, not resolved to a concrete type
            ctx.type_arena.borrow_mut().invalid()
        }
    }
}

/// Resolve a named type (non-generic) to TypeId
fn resolve_named_type_to_id(sym: Symbol, ctx: &mut TypeResolutionContext<'_>) -> TypeId {
    // Handle "void" as a special case
    let name_str = ctx.interner.resolve(sym);
    if name_str == "void" {
        return ctx.type_arena.borrow_mut().void();
    }

    // Check if it's a type parameter in scope first
    if let Some(type_params) = ctx.type_params
        && let Some(tp_info) = type_params.get(sym)
    {
        return ctx.type_arena.borrow_mut().type_param(tp_info.name_id);
    }

    // Look up type via EntityRegistry
    if let Some(type_def_id) = ctx
        .resolver()
        .resolve_type_or_interface(sym, ctx.entity_registry)
    {
        let type_def = ctx.entity_registry.get_type(type_def_id);
        match type_def.kind {
            TypeDefKind::Alias => {
                // Return aliased type directly
                type_def
                    .aliased_type
                    .unwrap_or_else(|| ctx.type_arena.borrow_mut().invalid())
            }
            TypeDefKind::Record => ctx
                .type_arena
                .borrow_mut()
                .record(type_def_id, TypeIdVec::new()),
            TypeDefKind::Class => ctx
                .type_arena
                .borrow_mut()
                .class(type_def_id, TypeIdVec::new()),
            TypeDefKind::Interface => ctx
                .type_arena
                .borrow_mut()
                .interface(type_def_id, TypeIdVec::new()),
            TypeDefKind::ErrorType => ctx.type_arena.borrow_mut().error_type(type_def_id),
            TypeDefKind::Primitive => {
                // Shouldn't reach here - primitives are handled by TypeExpr::Primitive
                ctx.type_arena.borrow_mut().invalid()
            }
        }
    } else {
        // Unknown type name
        ctx.type_arena.borrow_mut().invalid()
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

    // Look up the type
    if let Some(type_def_id) = ctx
        .resolver()
        .resolve_type_or_interface(name, ctx.entity_registry)
    {
        let type_def = ctx.entity_registry.get_type(type_def_id);
        match type_def.kind {
            TypeDefKind::Class => ctx.type_arena.borrow_mut().class(type_def_id, type_args_id),
            TypeDefKind::Record => ctx
                .type_arena
                .borrow_mut()
                .record(type_def_id, type_args_id),
            TypeDefKind::Interface => ctx
                .type_arena
                .borrow_mut()
                .interface(type_def_id, type_args_id),
            TypeDefKind::Alias | TypeDefKind::ErrorType | TypeDefKind::Primitive => {
                // These types don't support type parameters
                ctx.type_arena.borrow_mut().invalid()
            }
        }
    } else {
        // Unknown type name
        ctx.type_arena.borrow_mut().invalid()
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
                .name_table
                .intern(ctx.module_id, &[f.name], ctx.interner);
            let ty_id = resolve_type_to_id(&f.ty, ctx);
            (name_id, ty_id)
        })
        .collect();

    let resolved_methods: SmallVec<[InternedStructuralMethod; 2]> = methods
        .iter()
        .map(|m| {
            let name_id = ctx
                .name_table
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

    ctx.type_arena
        .borrow_mut()
        .structural(resolved_fields, resolved_methods)
}

#[cfg(test)]
mod tests {
    use super::*;
    use vole_frontend::PrimitiveType as FrontendPrimitiveType;
    use vole_identity::NameTable;

    fn with_empty_context<F, R>(interner: &Interner, f: F) -> R
    where
        F: FnOnce(&mut TypeResolutionContext<'_>) -> R,
    {
        use std::cell::RefCell;
        use vole_identity::NameTable;

        static EMPTY_ENTITY_REGISTRY: std::sync::LazyLock<EntityRegistry> =
            std::sync::LazyLock::new(EntityRegistry::new);

        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let arena = RefCell::new(TypeArena::new());
        let mut ctx = TypeResolutionContext {
            entity_registry: &EMPTY_ENTITY_REGISTRY,
            interner,
            name_table: &mut name_table,
            module_id,
            type_params: None,
            self_type: None,
            type_arena: &arena,
        };
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
            let elem = ctx.type_arena.borrow().unwrap_array(type_id);
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
            let inner = ctx.type_arena.borrow().unwrap_optional(type_id);
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
            let arena = ctx.type_arena.borrow();
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

        static EMPTY_ENTITY_REGISTRY: std::sync::LazyLock<EntityRegistry> =
            std::sync::LazyLock::new(EntityRegistry::new);
        static TEST_INTERNER: std::sync::LazyLock<Interner> = std::sync::LazyLock::new(|| {
            let mut interner = Interner::new();
            interner.intern("UnknownType"); // Symbol(0) = "UnknownType"
            interner
        });

        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let arena = RefCell::new(TypeArena::new());
        let mut ctx = TypeResolutionContext {
            entity_registry: &EMPTY_ENTITY_REGISTRY,
            interner: &TEST_INTERNER,
            name_table: &mut name_table,
            module_id,
            type_params: None,
            self_type: None,
            type_arena: &arena,
        };
        let named = TypeExpr::Named(Symbol(0));
        assert!(resolve_type_to_id(&named, &mut ctx).is_invalid());
    }

    #[test]
    fn resolve_self_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            // Self type is only valid in interface/implement context
            assert!(resolve_type_to_id(&TypeExpr::SelfType, ctx).is_invalid());
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
            let arena = ctx.type_arena.borrow();
            if let Some(elements) = arena.unwrap_tuple(type_id) {
                assert_eq!(elements.len(), 2);
                assert_eq!(elements[0], TypeId::I32);
                assert_eq!(elements[1], TypeId::STRING);
            } else {
                panic!("Expected tuple type");
            }
        });
    }
}
