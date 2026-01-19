// src/sema/resolve.rs
//
// Type resolution: converts TypeExpr (AST representation) to Type (semantic representation)

use std::cell::RefCell;

use crate::frontend::{Interner, Symbol, TypeExpr};
use crate::identity::{ModuleId, NameTable, Resolver};
use crate::sema::EntityRegistry;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::TypeParamScope;
use crate::sema::type_arena::{TypeArena, TypeId, TypeIdVec};
use crate::sema::types::DisplayType;

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

/// Resolve a TypeExpr to a Type
///
/// This converts AST type expressions (from parsing) to semantic types (for type checking).
/// It handles primitives, named types (aliases, classes, records, interfaces), arrays,
/// optionals, unions, and function types.
pub fn resolve_type(ty: &TypeExpr, ctx: &mut TypeResolutionContext<'_>) -> DisplayType {
    // Resolve to TypeId first, then project to DisplayType for backwards compatibility
    let type_id = resolve_type_to_id(ty, ctx);
    ctx.type_arena.borrow().to_display(type_id)
}

/// Resolve a TypeExpr directly to a TypeId.
///
/// This is the TypeId-based version of resolve_type. It returns an interned TypeId
/// for O(1) equality and reduced allocations. Uses ctx.type_arena for interning.
pub fn resolve_type_to_id(ty: &TypeExpr, ctx: &mut TypeResolutionContext<'_>) -> TypeId {
    match ty {
        TypeExpr::Primitive(p) => {
            let prim_type = crate::sema::types::PrimitiveType::from_ast(*p);
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
    fields: &[crate::frontend::StructuralField],
    methods: &[crate::frontend::StructuralMethod],
    ctx: &mut TypeResolutionContext<'_>,
) -> TypeId {
    use crate::sema::type_arena::InternedStructuralMethod;
    use smallvec::SmallVec;

    let resolved_fields: SmallVec<[(crate::identity::NameId, TypeId); 4]> = fields
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
    use crate::frontend::PrimitiveType as FrontendPrimitiveType;
    use crate::identity::NameTable;
    use crate::sema::types::PrimitiveType;

    fn with_empty_context<F, R>(interner: &Interner, f: F) -> R
    where
        F: FnOnce(&mut TypeResolutionContext<'_>) -> R,
    {
        use crate::identity::NameTable;
        use std::cell::RefCell;

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
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(FrontendPrimitiveType::I32), ctx),
                DisplayType::Primitive(PrimitiveType::I32)
            );
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(FrontendPrimitiveType::Bool), ctx),
                DisplayType::Primitive(PrimitiveType::Bool)
            );
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(FrontendPrimitiveType::String), ctx),
                DisplayType::Primitive(PrimitiveType::String)
            );
        });
    }

    #[test]
    fn resolve_nil_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            assert_eq!(resolve_type(&TypeExpr::Nil, ctx), DisplayType::Nil);
        });
    }

    #[test]
    fn resolve_array_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let array_expr =
                TypeExpr::Array(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::I64)));
            let resolved = resolve_type(&array_expr, ctx);
            assert_eq!(
                resolved,
                DisplayType::Array(Box::new(DisplayType::Primitive(PrimitiveType::I64)))
            );
        });
    }

    #[test]
    fn resolve_optional_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let opt_expr =
                TypeExpr::Optional(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::I32)));
            let resolved = resolve_type(&opt_expr, ctx);
            assert!(resolved.is_optional());
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
            let resolved = resolve_type(&func_expr, ctx);
            if let DisplayType::Function(ft) = resolved {
                assert_eq!(ft.params_id.len(), 2);
                let arena = ctx.type_arena.borrow();
                assert_eq!(
                    arena.to_display(ft.params_id[0]),
                    DisplayType::Primitive(PrimitiveType::I32)
                );
                assert_eq!(
                    arena.to_display(ft.params_id[1]),
                    DisplayType::Primitive(PrimitiveType::I32)
                );
                assert_eq!(
                    arena.to_display(ft.return_type_id),
                    DisplayType::Primitive(PrimitiveType::Bool)
                );
                assert!(!ft.is_closure);
            } else {
                panic!("Expected function type");
            }
        });
    }

    #[test]
    fn resolve_unknown_named_type() {
        // Create a context with an interner that has the symbol
        use crate::frontend::Interner;
        use std::cell::RefCell;

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
        assert!(resolve_type(&named, &mut ctx).is_invalid());
    }

    #[test]
    fn resolve_self_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            // Self type is only valid in interface/implement context
            assert!(resolve_type(&TypeExpr::SelfType, ctx).is_invalid());
        });
    }

    // ========================================================================
    // Phase 2.2 tests: resolve_type_to_id
    // ========================================================================

    #[test]
    fn resolve_to_id_primitives() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let i32_expr = TypeExpr::Primitive(FrontendPrimitiveType::I32);
            let type_id = resolve_type_to_id(&i32_expr, ctx);
            let back = ctx.type_arena.borrow().to_display(type_id);

            assert_eq!(back, DisplayType::Primitive(PrimitiveType::I32));

            // Interning should work - same expr gives same TypeId
            let type_id2 = resolve_type_to_id(&i32_expr, ctx);
            assert_eq!(type_id, type_id2);
        });
    }

    #[test]
    fn resolve_to_id_array() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let array_expr =
                TypeExpr::Array(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::String)));
            let type_id = resolve_type_to_id(&array_expr, ctx);
            let back = ctx.type_arena.borrow().to_display(type_id);

            assert_eq!(
                back,
                DisplayType::Array(Box::new(DisplayType::Primitive(PrimitiveType::String)))
            );
        });
    }

    #[test]
    fn resolve_to_id_function() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let func_expr = TypeExpr::Function {
                params: vec![TypeExpr::Primitive(FrontendPrimitiveType::I32)],
                return_type: Box::new(TypeExpr::Primitive(FrontendPrimitiveType::Bool)),
            };
            let type_id = resolve_type_to_id(&func_expr, ctx);
            let back = ctx.type_arena.borrow().to_display(type_id);

            if let DisplayType::Function(ft) = back {
                assert_eq!(ft.params_id.len(), 1);
                let arena = ctx.type_arena.borrow();
                assert_eq!(
                    arena.to_display(ft.params_id[0]),
                    DisplayType::Primitive(PrimitiveType::I32)
                );
                assert_eq!(
                    arena.to_display(ft.return_type_id),
                    DisplayType::Primitive(PrimitiveType::Bool)
                );
            } else {
                panic!("Expected function type, got {:?}", back);
            }
        });
    }

    #[test]
    fn resolve_to_id_optional() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let opt_expr =
                TypeExpr::Optional(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::I32)));
            let type_id = resolve_type_to_id(&opt_expr, ctx);
            let back = ctx.type_arena.borrow().to_display(type_id);

            // Optional is represented as Union([inner, nil])
            if let DisplayType::Union(variants) = back {
                assert_eq!(variants.len(), 2);
                assert!(variants.contains(&DisplayType::Primitive(PrimitiveType::I32)));
                assert!(variants.contains(&DisplayType::Nil));
            } else {
                panic!("Expected union type for optional, got {:?}", back);
            }
        });
    }

    #[test]
    fn resolve_to_id_matches_resolve_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            // Test various expressions
            let exprs = vec![
                TypeExpr::Nil,
                TypeExpr::Done,
                TypeExpr::Primitive(FrontendPrimitiveType::F64),
                TypeExpr::Array(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::I32))),
                TypeExpr::Tuple(vec![
                    TypeExpr::Primitive(FrontendPrimitiveType::I32),
                    TypeExpr::Primitive(FrontendPrimitiveType::String),
                ]),
            ];

            for expr in exprs {
                let legacy = resolve_type(&expr, ctx);
                let type_id = resolve_type_to_id(&expr, ctx);
                let arena_result = ctx.type_arena.borrow().to_display(type_id);
                assert_eq!(legacy, arena_result, "Mismatch for {:?}", expr);
            }
        });
    }
}
