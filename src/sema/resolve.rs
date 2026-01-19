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
use crate::sema::types::{
    ClassType, DisplayType, FallibleType, FunctionType, InterfaceMethodType, InterfaceType,
    NominalType, RecordType, StructuralFieldType, StructuralMethodType, StructuralType,
};

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

fn interface_instance(
    name: Symbol,
    type_args: Vec<DisplayType>,
    ctx: &mut TypeResolutionContext<'_>,
) -> Option<DisplayType> {
    // Look up interface by Symbol -> TypeDefId via resolver with interface fallback
    let name_str = ctx.interner.resolve(name);
    let type_def_id = ctx
        .resolver()
        .resolve_type_str_or_interface(name_str, ctx.entity_registry)?;
    let type_def = ctx.entity_registry.get_type(type_def_id);

    // Verify it's an interface
    if type_def.kind != TypeDefKind::Interface {
        return None;
    }

    if !type_def.type_params.is_empty() && type_def.type_params.len() != type_args.len() {
        return Some(DisplayType::invalid("propagate"));
    }

    // Build methods with substituted types using TypeId-based substitution
    let mut arena = ctx.type_arena.borrow_mut();
    let substitutions: hashbrown::HashMap<_, _> = type_def
        .type_params
        .iter()
        .zip(type_args.iter())
        .map(|(name_id, arg)| (*name_id, arena.from_display(arg)))
        .collect();

    let methods: Vec<InterfaceMethodType> = type_def
        .methods
        .iter()
        .map(|&method_id| {
            let method = ctx.entity_registry.get_method(method_id);
            let sig = &method.signature;

            // Substitute using TypeId
            let substituted_params: TypeIdVec = sig
                .params_id
                .iter()
                .map(|&p| arena.substitute(p, &substitutions))
                .collect();
            let substituted_return = arena.substitute(sig.return_type_id, &substitutions);

            InterfaceMethodType {
                name: method.name_id,
                has_default: method.has_default,
                params_id: substituted_params,
                return_type_id: substituted_return,
            }
        })
        .collect();
    drop(arena);

    // Keep extends as TypeDefIds directly
    let extends = type_def.extends.to_vec();

    // Convert type_args to TypeIds
    let type_args_id: TypeIdVec = {
        let mut arena = ctx.type_arena.borrow_mut();
        type_args.iter().map(|t| arena.from_display(t)).collect()
    };

    Some(DisplayType::Nominal(NominalType::Interface(
        InterfaceType {
            type_def_id,
            type_args_id,
            methods: methods.into(),
            extends: extends.into(),
        },
    )))
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
    resolve_type_impl(ty, ctx)
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
        TypeExpr::Named(sym) => {
            // Check if it's a type parameter in scope first
            if let Some(type_params) = ctx.type_params
                && let Some(tp_info) = type_params.get(*sym)
            {
                return ctx.type_arena.borrow_mut().type_param(tp_info.name_id);
            }
            // Check for type alias - use aliased_type_id directly
            if let Some(type_def_id) = ctx
                .resolver()
                .resolve_type_or_interface(*sym, ctx.entity_registry)
            {
                let type_def = ctx.entity_registry.get_type(type_def_id);
                if type_def.kind == TypeDefKind::Alias
                    && let Some(aliased_type_id) = type_def.aliased_type
                {
                    return aliased_type_id;
                }
            }
            // For other named types, fall back to Type-based resolution and convert
            let ty = resolve_type_impl(&TypeExpr::Named(*sym), ctx);
            ctx.type_arena.borrow_mut().from_display(&ty)
        }
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
        // For complex cases (Generic, SelfType, Fallible, Structural, Combination),
        // fall back to Type-based resolution and convert
        _ => {
            let ty = resolve_type_impl(ty, ctx);
            ctx.type_arena.borrow_mut().from_display(&ty)
        }
    }
}

/// Internal implementation of resolve_type (non-arena version).
fn resolve_type_impl(ty: &TypeExpr, ctx: &mut TypeResolutionContext<'_>) -> DisplayType {
    match ty {
        TypeExpr::Primitive(p) => DisplayType::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Handle "void" as a special case - it's not a registered type but a language primitive
            let name_str = ctx.interner.resolve(*sym);
            if name_str == "void" {
                return DisplayType::Void;
            }

            // Check if it's a type parameter in scope first
            if let Some(type_params) = ctx.type_params
                && let Some(tp_info) = type_params.get(*sym)
            {
                return DisplayType::TypeParam(tp_info.name_id);
            }
            // Look up type via EntityRegistry (handles aliases via TypeDefKind::Alias)
            // Uses resolve_type_or_interface to also find prelude classes like Map/Set
            if let Some(type_id) = ctx
                .resolver()
                .resolve_type_or_interface(*sym, ctx.entity_registry)
            {
                // Look up via EntityRegistry
                let type_def = ctx.entity_registry.get_type(type_id);
                match type_def.kind {
                    TypeDefKind::Record => {
                        if let Some(record) = ctx.entity_registry.build_record_type(type_id) {
                            DisplayType::Nominal(NominalType::Record(record))
                        } else {
                            DisplayType::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Class => {
                        if let Some(class) = ctx.entity_registry.build_class_type(type_id) {
                            DisplayType::Nominal(NominalType::Class(class))
                        } else {
                            DisplayType::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Interface => {
                        // Use interface_instance for proper method resolution
                        interface_instance(*sym, Vec::new(), ctx)
                            .unwrap_or_else(|| DisplayType::invalid("unwrap_failed"))
                    }
                    TypeDefKind::ErrorType => {
                        // Get error info from EntityRegistry
                        if let Some(error_info) = type_def.error_info.clone() {
                            DisplayType::Nominal(NominalType::Error(error_info))
                        } else {
                            DisplayType::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Primitive => DisplayType::invalid("resolve_primitive"),
                    TypeDefKind::Alias => {
                        if let Some(aliased_type_id) = type_def.aliased_type {
                            ctx.type_arena.borrow().to_display(aliased_type_id)
                        } else {
                            DisplayType::invalid("resolve_failed")
                        }
                    }
                }
            } else if let Some(interface) = interface_instance(*sym, Vec::new(), ctx) {
                interface
            } else {
                DisplayType::invalid("unknown_type_name") // Unknown type name
            }
        }
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type(elem, ctx);
            DisplayType::Array(Box::new(elem_ty))
        }
        TypeExpr::Nil => DisplayType::Nil,
        TypeExpr::Done => DisplayType::Done,
        TypeExpr::Optional(inner) => {
            let inner_ty = resolve_type(inner, ctx);
            DisplayType::optional(inner_ty)
        }
        TypeExpr::Union(variants) => {
            let types: Vec<DisplayType> = variants.iter().map(|t| resolve_type(t, ctx)).collect();
            DisplayType::normalize_union(types)
        }
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_types: Vec<DisplayType> =
                params.iter().map(|p| resolve_type(p, ctx)).collect();
            let ret = resolve_type(return_type, ctx);
            // Intern types to get TypeIds
            let mut arena = ctx.type_arena.borrow_mut();
            let params_id: TypeIdVec = param_types.iter().map(|p| arena.from_display(p)).collect();
            let return_type_id = arena.from_display(&ret);
            DisplayType::Function(FunctionType {
                is_closure: false, // Type annotations don't know if it's a closure
                params_id,
                return_type_id,
            })
        }
        TypeExpr::SelfType => {
            // Self resolves to the implementing type when in a method context
            if let Some(self_type_id) = ctx.self_type {
                // Convert TypeId to DisplayType using arena
                ctx.type_arena.borrow().to_display(self_type_id)
            } else {
                // Return Error to indicate Self can't be used outside method context
                DisplayType::invalid("resolve_failed")
            }
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success = resolve_type(success_type, ctx);
            let error = resolve_type(error_type, ctx);
            DisplayType::Fallible(FallibleType {
                success_type: Box::new(success),
                error_type: Box::new(error),
            })
        }
        TypeExpr::Generic { name, args } => {
            // Resolve all type arguments
            let resolved_args: Vec<DisplayType> =
                args.iter().map(|a| resolve_type(a, ctx)).collect();
            if let Some(interface) = interface_instance(*name, resolved_args.clone(), ctx) {
                return interface;
            }

            // Check if this is a class, record, or other type kind
            let name_str = ctx.interner.resolve(*name);
            if let Some(type_id) = ctx
                .resolver()
                .resolve_type_or_interface(*name, ctx.entity_registry)
            {
                let type_def = ctx.entity_registry.get_type(type_id);
                match type_def.kind {
                    TypeDefKind::Class => {
                        // Convert type args to TypeIds for canonical representation
                        let type_args_id: TypeIdVec = resolved_args
                            .iter()
                            .map(|t| ctx.type_arena.borrow_mut().from_display(t))
                            .collect();
                        return DisplayType::Nominal(NominalType::Class(ClassType {
                            type_def_id: type_id,
                            type_args_id,
                        }));
                    }
                    TypeDefKind::Record => {
                        // Convert type args to TypeIds for canonical representation
                        let type_args_id: TypeIdVec = resolved_args
                            .iter()
                            .map(|t| ctx.type_arena.borrow_mut().from_display(t))
                            .collect();
                        return DisplayType::Nominal(NominalType::Record(RecordType {
                            type_def_id: type_id,
                            type_args_id,
                        }));
                    }
                    TypeDefKind::Interface => {
                        // interface_instance() should have handled this, but as fallback
                        // return invalid - interfaces need full method info
                        return DisplayType::invalid_msg(
                            "resolve_generic_interface",
                            format!(
                                "interface '{}' requires interface_instance resolution",
                                name_str
                            ),
                        );
                    }
                    TypeDefKind::Alias => {
                        // Type aliases don't support type parameters
                        return DisplayType::invalid_msg(
                            "resolve_generic_alias",
                            format!("type alias '{}' cannot have type arguments", name_str),
                        );
                    }
                    TypeDefKind::ErrorType => {
                        // Error types don't support type parameters
                        return DisplayType::invalid_msg(
                            "resolve_generic_error",
                            format!("error type '{}' cannot have type arguments", name_str),
                        );
                    }
                    TypeDefKind::Primitive => {
                        // Primitives don't support type parameters
                        return DisplayType::invalid_msg(
                            "resolve_generic_primitive",
                            format!("primitive type '{}' cannot have type arguments", name_str),
                        );
                    }
                }
            }

            // Type not found - return invalid
            DisplayType::invalid_msg(
                "resolve_unknown_generic",
                format!("unknown generic type '{}'", name_str),
            )
        }
        TypeExpr::Tuple(elements) => {
            let resolved_elements: Vec<DisplayType> =
                elements.iter().map(|e| resolve_type(e, ctx)).collect();
            DisplayType::Tuple(resolved_elements.into())
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_ty = resolve_type(element, ctx);
            DisplayType::FixedArray {
                element: Box::new(elem_ty),
                size: *size,
            }
        }
        TypeExpr::Structural { fields, methods } => {
            let resolved_fields = fields
                .iter()
                .map(|f| {
                    let name_id = ctx
                        .name_table
                        .intern(ctx.module_id, &[f.name], ctx.interner);
                    StructuralFieldType {
                        name: name_id,
                        ty: resolve_type(&f.ty, ctx),
                    }
                })
                .collect();
            let resolved_methods = methods
                .iter()
                .map(|m| {
                    let name_id = ctx
                        .name_table
                        .intern(ctx.module_id, &[m.name], ctx.interner);
                    StructuralMethodType {
                        name: name_id,
                        params: m.params.iter().map(|p| resolve_type(p, ctx)).collect(),
                        return_type: resolve_type(&m.return_type, ctx),
                    }
                })
                .collect();
            DisplayType::Structural(StructuralType {
                fields: resolved_fields,
                methods: resolved_methods,
            })
        }
        TypeExpr::Combination(_) => {
            // Type combinations are constraint-only, not resolved to a concrete Type
            // Semantic analysis handles these specially in constraint contexts
            DisplayType::invalid("resolve_failed")
        }
    }
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
