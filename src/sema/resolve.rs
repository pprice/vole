// src/sema/resolve.rs
//
// Type resolution: converts TypeExpr (AST representation) to Type (semantic representation)

use crate::frontend::{Interner, Symbol, TypeExpr};
use crate::identity::{ModuleId, NameTable, Resolver};
use crate::sema::EntityRegistry;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::{TypeParamScope, substitute_type};
use crate::sema::type_arena::{TypeArena, TypeId, TypeIdVec};
use crate::sema::types::{
    ClassType, FallibleType, FunctionType, InterfaceMethodType, InterfaceType, LegacyType,
    NominalType, RecordType, StructuralFieldType, StructuralMethodType, StructuralType,
};
use std::collections::HashMap;

/// Context needed for type resolution
pub struct TypeResolutionContext<'a> {
    pub entity_registry: &'a EntityRegistry,
    pub interner: &'a Interner,
    pub name_table: &'a mut NameTable,
    pub module_id: ModuleId,
    /// Type parameters in scope (for generic contexts)
    pub type_params: Option<&'a TypeParamScope>,
    /// The concrete type that `Self` resolves to (for method signatures)
    pub self_type: Option<LegacyType>,
}

fn interface_instance(
    name: Symbol,
    type_args: Vec<LegacyType>,
    ctx: &mut TypeResolutionContext<'_>,
) -> Option<LegacyType> {
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
        return Some(LegacyType::invalid("propagate"));
    }

    // Build substitution map using type param NameIds
    let mut substitutions = HashMap::new();
    for (name_id, arg) in type_def.type_params.iter().zip(type_args.iter()) {
        substitutions.insert(*name_id, arg.clone());
    }

    // Build methods with substituted types
    let methods: Vec<InterfaceMethodType> = type_def
        .methods
        .iter()
        .map(|&method_id| {
            let method = ctx.entity_registry.get_method(method_id);
            InterfaceMethodType {
                name: method.name_id,
                params: method
                    .signature
                    .params
                    .iter()
                    .map(|t| substitute_type(t, &substitutions))
                    .collect::<Vec<_>>()
                    .into(),
                return_type: Box::new(substitute_type(
                    &method.signature.return_type,
                    &substitutions,
                )),
                has_default: method.has_default,
            }
        })
        .collect();

    // Keep extends as TypeDefIds directly
    let extends = type_def.extends.to_vec();

    Some(LegacyType::Nominal(NominalType::Interface(InterfaceType {
        type_def_id,
        type_args: type_args.into(),
        methods: methods.into(),
        extends: extends.into(),
    })))
}

impl<'a> TypeResolutionContext<'a> {
    pub fn new(
        entity_registry: &'a EntityRegistry,
        interner: &'a Interner,
        name_table: &'a mut NameTable,
        module_id: ModuleId,
    ) -> Self {
        Self {
            entity_registry,
            interner,
            name_table,
            module_id,
            type_params: None,
            self_type: None,
        }
    }

    /// Create a context with type parameters in scope
    pub fn with_type_params(
        entity_registry: &'a EntityRegistry,
        interner: &'a Interner,
        name_table: &'a mut NameTable,
        module_id: ModuleId,
        type_params: &'a TypeParamScope,
    ) -> Self {
        Self {
            entity_registry,
            interner,
            name_table,
            module_id,
            type_params: Some(type_params),
            self_type: None,
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
pub fn resolve_type(ty: &TypeExpr, ctx: &mut TypeResolutionContext<'_>) -> LegacyType {
    resolve_type_impl(ty, ctx)
}

/// Resolve a TypeExpr to a TypeId using the arena.
///
/// This is the arena-based version of resolve_type. It returns an interned TypeId
/// for O(1) equality and reduced allocations.
///
/// Use this when you have access to a TypeArena; otherwise use resolve_type.
pub fn resolve_type_with_arena(
    ty: &TypeExpr,
    ctx: &mut TypeResolutionContext<'_>,
    arena: &mut TypeArena,
) -> TypeId {
    match ty {
        TypeExpr::Primitive(p) => {
            let prim_type = crate::sema::types::PrimitiveType::from_ast(*p);
            arena.primitive(prim_type)
        }
        TypeExpr::Named(sym) => {
            // Check if it's a type parameter in scope first
            if let Some(type_params) = ctx.type_params
                && let Some(tp_info) = type_params.get(*sym)
            {
                return arena.type_param(tp_info.name_id);
            }
            // For other named types, fall back to Type-based resolution and convert
            let ty = resolve_type_impl(&TypeExpr::Named(*sym), ctx);
            arena.from_type(&ty)
        }
        TypeExpr::Array(elem) => {
            let elem_id = resolve_type_with_arena(elem, ctx, arena);
            arena.array(elem_id)
        }
        TypeExpr::Nil => arena.nil(),
        TypeExpr::Done => arena.done(),
        TypeExpr::Optional(inner) => {
            let inner_id = resolve_type_with_arena(inner, ctx, arena);
            arena.optional(inner_id)
        }
        TypeExpr::Union(variants) => {
            let variant_ids: TypeIdVec = variants
                .iter()
                .map(|t| resolve_type_with_arena(t, ctx, arena))
                .collect();
            arena.union(variant_ids)
        }
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_ids: TypeIdVec = params
                .iter()
                .map(|p| resolve_type_with_arena(p, ctx, arena))
                .collect();
            let ret_id = resolve_type_with_arena(return_type, ctx, arena);
            arena.function(param_ids, ret_id, false)
        }
        TypeExpr::Tuple(elements) => {
            let elem_ids: TypeIdVec = elements
                .iter()
                .map(|e| resolve_type_with_arena(e, ctx, arena))
                .collect();
            arena.tuple(elem_ids)
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_id = resolve_type_with_arena(element, ctx, arena);
            arena.fixed_array(elem_id, *size)
        }
        // For complex cases (Generic, SelfType, Fallible, Structural, Combination),
        // fall back to Type-based resolution and convert
        _ => {
            let ty = resolve_type_impl(ty, ctx);
            arena.from_type(&ty)
        }
    }
}

/// Internal implementation of resolve_type (non-arena version).
fn resolve_type_impl(ty: &TypeExpr, ctx: &mut TypeResolutionContext<'_>) -> LegacyType {
    match ty {
        TypeExpr::Primitive(p) => LegacyType::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Check if it's a type parameter in scope first
            if let Some(type_params) = ctx.type_params
                && let Some(tp_info) = type_params.get(*sym)
            {
                return LegacyType::TypeParam(tp_info.name_id);
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
                            LegacyType::Nominal(NominalType::Record(record))
                        } else {
                            LegacyType::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Class => {
                        if let Some(class) = ctx.entity_registry.build_class_type(type_id) {
                            LegacyType::Nominal(NominalType::Class(class))
                        } else {
                            LegacyType::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Interface => {
                        // Use interface_instance for proper method resolution
                        interface_instance(*sym, Vec::new(), ctx)
                            .unwrap_or_else(|| LegacyType::invalid("unwrap_failed"))
                    }
                    TypeDefKind::ErrorType => {
                        // Get error info from EntityRegistry
                        if let Some(error_info) = type_def.error_info.clone() {
                            LegacyType::Nominal(NominalType::Error(error_info))
                        } else {
                            LegacyType::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Primitive => LegacyType::invalid("resolve_primitive"),
                    TypeDefKind::Alias => {
                        if let Some(ref aliased) = type_def.aliased_type {
                            aliased.clone()
                        } else {
                            LegacyType::invalid("resolve_failed")
                        }
                    }
                }
            } else if let Some(interface) = interface_instance(*sym, Vec::new(), ctx) {
                interface
            } else {
                LegacyType::invalid("unknown_type_name") // Unknown type name
            }
        }
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type(elem, ctx);
            LegacyType::Array(Box::new(elem_ty))
        }
        TypeExpr::Nil => LegacyType::Nil,
        TypeExpr::Done => LegacyType::Done,
        TypeExpr::Optional(inner) => {
            let inner_ty = resolve_type(inner, ctx);
            LegacyType::optional(inner_ty)
        }
        TypeExpr::Union(variants) => {
            let types: Vec<LegacyType> = variants.iter().map(|t| resolve_type(t, ctx)).collect();
            LegacyType::normalize_union(types)
        }
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_types: Vec<LegacyType> = params.iter().map(|p| resolve_type(p, ctx)).collect();
            let ret = resolve_type(return_type, ctx);
            LegacyType::Function(FunctionType {
                params: param_types.into(),
                return_type: Box::new(ret),
                is_closure: false, // Type annotations don't know if it's a closure
            })
        }
        TypeExpr::SelfType => {
            // Self resolves to the implementing type when in a method context
            if let Some(ref self_type) = ctx.self_type {
                self_type.clone()
            } else {
                // Return Error to indicate Self can't be used outside method context
                LegacyType::invalid("resolve_failed")
            }
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success = resolve_type(success_type, ctx);
            let error = resolve_type(error_type, ctx);
            LegacyType::Fallible(FallibleType {
                success_type: Box::new(success),
                error_type: Box::new(error),
            })
        }
        TypeExpr::Generic { name, args } => {
            // Resolve all type arguments
            let resolved_args: Vec<LegacyType> = args.iter().map(|a| resolve_type(a, ctx)).collect();
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
                        return LegacyType::Nominal(NominalType::Class(ClassType {
                            type_def_id: type_id,
                            type_args: resolved_args.into(),
                        }));
                    }
                    TypeDefKind::Record => {
                        return LegacyType::Nominal(NominalType::Record(RecordType {
                            type_def_id: type_id,
                            type_args: resolved_args.into(),
                        }));
                    }
                    TypeDefKind::Interface => {
                        // interface_instance() should have handled this, but as fallback
                        // return invalid - interfaces need full method info
                        return LegacyType::invalid_msg("resolve_generic_interface",
                        format!(
                            "interface '{}' requires interface_instance resolution",
                            name_str
                        ),);
                    }
                    TypeDefKind::Alias => {
                        // Type aliases don't support type parameters
                        return LegacyType::invalid_msg("resolve_generic_alias",
                        format!("type alias '{}' cannot have type arguments", name_str),);
                    }
                    TypeDefKind::ErrorType => {
                        // Error types don't support type parameters
                        return LegacyType::invalid_msg("resolve_generic_error",
                        format!("error type '{}' cannot have type arguments", name_str),);
                    }
                    TypeDefKind::Primitive => {
                        // Primitives don't support type parameters
                        return LegacyType::invalid_msg("resolve_generic_primitive",
                        format!("primitive type '{}' cannot have type arguments", name_str),);
                    }
                }
            }

            // Type not found - return invalid
            LegacyType::invalid_msg("resolve_unknown_generic",
            format!("unknown generic type '{}'", name_str),)
        }
        TypeExpr::Tuple(elements) => {
            let resolved_elements: Vec<LegacyType> =
                elements.iter().map(|e| resolve_type(e, ctx)).collect();
            LegacyType::Tuple(resolved_elements.into())
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_ty = resolve_type(element, ctx);
            LegacyType::FixedArray {
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
            LegacyType::Structural(StructuralType {
                fields: resolved_fields,
                methods: resolved_methods,
            })
        }
        TypeExpr::Combination(_) => {
            // Type combinations are constraint-only, not resolved to a concrete Type
            // Semantic analysis handles these specially in constraint contexts
            LegacyType::invalid("resolve_failed")
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

        static EMPTY_ENTITY_REGISTRY: std::sync::LazyLock<EntityRegistry> =
            std::sync::LazyLock::new(EntityRegistry::new);

        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let mut ctx = TypeResolutionContext::new(
            &EMPTY_ENTITY_REGISTRY,
            interner,
            &mut name_table,
            module_id,
        );
        f(&mut ctx)
    }

    #[test]
    fn resolve_primitive_types() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(FrontendPrimitiveType::I32), ctx),
                LegacyType::Primitive(PrimitiveType::I32)
            );
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(FrontendPrimitiveType::Bool), ctx),
                LegacyType::Primitive(PrimitiveType::Bool)
            );
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(FrontendPrimitiveType::String), ctx),
                LegacyType::Primitive(PrimitiveType::String)
            );
        });
    }

    #[test]
    fn resolve_nil_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            assert_eq!(resolve_type(&TypeExpr::Nil, ctx), LegacyType::Nil);
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
                LegacyType::Array(Box::new(LegacyType::Primitive(PrimitiveType::I64)))
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
            if let LegacyType::Function(ft) = resolved {
                assert_eq!(ft.params.len(), 2);
                assert_eq!(ft.params[0], LegacyType::Primitive(PrimitiveType::I32));
                assert_eq!(ft.params[1], LegacyType::Primitive(PrimitiveType::I32));
                assert_eq!(*ft.return_type, LegacyType::Primitive(PrimitiveType::Bool));
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

        static EMPTY_ENTITY_REGISTRY: std::sync::LazyLock<EntityRegistry> =
            std::sync::LazyLock::new(EntityRegistry::new);
        static TEST_INTERNER: std::sync::LazyLock<Interner> = std::sync::LazyLock::new(|| {
            let mut interner = Interner::new();
            interner.intern("UnknownType"); // Symbol(0) = "UnknownType"
            interner
        });

        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let mut ctx = TypeResolutionContext::new(
            &EMPTY_ENTITY_REGISTRY,
            &TEST_INTERNER,
            &mut name_table,
            module_id,
        );
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
    // Phase 2.2 tests: resolve_type_with_arena
    // ========================================================================

    #[test]
    fn resolve_with_arena_primitives() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let mut arena = TypeArena::new();

            let i32_expr = TypeExpr::Primitive(FrontendPrimitiveType::I32);
            let type_id = resolve_type_with_arena(&i32_expr, ctx, &mut arena);
            let back = arena.to_type(type_id);

            assert_eq!(back, LegacyType::Primitive(PrimitiveType::I32));

            // Interning should work - same expr gives same TypeId
            let type_id2 = resolve_type_with_arena(&i32_expr, ctx, &mut arena);
            assert_eq!(type_id, type_id2);
        });
    }

    #[test]
    fn resolve_with_arena_array() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let mut arena = TypeArena::new();

            let array_expr =
                TypeExpr::Array(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::String)));
            let type_id = resolve_type_with_arena(&array_expr, ctx, &mut arena);
            let back = arena.to_type(type_id);

            assert_eq!(
                back,
                LegacyType::Array(Box::new(LegacyType::Primitive(PrimitiveType::String)))
            );
        });
    }

    #[test]
    fn resolve_with_arena_function() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let mut arena = TypeArena::new();

            let func_expr = TypeExpr::Function {
                params: vec![TypeExpr::Primitive(FrontendPrimitiveType::I32)],
                return_type: Box::new(TypeExpr::Primitive(FrontendPrimitiveType::Bool)),
            };
            let type_id = resolve_type_with_arena(&func_expr, ctx, &mut arena);
            let back = arena.to_type(type_id);

            if let LegacyType::Function(ft) = back {
                assert_eq!(ft.params.len(), 1);
                assert_eq!(ft.params[0], LegacyType::Primitive(PrimitiveType::I32));
                assert_eq!(*ft.return_type, LegacyType::Primitive(PrimitiveType::Bool));
            } else {
                panic!("Expected function type, got {:?}", back);
            }
        });
    }

    #[test]
    fn resolve_with_arena_optional() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let mut arena = TypeArena::new();

            let opt_expr =
                TypeExpr::Optional(Box::new(TypeExpr::Primitive(FrontendPrimitiveType::I32)));
            let type_id = resolve_type_with_arena(&opt_expr, ctx, &mut arena);
            let back = arena.to_type(type_id);

            // Optional is represented as Union([inner, nil])
            if let LegacyType::Union(variants) = back {
                assert_eq!(variants.len(), 2);
                assert!(variants.contains(&LegacyType::Primitive(PrimitiveType::I32)));
                assert!(variants.contains(&LegacyType::Nil));
            } else {
                panic!("Expected union type for optional, got {:?}", back);
            }
        });
    }

    #[test]
    fn resolve_with_arena_matches_resolve_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let mut arena = TypeArena::new();

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
                let type_id = resolve_type_with_arena(&expr, ctx, &mut arena);
                let arena_result = arena.to_type(type_id);
                assert_eq!(legacy, arena_result, "Mismatch for {:?}", expr);
            }
        });
    }
}
