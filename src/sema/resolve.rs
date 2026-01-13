// src/sema/resolve.rs
//
// Type resolution: converts TypeExpr (AST representation) to Type (semantic representation)

use crate::frontend::{Interner, Symbol, TypeExpr};
use crate::identity::{ModuleId, NameId, NameTable, Resolver};
use crate::sema::EntityRegistry;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::{TypeParamScope, substitute_type};
use crate::sema::types::{
    ClassType, FallibleType, FunctionType, InterfaceMethodType, InterfaceType, RecordType,
    StructField, StructuralFieldType, StructuralMethodType, StructuralType, Type,
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
    pub self_type: Option<Type>,
}

fn interface_instance(
    name: Symbol,
    type_args: Vec<Type>,
    ctx: &mut TypeResolutionContext<'_>,
) -> Option<Type> {
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
        return Some(Type::invalid("propagate"));
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
                    .collect(),
                return_type: Box::new(substitute_type(
                    &method.signature.return_type,
                    &substitutions,
                )),
                has_default: method.has_default,
            }
        })
        .collect();

    // Build extends from TypeDefIds -> NameIds
    let extends: Vec<NameId> = type_def
        .extends
        .iter()
        .map(|&parent_id| ctx.entity_registry.get_type(parent_id).name_id)
        .collect();

    Some(Type::Interface(InterfaceType {
        name_id: type_def.name_id,
        type_args,
        methods,
        extends,
    }))
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
pub fn resolve_type(ty: &TypeExpr, ctx: &mut TypeResolutionContext<'_>) -> Type {
    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Check if it's a type parameter in scope first
            if let Some(type_params) = ctx.type_params
                && let Some(tp_info) = type_params.get(*sym)
            {
                return Type::TypeParam(tp_info.name_id);
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
                        if let Some(record) = ctx
                            .entity_registry
                            .build_record_type(type_id, ctx.name_table)
                        {
                            Type::Record(record)
                        } else {
                            Type::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Class => {
                        if let Some(class) = ctx
                            .entity_registry
                            .build_class_type(type_id, ctx.name_table)
                        {
                            Type::Class(class)
                        } else {
                            Type::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Interface => {
                        // Use interface_instance for proper method resolution
                        interface_instance(*sym, Vec::new(), ctx)
                            .unwrap_or_else(|| Type::invalid("unwrap_failed"))
                    }
                    TypeDefKind::ErrorType => {
                        // Get error info from EntityRegistry
                        if let Some(error_info) = type_def.error_info.clone() {
                            Type::ErrorType(error_info)
                        } else {
                            Type::invalid("resolve_failed")
                        }
                    }
                    TypeDefKind::Primitive => Type::invalid("resolve_primitive"),
                    TypeDefKind::Alias => {
                        if let Some(ref aliased) = type_def.aliased_type {
                            aliased.clone()
                        } else {
                            Type::invalid("resolve_failed")
                        }
                    }
                }
            } else if let Some(interface) = interface_instance(*sym, Vec::new(), ctx) {
                interface
            } else {
                Type::invalid("unknown_type_name") // Unknown type name
            }
        }
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type(elem, ctx);
            Type::Array(Box::new(elem_ty))
        }
        TypeExpr::Nil => Type::Nil,
        TypeExpr::Done => Type::Done,
        TypeExpr::Optional(inner) => {
            let inner_ty = resolve_type(inner, ctx);
            Type::optional(inner_ty)
        }
        TypeExpr::Union(variants) => {
            let types: Vec<Type> = variants.iter().map(|t| resolve_type(t, ctx)).collect();
            Type::normalize_union(types)
        }
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_types: Vec<Type> = params.iter().map(|p| resolve_type(p, ctx)).collect();
            let ret = resolve_type(return_type, ctx);
            Type::Function(FunctionType {
                params: param_types,
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
                Type::invalid("resolve_failed")
            }
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success = resolve_type(success_type, ctx);
            let error = resolve_type(error_type, ctx);
            Type::Fallible(FallibleType {
                success_type: Box::new(success),
                error_type: Box::new(error),
            })
        }
        TypeExpr::Generic { name, args } => {
            // Resolve all type arguments
            let resolved_args: Vec<Type> = args.iter().map(|a| resolve_type(a, ctx)).collect();
            if let Some(interface) = interface_instance(*name, resolved_args.clone(), ctx) {
                return interface;
            }

            // Check if this is a class or record - use Type::Class/Record with type_args
            if let Some(type_id) = ctx
                .resolver()
                .resolve_type_or_interface(*name, ctx.entity_registry)
            {
                let type_def = ctx.entity_registry.get_type(type_id);
                match type_def.kind {
                    TypeDefKind::Class => {
                        // Build ClassType with the resolved type args
                        // Get fields from the generic info and substitute type params
                        if let Some(ref generic_info) = type_def.generic_info {
                            let inferred: HashMap<NameId, Type> = generic_info
                                .type_params
                                .iter()
                                .zip(resolved_args.iter())
                                .map(|(tp, arg)| (tp.name_id, arg.clone()))
                                .collect();

                            let fields: Vec<StructField> = generic_info
                                .field_names
                                .iter()
                                .zip(generic_info.field_types.iter())
                                .enumerate()
                                .map(|(i, (name, ty))| {
                                    let field_name = ctx.interner.resolve(*name).to_string();
                                    StructField {
                                        name: field_name,
                                        ty: substitute_type(ty, &inferred),
                                        slot: i,
                                    }
                                })
                                .collect();

                            return Type::Class(ClassType {
                                name_id: type_def.name_id,
                                fields,
                                type_args: resolved_args,
                            });
                        } else {
                            // Forward reference: shell exists but generic_info not yet set
                            // Return ClassType with empty fields - will be resolved at use site
                            return Type::Class(ClassType {
                                name_id: type_def.name_id,
                                fields: Vec::new(),
                                type_args: resolved_args,
                            });
                        }
                    }
                    TypeDefKind::Record => {
                        // Build RecordType with the resolved type args
                        if let Some(ref generic_info) = type_def.generic_info {
                            let inferred: HashMap<NameId, Type> = generic_info
                                .type_params
                                .iter()
                                .zip(resolved_args.iter())
                                .map(|(tp, arg)| (tp.name_id, arg.clone()))
                                .collect();

                            let fields: Vec<StructField> = generic_info
                                .field_names
                                .iter()
                                .zip(generic_info.field_types.iter())
                                .enumerate()
                                .map(|(i, (name, ty))| {
                                    let field_name = ctx.interner.resolve(*name).to_string();
                                    StructField {
                                        name: field_name,
                                        ty: substitute_type(ty, &inferred),
                                        slot: i,
                                    }
                                })
                                .collect();

                            return Type::Record(RecordType {
                                name_id: type_def.name_id,
                                fields,
                                type_args: resolved_args,
                            });
                        } else {
                            // Forward reference: shell exists but generic_info not yet set
                            // Return RecordType with empty fields - will be resolved at use site
                            return Type::Record(RecordType {
                                name_id: type_def.name_id,
                                fields: Vec::new(),
                                type_args: resolved_args,
                            });
                        }
                    }
                    _ => {}
                }
            }

            // Fallback: use GenericInstance for non-class/record types
            let name_str = ctx.interner.resolve(*name);
            let name_id = ctx.name_table.intern_raw(ctx.module_id, &[name_str]);
            Type::GenericInstance {
                def: name_id,
                args: resolved_args,
            }
        }
        TypeExpr::Tuple(elements) => {
            let resolved_elements: Vec<Type> =
                elements.iter().map(|e| resolve_type(e, ctx)).collect();
            Type::Tuple(resolved_elements)
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_ty = resolve_type(element, ctx);
            Type::FixedArray {
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
            Type::Structural(StructuralType {
                fields: resolved_fields,
                methods: resolved_methods,
            })
        }
        TypeExpr::Combination(_) => {
            // Type combinations are constraint-only, not resolved to a concrete Type
            // Semantic analysis handles these specially in constraint contexts
            Type::invalid("resolve_failed")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::PrimitiveType;
    use crate::identity::NameTable;

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
                resolve_type(&TypeExpr::Primitive(PrimitiveType::I32), ctx),
                Type::I32
            );
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(PrimitiveType::Bool), ctx),
                Type::Bool
            );
            assert_eq!(
                resolve_type(&TypeExpr::Primitive(PrimitiveType::String), ctx),
                Type::String
            );
        });
    }

    #[test]
    fn resolve_nil_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            assert_eq!(resolve_type(&TypeExpr::Nil, ctx), Type::Nil);
        });
    }

    #[test]
    fn resolve_array_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let array_expr = TypeExpr::Array(Box::new(TypeExpr::Primitive(PrimitiveType::I64)));
            let resolved = resolve_type(&array_expr, ctx);
            assert_eq!(resolved, Type::Array(Box::new(Type::I64)));
        });
    }

    #[test]
    fn resolve_optional_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            let opt_expr = TypeExpr::Optional(Box::new(TypeExpr::Primitive(PrimitiveType::I32)));
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
                    TypeExpr::Primitive(PrimitiveType::I32),
                    TypeExpr::Primitive(PrimitiveType::I32),
                ],
                return_type: Box::new(TypeExpr::Primitive(PrimitiveType::Bool)),
            };
            let resolved = resolve_type(&func_expr, ctx);
            if let Type::Function(ft) = resolved {
                assert_eq!(ft.params.len(), 2);
                assert_eq!(ft.params[0], Type::I32);
                assert_eq!(ft.params[1], Type::I32);
                assert_eq!(*ft.return_type, Type::Bool);
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
}
