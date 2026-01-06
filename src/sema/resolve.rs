// src/sema/resolve.rs
//
// Type resolution: converts TypeExpr (AST representation) to Type (semantic representation)

use crate::frontend::{Interner, Symbol, TypeExpr};
use crate::sema::generic::TypeParamScope;
use crate::sema::interface_registry::InterfaceRegistry;
use crate::sema::types::{
    ClassType, ErrorTypeInfo, FallibleType, FunctionType, InterfaceMethodType, InterfaceType,
    RecordType, Type,
};
use std::collections::HashMap;

/// Context needed for type resolution
pub struct TypeResolutionContext<'a> {
    pub type_aliases: &'a HashMap<Symbol, Type>,
    pub classes: &'a HashMap<Symbol, ClassType>,
    pub records: &'a HashMap<Symbol, RecordType>,
    pub error_types: &'a HashMap<Symbol, ErrorTypeInfo>,
    pub interface_registry: &'a InterfaceRegistry,
    pub interner: &'a Interner,
    /// Type parameters in scope (for generic contexts)
    pub type_params: Option<&'a TypeParamScope>,
}

impl<'a> TypeResolutionContext<'a> {
    pub fn new(
        type_aliases: &'a HashMap<Symbol, Type>,
        classes: &'a HashMap<Symbol, ClassType>,
        records: &'a HashMap<Symbol, RecordType>,
        error_types: &'a HashMap<Symbol, ErrorTypeInfo>,
        interface_registry: &'a InterfaceRegistry,
        interner: &'a Interner,
    ) -> Self {
        Self {
            type_aliases,
            classes,
            records,
            error_types,
            interface_registry,
            interner,
            type_params: None,
        }
    }

    /// Create a context with type parameters in scope
    pub fn with_type_params(
        type_aliases: &'a HashMap<Symbol, Type>,
        classes: &'a HashMap<Symbol, ClassType>,
        records: &'a HashMap<Symbol, RecordType>,
        error_types: &'a HashMap<Symbol, ErrorTypeInfo>,
        interface_registry: &'a InterfaceRegistry,
        interner: &'a Interner,
        type_params: &'a TypeParamScope,
    ) -> Self {
        Self {
            type_aliases,
            classes,
            records,
            error_types,
            interface_registry,
            interner,
            type_params: Some(type_params),
        }
    }
}

/// Resolve a TypeExpr to a Type
///
/// This converts AST type expressions (from parsing) to semantic types (for type checking).
/// It handles primitives, named types (aliases, classes, records, interfaces), arrays,
/// optionals, unions, and function types.
pub fn resolve_type(ty: &TypeExpr, ctx: &TypeResolutionContext<'_>) -> Type {
    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Check if it's a type parameter in scope first
            if let Some(type_params) = ctx.type_params
                && type_params.is_type_param(*sym)
            {
                return Type::TypeParam(*sym);
            }
            // Look up type alias first
            if let Some(aliased) = ctx.type_aliases.get(sym) {
                aliased.clone()
            } else if let Some(record) = ctx.records.get(sym) {
                Type::Record(record.clone())
            } else if let Some(class) = ctx.classes.get(sym) {
                Type::Class(class.clone())
            } else if let Some(iface) = ctx.interface_registry.get(*sym, ctx.interner) {
                Type::Interface(InterfaceType {
                    name: *sym,
                    methods: iface
                        .methods
                        .iter()
                        .map(|m| InterfaceMethodType {
                            name: m.name,
                            params: m.params.clone(),
                            return_type: Box::new(m.return_type.clone()),
                            has_default: m.has_default,
                        })
                        .collect(),
                    extends: iface.extends.clone(),
                })
            } else if let Some(error_info) = ctx.error_types.get(sym) {
                // Check if it's an error type
                Type::ErrorType(error_info.clone())
            } else {
                Type::Error // Unknown type name
            }
        }
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type(elem, ctx);
            Type::Array(Box::new(elem_ty))
        }
        TypeExpr::Iterator(elem) => {
            let elem_ty = resolve_type(elem, ctx);
            Type::Iterator(Box::new(elem_ty))
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
            // Self is resolved during interface/implement checking
            // For now, return Error to indicate it can't be used outside that context
            Type::Error
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
            Type::GenericInstance {
                def: *name,
                args: resolved_args,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::PrimitiveType;

    fn empty_context() -> TypeResolutionContext<'static> {
        use crate::frontend::Interner;

        static EMPTY_ALIASES: std::sync::LazyLock<HashMap<Symbol, Type>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_CLASSES: std::sync::LazyLock<HashMap<Symbol, ClassType>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_RECORDS: std::sync::LazyLock<HashMap<Symbol, RecordType>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_ERRORS: std::sync::LazyLock<HashMap<Symbol, ErrorTypeInfo>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_INTERFACES: std::sync::LazyLock<InterfaceRegistry> =
            std::sync::LazyLock::new(InterfaceRegistry::new);
        static EMPTY_INTERNER: std::sync::LazyLock<Interner> =
            std::sync::LazyLock::new(Interner::new);

        TypeResolutionContext::new(
            &EMPTY_ALIASES,
            &EMPTY_CLASSES,
            &EMPTY_RECORDS,
            &EMPTY_ERRORS,
            &EMPTY_INTERFACES,
            &EMPTY_INTERNER,
        )
    }

    #[test]
    fn resolve_primitive_types() {
        let ctx = empty_context();
        assert_eq!(
            resolve_type(&TypeExpr::Primitive(PrimitiveType::I32), &ctx),
            Type::I32
        );
        assert_eq!(
            resolve_type(&TypeExpr::Primitive(PrimitiveType::Bool), &ctx),
            Type::Bool
        );
        assert_eq!(
            resolve_type(&TypeExpr::Primitive(PrimitiveType::String), &ctx),
            Type::String
        );
    }

    #[test]
    fn resolve_nil_type() {
        let ctx = empty_context();
        assert_eq!(resolve_type(&TypeExpr::Nil, &ctx), Type::Nil);
    }

    #[test]
    fn resolve_array_type() {
        let ctx = empty_context();
        let array_expr = TypeExpr::Array(Box::new(TypeExpr::Primitive(PrimitiveType::I64)));
        let resolved = resolve_type(&array_expr, &ctx);
        assert_eq!(resolved, Type::Array(Box::new(Type::I64)));
    }

    #[test]
    fn resolve_optional_type() {
        let ctx = empty_context();
        let opt_expr = TypeExpr::Optional(Box::new(TypeExpr::Primitive(PrimitiveType::I32)));
        let resolved = resolve_type(&opt_expr, &ctx);
        assert!(resolved.is_optional());
    }

    #[test]
    fn resolve_function_type() {
        let ctx = empty_context();
        let func_expr = TypeExpr::Function {
            params: vec![
                TypeExpr::Primitive(PrimitiveType::I32),
                TypeExpr::Primitive(PrimitiveType::I32),
            ],
            return_type: Box::new(TypeExpr::Primitive(PrimitiveType::Bool)),
        };
        let resolved = resolve_type(&func_expr, &ctx);
        if let Type::Function(ft) = resolved {
            assert_eq!(ft.params.len(), 2);
            assert_eq!(ft.params[0], Type::I32);
            assert_eq!(ft.params[1], Type::I32);
            assert_eq!(*ft.return_type, Type::Bool);
            assert!(!ft.is_closure);
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn resolve_unknown_named_type() {
        // Create a context with an interner that has the symbol
        use crate::frontend::Interner;

        static EMPTY_ALIASES: std::sync::LazyLock<HashMap<Symbol, Type>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_CLASSES: std::sync::LazyLock<HashMap<Symbol, ClassType>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_RECORDS: std::sync::LazyLock<HashMap<Symbol, RecordType>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_ERRORS: std::sync::LazyLock<HashMap<Symbol, ErrorTypeInfo>> =
            std::sync::LazyLock::new(HashMap::new);
        static EMPTY_INTERFACES: std::sync::LazyLock<InterfaceRegistry> =
            std::sync::LazyLock::new(InterfaceRegistry::new);
        static TEST_INTERNER: std::sync::LazyLock<Interner> = std::sync::LazyLock::new(|| {
            let mut interner = Interner::new();
            interner.intern("UnknownType"); // Symbol(0) = "UnknownType"
            interner
        });

        let ctx = TypeResolutionContext::new(
            &EMPTY_ALIASES,
            &EMPTY_CLASSES,
            &EMPTY_RECORDS,
            &EMPTY_ERRORS,
            &EMPTY_INTERFACES,
            &TEST_INTERNER,
        );
        // Use Symbol(0) which corresponds to "UnknownType"
        let named = TypeExpr::Named(Symbol(0));
        assert_eq!(resolve_type(&named, &ctx), Type::Error);
    }

    #[test]
    fn resolve_self_type() {
        let ctx = empty_context();
        // Self type is only valid in interface/implement context
        assert_eq!(resolve_type(&TypeExpr::SelfType, &ctx), Type::Error);
    }

    #[test]
    fn resolve_iterator_type() {
        let ctx = empty_context();
        let iter_expr = TypeExpr::Iterator(Box::new(TypeExpr::Primitive(PrimitiveType::I32)));
        let resolved = resolve_type(&iter_expr, &ctx);
        assert_eq!(resolved, Type::Iterator(Box::new(Type::I32)));
    }
}
