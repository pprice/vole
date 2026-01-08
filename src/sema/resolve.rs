// src/sema/resolve.rs
//
// Type resolution: converts TypeExpr (AST representation) to Type (semantic representation)

use crate::frontend::{Interner, Symbol, TypeExpr};
use crate::identity::{ModuleId, NameTable};
use crate::sema::generic::{TypeParamScope, substitute_type};
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
    pub name_table: &'a mut NameTable,
    pub module_id: ModuleId,
    /// Type parameters in scope (for generic contexts)
    pub type_params: Option<&'a TypeParamScope>,
}

fn interface_instance(
    name: Symbol,
    type_args: Vec<Type>,
    ctx: &mut TypeResolutionContext<'_>,
) -> Option<Type> {
    let def = ctx.interface_registry.get(name, ctx.interner)?;
    if !def.type_params.is_empty() && def.type_params.len() != type_args.len() {
        return Some(Type::Error);
    }

    let mut substitutions = HashMap::new();
    for (param, arg) in def.type_params.iter().zip(type_args.iter()) {
        substitutions.insert(*param, arg.clone());
    }

    let methods = def
        .methods
        .iter()
        .map(|method| InterfaceMethodType {
            name: method.name,
            params: method
                .params
                .iter()
                .map(|t| substitute_type(t, &substitutions))
                .collect(),
            return_type: Box::new(substitute_type(&method.return_type, &substitutions)),
            has_default: method.has_default,
        })
        .collect();
    let name_id = ctx.name_table.intern(ctx.module_id, &[name]);
    Some(Type::Interface(InterfaceType {
        name,
        name_id,
        type_args,
        methods,
        extends: def.extends.clone(),
    }))
}

impl<'a> TypeResolutionContext<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        type_aliases: &'a HashMap<Symbol, Type>,
        classes: &'a HashMap<Symbol, ClassType>,
        records: &'a HashMap<Symbol, RecordType>,
        error_types: &'a HashMap<Symbol, ErrorTypeInfo>,
        interface_registry: &'a InterfaceRegistry,
        interner: &'a Interner,
        name_table: &'a mut NameTable,
        module_id: ModuleId,
    ) -> Self {
        Self {
            type_aliases,
            classes,
            records,
            error_types,
            interface_registry,
            interner,
            name_table,
            module_id,
            type_params: None,
        }
    }

    /// Create a context with type parameters in scope
    #[allow(clippy::too_many_arguments)]
    pub fn with_type_params(
        type_aliases: &'a HashMap<Symbol, Type>,
        classes: &'a HashMap<Symbol, ClassType>,
        records: &'a HashMap<Symbol, RecordType>,
        error_types: &'a HashMap<Symbol, ErrorTypeInfo>,
        interface_registry: &'a InterfaceRegistry,
        interner: &'a Interner,
        name_table: &'a mut NameTable,
        module_id: ModuleId,
        type_params: &'a TypeParamScope,
    ) -> Self {
        Self {
            type_aliases,
            classes,
            records,
            error_types,
            interface_registry,
            interner,
            name_table,
            module_id,
            type_params: Some(type_params),
        }
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
            } else if let Some(interface) = interface_instance(*sym, Vec::new(), ctx) {
                interface
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
            if let Some(interface) = interface_instance(*name, resolved_args.clone(), ctx) {
                return interface;
            }
            let name_id = ctx.name_table.intern(ctx.module_id, &[*name]);
            Type::GenericInstance {
                def: name_id,
                args: resolved_args,
            }
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

        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let mut ctx = TypeResolutionContext::new(
            &EMPTY_ALIASES,
            &EMPTY_CLASSES,
            &EMPTY_RECORDS,
            &EMPTY_ERRORS,
            &EMPTY_INTERFACES,
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

        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let mut ctx = TypeResolutionContext::new(
            &EMPTY_ALIASES,
            &EMPTY_CLASSES,
            &EMPTY_RECORDS,
            &EMPTY_ERRORS,
            &EMPTY_INTERFACES,
            &TEST_INTERNER,
            &mut name_table,
            module_id,
        );
        let named = TypeExpr::Named(Symbol(0));
        assert_eq!(resolve_type(&named, &mut ctx), Type::Error);
    }

    #[test]
    fn resolve_self_type() {
        let interner = Interner::new();
        with_empty_context(&interner, |ctx| {
            // Self type is only valid in interface/implement context
            assert_eq!(resolve_type(&TypeExpr::SelfType, ctx), Type::Error);
        });
    }
}
