// src/codegen/types.rs
//
// Type-related utilities for code generation.
// This module contains shared type utilities used throughout the codegen module.

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use cranelift_jit::JITModule;
use std::collections::HashMap;

use crate::codegen::FunctionRegistry;
use crate::commands::common::AnalyzedProgram;
use crate::errors::CodegenError;
use crate::frontend::{Interner, LetStmt, NodeId, Symbol, TypeExpr};
use crate::identity::{self, ModuleId, NameId, NameTable, NamerLookup, Resolver, TypeDefId};
use crate::runtime::NativeRegistry;
use crate::runtime::native_registry::NativeType;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::{MonomorphCache, substitute_type};
use crate::sema::types::NominalType;
use crate::sema::{EntityRegistry, FunctionType, PrimitiveType, Type, TypeId, TypeKey};

// Re-export box_interface_value for centralized access to all boxing helpers
pub(crate) use super::interface_vtable::box_interface_value;

/// Compiled value with its type
#[derive(Clone)]
pub struct CompiledValue {
    pub value: Value,
    pub ty: types::Type,
    /// The Vole type of this value (needed to distinguish strings/arrays from regular I64)
    pub vole_type: Type,
}

impl CompiledValue {
    /// Create a void return value (zero i64)
    pub fn void(builder: &mut FunctionBuilder) -> Self {
        let zero = builder.ins().iconst(types::I64, 0);
        Self {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        }
    }

    /// Create a new CompiledValue with a different value but the same types
    pub fn with_value(&self, value: Value) -> Self {
        Self {
            value,
            ty: self.ty,
            vole_type: self.vole_type.clone(),
        }
    }
}

/// Metadata about a class or record type for code generation
#[derive(Debug, Clone)]
pub(crate) struct TypeMetadata {
    /// Unique type ID for runtime
    pub type_id: u32,
    /// Opaque type key from semantic analysis (when available)
    #[allow(dead_code)]
    pub type_key: Option<TypeKey>,
    /// Map from field name to slot index
    pub field_slots: HashMap<String, usize>,
    /// Whether this is a class (true) or record (false)
    #[allow(dead_code)]
    pub is_class: bool,
    /// The Vole type (Class or Record)
    pub vole_type: Type,
    /// Method info: method name -> method info
    pub method_infos: HashMap<NameId, MethodInfo>,
}

/// Metadata for a compiled method (opaque function key + return type)
#[derive(Debug, Clone)]
pub(crate) struct MethodInfo {
    pub func_key: crate::codegen::FunctionKey,
    pub return_type: Type,
}

/// Look up TypeMetadata by NameId (cross-interner safe)
/// Returns the TypeMetadata for a class/record with the given name_id
pub(crate) fn type_metadata_by_name_id<'a>(
    type_metadata: &'a HashMap<Symbol, TypeMetadata>,
    name_id: NameId,
    entity_registry: &EntityRegistry,
) -> Option<&'a TypeMetadata> {
    tracing::trace!(
        ?name_id,
        count = type_metadata.len(),
        "type_metadata_by_name_id lookup"
    );
    let result = type_metadata.values().find(|meta| match &meta.vole_type {
        Type::Nominal(NominalType::Class(c)) => {
            let class_name_id = entity_registry.class_name_id(c);
            tracing::trace!(target_name_id = ?name_id, class_name_id = ?class_name_id, "comparing class name_id");
            class_name_id == name_id
        }
        Type::Nominal(NominalType::Record(r)) => entity_registry.record_name_id(r) == name_id,
        _ => false,
    });
    if result.is_none() {
        // Log all class name_ids for debugging
        let class_name_ids: Vec<_> = type_metadata
            .values()
            .filter_map(|meta| {
                if let Type::Nominal(NominalType::Class(c)) = &meta.vole_type {
                    Some(entity_registry.class_name_id(c))
                } else {
                    None
                }
            })
            .collect();
        tracing::debug!(
            ?name_id,
            ?class_name_ids,
            "type_metadata_by_name_id: no match found"
        );
    }
    result
}

/// Context for compiling expressions and statements
/// Bundles common parameters to reduce function argument count
pub(crate) struct CompileCtx<'a> {
    /// Analyzed program containing expr_types, method_resolutions, etc.
    pub analyzed: &'a AnalyzedProgram,
    /// Interner for symbol resolution (may differ from analyzed.interner for module code)
    pub interner: &'a Interner,
    pub pointer_type: types::Type,
    pub module: &'a mut JITModule,
    pub func_registry: &'a mut FunctionRegistry,
    pub source_file_ptr: (*const u8, usize),
    /// Global variable declarations for lookup when identifier not in local scope
    pub globals: &'a [LetStmt],
    /// Counter for generating unique lambda names
    pub lambda_counter: &'a mut usize,
    /// Class and record metadata for struct literals, field access, and method calls
    pub type_metadata: &'a HashMap<Symbol, TypeMetadata>,
    /// Implement block method info for primitive and named types
    pub impl_method_infos: &'a HashMap<(TypeId, NameId), MethodInfo>,
    /// Static method info keyed by (TypeDefId, method_name)
    pub static_method_infos: &'a HashMap<(TypeDefId, NameId), MethodInfo>,
    /// Interface vtable registry (interface + concrete type -> data id)
    pub interface_vtables:
        &'a std::cell::RefCell<crate::codegen::interface_vtable::InterfaceVtableRegistry>,
    /// Current function's return type (needed for raise statements in fallible functions)
    pub current_function_return_type: Option<Type>,
    /// Registry of native functions for external method calls
    pub native_registry: &'a NativeRegistry,
    /// Current module path when compiling module code (e.g., "std:math")
    /// None when compiling main program code
    pub current_module: Option<&'a str>,
    /// Cache of monomorphized function instances
    pub monomorph_cache: &'a MonomorphCache,
    /// Type substitutions for monomorphized class method compilation
    /// Maps type param NameId -> concrete Type
    pub type_substitutions: Option<&'a HashMap<NameId, Type>>,
}

impl<'a> CompileCtx<'a> {
    /// Substitute type parameters with concrete types using current context.
    /// If no type_substitutions are set, returns the original type unchanged.
    pub fn substitute_type(&self, ty: &Type) -> Type {
        if let Some(substitutions) = self.type_substitutions {
            ty.substitute(substitutions)
        } else {
            ty.clone()
        }
    }

    /// Get a Resolver for name lookups in codegen
    pub fn resolver(&self) -> Resolver<'_> {
        let module_id = self
            .current_module
            .and_then(|path| self.analyzed.name_table.module_id_if_known(path))
            .unwrap_or_else(|| self.analyzed.name_table.main_module());
        Resolver::new(
            self.interner,
            &self.analyzed.name_table,
            module_id,
            &[], // No imports in codegen context
        )
    }

    /// Look up expression type, checking module-specific expr_types if compiling module code
    pub fn get_expr_type(&self, node_id: &NodeId) -> Option<&Type> {
        // When compiling module code, NodeIds are relative to that module's program
        // Use module-specific expr_types if available
        if let Some(module_path) = self.current_module
            && let Some(module_types) = self.analyzed.query().expr_data().module_types(module_path)
            && let Some(ty) = module_types.get(node_id)
        {
            return Some(ty);
        }
        // Fall back to main program expr_types via query interface
        self.analyzed.query().type_of(*node_id)
    }
}

/// Resolve a type expression to a Vole Type (uses CompileCtx for full context)
pub(crate) fn resolve_type_expr(ty: &TypeExpr, ctx: &CompileCtx) -> Type {
    let module_id = ctx
        .current_module
        .and_then(|path| ctx.analyzed.name_table.module_id_if_known(path))
        .unwrap_or_else(|| ctx.analyzed.name_table.main_module());
    let resolved = resolve_type_expr_with_metadata(
        ty,
        &ctx.analyzed.entity_registry,
        ctx.type_metadata,
        ctx.interner,
        &ctx.analyzed.name_table,
        module_id,
    );
    // Apply type substitutions if compiling a monomorphized context
    // This allows lambda params like (a: T, b: T) to use concrete types
    if let Some(substitutions) = ctx.type_substitutions {
        // First handle Placeholder::TypeParam which has a string name
        // We need to find the matching NameId in substitutions
        if let Type::Placeholder(crate::sema::types::PlaceholderKind::TypeParam(ref name)) =
            resolved
        {
            // Look for a substitution with matching name
            for (name_id, concrete_type) in substitutions {
                if let Some(name_str) = ctx.analyzed.name_table.last_segment_str(*name_id)
                    && &name_str == name
                {
                    return concrete_type.clone();
                }
            }
        }
        // Then apply normal TypeParam substitution
        substitute_type(&resolved, substitutions)
    } else {
        resolved
    }
}

pub(crate) fn module_name_id(
    analyzed: &AnalyzedProgram,
    module_id: ModuleId,
    name: &str,
) -> Option<NameId> {
    let query = analyzed.query();
    let module_path = query.module_path(module_id);
    let (_, module_interner) = query.module_program(module_path)?;
    let sym = module_interner.lookup(name)?;
    analyzed
        .name_table
        .name_id(module_id, &[sym], module_interner)
}

/// Look up a method NameId by Symbol with explicit interner (for cross-interner usage)
pub(crate) fn method_name_id_with_interner(
    analyzed: &AnalyzedProgram,
    interner: &Interner,
    name: Symbol,
) -> Option<NameId> {
    let namer = NamerLookup::new(&analyzed.name_table, interner);
    namer.method(name)
}

/// Look up a method NameId by string name (cross-interner safe)
pub(crate) fn method_name_id_by_str(
    analyzed: &AnalyzedProgram,
    interner: &Interner,
    name_str: &str,
) -> Option<NameId> {
    identity::method_name_id_by_str(&analyzed.name_table, interner, name_str)
}

/// Look up a function NameId by Symbol with explicit interner (for cross-interner usage)
pub(crate) fn function_name_id_with_interner(
    analyzed: &AnalyzedProgram,
    interner: &Interner,
    module: ModuleId,
    name: Symbol,
) -> Option<NameId> {
    let namer = NamerLookup::new(&analyzed.name_table, interner);
    namer.function(module, name)
}

#[allow(clippy::only_used_in_recursion)]
pub(crate) fn display_type(analyzed: &AnalyzedProgram, interner: &Interner, ty: &Type) -> String {
    match ty {
        Type::Nominal(NominalType::Class(class_type)) => {
            let name_id = analyzed.entity_registry.class_name_id(class_type);
            let base = analyzed.name_table.display(name_id);
            if class_type.type_args.is_empty() {
                base
            } else {
                let arg_list = class_type
                    .type_args
                    .iter()
                    .map(|arg| display_type(analyzed, interner, arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{}>", base, arg_list)
            }
        }
        Type::Nominal(NominalType::Record(record_type)) => {
            let name_id = analyzed.entity_registry.record_name_id(record_type);
            let base = analyzed.name_table.display(name_id);
            if record_type.type_args.is_empty() {
                base
            } else {
                let arg_list = record_type
                    .type_args
                    .iter()
                    .map(|arg| display_type(analyzed, interner, arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{}>", base, arg_list)
            }
        }
        Type::Nominal(NominalType::Interface(interface_type)) => {
            let name_id = analyzed.entity_registry.name_id(interface_type.type_def_id);
            let base = analyzed.name_table.display(name_id);
            if interface_type.type_args.is_empty() {
                base
            } else {
                let arg_list = interface_type
                    .type_args
                    .iter()
                    .map(|arg| display_type(analyzed, interner, arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{}>", base, arg_list)
            }
        }
        Type::Nominal(NominalType::Error(error_type)) => {
            let name_id = analyzed.entity_registry.name_id(error_type.type_def_id);
            analyzed.name_table.display(name_id)
        }
        Type::Module(module_type) => format!(
            "module(\"{}\")",
            analyzed.name_table.module_path(module_type.module_id)
        ),
        Type::Tuple(elements) => {
            let elem_list = elements
                .iter()
                .map(|elem| display_type(analyzed, interner, elem))
                .collect::<Vec<_>>()
                .join(", ");
            format!("[{}]", elem_list)
        }
        Type::FixedArray { element, size } => {
            format!("[{}; {}]", display_type(analyzed, interner, element), size)
        }
        _ => ty.name().to_string(),
    }
}

/// Build an InterfaceType from EntityRegistry's TypeDef
fn build_interface_type_from_entity(
    type_def_id: TypeDefId,
    entity_registry: &EntityRegistry,
    type_args: Vec<Type>,
) -> Type {
    let type_def = entity_registry.get_type(type_def_id);

    // Build methods from MethodDef
    let methods: Vec<crate::sema::types::InterfaceMethodType> = type_def
        .methods
        .iter()
        .map(|&method_id| {
            let method = entity_registry.get_method(method_id);
            crate::sema::types::InterfaceMethodType {
                name: method.name_id,
                params: method.signature.params.clone(),
                return_type: Box::new((*method.signature.return_type).clone()),
                has_default: method.has_default,
            }
        })
        .collect();

    // Keep extends as TypeDefIds directly
    let extends = type_def.extends.clone();

    Type::Nominal(NominalType::Interface(crate::sema::types::InterfaceType {
        type_def_id,
        type_args: type_args.into(),
        methods: methods.into(),
        extends: extends.into(),
    }))
}

/// Resolve a type expression using entity registry, error types, and type metadata
/// This is the full resolution function that handles all named types including classes/records
#[allow(clippy::too_many_arguments)]
pub(crate) fn resolve_type_expr_with_metadata(
    ty: &TypeExpr,
    entity_registry: &EntityRegistry,
    type_metadata: &HashMap<Symbol, TypeMetadata>,
    interner: &Interner,
    name_table: &NameTable,
    module_id: ModuleId,
) -> Type {
    // Create resolver for name lookups
    let resolver = Resolver::new(interner, name_table, module_id, &[]);

    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Check entity registry for type definition (aliases, interfaces, etc.)
            let type_def_id = resolver.resolve_type_or_interface(*sym, entity_registry);

            if let Some(type_def_id) = type_def_id {
                let type_def = entity_registry.get_type(type_def_id);
                match type_def.kind {
                    TypeDefKind::Alias => {
                        // Type alias - return the aliased type
                        if let Some(ref aliased) = type_def.aliased_type {
                            return aliased.clone();
                        }
                        panic!(
                            "INTERNAL ERROR: type alias has no aliased_type\n\
                             type_def_id: {:?}, name_id: {:?}",
                            type_def_id, type_def.name_id
                        )
                    }
                    TypeDefKind::Interface => {
                        // Generic interface without type args is an error
                        if !type_def.type_params.is_empty() {
                            panic!(
                                "INTERNAL ERROR: generic interface used without type args\n\
                                 type_def_id: {:?}, name_id: {:?}, type_params: {:?}",
                                type_def_id, type_def.name_id, type_def.type_params
                            );
                        }
                        build_interface_type_from_entity(type_def_id, entity_registry, Vec::new())
                    }
                    TypeDefKind::ErrorType => {
                        // Error type - get info from EntityRegistry
                        if let Some(error_info) = type_def.error_info.clone() {
                            Type::Nominal(NominalType::Error(error_info))
                        } else {
                            panic!(
                                "INTERNAL ERROR: error type has no error_info\n\
                                 type_def_id: {:?}, name_id: {:?}",
                                type_def_id, type_def.name_id
                            )
                        }
                    }
                    TypeDefKind::Record | TypeDefKind::Class => {
                        // For Record and Class types, first try direct lookup by Symbol
                        // This works when Symbol is from the main interner
                        // IMPORTANT: Verify the type matches by type_def_id to avoid Symbol collisions
                        // between different interners (module vs main)
                        if let Some(metadata) = type_metadata.get(sym) {
                            // Verify this is the right type by comparing type_def_ids
                            let matches = match &metadata.vole_type {
                                Type::Nominal(NominalType::Record(r)) => {
                                    r.type_def_id == type_def_id
                                }
                                Type::Nominal(NominalType::Class(c)) => {
                                    c.type_def_id == type_def_id
                                }
                                _ => false,
                            };
                            if matches {
                                return metadata.vole_type.clone();
                            }
                            // Symbol collision - fall through to build from entity registry
                        }
                        // Build from entity registry - handles module code where
                        // Symbols are from module interners
                        if type_def.kind == TypeDefKind::Record {
                            if let Some(record_type) =
                                entity_registry.build_record_type(type_def_id)
                            {
                                return Type::Nominal(NominalType::Record(record_type));
                            }
                        } else if let Some(class_type) =
                            entity_registry.build_class_type(type_def_id)
                        {
                            return Type::Nominal(NominalType::Class(class_type));
                        }
                        panic!(
                            "INTERNAL ERROR: failed to build record/class type\n\
                             type_def_id: {:?}, kind: {:?}, name_id: {:?}",
                            type_def_id, type_def.kind, type_def.name_id
                        )
                    }
                    _ => {
                        // Primitive or unknown - check type metadata
                        if let Some(metadata) = type_metadata.get(sym) {
                            metadata.vole_type.clone()
                        } else {
                            panic!(
                                "INTERNAL ERROR: unknown type kind with no metadata\n\
                                 type_def_id: {:?}, kind: {:?}, sym: {:?}",
                                type_def_id, type_def.kind, sym
                            )
                        }
                    }
                }
            } else if let Some(metadata) = type_metadata.get(sym) {
                metadata.vole_type.clone()
            } else {
                // This is a type parameter (e.g., T in Box<T>).
                // Type parameters are resolved when the generic is instantiated.
                // Use Placeholder with the param name for debugging clarity.
                let name = interner.resolve(*sym);
                tracing::trace!(name, "type parameter in codegen, using Placeholder");
                Type::type_param_placeholder(name)
            }
        }
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type_expr_with_metadata(
                elem,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            Type::Array(Box::new(elem_ty))
        }
        TypeExpr::Optional(inner) => {
            // T? desugars to T | nil
            let inner_ty = resolve_type_expr_with_metadata(
                inner,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            Type::Union(vec![inner_ty, Type::Nil].into())
        }
        TypeExpr::Union(variants) => {
            let variant_types: Vec<Type> = variants
                .iter()
                .map(|v| {
                    resolve_type_expr_with_metadata(
                        v,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                    )
                })
                .collect();
            Type::normalize_union(variant_types)
        }
        TypeExpr::Nil => Type::Nil,
        TypeExpr::Done => Type::Done,
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_types: Vec<Type> = params
                .iter()
                .map(|p| {
                    resolve_type_expr_with_metadata(
                        p,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                    )
                })
                .collect();
            let ret_type = resolve_type_expr_with_metadata(
                return_type,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            Type::Function(FunctionType {
                params: param_types.into(),
                return_type: Box::new(ret_type),
                is_closure: false, // Type expressions don't know if closure
            })
        }
        TypeExpr::SelfType => {
            // Self type in interface signatures is resolved when the interface is implemented.
            // For interface method signature compilation, we use a Self placeholder.
            // The actual Self type is substituted when compiling implement blocks.
            Type::self_placeholder()
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success = resolve_type_expr_with_metadata(
                success_type,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            let error = resolve_type_expr_with_metadata(
                error_type,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            Type::Fallible(crate::sema::types::FallibleType {
                success_type: Box::new(success),
                error_type: Box::new(error),
            })
        }
        TypeExpr::Generic { name, args } => {
            // Resolve all type arguments
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| {
                    resolve_type_expr_with_metadata(
                        a,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                    )
                })
                .collect();
            // Check entity registry for generic interface via Resolver
            let type_def_id = resolver.resolve_type_or_interface(*name, entity_registry);

            let name_str = interner.resolve(*name);
            if let Some(type_def_id) = type_def_id {
                let type_def = entity_registry.get_type(type_def_id);
                match type_def.kind {
                    TypeDefKind::Class => {
                        return Type::Nominal(NominalType::Class(crate::sema::types::ClassType {
                            type_def_id,
                            type_args: resolved_args.into(),
                        }));
                    }
                    TypeDefKind::Record => {
                        return Type::Nominal(NominalType::Record(
                            crate::sema::types::RecordType {
                                type_def_id,
                                type_args: resolved_args.into(),
                            },
                        ));
                    }
                    TypeDefKind::Interface => {
                        if !type_def.type_params.is_empty()
                            && type_def.type_params.len() != resolved_args.len()
                        {
                            panic!(
                                "INTERNAL ERROR: generic interface type arg count mismatch\n\
                                 expected {} type args, got {}\n\
                                 type_def_id: {:?}, name_id: {:?}",
                                type_def.type_params.len(),
                                resolved_args.len(),
                                type_def_id,
                                type_def.name_id
                            );
                        }
                        // Build substitution map using type param NameIds
                        let mut substitutions = HashMap::new();
                        for (name_id, arg) in type_def.type_params.iter().zip(resolved_args.iter())
                        {
                            substitutions.insert(*name_id, arg.clone());
                        }

                        // Build methods with substituted types
                        let methods: Vec<crate::sema::types::InterfaceMethodType> = type_def
                            .methods
                            .iter()
                            .map(|&method_id| {
                                let method = entity_registry.get_method(method_id);
                                crate::sema::types::InterfaceMethodType {
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
                        let extends = type_def.extends.clone();

                        return Type::Nominal(NominalType::Interface(
                            crate::sema::types::InterfaceType {
                                type_def_id,
                                type_args: resolved_args.into(),
                                methods: methods.into(),
                                extends: extends.into(),
                            },
                        ));
                    }
                    TypeDefKind::Alias | TypeDefKind::ErrorType | TypeDefKind::Primitive => {
                        panic!(
                            "INTERNAL ERROR: type '{}' cannot have type arguments\n\
                             kind: {:?}, type_def_id: {:?}",
                            name_str, type_def.kind, type_def_id
                        );
                    }
                }
            }
            panic!(
                "INTERNAL ERROR: unknown generic type '{}'\n\
                 module_id: {:?}",
                name_str, module_id
            )
        }
        TypeExpr::Tuple(elements) => {
            let resolved_elements: Vec<Type> = elements
                .iter()
                .map(|e| {
                    resolve_type_expr_with_metadata(
                        e,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                    )
                })
                .collect();
            Type::Tuple(resolved_elements.into())
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_ty = resolve_type_expr_with_metadata(
                element,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            Type::FixedArray {
                element: Box::new(elem_ty),
                size: *size,
            }
        }
        TypeExpr::Structural { .. } => {
            // Structural types are constraint-only, not concrete types for codegen
            Type::Void
        }
        TypeExpr::Combination(_) => {
            // Type combinations are constraint-only, not concrete types for codegen
            Type::Void
        }
    }
}

/// Convert a Vole type to a Cranelift type
pub(crate) fn type_to_cranelift(ty: &Type, pointer_type: types::Type) -> types::Type {
    match ty {
        Type::Primitive(PrimitiveType::I8) | Type::Primitive(PrimitiveType::U8) => types::I8,
        Type::Primitive(PrimitiveType::I16) | Type::Primitive(PrimitiveType::U16) => types::I16,
        Type::Primitive(PrimitiveType::I32) | Type::Primitive(PrimitiveType::U32) => types::I32,
        Type::Primitive(PrimitiveType::I64) | Type::Primitive(PrimitiveType::U64) => types::I64,
        Type::Primitive(PrimitiveType::I128) => types::I128,
        Type::Primitive(PrimitiveType::F32) => types::F32,
        Type::Primitive(PrimitiveType::F64) => types::F64,
        Type::Primitive(PrimitiveType::Bool) => types::I8,
        Type::Primitive(PrimitiveType::String) => pointer_type,
        Type::Nominal(NominalType::Interface(_)) => pointer_type,
        Type::Nil => types::I8,            // Nil uses minimal representation
        Type::Done => types::I8,           // Done uses minimal representation (like Nil)
        Type::Union(_) => pointer_type,    // Unions are passed by pointer
        Type::Fallible(_) => pointer_type, // Fallibles are passed by pointer (tagged union)
        Type::Function(_) => pointer_type, // Function pointers
        Type::Range => pointer_type,       // Ranges are passed by pointer (start, end)
        Type::Tuple(_) => pointer_type,    // Tuples are passed by pointer
        Type::FixedArray { .. } => pointer_type, // Fixed arrays are passed by pointer
        _ => types::I64,                   // Default
    }
}

/// Get the size in bytes for a Vole type (used for union layout)
pub(crate) fn type_size(ty: &Type, pointer_type: types::Type) -> u32 {
    match ty {
        Type::Primitive(PrimitiveType::I8)
        | Type::Primitive(PrimitiveType::U8)
        | Type::Primitive(PrimitiveType::Bool) => 1,
        Type::Primitive(PrimitiveType::I16) | Type::Primitive(PrimitiveType::U16) => 2,
        Type::Primitive(PrimitiveType::I32)
        | Type::Primitive(PrimitiveType::U32)
        | Type::Primitive(PrimitiveType::F32) => 4,
        Type::Primitive(PrimitiveType::I64)
        | Type::Primitive(PrimitiveType::U64)
        | Type::Primitive(PrimitiveType::F64) => 8,
        Type::Primitive(PrimitiveType::I128) => 16,
        Type::Primitive(PrimitiveType::String) | Type::Array(_) => pointer_type.bytes(), // pointer size
        Type::Nominal(NominalType::Interface(_)) => pointer_type.bytes(),
        Type::Nil | Type::Done | Type::Void => 0,
        Type::Range => 16, // start (i64) + end (i64)
        Type::Union(variants) => {
            // Tag (1 byte) + padding + max payload size, aligned to 8
            let max_payload = variants
                .iter()
                .map(|t| type_size(t, pointer_type))
                .max()
                .unwrap_or(0);
            // Layout: [tag:1][padding:7][payload:max_payload] aligned to 8
            8 + max_payload.div_ceil(8) * 8
        }
        Type::Nominal(NominalType::Error(info)) => {
            // Error types are struct-like: sum of all field sizes, aligned to 8
            let fields_size: u32 = info
                .fields
                .iter()
                .map(|f| type_size(&f.ty, pointer_type))
                .sum();
            fields_size.div_ceil(8) * 8
        }
        Type::Fallible(ft) => {
            // Fallible layout: | tag (i64) | payload (max size of T or any E) |
            // Tag is always 8 bytes (i64)
            let success_size = type_size(&ft.success_type, pointer_type);

            // Compute max error payload size
            let error_size = match ft.error_type.as_ref() {
                Type::Nominal(NominalType::Error(info)) => {
                    // Single error type
                    info.fields
                        .iter()
                        .map(|f| type_size(&f.ty, pointer_type))
                        .sum()
                }
                Type::Union(variants) => {
                    // Union of error types - find max payload
                    variants
                        .iter()
                        .filter_map(|v| match v {
                            Type::Nominal(NominalType::Error(info)) => Some(
                                info.fields
                                    .iter()
                                    .map(|f| type_size(&f.ty, pointer_type))
                                    .sum(),
                            ),
                            _ => None,
                        })
                        .max()
                        .unwrap_or(0)
                }
                _ => 0,
            };

            let max_payload = success_size.max(error_size);
            // Layout: [tag:8][payload:max_payload] aligned to 8
            8 + max_payload.div_ceil(8) * 8
        }
        Type::Tuple(elements) => {
            // Sum of element sizes, each aligned to 8 bytes
            elements
                .iter()
                .map(|t| type_size(t, pointer_type).div_ceil(8) * 8)
                .sum()
        }
        Type::FixedArray { element, size } => {
            // Element size * count, each element aligned to 8 bytes
            let elem_size = type_size(element, pointer_type).div_ceil(8) * 8;
            elem_size * (*size as u32)
        }
        _ => 8, // default
    }
}

/// Calculate layout for tuple elements.
/// Returns (total_size, offsets) where offsets[i] is the byte offset for element i.
/// Each element is aligned to 8 bytes for simplicity.
pub(crate) fn tuple_layout(elements: &[Type], pointer_type: types::Type) -> (u32, Vec<i32>) {
    let mut offsets = Vec::with_capacity(elements.len());
    let mut offset = 0i32;

    for elem in elements {
        offsets.push(offset);
        let elem_size = type_size(elem, pointer_type).div_ceil(8) * 8;
        offset += elem_size as i32;
    }

    (offset as u32, offsets)
}

// ============================================================================
// Fallible type layout helpers
// ============================================================================

/// Tag value for success in a fallible type (payload is the success value)
pub(crate) const FALLIBLE_SUCCESS_TAG: i64 = 0;

/// Offset of the tag field in a fallible value (always 0)
pub(crate) const FALLIBLE_TAG_OFFSET: i32 = 0;

/// Offset of the payload field in a fallible value (always 8, after the i64 tag)
pub(crate) const FALLIBLE_PAYLOAD_OFFSET: i32 = 8;

/// Size of the tag field in bytes
#[allow(dead_code)] // Will be used in subsequent codegen tasks
pub(crate) const FALLIBLE_TAG_SIZE: u32 = 8;

/// Get the error tag for a specific error type within a fallible type.
/// Returns the 1-based index (tag 0 is reserved for success).
///
/// Uses string comparison via the NameTable/EntityRegistry to look up error type names
/// and compares with the resolved error_name Symbol.
pub(crate) fn fallible_error_tag(
    fallible: &crate::sema::types::FallibleType,
    error_name: Symbol,
    interner: &Interner,
    name_table: &NameTable,
    entity_registry: &EntityRegistry,
) -> Option<i64> {
    let error_name_str = interner.resolve(error_name);
    match fallible.error_type.as_ref() {
        Type::Nominal(NominalType::Error(info)) => {
            let info_name = name_table.last_segment_str(entity_registry.name_id(info.type_def_id));
            if info_name.as_deref() == Some(error_name_str) {
                Some(1) // Single error type always gets tag 1
            } else {
                None
            }
        }
        Type::Union(variants) => {
            // Find the 1-based index of the error type in the union
            for (idx, variant) in variants.iter().enumerate() {
                if let Type::Nominal(NominalType::Error(info)) = variant {
                    let info_name =
                        name_table.last_segment_str(entity_registry.name_id(info.type_def_id));
                    if info_name.as_deref() == Some(error_name_str) {
                        return Some((idx + 1) as i64);
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Convert a Cranelift type back to a Vole type (for return value inference)
#[allow(dead_code)] // Used by compiler.rs during migration
pub(crate) fn cranelift_to_vole_type(ty: types::Type) -> Type {
    match ty {
        types::I8 => Type::Primitive(PrimitiveType::I8),
        types::I16 => Type::Primitive(PrimitiveType::I16),
        types::I32 => Type::Primitive(PrimitiveType::I32),
        types::I64 => Type::Primitive(PrimitiveType::I64),
        types::I128 => Type::Primitive(PrimitiveType::I128),
        types::F32 => Type::Primitive(PrimitiveType::F32),
        types::F64 => Type::Primitive(PrimitiveType::F64),
        _ => Type::unknown(), // Pointer types, etc. use inference placeholder for now
    }
}

/// Convert a compiled value to a target Cranelift type
pub(crate) fn convert_to_type(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    target: types::Type,
) -> Value {
    if val.ty == target {
        return val.value;
    }

    if target == types::F64 {
        // Convert int to float
        if val.ty == types::I64 || val.ty == types::I32 {
            return builder.ins().fcvt_from_sint(types::F64, val.value);
        }
        // Convert f32 to f64
        if val.ty == types::F32 {
            return builder.ins().fpromote(types::F64, val.value);
        }
    }

    if target == types::F32 {
        // Convert f64 to f32
        if val.ty == types::F64 {
            return builder.ins().fdemote(types::F32, val.value);
        }
    }

    // Integer widening - use uextend for unsigned types, sextend for signed
    if target.is_int() && val.ty.is_int() && target.bits() > val.ty.bits() {
        if val.vole_type.is_unsigned() {
            return builder.ins().uextend(target, val.value);
        } else {
            return builder.ins().sextend(target, val.value);
        }
    }

    // Integer narrowing
    if target.is_int() && val.ty.is_int() && target.bits() < val.ty.bits() {
        return builder.ins().ireduce(target, val.value);
    }

    val.value
}

/// Convert a value to a uniform word representation for interface dispatch.
pub(crate) fn value_to_word(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
    pointer_type: types::Type,
    heap_alloc_ref: Option<FuncRef>,
) -> Result<Value, String> {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let needs_box = type_size(&value.vole_type, pointer_type) > word_bytes;

    if needs_box {
        // If the Cranelift type is already a pointer and the Vole type needs boxing,
        // then the value is already a pointer to boxed data (e.g., from external functions
        // returning unions). Just return it directly - don't double-box.
        if value.ty == pointer_type {
            return Ok(value.value);
        }
        let Some(heap_alloc_ref) = heap_alloc_ref else {
            return Err(
                CodegenError::missing_resource("heap allocator for interface boxing").into(),
            );
        };
        let size_val = builder.ins().iconst(
            pointer_type,
            type_size(&value.vole_type, pointer_type) as i64,
        );
        let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
        let alloc_ptr = builder.inst_results(alloc_call)[0];
        builder
            .ins()
            .store(MemFlags::new(), value.value, alloc_ptr, 0);
        return Ok(alloc_ptr);
    }

    let word = match value.vole_type {
        Type::Primitive(PrimitiveType::F64) => {
            builder
                .ins()
                .bitcast(types::I64, MemFlags::new(), value.value)
        }
        Type::Primitive(PrimitiveType::F32) => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            builder.ins().uextend(word_type, i32_val)
        }
        Type::Primitive(PrimitiveType::Bool) => builder.ins().uextend(word_type, value.value),
        Type::Primitive(PrimitiveType::I8) | Type::Primitive(PrimitiveType::U8) => {
            builder.ins().uextend(word_type, value.value)
        }
        Type::Primitive(PrimitiveType::I16) | Type::Primitive(PrimitiveType::U16) => {
            builder.ins().uextend(word_type, value.value)
        }
        Type::Primitive(PrimitiveType::I32) | Type::Primitive(PrimitiveType::U32) => {
            builder.ins().uextend(word_type, value.value)
        }
        Type::Primitive(PrimitiveType::I64) | Type::Primitive(PrimitiveType::U64) => value.value,
        Type::Primitive(PrimitiveType::I128) => {
            let low = builder.ins().ireduce(types::I64, value.value);
            if word_type == types::I64 {
                low
            } else {
                builder.ins().uextend(word_type, low)
            }
        }
        _ => value.value,
    };

    Ok(word)
}

/// Convert a uniform word representation back into a typed value.
pub(crate) fn word_to_value(
    builder: &mut FunctionBuilder,
    word: Value,
    vole_type: &Type,
    pointer_type: types::Type,
) -> Value {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let needs_unbox = type_size(vole_type, pointer_type) > word_bytes;

    if needs_unbox {
        // If the target Cranelift type is pointer_type (e.g., unions), the word is
        // already a pointer to the data - just return it, don't load from it.
        let target_type = type_to_cranelift(vole_type, pointer_type);
        if target_type == pointer_type {
            return word;
        }
        return builder.ins().load(target_type, MemFlags::new(), word, 0);
    }

    match vole_type {
        Type::Primitive(PrimitiveType::F64) => {
            builder.ins().bitcast(types::F64, MemFlags::new(), word)
        }
        Type::Primitive(PrimitiveType::F32) => {
            let i32_val = builder.ins().ireduce(types::I32, word);
            builder.ins().bitcast(types::F32, MemFlags::new(), i32_val)
        }
        Type::Primitive(PrimitiveType::Bool) => builder.ins().ireduce(types::I8, word),
        Type::Primitive(PrimitiveType::I8) | Type::Primitive(PrimitiveType::U8) => {
            builder.ins().ireduce(types::I8, word)
        }
        Type::Primitive(PrimitiveType::I16) | Type::Primitive(PrimitiveType::U16) => {
            builder.ins().ireduce(types::I16, word)
        }
        Type::Primitive(PrimitiveType::I32) | Type::Primitive(PrimitiveType::U32) => {
            builder.ins().ireduce(types::I32, word)
        }
        Type::Primitive(PrimitiveType::I64) | Type::Primitive(PrimitiveType::U64) => word,
        Type::Primitive(PrimitiveType::I128) => {
            let low = if word_type == types::I64 {
                word
            } else {
                builder.ins().ireduce(types::I64, word)
            };
            builder.ins().uextend(types::I128, low)
        }
        _ => word,
    }
}

/// Get the runtime tag value for an array element type.
/// These tags are used by the runtime to distinguish element types.
pub(crate) fn array_element_tag(ty: &Type) -> i64 {
    match ty {
        Type::Primitive(PrimitiveType::String) => 1,
        Type::Primitive(PrimitiveType::I64)
        | Type::Primitive(PrimitiveType::I32)
        | Type::Primitive(PrimitiveType::I16)
        | Type::Primitive(PrimitiveType::I8) => 2,
        Type::Primitive(PrimitiveType::F64) | Type::Primitive(PrimitiveType::F32) => 3,
        Type::Primitive(PrimitiveType::Bool) => 4,
        Type::Array(_) => 5,
        _ => 2, // default to integer
    }
}

/// Convert NativeType to Cranelift type.
/// Shared utility for external function calls in both compiler.rs and context.rs.
pub(crate) fn native_type_to_cranelift(nt: &NativeType, pointer_type: types::Type) -> types::Type {
    match nt {
        NativeType::I8 => types::I8,
        NativeType::I16 => types::I16,
        NativeType::I32 => types::I32,
        NativeType::I64 => types::I64,
        NativeType::I128 => types::I128,
        NativeType::U8 => types::I8,
        NativeType::U16 => types::I16,
        NativeType::U32 => types::I32,
        NativeType::U64 => types::I64,
        NativeType::F32 => types::F32,
        NativeType::F64 => types::F64,
        NativeType::Bool => types::I8,
        NativeType::String => pointer_type,
        NativeType::Nil => types::I8, // Nil uses I8 as placeholder
        NativeType::Optional(_) => types::I64, // Optionals are boxed
        NativeType::Array(_) => pointer_type,
    }
}
