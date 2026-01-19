// src/codegen/types.rs
//
// Type-related utilities for code generation.
// This module contains shared type utilities used throughout the codegen module.

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use cranelift_jit::JITModule;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::codegen::FunctionRegistry;
use crate::commands::common::AnalyzedProgram;
use crate::errors::CodegenError;
use crate::frontend::{Interner, LetStmt, NodeId, Symbol, TypeExpr};
use crate::identity::{self, ModuleId, NameId, NameTable, NamerLookup, Resolver, TypeDefId};
use crate::runtime::NativeRegistry;
use crate::runtime::native_registry::NativeType;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::MonomorphCache;
use crate::sema::implement_registry::ImplTypeId;
use crate::sema::type_arena::{TypeArena, TypeId, TypeIdVec};
use crate::sema::{EntityRegistry, PrimitiveType};

// Re-export box_interface_value_id for centralized access to boxing helper
pub(crate) use super::interface_vtable::box_interface_value_id;

/// Compiled value with its type
#[derive(Clone, Copy)]
pub struct CompiledValue {
    pub value: Value,
    pub ty: Type,
    /// The Vole type of this value (interned TypeId handle - use arena to query)
    pub type_id: TypeId,
}

impl CompiledValue {
    /// Create a new CompiledValue with a different value but the same types
    pub fn with_value(&self, value: Value) -> Self {
        Self {
            value,
            ty: self.ty,
            type_id: self.type_id,
        }
    }
}

/// Metadata about a class or record type for code generation
#[derive(Debug, Clone)]
pub(crate) struct TypeMetadata {
    /// Unique type ID for runtime
    pub type_id: u32,
    /// Map from field name to slot index
    pub field_slots: HashMap<String, usize>,
    /// The Vole type (Class or Record) - interned TypeId handle
    pub vole_type: TypeId,
    /// Method info: method name -> method info
    pub method_infos: HashMap<NameId, MethodInfo>,
}

/// Metadata for a compiled method (opaque function key + return type)
#[derive(Debug, Clone, Copy)]
pub(crate) struct MethodInfo {
    pub func_key: crate::codegen::FunctionKey,
    pub return_type: TypeId,
}

/// Look up TypeMetadata by NameId (cross-interner safe)
/// Returns the TypeMetadata for a class/record with the given name_id
pub(crate) fn type_metadata_by_name_id<'a>(
    type_metadata: &'a HashMap<Symbol, TypeMetadata>,
    name_id: NameId,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> Option<&'a TypeMetadata> {
    tracing::trace!(
        ?name_id,
        count = type_metadata.len(),
        "type_metadata_by_name_id lookup"
    );
    let result = type_metadata.values().find(|meta| {
        // Use arena queries to check if this is a class or record with matching name_id
        if let Some((type_def_id, _)) = arena.unwrap_class(meta.vole_type) {
            let class_name_id = entity_registry.get_type(type_def_id).name_id;
            tracing::trace!(target_name_id = ?name_id, class_name_id = ?class_name_id, "comparing class name_id");
            return class_name_id == name_id;
        }
        if let Some((type_def_id, _)) = arena.unwrap_record(meta.vole_type) {
            let record_name_id = entity_registry.get_type(type_def_id).name_id;
            return record_name_id == name_id;
        }
        false
    });
    if result.is_none() {
        // Log all class name_ids for debugging
        let class_name_ids: Vec<_> = type_metadata
            .values()
            .filter_map(|meta| {
                arena
                    .unwrap_class(meta.vole_type)
                    .map(|(type_def_id, _)| entity_registry.get_type(type_def_id).name_id)
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
    /// Shared type arena for interned type access (same arena used by ExpressionData)
    pub arena: &'a Rc<RefCell<TypeArena>>,
    pub pointer_type: Type,
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
    pub impl_method_infos: &'a HashMap<(ImplTypeId, NameId), MethodInfo>,
    /// Static method info keyed by (TypeDefId, method_name)
    pub static_method_infos: &'a HashMap<(TypeDefId, NameId), MethodInfo>,
    /// Interface vtable registry (interface + concrete type -> data id)
    pub interface_vtables: &'a RefCell<crate::codegen::interface_vtable::InterfaceVtableRegistry>,
    /// Current function's return type (needed for raise statements in fallible functions)
    /// Stored as TypeId for O(1) equality; convert via arena.to_type() when needed
    pub current_function_return_type: Option<TypeId>,
    /// Registry of native functions for external method calls
    pub native_registry: &'a NativeRegistry,
    /// Current module path when compiling module code (e.g., "std:math")
    /// None when compiling main program code
    pub current_module: Option<&'a str>,
    /// Cache of monomorphized function instances
    pub monomorph_cache: &'a MonomorphCache,
    /// Type substitutions for monomorphized class method compilation
    /// Maps type param NameId -> concrete TypeId (interned for O(1) equality)
    pub type_substitutions: Option<&'a HashMap<NameId, TypeId>>,
}

impl<'a> CompileCtx<'a> {
    /// Substitute type parameters with concrete types using TypeId directly.
    pub fn substitute_type_id(&self, ty: TypeId) -> TypeId {
        if let Some(substitutions) = self.type_substitutions {
            // Convert std HashMap to hashbrown HashMap for arena compatibility
            let subs: hashbrown::HashMap<NameId, TypeId> =
                substitutions.iter().map(|(&k, &v)| (k, v)).collect();
            self.arena.borrow_mut().substitute(ty, &subs)
        } else {
            ty
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

    /// Look up expression type, checking module-specific expr_types if compiling module code.
    /// Returns the interned TypeId handle.
    pub fn get_expr_type(&self, node_id: &NodeId) -> Option<TypeId> {
        // When compiling module code, NodeIds are relative to that module's program
        // Use module-specific expr_types if available
        if let Some(module_path) = self.current_module
            && let Some(module_types) = self.analyzed.query().expr_data().module_types(module_path)
            && let Some(ty) = module_types.get(node_id)
        {
            return Some(*ty);
        }
        // Fall back to main program expr_types via query interface
        self.analyzed.query().type_of(*node_id)
    }
}

/// Resolve a type expression to a TypeId (uses CompileCtx for full context)
/// This is the TypeId-based version that avoids intermediate LegacyType allocation
/// when callers only need a TypeId.
pub(crate) fn resolve_type_expr_id(ty: &TypeExpr, ctx: &CompileCtx) -> TypeId {
    let module_id = ctx
        .current_module
        .and_then(|path| ctx.analyzed.name_table.module_id_if_known(path))
        .unwrap_or_else(|| ctx.analyzed.name_table.main_module());

    // Use the TypeId-native resolution function directly
    let type_id = resolve_type_expr_to_id(
        ty,
        &ctx.analyzed.entity_registry,
        ctx.type_metadata,
        ctx.interner,
        &ctx.analyzed.name_table,
        module_id,
        ctx.arena,
    );

    // Apply type substitutions if compiling a monomorphized context
    if let Some(substitutions) = ctx.type_substitutions {
        // Convert std::collections::HashMap to hashbrown::HashMap for arena.substitute
        let subs: hashbrown::HashMap<NameId, TypeId> =
            substitutions.iter().map(|(&k, &v)| (k, v)).collect();
        ctx.arena.borrow_mut().substitute(type_id, &subs)
    } else {
        type_id
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

/// Resolve a type expression directly to TypeId (no LegacyType intermediate).
/// Use this function when you don't need to handle generic interface method substitution.
#[allow(clippy::too_many_arguments)]
pub(crate) fn resolve_type_expr_to_id(
    ty: &TypeExpr,
    entity_registry: &EntityRegistry,
    type_metadata: &HashMap<Symbol, TypeMetadata>,
    interner: &Interner,
    name_table: &NameTable,
    module_id: ModuleId,
    arena: &RefCell<TypeArena>,
) -> TypeId {
    use crate::sema::type_arena::SemaType;
    use crate::sema::types::primitive::PrimitiveType as SemaPrimitive;

    // Create resolver for name lookups
    let resolver = Resolver::new(interner, name_table, module_id, &[]);

    match ty {
        TypeExpr::Primitive(p) => {
            // Convert ast::PrimitiveType to sema::PrimitiveType
            let sema_prim = match p {
                crate::frontend::ast::PrimitiveType::I8 => SemaPrimitive::I8,
                crate::frontend::ast::PrimitiveType::I16 => SemaPrimitive::I16,
                crate::frontend::ast::PrimitiveType::I32 => SemaPrimitive::I32,
                crate::frontend::ast::PrimitiveType::I64 => SemaPrimitive::I64,
                crate::frontend::ast::PrimitiveType::I128 => SemaPrimitive::I128,
                crate::frontend::ast::PrimitiveType::U8 => SemaPrimitive::U8,
                crate::frontend::ast::PrimitiveType::U16 => SemaPrimitive::U16,
                crate::frontend::ast::PrimitiveType::U32 => SemaPrimitive::U32,
                crate::frontend::ast::PrimitiveType::U64 => SemaPrimitive::U64,
                crate::frontend::ast::PrimitiveType::F32 => SemaPrimitive::F32,
                crate::frontend::ast::PrimitiveType::F64 => SemaPrimitive::F64,
                crate::frontend::ast::PrimitiveType::Bool => SemaPrimitive::Bool,
                crate::frontend::ast::PrimitiveType::String => SemaPrimitive::String,
            };
            arena.borrow().primitive(sema_prim)
        }
        TypeExpr::Named(sym) => {
            // Check entity registry for type definition (aliases, interfaces, etc.)
            let type_def_id = resolver.resolve_type_or_interface(*sym, entity_registry);

            if let Some(type_def_id) = type_def_id {
                let type_def = entity_registry.get_type(type_def_id);
                match type_def.kind {
                    TypeDefKind::Alias => {
                        // Type alias - return the aliased type directly
                        type_def.aliased_type.unwrap_or_else(|| {
                            panic!(
                                "INTERNAL ERROR: type alias has no aliased_type\n\
                                 type_def_id: {:?}, name_id: {:?}",
                                type_def_id, type_def.name_id
                            )
                        })
                    }
                    TypeDefKind::Interface => {
                        // Non-generic interface - just use type_def_id
                        if !type_def.type_params.is_empty() {
                            panic!(
                                "INTERNAL ERROR: generic interface used without type args\n\
                                 type_def_id: {:?}, name_id: {:?}, type_params: {:?}",
                                type_def_id, type_def.name_id, type_def.type_params
                            );
                        }
                        arena.borrow_mut().interface(type_def_id, TypeIdVec::new())
                    }
                    TypeDefKind::ErrorType => arena.borrow_mut().error_type(type_def_id),
                    TypeDefKind::Record | TypeDefKind::Class => {
                        // For Record and Class types, first try direct lookup by Symbol
                        if let Some(metadata) = type_metadata.get(sym) {
                            // Verify this is the right type by comparing type_def_ids
                            let matches = {
                                let arena_ref = arena.borrow();
                                match arena_ref.get(metadata.vole_type) {
                                    SemaType::Record {
                                        type_def_id: id, ..
                                    } => *id == type_def_id,
                                    SemaType::Class {
                                        type_def_id: id, ..
                                    } => *id == type_def_id,
                                    _ => false,
                                }
                            };
                            if matches {
                                return metadata.vole_type;
                            }
                        }
                        // Build from entity registry
                        if type_def.kind == TypeDefKind::Record {
                            arena.borrow_mut().record(type_def_id, TypeIdVec::new())
                        } else {
                            arena.borrow_mut().class(type_def_id, TypeIdVec::new())
                        }
                    }
                    _ => {
                        // Primitive or unknown - check type metadata
                        type_metadata
                            .get(sym)
                            .map(|m| m.vole_type)
                            .unwrap_or_else(|| {
                                panic!(
                                    "INTERNAL ERROR: unknown type kind with no metadata\n\
                                 type_def_id: {:?}, kind: {:?}, sym: {:?}",
                                    type_def_id, type_def.kind, sym
                                )
                            })
                    }
                }
            } else if let Some(metadata) = type_metadata.get(sym) {
                metadata.vole_type
            } else {
                // Type parameter - use placeholder
                let name = interner.resolve(*sym);
                tracing::trace!(name, "type parameter in codegen, using Placeholder");
                arena
                    .borrow_mut()
                    .placeholder(crate::sema::types::PlaceholderKind::TypeParam(
                        name.to_string(),
                    ))
            }
        }
        TypeExpr::Array(elem) => {
            let elem_id = resolve_type_expr_to_id(
                elem,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
                arena,
            );
            arena.borrow_mut().array(elem_id)
        }
        TypeExpr::Optional(inner) => {
            // T? desugars to T | nil
            let inner_id = resolve_type_expr_to_id(
                inner,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
                arena,
            );
            arena.borrow_mut().optional(inner_id)
        }
        TypeExpr::Union(variants) => {
            let variant_ids: Vec<TypeId> = variants
                .iter()
                .map(|v| {
                    resolve_type_expr_to_id(
                        v,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                        arena,
                    )
                })
                .collect();
            arena.borrow_mut().union(variant_ids)
        }
        TypeExpr::Nil => arena.borrow().nil(),
        TypeExpr::Done => arena.borrow().done(),
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_ids: TypeIdVec = params
                .iter()
                .map(|p| {
                    resolve_type_expr_to_id(
                        p,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                        arena,
                    )
                })
                .collect();
            let ret_id = resolve_type_expr_to_id(
                return_type,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
                arena,
            );
            arena.borrow_mut().function(param_ids, ret_id, false)
        }
        TypeExpr::SelfType => {
            // Self type placeholder
            arena
                .borrow_mut()
                .placeholder(crate::sema::types::PlaceholderKind::SelfType)
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success_id = resolve_type_expr_to_id(
                success_type,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
                arena,
            );
            let error_id = resolve_type_expr_to_id(
                error_type,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
                arena,
            );
            arena.borrow_mut().fallible(success_id, error_id)
        }
        TypeExpr::Generic { name, args } => {
            // Resolve all type arguments
            let arg_ids: TypeIdVec = args
                .iter()
                .map(|a| {
                    resolve_type_expr_to_id(
                        a,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                        arena,
                    )
                })
                .collect();

            // Check entity registry for generic type
            let type_def_id = resolver.resolve_type_or_interface(*name, entity_registry);

            let name_str = interner.resolve(*name);
            if let Some(type_def_id) = type_def_id {
                let type_def = entity_registry.get_type(type_def_id);
                match type_def.kind {
                    TypeDefKind::Class => arena.borrow_mut().class(type_def_id, arg_ids),
                    TypeDefKind::Record => arena.borrow_mut().record(type_def_id, arg_ids),
                    TypeDefKind::Interface => {
                        if !type_def.type_params.is_empty()
                            && type_def.type_params.len() != arg_ids.len()
                        {
                            panic!(
                                "INTERNAL ERROR: generic interface type arg count mismatch\n\
                                 expected {} type args, got {}\n\
                                 type_def_id: {:?}, name_id: {:?}",
                                type_def.type_params.len(),
                                arg_ids.len(),
                                type_def_id,
                                type_def.name_id
                            );
                        }
                        arena.borrow_mut().interface(type_def_id, arg_ids)
                    }
                    TypeDefKind::Alias | TypeDefKind::ErrorType | TypeDefKind::Primitive => {
                        panic!(
                            "INTERNAL ERROR: type '{}' cannot have type arguments\n\
                             kind: {:?}, type_def_id: {:?}",
                            name_str, type_def.kind, type_def_id
                        );
                    }
                }
            } else {
                panic!(
                    "INTERNAL ERROR: unknown generic type '{}'\n\
                     module_id: {:?}",
                    name_str, module_id
                )
            }
        }
        TypeExpr::Tuple(elements) => {
            let element_ids: TypeIdVec = elements
                .iter()
                .map(|e| {
                    resolve_type_expr_to_id(
                        e,
                        entity_registry,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                        arena,
                    )
                })
                .collect();
            arena.borrow_mut().tuple(element_ids)
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_id = resolve_type_expr_to_id(
                element,
                entity_registry,
                type_metadata,
                interner,
                name_table,
                module_id,
                arena,
            );
            arena.borrow_mut().fixed_array(elem_id, *size)
        }
        TypeExpr::Structural { .. } | TypeExpr::Combination(_) => {
            // Constraint-only types - use void
            arena.borrow().void()
        }
    }
}

/// Convert a TypeId to a Cranelift type.
pub(crate) fn type_id_to_cranelift(ty: TypeId, arena: &TypeArena, pointer_type: Type) -> Type {
    use crate::sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        ArenaType::Primitive(PrimitiveType::I8) | ArenaType::Primitive(PrimitiveType::U8) => {
            types::I8
        }
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => {
            types::I16
        }
        ArenaType::Primitive(PrimitiveType::I32) | ArenaType::Primitive(PrimitiveType::U32) => {
            types::I32
        }
        ArenaType::Primitive(PrimitiveType::I64) | ArenaType::Primitive(PrimitiveType::U64) => {
            types::I64
        }
        ArenaType::Primitive(PrimitiveType::I128) => types::I128,
        ArenaType::Primitive(PrimitiveType::F32) => types::F32,
        ArenaType::Primitive(PrimitiveType::F64) => types::F64,
        ArenaType::Primitive(PrimitiveType::Bool) => types::I8,
        ArenaType::Primitive(PrimitiveType::String) => pointer_type,
        ArenaType::Interface { .. } => pointer_type,
        ArenaType::Nil => types::I8,
        ArenaType::Done => types::I8,
        ArenaType::Union(_) => pointer_type,
        ArenaType::Fallible { .. } => pointer_type,
        ArenaType::Function { .. } => pointer_type,
        ArenaType::Range => pointer_type,
        ArenaType::Tuple(_) => pointer_type,
        ArenaType::FixedArray { .. } => pointer_type,
        _ => types::I64,
    }
}

/// Get the size in bytes for a TypeId (no LegacyType conversion)
pub(crate) fn type_id_size(
    ty: TypeId,
    pointer_type: Type,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> u32 {
    use crate::sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        ArenaType::Primitive(PrimitiveType::I8)
        | ArenaType::Primitive(PrimitiveType::U8)
        | ArenaType::Primitive(PrimitiveType::Bool) => 1,
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => 2,
        ArenaType::Primitive(PrimitiveType::I32)
        | ArenaType::Primitive(PrimitiveType::U32)
        | ArenaType::Primitive(PrimitiveType::F32) => 4,
        ArenaType::Primitive(PrimitiveType::I64)
        | ArenaType::Primitive(PrimitiveType::U64)
        | ArenaType::Primitive(PrimitiveType::F64) => 8,
        ArenaType::Primitive(PrimitiveType::I128) => 16,
        ArenaType::Primitive(PrimitiveType::String) | ArenaType::Array(_) => pointer_type.bytes(),
        ArenaType::Interface { .. } => pointer_type.bytes(),
        ArenaType::Nil | ArenaType::Done | ArenaType::Void => 0,
        ArenaType::Range => 16,
        ArenaType::Union(variants) => {
            let max_payload = variants
                .iter()
                .map(|&t| type_id_size(t, pointer_type, entity_registry, arena))
                .max()
                .unwrap_or(0);
            8 + max_payload.div_ceil(8) * 8
        }
        ArenaType::Error { type_def_id } => {
            let fields_size: u32 = entity_registry
                .fields_on_type(*type_def_id)
                .map(|field_id| {
                    let field = entity_registry.get_field(field_id);
                    type_id_size(field.ty, pointer_type, entity_registry, arena)
                })
                .sum();
            fields_size.div_ceil(8) * 8
        }
        ArenaType::Fallible { success, error } => {
            let success_size = type_id_size(*success, pointer_type, entity_registry, arena);
            let error_size = match arena.get(*error) {
                ArenaType::Error { type_def_id } => entity_registry
                    .fields_on_type(*type_def_id)
                    .map(|field_id| {
                        let field = entity_registry.get_field(field_id);
                        type_id_size(field.ty, pointer_type, entity_registry, arena)
                    })
                    .sum(),
                ArenaType::Union(variants) => variants
                    .iter()
                    .filter_map(|&v| match arena.get(v) {
                        ArenaType::Error { type_def_id } => {
                            let size: u32 = entity_registry
                                .fields_on_type(*type_def_id)
                                .map(|field_id| {
                                    let field = entity_registry.get_field(field_id);
                                    type_id_size(field.ty, pointer_type, entity_registry, arena)
                                })
                                .sum();
                            Some(size)
                        }
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0),
                _ => 0,
            };
            let max_payload = success_size.max(error_size);
            8 + max_payload.div_ceil(8) * 8
        }
        ArenaType::Tuple(elements) => elements
            .iter()
            .map(|&t| type_id_size(t, pointer_type, entity_registry, arena).div_ceil(8) * 8)
            .sum(),
        ArenaType::FixedArray { element, size } => {
            let elem_size =
                type_id_size(*element, pointer_type, entity_registry, arena).div_ceil(8) * 8;
            elem_size * (*size as u32)
        }
        _ => 8,
    }
}

/// Calculate layout for tuple elements using TypeId.
/// Returns (total_size, offsets) where offsets[i] is the byte offset for element i.
/// Each element is aligned to 8 bytes for simplicity.
pub(crate) fn tuple_layout_id(
    elements: &[TypeId],
    pointer_type: Type,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> (u32, Vec<i32>) {
    let mut offsets = Vec::with_capacity(elements.len());
    let mut offset = 0i32;

    for &elem in elements {
        offsets.push(offset);
        let elem_size = type_id_size(elem, pointer_type, entity_registry, arena).div_ceil(8) * 8;
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

/// Get the error tag for a specific error type within a fallible type.
/// Returns the 1-based index (tag 0 is reserved for success).
///
/// Takes the error part of a fallible type as a TypeId and uses arena queries
/// to determine the tag for the given error_name.
pub(crate) fn fallible_error_tag_by_id(
    error_type_id: TypeId,
    error_name: Symbol,
    arena: &TypeArena,
    interner: &Interner,
    name_table: &NameTable,
    entity_registry: &EntityRegistry,
) -> Option<i64> {
    let error_name_str = interner.resolve(error_name);

    // Check if error_type_id is a single Error type
    if let Some(type_def_id) = arena.unwrap_error(error_type_id) {
        let info_name = name_table.last_segment_str(entity_registry.name_id(type_def_id));
        if info_name.as_deref() == Some(error_name_str) {
            return Some(1); // Single error type always gets tag 1
        }
        return None;
    }

    // Check if error_type_id is a Union of error types
    if let Some(variants) = arena.unwrap_union(error_type_id) {
        for (idx, &variant) in variants.iter().enumerate() {
            if let Some(type_def_id) = arena.unwrap_error(variant) {
                let info_name = name_table.last_segment_str(entity_registry.name_id(type_def_id));
                if info_name.as_deref() == Some(error_name_str) {
                    return Some((idx + 1) as i64);
                }
            }
        }
        return None;
    }

    None
}

/// Convert a compiled value to a target Cranelift type
pub(crate) fn convert_to_type(
    builder: &mut FunctionBuilder,
    val: CompiledValue,
    target: Type,
    arena: &Rc<RefCell<TypeArena>>,
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
        if arena.borrow().is_unsigned(val.type_id) {
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
    pointer_type: Type,
    heap_alloc_ref: Option<FuncRef>,
    arena: &Rc<RefCell<TypeArena>>,
    entity_registry: &EntityRegistry,
) -> Result<Value, String> {
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let arena_ref = arena.borrow();
    // Use type_id_size to avoid LegacyType conversion for size calculation
    let value_size = type_id_size(value.type_id, pointer_type, entity_registry, &arena_ref);
    let needs_box = value_size > word_bytes;

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
        let size_val = builder.ins().iconst(pointer_type, value_size as i64);
        let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
        let alloc_ptr = builder.inst_results(alloc_call)[0];
        builder
            .ins()
            .store(MemFlags::new(), value.value, alloc_ptr, 0);
        return Ok(alloc_ptr);
    }

    use crate::sema::type_arena::SemaType as ArenaType;
    let word = match arena_ref.get(value.type_id) {
        ArenaType::Primitive(PrimitiveType::F64) => {
            builder
                .ins()
                .bitcast(types::I64, MemFlags::new(), value.value)
        }
        ArenaType::Primitive(PrimitiveType::F32) => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            builder.ins().uextend(word_type, i32_val)
        }
        ArenaType::Primitive(PrimitiveType::Bool) => builder.ins().uextend(word_type, value.value),
        ArenaType::Primitive(PrimitiveType::I8) | ArenaType::Primitive(PrimitiveType::U8) => {
            builder.ins().uextend(word_type, value.value)
        }
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => {
            builder.ins().uextend(word_type, value.value)
        }
        ArenaType::Primitive(PrimitiveType::I32) | ArenaType::Primitive(PrimitiveType::U32) => {
            builder.ins().uextend(word_type, value.value)
        }
        ArenaType::Primitive(PrimitiveType::I64) | ArenaType::Primitive(PrimitiveType::U64) => {
            value.value
        }
        ArenaType::Primitive(PrimitiveType::I128) => {
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

/// Convert a uniform word representation back into a typed value using TypeId.
/// Native TypeId version that avoids LegacyType conversion.
pub(crate) fn word_to_value_type_id(
    builder: &mut FunctionBuilder,
    word: Value,
    type_id: TypeId,
    pointer_type: Type,
    entity_registry: &EntityRegistry,
    arena: &TypeArena,
) -> Value {
    use crate::sema::type_arena::SemaType as ArenaType;
    let word_type = pointer_type;
    let word_bytes = word_type.bytes();
    let needs_unbox = type_id_size(type_id, pointer_type, entity_registry, arena) > word_bytes;

    if needs_unbox {
        // If the target Cranelift type is pointer_type (e.g., unions), the word is
        // already a pointer to the data - just return it, don't load from it.
        let target_type = type_id_to_cranelift(type_id, arena, pointer_type);
        if target_type == pointer_type {
            return word;
        }
        return builder.ins().load(target_type, MemFlags::new(), word, 0);
    }

    match arena.get(type_id) {
        ArenaType::Primitive(PrimitiveType::F64) => {
            builder.ins().bitcast(types::F64, MemFlags::new(), word)
        }
        ArenaType::Primitive(PrimitiveType::F32) => {
            let i32_val = builder.ins().ireduce(types::I32, word);
            builder.ins().bitcast(types::F32, MemFlags::new(), i32_val)
        }
        ArenaType::Primitive(PrimitiveType::Bool) => builder.ins().ireduce(types::I8, word),
        ArenaType::Primitive(PrimitiveType::I8) | ArenaType::Primitive(PrimitiveType::U8) => {
            builder.ins().ireduce(types::I8, word)
        }
        ArenaType::Primitive(PrimitiveType::I16) | ArenaType::Primitive(PrimitiveType::U16) => {
            builder.ins().ireduce(types::I16, word)
        }
        ArenaType::Primitive(PrimitiveType::I32) | ArenaType::Primitive(PrimitiveType::U32) => {
            builder.ins().ireduce(types::I32, word)
        }
        ArenaType::Primitive(PrimitiveType::I64) | ArenaType::Primitive(PrimitiveType::U64) => word,
        ArenaType::Primitive(PrimitiveType::I128) => {
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
pub(crate) fn array_element_tag_id(ty: TypeId, arena: &TypeArena) -> i64 {
    use crate::sema::type_arena::SemaType as ArenaType;
    match arena.get(ty) {
        ArenaType::Primitive(PrimitiveType::String) => 1,
        ArenaType::Primitive(PrimitiveType::I64)
        | ArenaType::Primitive(PrimitiveType::I32)
        | ArenaType::Primitive(PrimitiveType::I16)
        | ArenaType::Primitive(PrimitiveType::I8) => 2,
        ArenaType::Primitive(PrimitiveType::F64) | ArenaType::Primitive(PrimitiveType::F32) => 3,
        ArenaType::Primitive(PrimitiveType::Bool) => 4,
        ArenaType::Array(_) => 5,
        _ => 2, // default to integer
    }
}

/// Convert NativeType to Cranelift type.
/// Shared utility for external function calls in both compiler.rs and context.rs.
pub(crate) fn native_type_to_cranelift(nt: &NativeType, pointer_type: Type) -> Type {
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
