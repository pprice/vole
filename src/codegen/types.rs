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
use crate::identity::{ModuleId, NameId, NameTable, NamerLookup};
use crate::runtime::NativeRegistry;
use crate::runtime::native_registry::NativeType;
use crate::sema::generic::{MonomorphCache, MonomorphKey, substitute_type};
use crate::sema::interface_registry::InterfaceRegistry;
use crate::sema::{ErrorTypeInfo, FunctionType, Type, TypeId, TypeKey};

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
pub(crate) fn type_metadata_by_name_id(
    type_metadata: &HashMap<Symbol, TypeMetadata>,
    name_id: NameId,
) -> Option<&TypeMetadata> {
    type_metadata.values().find(|meta| match &meta.vole_type {
        Type::Class(c) => c.name_id == name_id,
        Type::Record(r) => r.name_id == name_id,
        _ => false,
    })
}

/// Context for compiling expressions and statements
/// Bundles common parameters to reduce function argument count
pub(crate) struct CompileCtx<'a> {
    /// Analyzed program containing type_aliases, expr_types, method_resolutions, etc.
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
    /// Mapping from call expression NodeId to MonomorphKey (for generic function calls)
    pub generic_calls: &'a HashMap<NodeId, MonomorphKey>,
    /// Cache of monomorphized function instances
    pub monomorph_cache: &'a MonomorphCache,
}

/// Resolve a type expression to a Vole Type (uses CompileCtx for full context)
pub(crate) fn resolve_type_expr(ty: &TypeExpr, ctx: &CompileCtx) -> Type {
    let module_id = ctx
        .current_module
        .and_then(|path| ctx.analyzed.name_table.module_id_if_known(path))
        .unwrap_or_else(|| ctx.analyzed.name_table.main_module());
    resolve_type_expr_with_metadata(
        ty,
        &ctx.analyzed.type_aliases,
        &ctx.analyzed.interface_registry,
        &ctx.analyzed.error_types,
        ctx.type_metadata,
        ctx.interner,
        &ctx.analyzed.name_table,
        module_id,
    )
}

pub(crate) fn module_name_id(
    analyzed: &AnalyzedProgram,
    module_id: ModuleId,
    name: &str,
) -> Option<NameId> {
    let module_path = analyzed.name_table.module_path(module_id);
    let (_, module_interner) = analyzed.module_programs.get(module_path)?;
    let sym = module_interner.lookup(name)?;
    analyzed
        .name_table
        .name_id(module_id, &[sym], module_interner)
}

pub(crate) fn method_name_id(
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
    let namer = NamerLookup::new(&analyzed.name_table, interner);
    namer.method_by_str(name_str)
}

#[allow(clippy::only_used_in_recursion)]
pub(crate) fn display_type(analyzed: &AnalyzedProgram, interner: &Interner, ty: &Type) -> String {
    match ty {
        Type::Class(class_type) => analyzed.name_table.display(class_type.name_id),
        Type::Record(record_type) => analyzed.name_table.display(record_type.name_id),
        Type::Interface(interface_type) => {
            let base = analyzed.name_table.display(interface_type.name_id);
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
        Type::ErrorType(error_type) => analyzed.name_table.display(error_type.name_id),
        Type::Module(module_type) => format!(
            "module(\"{}\")",
            analyzed.name_table.module_path(module_type.module_id)
        ),
        Type::GenericInstance { def, args } => {
            let def_name = analyzed.name_table.display(*def);
            let arg_list = args
                .iter()
                .map(|arg| display_type(analyzed, interner, arg))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}<{}>", def_name, arg_list)
        }
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

/// Resolve a type expression using aliases, interface registry, error types, and type metadata
/// This is the full resolution function that handles all named types including classes/records
#[allow(clippy::too_many_arguments)]
pub(crate) fn resolve_type_expr_with_metadata(
    ty: &TypeExpr,
    type_aliases: &HashMap<Symbol, Type>,
    interface_registry: &InterfaceRegistry,
    error_types: &HashMap<Symbol, ErrorTypeInfo>,
    type_metadata: &HashMap<Symbol, TypeMetadata>,
    interner: &Interner,
    name_table: &NameTable,
    module_id: ModuleId,
) -> Type {
    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Look up type alias first
            if let Some(aliased) = type_aliases.get(sym) {
                aliased.clone()
            } else if let Some(iface) = interface_registry.get(*sym, interner) {
                // Check interface registry
                if !iface.type_params.is_empty() {
                    return Type::Error;
                }
                Type::Interface(crate::sema::types::InterfaceType {
                    name_id: iface.name_id,
                    type_args: Vec::new(),
                    methods: iface
                        .methods
                        .iter()
                        .map(|m| crate::sema::types::InterfaceMethodType {
                            name: m.name,
                            params: m.params.clone(),
                            return_type: Box::new(m.return_type.clone()),
                            has_default: m.has_default,
                        })
                        .collect(),
                    extends: iface.extends.clone(),
                })
            } else if let Some(error_info) = error_types.get(sym) {
                // Check error types
                Type::ErrorType(error_info.clone())
            } else if let Some(metadata) = type_metadata.get(sym) {
                // Check class/record type metadata
                metadata.vole_type.clone()
            } else {
                Type::Error
            }
        }
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type_expr_with_metadata(
                elem,
                type_aliases,
                interface_registry,
                error_types,
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
                type_aliases,
                interface_registry,
                error_types,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            Type::Union(vec![inner_ty, Type::Nil])
        }
        TypeExpr::Union(variants) => {
            let variant_types: Vec<Type> = variants
                .iter()
                .map(|v| {
                    resolve_type_expr_with_metadata(
                        v,
                        type_aliases,
                        interface_registry,
                        error_types,
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
                        type_aliases,
                        interface_registry,
                        error_types,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                    )
                })
                .collect();
            let ret_type = resolve_type_expr_with_metadata(
                return_type,
                type_aliases,
                interface_registry,
                error_types,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            Type::Function(FunctionType {
                params: param_types,
                return_type: Box::new(ret_type),
                is_closure: false, // Type expressions don't know if closure
            })
        }
        TypeExpr::SelfType => {
            // Self type is resolved during interface/implement compilation
            Type::Error
        }
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => {
            let success = resolve_type_expr_with_metadata(
                success_type,
                type_aliases,
                interface_registry,
                error_types,
                type_metadata,
                interner,
                name_table,
                module_id,
            );
            let error = resolve_type_expr_with_metadata(
                error_type,
                type_aliases,
                interface_registry,
                error_types,
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
                        type_aliases,
                        interface_registry,
                        error_types,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                    )
                })
                .collect();
            if let Some(iface) = interface_registry.get(*name, interner) {
                if !iface.type_params.is_empty() && iface.type_params.len() != resolved_args.len() {
                    return Type::Error;
                }
                let mut substitutions = HashMap::new();
                for (param, arg) in iface.type_params.iter().zip(resolved_args.iter()) {
                    substitutions.insert(*param, arg.clone());
                }
                let methods = iface
                    .methods
                    .iter()
                    .map(|method| crate::sema::types::InterfaceMethodType {
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
                return Type::Interface(crate::sema::types::InterfaceType {
                    name_id: iface.name_id,
                    type_args: resolved_args,
                    methods,
                    extends: iface.extends.clone(),
                });
            }
            let Some(name_id) = name_table.name_id(module_id, &[*name], interner) else {
                return Type::Error;
            };
            Type::GenericInstance {
                def: name_id,
                args: resolved_args,
            }
        }
        TypeExpr::Tuple(elements) => {
            let resolved_elements: Vec<Type> = elements
                .iter()
                .map(|e| {
                    resolve_type_expr_with_metadata(
                        e,
                        type_aliases,
                        interface_registry,
                        error_types,
                        type_metadata,
                        interner,
                        name_table,
                        module_id,
                    )
                })
                .collect();
            Type::Tuple(resolved_elements)
        }
        TypeExpr::FixedArray { element, size } => {
            let elem_ty = resolve_type_expr_with_metadata(
                element,
                type_aliases,
                interface_registry,
                error_types,
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
    }
}

/// Resolve a type expression using aliases, interface registry, and error types
/// This is used when CompileCtx is not available (e.g., during Compiler setup)
/// Note: This does NOT resolve class/record types from type_metadata - use resolve_type_expr for that
pub(crate) fn resolve_type_expr_full(
    ty: &TypeExpr,
    type_aliases: &HashMap<Symbol, Type>,
    interface_registry: &InterfaceRegistry,
    error_types: &HashMap<Symbol, ErrorTypeInfo>,
    interner: &Interner,
    name_table: &NameTable,
    module_id: ModuleId,
) -> Type {
    // Use empty type_metadata for backward compatibility
    let empty_type_metadata = HashMap::new();
    resolve_type_expr_with_metadata(
        ty,
        type_aliases,
        interface_registry,
        error_types,
        &empty_type_metadata,
        interner,
        name_table,
        module_id,
    )
}

/// Convert a Vole type to a Cranelift type
pub(crate) fn type_to_cranelift(ty: &Type, pointer_type: types::Type) -> types::Type {
    match ty {
        Type::I8 | Type::U8 => types::I8,
        Type::I16 | Type::U16 => types::I16,
        Type::I32 | Type::U32 => types::I32,
        Type::I64 | Type::U64 => types::I64,
        Type::I128 => types::I128,
        Type::F32 => types::F32,
        Type::F64 => types::F64,
        Type::Bool => types::I8,
        Type::String => pointer_type,
        Type::Interface(_) => pointer_type,
        Type::Nil => types::I8,            // Nil uses minimal representation
        Type::Done => types::I8,           // Done uses minimal representation (like Nil)
        Type::Union(_) => pointer_type,    // Unions are passed by pointer
        Type::Fallible(_) => pointer_type, // Fallibles are passed by pointer (tagged union)
        Type::Function(_) => pointer_type, // Function pointers
        Type::Range => pointer_type,       // Ranges are passed by pointer (start, end)
        _ => types::I64,                   // Default
    }
}

/// Get the size in bytes for a Vole type (used for union layout)
pub(crate) fn type_size(ty: &Type, pointer_type: types::Type) -> u32 {
    match ty {
        Type::I8 | Type::U8 | Type::Bool => 1,
        Type::I16 | Type::U16 => 2,
        Type::I32 | Type::U32 | Type::F32 => 4,
        Type::I64 | Type::U64 | Type::F64 => 8,
        Type::I128 => 16,
        Type::String | Type::Array(_) => pointer_type.bytes(), // pointer size
        Type::Interface(_) => pointer_type.bytes(),
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
        Type::ErrorType(info) => {
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
                Type::ErrorType(info) => {
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
                            Type::ErrorType(info) => Some(
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
        _ => 8, // default
    }
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
/// Uses string comparison via the Interner to handle cross-interner Symbol lookup.
/// This is necessary because error types in the fallible type may have Symbols from
/// the analyzed program's interner, while the error_name may come from a different
/// interner (e.g., when compiling module code).
pub(crate) fn fallible_error_tag(
    fallible: &crate::sema::types::FallibleType,
    error_name: Symbol,
    interner: &Interner,
) -> Option<i64> {
    let error_name_str = interner.resolve(error_name);
    match fallible.error_type.as_ref() {
        Type::ErrorType(info) => {
            let info_name_str = interner.resolve(info.name);
            if info_name_str == error_name_str {
                Some(1) // Single error type always gets tag 1
            } else {
                None
            }
        }
        Type::Union(variants) => {
            // Find the 1-based index of the error type in the union
            for (idx, variant) in variants.iter().enumerate() {
                if let Type::ErrorType(info) = variant {
                    let info_name_str = interner.resolve(info.name);
                    if info_name_str == error_name_str {
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
        types::I8 => Type::I8,
        types::I16 => Type::I16,
        types::I32 => Type::I32,
        types::I64 => Type::I64,
        types::I128 => Type::I128,
        types::F32 => Type::F32,
        types::F64 => Type::F64,
        _ => Type::Unknown, // Pointer types, etc. stay Unknown for now
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
        Type::F64 => builder
            .ins()
            .bitcast(types::I64, MemFlags::new(), value.value),
        Type::F32 => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            builder.ins().uextend(word_type, i32_val)
        }
        Type::Bool => builder.ins().uextend(word_type, value.value),
        Type::I8 | Type::U8 => builder.ins().uextend(word_type, value.value),
        Type::I16 | Type::U16 => builder.ins().uextend(word_type, value.value),
        Type::I32 | Type::U32 => builder.ins().uextend(word_type, value.value),
        Type::I64 | Type::U64 => value.value,
        Type::I128 => {
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
        Type::F64 => builder.ins().bitcast(types::F64, MemFlags::new(), word),
        Type::F32 => {
            let i32_val = builder.ins().ireduce(types::I32, word);
            builder.ins().bitcast(types::F32, MemFlags::new(), i32_val)
        }
        Type::Bool => builder.ins().ireduce(types::I8, word),
        Type::I8 | Type::U8 => builder.ins().ireduce(types::I8, word),
        Type::I16 | Type::U16 => builder.ins().ireduce(types::I16, word),
        Type::I32 | Type::U32 => builder.ins().ireduce(types::I32, word),
        Type::I64 | Type::U64 => word,
        Type::I128 => {
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
        Type::String => 1,
        Type::I64 | Type::I32 | Type::I16 | Type::I8 => 2,
        Type::F64 | Type::F32 => 3,
        Type::Bool => 4,
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
