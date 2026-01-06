// src/codegen/types.rs
//
// Type-related utilities for code generation.
// This module contains shared type utilities used throughout the codegen module.

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::FuncId;
use std::collections::HashMap;

use crate::frontend::{Interner, LetStmt, NodeId, Symbol, TypeExpr};
use crate::runtime::NativeRegistry;
use crate::runtime::native_registry::NativeType;
use crate::sema::interface_registry::InterfaceRegistry;
use crate::sema::resolution::MethodResolutions;
use crate::sema::{ErrorTypeInfo, FunctionType, Type};

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
    /// Map from field name to slot index
    pub field_slots: HashMap<Symbol, usize>,
    /// Whether this is a class (true) or record (false)
    #[allow(dead_code)]
    pub is_class: bool,
    /// The Vole type (Class or Record)
    pub vole_type: Type,
    /// Method return types: method name -> return type
    pub method_return_types: HashMap<Symbol, Type>,
}

/// Context for compiling expressions and statements
/// Bundles common parameters to reduce function argument count
pub(crate) struct CompileCtx<'a> {
    pub interner: &'a Interner,
    pub pointer_type: types::Type,
    pub module: &'a mut JITModule,
    pub func_ids: &'a mut HashMap<String, FuncId>,
    pub source_file_ptr: (*const u8, usize),
    /// Global variable declarations for lookup when identifier not in local scope
    pub globals: &'a [LetStmt],
    /// Counter for generating unique lambda names
    pub lambda_counter: &'a mut usize,
    /// Type aliases from semantic analysis
    pub type_aliases: &'a HashMap<Symbol, Type>,
    /// Class and record metadata for struct literals, field access, and method calls
    pub type_metadata: &'a HashMap<Symbol, TypeMetadata>,
    /// Expression types from semantic analysis (includes narrowed types)
    pub expr_types: &'a HashMap<NodeId, Type>,
    /// Resolved method calls from semantic analysis
    pub method_resolutions: &'a MethodResolutions,
    /// Return types of compiled functions
    pub func_return_types: &'a HashMap<String, Type>,
    /// Interface definitions registry
    pub interface_registry: &'a InterfaceRegistry,
    /// Current function's return type (needed for raise statements in fallible functions)
    pub current_function_return_type: Option<Type>,
    /// Error type definitions from semantic analysis
    pub error_types: &'a HashMap<Symbol, ErrorTypeInfo>,
    /// Registry of native functions for external method calls
    pub native_registry: &'a NativeRegistry,
    /// Current module path when compiling module code (e.g., "std:math")
    /// None when compiling main program code
    pub current_module: Option<&'a str>,
}

/// Resolve a type expression to a Vole Type (uses CompileCtx for full context)
pub(crate) fn resolve_type_expr(ty: &TypeExpr, ctx: &CompileCtx) -> Type {
    resolve_type_expr_with_metadata(
        ty,
        ctx.type_aliases,
        ctx.interface_registry,
        ctx.error_types,
        ctx.type_metadata,
        ctx.interner,
    )
}

/// Resolve a type expression using aliases, interface registry, error types, and type metadata
/// This is the full resolution function that handles all named types including classes/records
pub(crate) fn resolve_type_expr_with_metadata(
    ty: &TypeExpr,
    type_aliases: &HashMap<Symbol, Type>,
    interface_registry: &InterfaceRegistry,
    error_types: &HashMap<Symbol, ErrorTypeInfo>,
    type_metadata: &HashMap<Symbol, TypeMetadata>,
    interner: &Interner,
) -> Type {
    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Look up type alias first
            if let Some(aliased) = type_aliases.get(sym) {
                aliased.clone()
            } else if let Some(iface) = interface_registry.get(*sym, interner) {
                // Check interface registry
                Type::Interface(crate::sema::types::InterfaceType {
                    name: *sym,
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
            );
            Type::Array(Box::new(elem_ty))
        }
        TypeExpr::Iterator(elem) => {
            let elem_ty = resolve_type_expr_with_metadata(
                elem,
                type_aliases,
                interface_registry,
                error_types,
                type_metadata,
                interner,
            );
            Type::Iterator(Box::new(elem_ty))
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
            );
            let error = resolve_type_expr_with_metadata(
                error_type,
                type_aliases,
                interface_registry,
                error_types,
                type_metadata,
                interner,
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
                    )
                })
                .collect();
            Type::GenericInstance {
                def: *name,
                args: resolved_args,
            }
        }
    }
}

/// Resolve a type expression using aliases and interface registry
/// This is used when CompileCtx is not available (e.g., during Compiler setup)
/// Note: This does NOT resolve class/record types from type_metadata - use resolve_type_expr for that
pub(crate) fn resolve_type_expr_full(
    ty: &TypeExpr,
    type_aliases: &HashMap<Symbol, Type>,
    interface_registry: &InterfaceRegistry,
    interner: &Interner,
) -> Type {
    // Use empty maps for backward compatibility
    let empty_error_types = HashMap::new();
    let empty_type_metadata = HashMap::new();
    resolve_type_expr_with_metadata(
        ty,
        type_aliases,
        interface_registry,
        &empty_error_types,
        &empty_type_metadata,
        interner,
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
        Type::Nil => types::I8,            // Nil uses minimal representation
        Type::Done => types::I8,           // Done uses minimal representation (like Nil)
        Type::Union(_) => pointer_type,    // Unions are passed by pointer
        Type::Fallible(_) => pointer_type, // Fallibles are passed by pointer (tagged union)
        Type::Function(_) => pointer_type, // Function pointers
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
        Type::Nil | Type::Done | Type::Void => 0,
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
pub(crate) fn fallible_error_tag(
    fallible: &crate::sema::types::FallibleType,
    error_name: Symbol,
) -> Option<i64> {
    match fallible.error_type.as_ref() {
        Type::ErrorType(info) => {
            if info.name == error_name {
                Some(1) // Single error type always gets tag 1
            } else {
                None
            }
        }
        Type::Union(variants) => {
            // Find the 1-based index of the error type in the union
            for (idx, variant) in variants.iter().enumerate() {
                if let Type::ErrorType(info) = variant
                    && info.name == error_name
                {
                    return Some((idx + 1) as i64);
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
