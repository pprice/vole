// src/codegen/types.rs
//
// Type-related utilities for code generation.
// This module contains shared type utilities used throughout the codegen module.

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::FuncId;
use std::collections::HashMap;

use crate::frontend::{Interner, LetStmt, NodeId, Symbol, TypeExpr};
use crate::sema::interface_registry::InterfaceRegistry;
use crate::sema::resolution::MethodResolutions;
use crate::sema::{FunctionType, Type};

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
    #[allow(dead_code)] // Will be used in subsequent refactor tasks
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
}

/// Resolve a type expression to a Vole Type (uses CompileCtx for full context)
pub(crate) fn resolve_type_expr(ty: &TypeExpr, ctx: &CompileCtx) -> Type {
    resolve_type_expr_full(ty, ctx.type_aliases, ctx.interface_registry)
}

/// Resolve a type expression using aliases and interface registry
/// This is used when CompileCtx is not available (e.g., during Compiler setup)
pub(crate) fn resolve_type_expr_full(
    ty: &TypeExpr,
    type_aliases: &HashMap<Symbol, Type>,
    interface_registry: &InterfaceRegistry,
) -> Type {
    match ty {
        TypeExpr::Primitive(p) => Type::from_primitive(*p),
        TypeExpr::Named(sym) => {
            // Look up type alias first
            if let Some(aliased) = type_aliases.get(sym) {
                aliased.clone()
            } else if let Some(iface) = interface_registry.get(*sym) {
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
            } else {
                Type::Error
            }
        }
        TypeExpr::Array(elem) => {
            let elem_ty = resolve_type_expr_full(elem, type_aliases, interface_registry);
            Type::Array(Box::new(elem_ty))
        }
        TypeExpr::Optional(inner) => {
            // T? desugars to T | nil
            let inner_ty = resolve_type_expr_full(inner, type_aliases, interface_registry);
            Type::Union(vec![inner_ty, Type::Nil])
        }
        TypeExpr::Union(variants) => {
            let variant_types: Vec<Type> = variants
                .iter()
                .map(|v| resolve_type_expr_full(v, type_aliases, interface_registry))
                .collect();
            Type::normalize_union(variant_types)
        }
        TypeExpr::Nil => Type::Nil,
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_types: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_full(p, type_aliases, interface_registry))
                .collect();
            let ret_type = resolve_type_expr_full(return_type, type_aliases, interface_registry);
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
    }
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
        Type::Union(_) => pointer_type,    // Unions are passed by pointer
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
        Type::Nil | Type::Void => 0,
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
        _ => 8, // default
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
