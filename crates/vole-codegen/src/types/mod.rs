// types/mod.rs
//
// Type-related utilities for code generation.
// This module contains shared type utilities used throughout the codegen module.

// Allow unused imports during migration - these will be used as CompileCtx is phased out
#![allow(unused_imports)]

mod codegen_ctx;
mod compile_ctx;
mod conversions;
mod function_ctx;
mod global_ctx;
mod type_ctx;

// Re-export all public types and functions for backward compatibility
pub use codegen_ctx::{CodegenCtx, JitCtx};
pub(crate) use compile_ctx::CompileCtx;
pub use global_ctx::GlobalCtx;
// Backward compatibility alias
pub use function_ctx::FunctionCtx;
pub use global_ctx::ExplicitParams;
pub use type_ctx::TypeCtx;

// Re-export conversion types and functions
pub use conversions::CompiledValue;
pub(crate) use conversions::{
    FALLIBLE_PAYLOAD_OFFSET,
    // Fallible type helpers
    FALLIBLE_SUCCESS_TAG,
    FALLIBLE_TAG_OFFSET,
    MethodInfo,
    TypeMetadata,
    array_element_tag_id,
    // Interface boxing re-export
    box_interface_value_id,
    convert_to_type,
    fallible_error_tag_by_id,
    fallible_error_tag_with_ctx,
    function_name_id_with_interner,
    load_fallible_payload,
    load_fallible_tag,
    method_name_id_by_str,
    method_name_id_with_interner,
    // Name resolution helpers
    module_name_id,
    native_type_to_cranelift,
    // Type resolution
    resolve_type_expr_id,
    resolve_type_expr_to_id,
    resolve_type_expr_with_ctx,
    tuple_layout_id,
    type_id_size,
    // Type conversion
    type_id_to_cranelift,
    type_metadata_by_name_id,
    // Word conversion
    value_to_word,
    value_to_word_with_ctx,
    word_to_value_type_id,
    word_to_value_with_ctx,
};
