// types/mod.rs
//
// Type-related utilities for code generation.
// This module contains shared type utilities used throughout the codegen module.

mod codegen_ctx;
mod codegen_state;
mod compile_env;
mod conversions;
mod function_ctx;
mod type_ctx;

// Re-export all public types and functions
pub use codegen_ctx::CodegenCtx;
pub use codegen_state::{CodegenState, TypeMetadataMap};
pub use compile_env::CompileEnv;
pub use function_ctx::FunctionCtx;
pub use type_ctx::TypeCtx;

// Re-export conversion types and functions
pub use conversions::CompiledValue;
pub(crate) use conversions::{
    FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, FALLIBLE_TAG_OFFSET, MethodInfo, TypeMetadata,
    array_element_tag_id, convert_to_type, fallible_error_tag_by_id,
    function_name_id_with_interner, load_fallible_payload, load_fallible_tag,
    method_name_id_by_str, method_name_id_with_interner, module_name_id, native_type_to_cranelift,
    resolve_type_expr_to_id, resolve_type_expr_with_ctx, tuple_layout_id, type_id_size,
    type_id_to_cranelift, type_metadata_by_name_id, value_to_word, word_to_value_type_id,
};
