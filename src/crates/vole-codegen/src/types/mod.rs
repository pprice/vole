// types/mod.rs
//
// Type-related utilities for code generation.
// This module contains shared type utilities used throughout the codegen module.

mod codegen_ctx;
mod codegen_state;
mod compile_env;
mod conversions;
mod function_ctx;
pub(crate) mod vir_conversions;
pub(crate) mod vir_struct_helpers;
pub(crate) mod wide_ops;

// Re-export all public types and functions
pub use codegen_ctx::{CodegenCtx, PendingMonomorph};
pub(crate) use codegen_state::{
    CodegenState, ExpandedClassMethodInfo, MonomorphIndexEntry, TypeMetadataMap,
};
pub use compile_env::{CompileEnv, ModuleExportBinding};

// Re-export conversion types and functions
pub use conversions::{CompiledValue, RcLifecycle};
pub(crate) use conversions::{
    FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, MethodInfo, TypeMetadata, convert_to_type,
    field_slot_count, load_fallible_payload, load_fallible_tag, method_name_id_by_str,
    module_name_id, native_type_to_cranelift, type_metadata_by_name_id,
};
// Re-exported for tests (rc_state.rs uses crate::types::{tuple_layout_id, type_id_size})
#[allow(unused_imports)]
pub(crate) use conversions::tuple_layout_id;
#[allow(unused_imports)]
pub(crate) use conversions::type_id_size;

// VirTypeTable-based conversion functions are in types::vir_conversions.
// Callers import directly from the submodule as needed.
