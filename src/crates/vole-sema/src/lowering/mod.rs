// lowering/mod.rs
//
// VIR lowering orchestration — walks the program AST to collect and lower
// functions, methods, default inits, tests, and metadata into VIR.
//
// Previously lived in vole-codegen as `analyzed_lower_*.rs` files; moved here
// because the orchestration only touches sema/frontend/VIR types with no
// codegen (Cranelift) dependency.

pub mod annotation_inits;
pub mod entity_metadata;
pub mod facade;
pub mod field_default_inits;
pub mod function_default_inits;
pub mod functions;
pub mod global_inits;
pub mod implement_blocks;
pub mod lambda_default_inits;
mod lambda_search;
pub mod method_default_inits;
pub mod module_bindings;
pub mod monomorph_functions;
pub mod monomorph_info;
pub mod test_bodies;
pub mod test_scoped_type_methods;
pub mod type_method_monomorph;
pub mod type_methods;
pub mod vir_monomorph;

// Re-export the main entry point.
pub use facade::{LowerVirProgramArgs, LowerVirProgramOutput, lower_vir_program};
