// calls.rs
//
// Call target descriptors for VIR function calls.

use vole_identity::FunctionId;

/// The target of a function or method call in VIR.
///
/// Codegen uses this to select the correct calling convention and linkage.
#[derive(Debug, Clone)]
pub enum CallTarget {
    /// A direct call to a known function.
    Direct { function_id: FunctionId },
}
