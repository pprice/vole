// analyzed.rs
//! Codegen-local helper types for method binding and external dispatch.

use vole_identity::NameId;

/// Codegen-local external binding payload from implement-registry lookups.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ExternalMethodInfoRef {
    pub module_path: NameId,
    pub native_name: NameId,
}

impl From<vole_vir::VirExternalMethodInfo> for ExternalMethodInfoRef {
    fn from(value: vole_vir::VirExternalMethodInfo) -> Self {
        Self {
            module_path: value.module_path,
            native_name: value.native_name,
        }
    }
}

impl From<vole_identity::ExternalMethodInfo> for ExternalMethodInfoRef {
    fn from(value: vole_identity::ExternalMethodInfo) -> Self {
        Self {
            module_path: value.module_path,
            native_name: value.native_name,
        }
    }
}
