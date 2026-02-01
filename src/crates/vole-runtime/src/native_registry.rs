// src/runtime/native_registry.rs
//! Registry for native functions callable from Vole via external blocks.

use rustc_hash::FxHashMap;

/// Type representation for native function signatures
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeType {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    String,
    Handle,
    Nil,
    Optional(Box<NativeType>),
    Array(Box<NativeType>),
    /// A C-ABI struct with a known number of i64-sized fields.
    /// Small structs (1-2 fields) are returned in registers (RAX+RDX).
    /// Large structs (3+ fields) use sret (caller-allocated buffer).
    Struct {
        field_count: usize,
    },
}

/// Signature of a native function
#[derive(Debug, Clone)]
pub struct NativeSignature {
    pub params: Vec<NativeType>,
    pub return_type: NativeType,
}

/// A registered native function
#[derive(Clone)]
pub struct NativeFunction {
    pub ptr: *const u8,
    pub signature: NativeSignature,
}

// Safety: Function pointers are Send+Sync if they don't capture state
unsafe impl Send for NativeFunction {}
unsafe impl Sync for NativeFunction {}

impl std::fmt::Debug for NativeFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeFunction")
            .field("ptr", &self.ptr)
            .field("signature", &self.signature)
            .finish()
    }
}

/// A module containing native functions
#[derive(Debug, Default)]
pub struct NativeModule {
    functions: FxHashMap<String, NativeFunction>,
}

impl NativeModule {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, name: &str, ptr: *const u8, signature: NativeSignature) {
        self.functions
            .insert(name.to_string(), NativeFunction { ptr, signature });
    }

    pub fn get(&self, name: &str) -> Option<&NativeFunction> {
        self.functions.get(name)
    }

    pub fn function_names(&self) -> impl Iterator<Item = &str> {
        self.functions.keys().map(|s| s.as_str())
    }
}

/// Registry of all native modules
#[derive(Debug, Default)]
pub struct NativeRegistry {
    modules: FxHashMap<String, NativeModule>,
}

impl NativeRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register_module(&mut self, path: &str, module: NativeModule) {
        self.modules.insert(path.to_string(), module);
    }

    pub fn get_module(&self, path: &str) -> Option<&NativeModule> {
        self.modules.get(path)
    }

    pub fn lookup(&self, module_path: &str, func_name: &str) -> Option<&NativeFunction> {
        self.modules.get(module_path)?.get(func_name)
    }

    pub fn module_exists(&self, path: &str) -> bool {
        self.modules.contains_key(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    extern "C" fn dummy_fn() -> i64 {
        42
    }

    #[test]
    fn register_and_lookup() {
        let mut registry = NativeRegistry::new();
        let mut module = NativeModule::new();

        module.register(
            "test_func",
            dummy_fn as *const u8,
            NativeSignature {
                params: vec![],
                return_type: NativeType::I64,
            },
        );

        registry.register_module("test:module", module);

        let func = registry.lookup("test:module", "test_func");
        assert!(func.is_some());
        assert_eq!(func.unwrap().signature.return_type, NativeType::I64);
    }

    #[test]
    fn lookup_nonexistent() {
        let registry = NativeRegistry::new();
        assert!(registry.lookup("test:module", "missing").is_none());
    }

    #[test]
    fn register_struct_return_type() {
        let mut module = NativeModule::new();
        module.register(
            "make_pair",
            dummy_fn as *const u8,
            NativeSignature {
                params: vec![NativeType::I64, NativeType::I64],
                return_type: NativeType::Struct { field_count: 2 },
            },
        );

        let func = module.get("make_pair").unwrap();
        assert_eq!(
            func.signature.return_type,
            NativeType::Struct { field_count: 2 }
        );
        assert_eq!(func.signature.params.len(), 2);
    }

    #[test]
    fn register_large_struct_return_type() {
        let mut module = NativeModule::new();
        module.register(
            "make_quad",
            dummy_fn as *const u8,
            NativeSignature {
                params: vec![NativeType::I64; 4],
                return_type: NativeType::Struct { field_count: 4 },
            },
        );

        let func = module.get("make_quad").unwrap();
        assert_eq!(
            func.signature.return_type,
            NativeType::Struct { field_count: 4 }
        );
    }
}
