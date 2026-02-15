// src/codegen/function_registry.rs
//
// Opaque function identity registry for codegen.

use std::rc::Rc;

use rustc_hash::FxHashMap;

use cranelift_module::FuncId;

use crate::runtime_registry::RuntimeKey;
use vole_identity::{ModuleId, NameId, NameTable};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionKey(u32);

#[derive(Debug, Clone)]
enum FunctionName {
    Qualified(NameId),
    Runtime(RuntimeKey),
    Lambda(usize),
    Test(usize),
}

use vole_sema::type_arena::TypeId;

#[derive(Debug, Clone)]
struct FunctionEntry {
    name: FunctionName,
    func_id: Option<FuncId>,
    return_type: Option<TypeId>,
}

pub struct FunctionRegistry {
    names: Rc<NameTable>,
    entries: Vec<FunctionEntry>,
    qualified_lookup: FxHashMap<NameId, FunctionKey>,
    runtime_lookup: FxHashMap<RuntimeKey, FunctionKey>,
    /// Counter for unique string data names in JIT module
    string_data_counter: u32,
}

impl FunctionRegistry {
    pub fn new(names: Rc<NameTable>) -> Self {
        Self {
            names,
            entries: Vec::new(),
            qualified_lookup: FxHashMap::default(),
            runtime_lookup: FxHashMap::default(),
            string_data_counter: 0,
        }
    }

    pub fn main_module(&self) -> ModuleId {
        self.names.main_module()
    }

    pub fn intern_name_id(&mut self, name_id: NameId) -> FunctionKey {
        if let Some(key) = self.qualified_lookup.get(&name_id) {
            return *key;
        }
        let key = self.insert(FunctionName::Qualified(name_id));
        self.qualified_lookup.insert(name_id, key);
        key
    }

    pub fn intern_runtime(&mut self, runtime: RuntimeKey) -> FunctionKey {
        if let Some(key) = self.runtime_lookup.get(&runtime) {
            return *key;
        }
        let key = self.insert(FunctionName::Runtime(runtime));
        self.runtime_lookup.insert(runtime, key);
        key
    }

    pub fn intern_lambda(&mut self, index: usize) -> FunctionKey {
        self.insert(FunctionName::Lambda(index))
    }

    pub fn intern_test(&mut self, index: usize) -> FunctionKey {
        self.insert(FunctionName::Test(index))
    }

    pub fn set_func_id(&mut self, key: FunctionKey, func_id: FuncId) {
        if let Some(entry) = self.entries.get_mut(key.0 as usize) {
            entry.func_id = Some(func_id);
        }
    }

    pub fn func_id(&self, key: FunctionKey) -> Option<FuncId> {
        self.entries.get(key.0 as usize)?.func_id
    }

    pub fn set_return_type(&mut self, key: FunctionKey, ty: TypeId) {
        if let Some(entry) = self.entries.get_mut(key.0 as usize) {
            entry.return_type = Some(ty);
        }
    }

    pub fn return_type(&self, key: FunctionKey) -> Option<TypeId> {
        self.entries.get(key.0 as usize)?.return_type
    }

    pub fn display(&self, key: FunctionKey) -> String {
        match &self.entries[key.0 as usize].name {
            FunctionName::Qualified(name_id) => self.names.display(*name_id),
            FunctionName::Runtime(runtime) => runtime.name().to_string(),
            FunctionName::Lambda(idx) => format!("__lambda_{idx}"),
            FunctionName::Test(idx) => format!("__test_{idx}"),
        }
    }

    pub fn runtime_key(&self, runtime: RuntimeKey) -> Option<FunctionKey> {
        self.runtime_lookup.get(&runtime).copied()
    }

    /// Check if a runtime function is registered and has a compiled func_id
    #[must_use]
    pub fn has_runtime(&self, runtime: RuntimeKey) -> bool {
        self.runtime_key(runtime)
            .and_then(|key| self.func_id(key))
            .is_some()
    }

    fn insert(&mut self, name: FunctionName) -> FunctionKey {
        let key = FunctionKey(self.entries.len() as u32);
        self.entries.push(FunctionEntry {
            name,
            func_id: None,
            return_type: None,
        });
        key
    }

    /// Generate a unique name for string data in the JIT module.
    pub fn next_string_data_name(&mut self) -> String {
        let id = self.string_data_counter;
        self.string_data_counter += 1;
        format!("__vole_string_data_{id}")
    }
}
