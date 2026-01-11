// src/codegen/function_registry.rs
//
// Opaque function identity registry for codegen.

use std::collections::HashMap;

use cranelift_module::FuncId;

use crate::frontend::{Interner, Symbol};
use crate::identity::{ModuleId, NameId, NameTable};
use crate::sema::Type;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionKey(u32);

/// Macro for defining runtime functions with a single source of truth.
/// Each entry defines the enum variant and its corresponding C function name.
macro_rules! runtime_fns {
    ($($variant:ident => $name:literal),* $(,)?) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum RuntimeFn {
            $($variant),*
        }

        impl RuntimeFn {
            pub const ALL: &'static [RuntimeFn] = &[
                $(RuntimeFn::$variant),*
            ];

            pub fn name(self) -> &'static str {
                match self {
                    $(RuntimeFn::$variant => $name),*
                }
            }
        }
    };
}

runtime_fns! {
    StringNew => "vole_string_new",
    StringConcat => "vole_string_concat",
    StringEq => "vole_string_eq",
    StringLen => "vole_string_len",
    PrintlnString => "vole_println_string",
    PrintlnI64 => "vole_println_i64",
    PrintlnF64 => "vole_println_f64",
    PrintlnBool => "vole_println_bool",
    PrintString => "vole_print_string",
    PrintI64 => "vole_print_i64",
    PrintF64 => "vole_print_f64",
    PrintBool => "vole_print_bool",
    PrintChar => "vole_print_char",
    I64ToString => "vole_i64_to_string",
    F64ToString => "vole_f64_to_string",
    BoolToString => "vole_bool_to_string",
    NilToString => "vole_nil_to_string",
    ArrayI64ToString => "vole_array_i64_to_string",
    Flush => "vole_flush",
    AssertFail => "vole_assert_fail",
    ArrayNew => "vole_array_new",
    ArrayPush => "vole_array_push",
    ArrayGetValue => "vole_array_get_value",
    ArrayLen => "vole_array_len",
    ArrayIter => "vole_array_iter",
    ArrayIterNext => "vole_array_iter_next",
    ArrayIterCollect => "vole_array_iter_collect",
    ArraySet => "vole_array_set",
    MapIter => "vole_map_iter",
    MapIterNext => "vole_map_iter_next",
    MapIterCollect => "vole_map_iter_collect",
    FilterIter => "vole_filter_iter",
    FilterIterNext => "vole_filter_iter_next",
    FilterIterCollect => "vole_filter_iter_collect",
    TakeIter => "vole_take_iter",
    TakeIterNext => "vole_take_iter_next",
    TakeIterCollect => "vole_take_iter_collect",
    SkipIter => "vole_skip_iter",
    SkipIterNext => "vole_skip_iter_next",
    SkipIterCollect => "vole_skip_iter_collect",
    IterCount => "vole_iter_count",
    IterSum => "vole_iter_sum",
    IterForEach => "vole_iter_for_each",
    IterReduce => "vole_iter_reduce",
    IterFirst => "vole_iter_first",
    IterLast => "vole_iter_last",
    IterNth => "vole_iter_nth",
    RangeIter => "vole_range_iter",
    StringCharsIter => "vole_string_chars_iter",
    ClosureAlloc => "vole_closure_alloc",
    ClosureSetCapture => "vole_closure_set_capture",
    ClosureGetCapture => "vole_closure_get_capture",
    ClosureGetFunc => "vole_closure_get_func",
    HeapAlloc => "vole_heap_alloc",
    InstanceNew => "vole_instance_new",
    InstanceGetField => "vole_instance_get_field",
    InstanceSetField => "vole_instance_set_field",
}

#[derive(Debug, Clone)]
enum FunctionName {
    Qualified(NameId),
    Runtime(RuntimeFn),
}

#[derive(Debug, Clone)]
struct FunctionEntry {
    name: FunctionName,
    func_id: Option<FuncId>,
    return_type: Option<Type>,
}

pub struct FunctionRegistry {
    names: NameTable,
    entries: Vec<FunctionEntry>,
    qualified_lookup: HashMap<NameId, FunctionKey>,
    runtime_lookup: HashMap<RuntimeFn, FunctionKey>,
}

impl FunctionRegistry {
    pub fn new(names: NameTable) -> Self {
        Self {
            names,
            entries: Vec::new(),
            qualified_lookup: HashMap::new(),
            runtime_lookup: HashMap::new(),
        }
    }

    pub fn main_module(&self) -> ModuleId {
        self.names.main_module()
    }

    pub fn builtin_module(&self) -> ModuleId {
        self.names
            .builtin_module_id()
            .unwrap_or_else(|| self.names.main_module())
    }

    pub fn module_id(&mut self, path: &str) -> ModuleId {
        self.names.module_id(path)
    }

    pub fn intern_qualified(
        &mut self,
        module: ModuleId,
        segments: &[Symbol],
        interner: &Interner,
    ) -> FunctionKey {
        let name_id = self.names.intern(module, segments, interner);
        self.intern_name_id(name_id)
    }

    pub fn intern_name_id(&mut self, name_id: NameId) -> FunctionKey {
        if let Some(key) = self.qualified_lookup.get(&name_id) {
            return *key;
        }
        let key = self.insert(FunctionName::Qualified(name_id));
        self.qualified_lookup.insert(name_id, key);
        key
    }

    pub fn intern_with_prefix(
        &mut self,
        prefix: NameId,
        segment: Symbol,
        interner: &Interner,
    ) -> FunctionKey {
        let name_id = self.names.intern_with_symbol(prefix, segment, interner);
        self.intern_name_id(name_id)
    }

    pub fn intern_raw_qualified(&mut self, module: ModuleId, segments: &[&str]) -> FunctionKey {
        let name_id = self.names.intern_raw(module, segments);
        self.intern_name_id(name_id)
    }

    pub fn intern_runtime(&mut self, runtime: RuntimeFn) -> FunctionKey {
        if let Some(key) = self.runtime_lookup.get(&runtime) {
            return *key;
        }
        let key = self.insert(FunctionName::Runtime(runtime));
        self.runtime_lookup.insert(runtime, key);
        key
    }

    pub fn intern_test_name(&mut self, index: usize) -> (NameId, FunctionKey) {
        let name_id = self
            .names
            .intern_indexed_raw(self.builtin_module(), "__test_", index);
        let key = self.intern_name_id(name_id);
        let name_id = self
            .name_for_qualified(key)
            .expect("test function name_id should be available");
        (name_id, key)
    }

    pub fn intern_lambda_name(&mut self, index: usize) -> (NameId, FunctionKey) {
        let name_id = self
            .names
            .intern_indexed_raw(self.builtin_module(), "__lambda_", index);
        let key = self.intern_name_id(name_id);
        let name_id = self
            .name_for_qualified(key)
            .expect("lambda name_id should be available");
        (name_id, key)
    }

    pub fn set_func_id(&mut self, key: FunctionKey, func_id: FuncId) {
        if let Some(entry) = self.entries.get_mut(key.0 as usize) {
            entry.func_id = Some(func_id);
        }
    }

    pub fn func_id(&self, key: FunctionKey) -> Option<FuncId> {
        self.entries.get(key.0 as usize)?.func_id
    }

    pub fn set_return_type(&mut self, key: FunctionKey, ty: Type) {
        if let Some(entry) = self.entries.get_mut(key.0 as usize) {
            entry.return_type = Some(ty);
        }
    }

    pub fn return_type(&self, key: FunctionKey) -> Option<&Type> {
        self.entries.get(key.0 as usize)?.return_type.as_ref()
    }

    pub fn display(&self, key: FunctionKey) -> String {
        match &self.entries[key.0 as usize].name {
            FunctionName::Qualified(name_id) => self.names.display(*name_id),
            FunctionName::Runtime(runtime) => runtime.name().to_string(),
        }
    }

    pub fn name_for_qualified(&self, key: FunctionKey) -> Option<NameId> {
        match &self.entries[key.0 as usize].name {
            FunctionName::Qualified(name_id) => Some(*name_id),
            FunctionName::Runtime(_) => None,
        }
    }

    pub fn runtime_key(&self, runtime: RuntimeFn) -> Option<FunctionKey> {
        self.runtime_lookup.get(&runtime).copied()
    }

    /// Check if a runtime function is registered and has a compiled func_id
    #[must_use]
    pub fn has_runtime(&self, runtime: RuntimeFn) -> bool {
        self.runtime_key(runtime)
            .and_then(|key| self.func_id(key))
            .is_some()
    }

    pub fn name_table(&self) -> &NameTable {
        &self.names
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
}
