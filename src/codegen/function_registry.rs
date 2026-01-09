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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeFn {
    StringNew,
    StringConcat,
    StringEq,
    StringLen,
    PrintlnString,
    PrintlnI64,
    PrintlnF64,
    PrintlnBool,
    PrintString,
    PrintI64,
    PrintF64,
    PrintBool,
    PrintChar,
    I64ToString,
    F64ToString,
    BoolToString,
    Flush,
    AssertFail,
    ArrayNew,
    ArrayPush,
    ArrayGetValue,
    ArrayLen,
    ArrayIter,
    ArrayIterNext,
    ArrayIterCollect,
    ArraySet,
    MapIter,
    MapIterNext,
    MapIterCollect,
    FilterIter,
    FilterIterNext,
    FilterIterCollect,
    TakeIter,
    TakeIterNext,
    TakeIterCollect,
    SkipIter,
    SkipIterNext,
    SkipIterCollect,
    IterCount,
    IterSum,
    IterForEach,
    IterReduce,
    IterFirst,
    IterLast,
    IterNth,
    RangeIter,
    StringCharsIter,
    ClosureAlloc,
    ClosureSetCapture,
    ClosureGetCapture,
    ClosureGetFunc,
    HeapAlloc,
    InstanceNew,
    InstanceGetField,
    InstanceSetField,
}

impl RuntimeFn {
    pub const ALL: &'static [RuntimeFn] = &[
        RuntimeFn::StringNew,
        RuntimeFn::StringConcat,
        RuntimeFn::StringEq,
        RuntimeFn::StringLen,
        RuntimeFn::PrintlnString,
        RuntimeFn::PrintlnI64,
        RuntimeFn::PrintlnF64,
        RuntimeFn::PrintlnBool,
        RuntimeFn::PrintString,
        RuntimeFn::PrintI64,
        RuntimeFn::PrintF64,
        RuntimeFn::PrintBool,
        RuntimeFn::PrintChar,
        RuntimeFn::I64ToString,
        RuntimeFn::F64ToString,
        RuntimeFn::BoolToString,
        RuntimeFn::Flush,
        RuntimeFn::AssertFail,
        RuntimeFn::ArrayNew,
        RuntimeFn::ArrayPush,
        RuntimeFn::ArrayGetValue,
        RuntimeFn::ArrayLen,
        RuntimeFn::ArrayIter,
        RuntimeFn::ArrayIterNext,
        RuntimeFn::ArrayIterCollect,
        RuntimeFn::ArraySet,
        RuntimeFn::MapIter,
        RuntimeFn::MapIterNext,
        RuntimeFn::MapIterCollect,
        RuntimeFn::FilterIter,
        RuntimeFn::FilterIterNext,
        RuntimeFn::FilterIterCollect,
        RuntimeFn::TakeIter,
        RuntimeFn::TakeIterNext,
        RuntimeFn::TakeIterCollect,
        RuntimeFn::SkipIter,
        RuntimeFn::SkipIterNext,
        RuntimeFn::SkipIterCollect,
        RuntimeFn::IterCount,
        RuntimeFn::IterSum,
        RuntimeFn::IterForEach,
        RuntimeFn::IterReduce,
        RuntimeFn::IterFirst,
        RuntimeFn::IterLast,
        RuntimeFn::IterNth,
        RuntimeFn::RangeIter,
        RuntimeFn::StringCharsIter,
        RuntimeFn::ClosureAlloc,
        RuntimeFn::ClosureSetCapture,
        RuntimeFn::ClosureGetCapture,
        RuntimeFn::ClosureGetFunc,
        RuntimeFn::HeapAlloc,
        RuntimeFn::InstanceNew,
        RuntimeFn::InstanceGetField,
        RuntimeFn::InstanceSetField,
    ];

    pub fn name(self) -> &'static str {
        match self {
            RuntimeFn::StringNew => "vole_string_new",
            RuntimeFn::StringConcat => "vole_string_concat",
            RuntimeFn::StringEq => "vole_string_eq",
            RuntimeFn::StringLen => "vole_string_len",
            RuntimeFn::PrintlnString => "vole_println_string",
            RuntimeFn::PrintlnI64 => "vole_println_i64",
            RuntimeFn::PrintlnF64 => "vole_println_f64",
            RuntimeFn::PrintlnBool => "vole_println_bool",
            RuntimeFn::PrintString => "vole_print_string",
            RuntimeFn::PrintI64 => "vole_print_i64",
            RuntimeFn::PrintF64 => "vole_print_f64",
            RuntimeFn::PrintBool => "vole_print_bool",
            RuntimeFn::PrintChar => "vole_print_char",
            RuntimeFn::I64ToString => "vole_i64_to_string",
            RuntimeFn::F64ToString => "vole_f64_to_string",
            RuntimeFn::BoolToString => "vole_bool_to_string",
            RuntimeFn::Flush => "vole_flush",
            RuntimeFn::AssertFail => "vole_assert_fail",
            RuntimeFn::ArrayNew => "vole_array_new",
            RuntimeFn::ArrayPush => "vole_array_push",
            RuntimeFn::ArrayGetValue => "vole_array_get_value",
            RuntimeFn::ArrayLen => "vole_array_len",
            RuntimeFn::ArrayIter => "vole_array_iter",
            RuntimeFn::ArrayIterNext => "vole_array_iter_next",
            RuntimeFn::ArrayIterCollect => "vole_array_iter_collect",
            RuntimeFn::ArraySet => "vole_array_set",
            RuntimeFn::MapIter => "vole_map_iter",
            RuntimeFn::MapIterNext => "vole_map_iter_next",
            RuntimeFn::MapIterCollect => "vole_map_iter_collect",
            RuntimeFn::FilterIter => "vole_filter_iter",
            RuntimeFn::FilterIterNext => "vole_filter_iter_next",
            RuntimeFn::FilterIterCollect => "vole_filter_iter_collect",
            RuntimeFn::TakeIter => "vole_take_iter",
            RuntimeFn::TakeIterNext => "vole_take_iter_next",
            RuntimeFn::TakeIterCollect => "vole_take_iter_collect",
            RuntimeFn::SkipIter => "vole_skip_iter",
            RuntimeFn::SkipIterNext => "vole_skip_iter_next",
            RuntimeFn::SkipIterCollect => "vole_skip_iter_collect",
            RuntimeFn::IterCount => "vole_iter_count",
            RuntimeFn::IterSum => "vole_iter_sum",
            RuntimeFn::IterForEach => "vole_iter_for_each",
            RuntimeFn::IterReduce => "vole_iter_reduce",
            RuntimeFn::IterFirst => "vole_iter_first",
            RuntimeFn::IterLast => "vole_iter_last",
            RuntimeFn::IterNth => "vole_iter_nth",
            RuntimeFn::RangeIter => "vole_range_iter",
            RuntimeFn::StringCharsIter => "vole_string_chars_iter",
            RuntimeFn::ClosureAlloc => "vole_closure_alloc",
            RuntimeFn::ClosureSetCapture => "vole_closure_set_capture",
            RuntimeFn::ClosureGetCapture => "vole_closure_get_capture",
            RuntimeFn::ClosureGetFunc => "vole_closure_get_func",
            RuntimeFn::HeapAlloc => "vole_heap_alloc",
            RuntimeFn::InstanceNew => "vole_instance_new",
            RuntimeFn::InstanceGetField => "vole_instance_get_field",
            RuntimeFn::InstanceSetField => "vole_instance_set_field",
        }
    }
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

    pub fn intern_qualified(&mut self, module: ModuleId, segments: &[Symbol]) -> FunctionKey {
        let name_id = self.names.intern(module, segments);
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

    pub fn intern_with_prefix(&mut self, prefix: NameId, segment: Symbol) -> FunctionKey {
        let name_id = self.names.intern_with_symbol(prefix, segment);
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

    pub fn display(&self, key: FunctionKey, interner: &Interner) -> String {
        match &self.entries[key.0 as usize].name {
            FunctionName::Qualified(name_id) => self.names.display(*name_id, interner),
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
