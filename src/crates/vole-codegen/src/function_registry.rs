// src/codegen/function_registry.rs
//
// Opaque function identity registry for codegen.

use std::rc::Rc;

use rustc_hash::FxHashMap;

use cranelift_module::FuncId;

use vole_identity::{ModuleId, NameId, NameTable};

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
    I128ToString => "vole_i128_to_string",
    F64ToString => "vole_f64_to_string",
    F32ToString => "vole_f32_to_string",
    BoolToString => "vole_bool_to_string",
    NilToString => "vole_nil_to_string",
    ArrayI64ToString => "vole_array_i64_to_string",
    Flush => "vole_flush",
    AssertFail => "vole_assert_fail",
    Panic => "vole_panic",
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
    IterReduceTagged => "vole_iter_reduce_tagged",
    IterSetElemTag => "vole_iter_set_elem_tag",
    IterSetProducesOwned => "vole_iter_set_produces_owned",
    IterFirst => "vole_iter_first",
    IterLast => "vole_iter_last",
    IterNth => "vole_iter_nth",
    RangeIter => "vole_range_iter",
    StringCharsIter => "vole_string_chars_iter",
    ClosureAlloc => "vole_closure_alloc",
    ClosureSetCapture => "vole_closure_set_capture",
    ClosureSetCaptureKind => "vole_closure_set_capture_kind",
    ClosureGetCapture => "vole_closure_get_capture",
    ClosureGetFunc => "vole_closure_get_func",
    HeapAlloc => "vole_heap_alloc",
    InstanceNew => "vole_instance_new",
    InstanceGetField => "vole_instance_get_field",
    InstanceSetField => "vole_instance_set_field",
    SbNew => "vole_sb_new",
    SbPushString => "vole_sb_push_string",
    SbFinish => "vole_sb_finish",
    RcInc => "rc_inc",
    RcDec => "rc_dec",
}

#[derive(Debug, Clone)]
enum FunctionName {
    Qualified(NameId),
    Runtime(RuntimeFn),
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
    runtime_lookup: FxHashMap<RuntimeFn, FunctionKey>,
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

    pub fn builtin_module(&self) -> ModuleId {
        self.names
            .builtin_module_id()
            .unwrap_or_else(|| self.names.main_module())
    }

    pub fn intern_name_id(&mut self, name_id: NameId) -> FunctionKey {
        if let Some(key) = self.qualified_lookup.get(&name_id) {
            return *key;
        }
        let key = self.insert(FunctionName::Qualified(name_id));
        self.qualified_lookup.insert(name_id, key);
        key
    }

    pub fn intern_runtime(&mut self, runtime: RuntimeFn) -> FunctionKey {
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

    pub fn name_for_qualified(&self, key: FunctionKey) -> Option<NameId> {
        match &self.entries[key.0 as usize].name {
            FunctionName::Qualified(name_id) => Some(*name_id),
            FunctionName::Runtime(_) | FunctionName::Lambda(_) | FunctionName::Test(_) => None,
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

    pub fn name_table_rc(&self) -> &Rc<NameTable> {
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

    /// Generate a unique name for string data in the JIT module.
    pub fn next_string_data_name(&mut self) -> String {
        let id = self.string_data_counter;
        self.string_data_counter += 1;
        format!("__vole_string_data_{id}")
    }
}
