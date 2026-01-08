// src/codegen/jit.rs

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use std::collections::HashMap;

/// JIT compiler context
pub struct JitContext {
    pub module: JITModule,
    pub ctx: codegen::Context,
    pub func_ids: HashMap<String, FuncId>,
    /// Source file path stored here so it lives as long as the JIT code.
    /// Used by assert failure messages.
    source_file: Option<Box<str>>,
}

impl JitContext {
    pub fn new() -> Self {
        // Build JIT module with native ISA
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();

        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("native ISA not available: {}", msg);
        });

        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();

        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        // Register runtime functions
        Self::register_runtime_symbols(&mut builder);

        let module = JITModule::new(builder);
        let ctx = module.make_context();

        let mut jit = Self {
            module,
            ctx,
            func_ids: HashMap::new(),
            source_file: None,
        };

        // Import runtime functions so they can be called
        jit.import_runtime_functions();

        jit
    }

    /// Import all runtime functions into the module
    fn import_runtime_functions(&mut self) {
        let ptr_ty = self.pointer_type();

        // vole_string_new(data: *const u8, len: usize) -> *mut RcString
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(ptr_ty));
        self.import_function("vole_string_new", &sig);

        // vole_string_concat(a: *const RcString, b: *const RcString) -> *mut RcString
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(ptr_ty));
        self.import_function("vole_string_concat", &sig);

        // vole_string_eq(a: *const RcString, b: *const RcString) -> i8 (0 or 1)
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I8));
        self.import_function("vole_string_eq", &sig);

        // vole_string_len(ptr: *const RcString) -> usize
        let sig = self.create_signature(&[ptr_ty], Some(types::I64));
        self.import_function("vole_string_len", &sig);

        // vole_println_string(ptr: *const RcString)
        let sig = self.create_signature(&[ptr_ty], None);
        self.import_function("vole_println_string", &sig);

        // vole_println_i64(value: i64)
        let sig = self.create_signature(&[types::I64], None);
        self.import_function("vole_println_i64", &sig);

        // vole_println_f64(value: f64)
        let sig = self.create_signature(&[types::F64], None);
        self.import_function("vole_println_f64", &sig);

        // vole_println_bool(value: i8)
        let sig = self.create_signature(&[types::I8], None);
        self.import_function("vole_println_bool", &sig);

        // vole_print_string(ptr: *const RcString)
        let sig = self.create_signature(&[ptr_ty], None);
        self.import_function("vole_print_string", &sig);

        // vole_print_i64(value: i64)
        let sig = self.create_signature(&[types::I64], None);
        self.import_function("vole_print_i64", &sig);

        // vole_print_f64(value: f64)
        let sig = self.create_signature(&[types::F64], None);
        self.import_function("vole_print_f64", &sig);

        // vole_print_bool(value: i8)
        let sig = self.create_signature(&[types::I8], None);
        self.import_function("vole_print_bool", &sig);

        // vole_print_char(c: u8)
        let sig = self.create_signature(&[types::I8], None);
        self.import_function("vole_print_char", &sig);

        // vole_i64_to_string(value: i64) -> *mut RcString
        let sig = self.create_signature(&[types::I64], Some(ptr_ty));
        self.import_function("vole_i64_to_string", &sig);

        // vole_f64_to_string(value: f64) -> *mut RcString
        let sig = self.create_signature(&[types::F64], Some(ptr_ty));
        self.import_function("vole_f64_to_string", &sig);

        // vole_bool_to_string(value: i8) -> *mut RcString
        let sig = self.create_signature(&[types::I8], Some(ptr_ty));
        self.import_function("vole_bool_to_string", &sig);

        // vole_flush()
        let sig = self.create_signature(&[], None);
        self.import_function("vole_flush", &sig);

        // vole_assert_fail(file_ptr: *const u8, file_len: usize, line: u32)
        let sig = self.create_signature(&[ptr_ty, types::I64, types::I32], None);
        self.import_function("vole_assert_fail", &sig);

        // vole_array_new() -> *mut RcArray
        let sig = self.create_signature(&[], Some(ptr_ty));
        self.import_function("vole_array_new", &sig);

        // vole_array_push(arr: *mut RcArray, tag: u64, value: u64)
        let sig = self.create_signature(&[ptr_ty, types::I64, types::I64], None);
        self.import_function("vole_array_push", &sig);

        // vole_array_get_value(arr: *const RcArray, index: usize) -> u64
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(types::I64));
        self.import_function("vole_array_get_value", &sig);

        // vole_array_len(arr: *const RcArray) -> usize
        let sig = self.create_signature(&[ptr_ty], Some(types::I64));
        self.import_function("vole_array_len", &sig);

        // vole_array_iter(arr: *const RcArray) -> *mut ArrayIterator
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_array_iter", &sig);

        // vole_array_iter_next(iter: *mut ArrayIterator, out_value: *mut i64) -> i64
        // Returns 1 if value available (stores in out_value), 0 if Done
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_array_iter_next", &sig);

        // vole_array_iter_collect(iter: *mut ArrayIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_array_iter_collect", &sig);

        // vole_map_iter(source: *mut ArrayIterator, transform: *const Closure) -> *mut MapIterator
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(ptr_ty));
        self.import_function("vole_map_iter", &sig);

        // vole_map_iter_next(iter: *mut MapIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_map_iter_next", &sig);

        // vole_map_iter_collect(iter: *mut MapIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_map_iter_collect", &sig);

        // vole_filter_iter(source: *mut UnifiedIterator, predicate: *const Closure) -> *mut FilterIterator
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(ptr_ty));
        self.import_function("vole_filter_iter", &sig);

        // vole_filter_iter_next(iter: *mut FilterIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_filter_iter_next", &sig);

        // vole_filter_iter_collect(iter: *mut FilterIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_filter_iter_collect", &sig);

        // vole_iter_count(iter: *mut UnifiedIterator) -> i64
        let sig = self.create_signature(&[ptr_ty], Some(types::I64));
        self.import_function("vole_iter_count", &sig);

        // vole_iter_sum(iter: *mut UnifiedIterator) -> i64
        let sig = self.create_signature(&[ptr_ty], Some(types::I64));
        self.import_function("vole_iter_sum", &sig);

        // vole_iter_for_each(iter: *mut UnifiedIterator, callback: *const Closure)
        let sig = self.create_signature(&[ptr_ty, ptr_ty], None);
        self.import_function("vole_iter_for_each", &sig);

        // vole_iter_reduce(iter: *mut UnifiedIterator, init: i64, reducer: *const Closure) -> i64
        let sig = self.create_signature(&[ptr_ty, types::I64, ptr_ty], Some(types::I64));
        self.import_function("vole_iter_reduce", &sig);

        // vole_take_iter(source: *mut UnifiedIterator, count: i64) -> *mut TakeIterator
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_take_iter", &sig);

        // vole_take_iter_next(iter: *mut TakeIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_take_iter_next", &sig);

        // vole_take_iter_collect(iter: *mut TakeIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_take_iter_collect", &sig);

        // vole_skip_iter(source: *mut UnifiedIterator, count: i64) -> *mut SkipIterator
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_skip_iter", &sig);

        // vole_skip_iter_next(iter: *mut SkipIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_skip_iter_next", &sig);

        // vole_skip_iter_collect(iter: *mut SkipIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_skip_iter_collect", &sig);

        // vole_array_set(arr: *mut RcArray, index: usize, tag: u64, value: u64)
        let sig = self.create_signature(&[ptr_ty, types::I64, types::I64, types::I64], None);
        self.import_function("vole_array_set", &sig);

        // Closure functions
        // vole_closure_alloc(func_ptr: *const u8, num_captures: usize) -> *mut Closure
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_closure_alloc", &sig);

        // vole_closure_get_capture(closure: *const Closure, index: usize) -> *mut u8
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_closure_get_capture", &sig);

        // vole_closure_set_capture(closure: *mut Closure, index: usize, ptr: *mut u8)
        let sig = self.create_signature(&[ptr_ty, types::I64, ptr_ty], None);
        self.import_function("vole_closure_set_capture", &sig);

        // vole_closure_get_func(closure: *const Closure) -> *const u8
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_closure_get_func", &sig);

        // vole_heap_alloc(size: usize) -> *mut u8
        let sig = self.create_signature(&[types::I64], Some(ptr_ty));
        self.import_function("vole_heap_alloc", &sig);

        // Instance functions (classes and records)
        // vole_instance_new(type_id: u32, field_count: u32, runtime_type_id: u32) -> *mut RcInstance
        let sig = self.create_signature(&[types::I32, types::I32, types::I32], Some(ptr_ty));
        self.import_function("vole_instance_new", &sig);

        // vole_instance_inc(ptr: *mut RcInstance)
        let sig = self.create_signature(&[ptr_ty], None);
        self.import_function("vole_instance_inc", &sig);

        // vole_instance_dec(ptr: *mut RcInstance)
        let sig = self.create_signature(&[ptr_ty], None);
        self.import_function("vole_instance_dec", &sig);

        // vole_instance_get_field(ptr: *const RcInstance, slot: u32) -> u64
        let sig = self.create_signature(&[ptr_ty, types::I32], Some(types::I64));
        self.import_function("vole_instance_get_field", &sig);

        // vole_instance_set_field(ptr: *mut RcInstance, slot: u32, value: u64)
        let sig = self.create_signature(&[ptr_ty, types::I32, types::I64], None);
        self.import_function("vole_instance_set_field", &sig);
    }

    fn register_runtime_symbols(builder: &mut JITBuilder) {
        // String functions
        builder.symbol(
            "vole_string_new",
            crate::runtime::string::vole_string_new as *const u8,
        );
        builder.symbol(
            "vole_string_inc",
            crate::runtime::string::vole_string_inc as *const u8,
        );
        builder.symbol(
            "vole_string_dec",
            crate::runtime::string::vole_string_dec as *const u8,
        );
        builder.symbol(
            "vole_string_len",
            crate::runtime::string::vole_string_len as *const u8,
        );
        builder.symbol(
            "vole_string_data",
            crate::runtime::string::vole_string_data as *const u8,
        );
        builder.symbol(
            "vole_string_eq",
            crate::runtime::string::vole_string_eq as *const u8,
        );
        builder.symbol(
            "vole_string_concat",
            crate::runtime::builtins::vole_string_concat as *const u8,
        );

        // Print functions
        builder.symbol(
            "vole_println_string",
            crate::runtime::builtins::vole_println_string as *const u8,
        );
        builder.symbol(
            "vole_println_i64",
            crate::runtime::builtins::vole_println_i64 as *const u8,
        );
        builder.symbol(
            "vole_println_f64",
            crate::runtime::builtins::vole_println_f64 as *const u8,
        );
        builder.symbol(
            "vole_println_bool",
            crate::runtime::builtins::vole_println_bool as *const u8,
        );
        builder.symbol(
            "vole_print_string",
            crate::runtime::builtins::vole_print_string as *const u8,
        );
        builder.symbol(
            "vole_print_i64",
            crate::runtime::builtins::vole_print_i64 as *const u8,
        );
        builder.symbol(
            "vole_print_f64",
            crate::runtime::builtins::vole_print_f64 as *const u8,
        );
        builder.symbol(
            "vole_print_bool",
            crate::runtime::builtins::vole_print_bool as *const u8,
        );
        builder.symbol(
            "vole_print_char",
            crate::runtime::builtins::vole_print_char as *const u8,
        );
        builder.symbol(
            "vole_flush",
            crate::runtime::builtins::vole_flush as *const u8,
        );

        // Conversion functions
        builder.symbol(
            "vole_i64_to_string",
            crate::runtime::builtins::vole_i64_to_string as *const u8,
        );
        builder.symbol(
            "vole_f64_to_string",
            crate::runtime::builtins::vole_f64_to_string as *const u8,
        );
        builder.symbol(
            "vole_bool_to_string",
            crate::runtime::builtins::vole_bool_to_string as *const u8,
        );

        // Assert functions
        builder.symbol(
            "vole_assert_fail",
            crate::runtime::assert::vole_assert_fail as *const u8,
        );

        // Array functions
        builder.symbol(
            "vole_array_new",
            crate::runtime::builtins::vole_array_new as *const u8,
        );
        builder.symbol(
            "vole_array_push",
            crate::runtime::builtins::vole_array_push as *const u8,
        );
        builder.symbol(
            "vole_array_get_value",
            crate::runtime::builtins::vole_array_get_value as *const u8,
        );
        builder.symbol(
            "vole_array_len",
            crate::runtime::builtins::vole_array_len as *const u8,
        );
        builder.symbol(
            "vole_array_iter",
            crate::runtime::iterator::vole_array_iter as *const u8,
        );
        builder.symbol(
            "vole_array_iter_next",
            crate::runtime::iterator::vole_array_iter_next as *const u8,
        );
        builder.symbol(
            "vole_array_iter_collect",
            crate::runtime::iterator::vole_array_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_map_iter",
            crate::runtime::iterator::vole_map_iter as *const u8,
        );
        builder.symbol(
            "vole_map_iter_next",
            crate::runtime::iterator::vole_map_iter_next as *const u8,
        );
        builder.symbol(
            "vole_map_iter_collect",
            crate::runtime::iterator::vole_map_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_filter_iter",
            crate::runtime::iterator::vole_filter_iter as *const u8,
        );
        builder.symbol(
            "vole_filter_iter_next",
            crate::runtime::iterator::vole_filter_iter_next as *const u8,
        );
        builder.symbol(
            "vole_filter_iter_collect",
            crate::runtime::iterator::vole_filter_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_iter_count",
            crate::runtime::iterator::vole_iter_count as *const u8,
        );
        builder.symbol(
            "vole_iter_sum",
            crate::runtime::iterator::vole_iter_sum as *const u8,
        );
        builder.symbol(
            "vole_iter_for_each",
            crate::runtime::iterator::vole_iter_for_each as *const u8,
        );
        builder.symbol(
            "vole_iter_reduce",
            crate::runtime::iterator::vole_iter_reduce as *const u8,
        );
        builder.symbol(
            "vole_take_iter",
            crate::runtime::iterator::vole_take_iter as *const u8,
        );
        builder.symbol(
            "vole_take_iter_next",
            crate::runtime::iterator::vole_take_iter_next as *const u8,
        );
        builder.symbol(
            "vole_take_iter_collect",
            crate::runtime::iterator::vole_take_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_skip_iter",
            crate::runtime::iterator::vole_skip_iter as *const u8,
        );
        builder.symbol(
            "vole_skip_iter_next",
            crate::runtime::iterator::vole_skip_iter_next as *const u8,
        );
        builder.symbol(
            "vole_skip_iter_collect",
            crate::runtime::iterator::vole_skip_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_array_set",
            crate::runtime::builtins::vole_array_set as *const u8,
        );

        // Closure functions
        builder.symbol(
            "vole_closure_alloc",
            crate::runtime::closure::vole_closure_alloc as *const u8,
        );
        builder.symbol(
            "vole_closure_get_capture",
            crate::runtime::closure::vole_closure_get_capture as *const u8,
        );
        builder.symbol(
            "vole_closure_set_capture",
            crate::runtime::closure::vole_closure_set_capture as *const u8,
        );
        builder.symbol(
            "vole_closure_get_func",
            crate::runtime::closure::vole_closure_get_func as *const u8,
        );
        builder.symbol(
            "vole_heap_alloc",
            crate::runtime::closure::vole_heap_alloc as *const u8,
        );

        // Instance functions (classes and records)
        builder.symbol(
            "vole_instance_new",
            crate::runtime::instance::vole_instance_new as *const u8,
        );
        builder.symbol(
            "vole_instance_inc",
            crate::runtime::instance::vole_instance_inc as *const u8,
        );
        builder.symbol(
            "vole_instance_dec",
            crate::runtime::instance::vole_instance_dec as *const u8,
        );
        builder.symbol(
            "vole_instance_get_field",
            crate::runtime::instance::vole_instance_get_field as *const u8,
        );
        builder.symbol(
            "vole_instance_set_field",
            crate::runtime::instance::vole_instance_set_field as *const u8,
        );
    }

    /// Get the pointer type for the target
    pub fn pointer_type(&self) -> Type {
        self.module.target_config().pointer_type()
    }

    /// Set the source file path. The string is stored in the JitContext
    /// so that it lives as long as the JIT code (for assert failure messages).
    pub fn set_source_file(&mut self, file: &str) {
        self.source_file = Some(file.into());
    }

    /// Get the source file path and its length as raw pointer info.
    /// Returns (ptr, len) where ptr is stable as long as JitContext exists.
    pub fn source_file_ptr(&self) -> (*const u8, usize) {
        match &self.source_file {
            Some(s) => (s.as_ptr(), s.len()),
            None => (std::ptr::null(), 0),
        }
    }

    /// Create a function signature with given parameters and return type
    pub fn create_signature(&self, params: &[Type], ret: Option<Type>) -> Signature {
        let mut sig = self.module.make_signature();
        for &param in params {
            sig.params.push(AbiParam::new(param));
        }
        if let Some(ret_type) = ret {
            sig.returns.push(AbiParam::new(ret_type));
        }
        sig
    }

    /// Declare a function in the module
    pub fn declare_function(&mut self, name: &str, sig: &Signature) -> FuncId {
        let func_id = self
            .module
            .declare_function(name, Linkage::Export, sig)
            .unwrap();
        self.func_ids.insert(name.to_string(), func_id);
        func_id
    }

    /// Import an external function
    pub fn import_function(&mut self, name: &str, sig: &Signature) -> FuncId {
        let func_id = self
            .module
            .declare_function(name, Linkage::Import, sig)
            .unwrap();
        self.func_ids.insert(name.to_string(), func_id);
        func_id
    }

    /// Define a function (after building IR)
    pub fn define_function(&mut self, func_id: FuncId) -> Result<(), String> {
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| format!("Compilation error: {:?}", e))
    }

    /// Finalize all functions and get code pointers
    /// Returns Ok(()) on success, Err on finalization failure (safe to ignore)
    pub fn finalize(&mut self) -> Result<(), String> {
        self.module
            .finalize_definitions()
            .map_err(|e| format!("Finalization error: {:?}", e))
    }

    /// Get a function pointer by name
    pub fn get_function_ptr(&self, name: &str) -> Option<*const u8> {
        self.func_ids
            .get(name)
            .map(|&func_id| self.module.get_finalized_function(func_id))
    }

    /// Get a function pointer by FuncId
    pub fn get_function_ptr_by_id(&self, func_id: FuncId) -> Option<*const u8> {
        Some(self.module.get_finalized_function(func_id))
    }

    /// Clear the context for reuse
    pub fn clear(&mut self) {
        self.ctx.clear();
    }

    /// Split into parts for compilation - allows FunctionBuilder and CompileCtx to coexist.
    /// Returns disjoint mutable references: (func, module, func_ids)
    pub fn split_for_compile(
        &mut self,
    ) -> (
        &mut cranelift_codegen::ir::Function,
        &mut JITModule,
        &mut HashMap<String, FuncId>,
    ) {
        (&mut self.ctx.func, &mut self.module, &mut self.func_ids)
    }
}

impl Default for JitContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_jit_context() {
        let jit = JitContext::new();
        assert!(jit.pointer_type() == types::I64 || jit.pointer_type() == types::I32);
    }

    #[test]
    fn create_and_call_simple_function() {
        let mut jit = JitContext::new();

        // Create a function that returns 42
        let sig = jit.create_signature(&[], Some(types::I64));
        let func_id = jit.declare_function("answer", &sig);

        jit.ctx.func.signature = sig;

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut jit.ctx.func, &mut builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let forty_two = builder.ins().iconst(types::I64, 42);
        builder.ins().return_(&[forty_two]);

        builder.finalize();

        jit.define_function(func_id).unwrap();
        let _ = jit.finalize();

        // Get and call the function
        let fn_ptr = jit.get_function_ptr("answer").unwrap();
        let answer: extern "C" fn() -> i64 = unsafe { std::mem::transmute(fn_ptr) };
        assert_eq!(answer(), 42);
    }

    #[test]
    fn create_function_with_params() {
        let mut jit = JitContext::new();

        // Create a function that adds two i64s
        let sig = jit.create_signature(&[types::I64, types::I64], Some(types::I64));
        let func_id = jit.declare_function("add", &sig);

        jit.ctx.func.signature = sig;

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut jit.ctx.func, &mut builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let a = builder.block_params(entry_block)[0];
        let b = builder.block_params(entry_block)[1];
        let sum = builder.ins().iadd(a, b);
        builder.ins().return_(&[sum]);

        builder.finalize();

        jit.define_function(func_id).unwrap();
        let _ = jit.finalize();

        let fn_ptr = jit.get_function_ptr("add").unwrap();
        let add: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(fn_ptr) };
        assert_eq!(add(10, 32), 42);
        assert_eq!(add(-5, 5), 0);
    }
}
