// src/codegen/jit.rs

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use rustc_hash::{FxHashMap, FxHashSet};

/// Cache of compiled module functions that can be shared across JitContexts.
/// The JitContext that compiled these functions must be kept alive.
pub struct CompiledModules {
    /// The JIT context holding the compiled module code (must stay alive)
    #[allow(dead_code)]
    jit: JitContext,
    /// Function name -> function pointer for all compiled module functions
    pub functions: FxHashMap<String, *const u8>,
    /// Module paths that have been processed (even if they only have external functions)
    compiled_module_paths: FxHashSet<String>,
}

// Safety: Function pointers are valid for the lifetime of the CompiledModules
// and can be safely shared across threads (they point to immutable code)
unsafe impl Send for CompiledModules {}
unsafe impl Sync for CompiledModules {}

impl CompiledModules {
    /// Create a new CompiledModules from a finalized JitContext.
    /// Extracts function pointers for all declared functions.
    /// `module_paths` is the list of module paths that were processed.
    pub fn new(mut jit: JitContext, module_paths: Vec<String>) -> Result<Self, String> {
        // Finalize to get function pointers
        jit.finalize()?;

        // Extract all function pointers
        let functions: FxHashMap<String, *const u8> = jit
            .func_ids
            .iter()
            .map(|(name, &func_id)| {
                let ptr = jit.module.get_finalized_function(func_id);
                (name.clone(), ptr)
            })
            .collect();

        Ok(Self {
            jit,
            functions,
            compiled_module_paths: module_paths.into_iter().collect(),
        })
    }

    /// Check if a function by name is present in the compiled modules
    pub fn has_function(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    /// Check if a module has been processed (compiled or registered external functions)
    pub fn has_module(&self, module_path: &str) -> bool {
        self.compiled_module_paths.contains(module_path)
    }
}

/// Options for JIT compilation
#[derive(Clone, Copy, Debug, Default)]
pub struct JitOptions {
    /// Release mode: disable verifier, enable speed optimizations
    pub release: bool,
    /// Enable disassembly output
    pub disasm: bool,
    /// Enable loop parameter optimization (removes invariant block params from loops)
    pub loop_param_opt: bool,
}

impl JitOptions {
    /// Create options for debug mode (default)
    pub fn debug() -> Self {
        Self {
            release: false,
            disasm: false,
            loop_param_opt: true, // Enable loop optimization in all modes
        }
    }

    /// Create options for release mode
    pub fn release() -> Self {
        Self {
            release: true,
            disasm: false,
            loop_param_opt: true,
        }
    }

    /// Create options for disassembly output
    pub fn disasm() -> Self {
        Self {
            release: false,
            disasm: true,
            loop_param_opt: true, // Enable loop optimization for IR inspection
        }
    }

    /// Enable loop parameter optimization
    pub fn with_loop_param_opt(mut self) -> Self {
        self.loop_param_opt = true;
        self
    }
}

/// JIT compiler context
pub struct JitContext {
    pub module: JITModule,
    pub ctx: codegen::Context,
    /// Functions declared with Export linkage (will be compiled)
    pub func_ids: FxHashMap<String, FuncId>,
    /// Functions declared with Import linkage (runtime/external functions)
    pub imported_func_ids: FxHashMap<String, FuncId>,
    /// Source file path stored here so it lives as long as the JIT code.
    /// Used by assert failure messages.
    source_file: Option<Box<str>>,
    /// Enable disassembly output
    disasm: bool,
    /// Collected disassembly output from compiled functions
    disasm_output: Vec<(String, String)>,
    /// Enable loop parameter optimization
    loop_param_opt: bool,
}

impl JitContext {
    /// Create a new JitContext with default (debug) options
    pub fn new() -> Self {
        Self::with_options(JitOptions::default())
    }

    /// Create a new JitContext with the specified options
    pub fn with_options(options: JitOptions) -> Self {
        Self::new_internal(None, options)
    }

    /// Create a new JitContext with pre-compiled module functions available as external symbols.
    /// This allows reusing compiled module code across multiple JitContexts.
    pub fn with_modules(modules: &CompiledModules) -> Self {
        Self::with_modules_and_options(modules, JitOptions::default())
    }

    /// Create a new JitContext with pre-compiled modules and custom options.
    pub fn with_modules_and_options(modules: &CompiledModules, options: JitOptions) -> Self {
        Self::new_internal(Some(&modules.functions), options)
    }

    fn new_internal(
        precompiled: Option<&FxHashMap<String, *const u8>>,
        options: JitOptions,
    ) -> Self {
        // Build JIT module with native ISA
        let mut flag_builder = settings::builder();
        flag_builder
            .set("use_colocated_libcalls", "false")
            .expect("Cranelift flag 'use_colocated_libcalls' should be valid");
        flag_builder
            .set("is_pic", "false")
            .expect("Cranelift flag 'is_pic' should be valid");
        // Enable LLVM ABI extensions for i128 support in function signatures
        flag_builder
            .set("enable_llvm_abi_extensions", "true")
            .expect("Cranelift flag 'enable_llvm_abi_extensions' should be valid");

        // Always enable speed optimizations for better codegen
        flag_builder
            .set("opt_level", "speed")
            .expect("Cranelift flag 'opt_level' should be valid");

        // Apply release mode settings
        if options.release {
            // Disable IR verifier for faster compilation
            flag_builder
                .set("enable_verifier", "false")
                .expect("Cranelift flag 'enable_verifier' should be valid");
        }

        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("native ISA not available: {}", msg);
        });

        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .expect("failed to build Cranelift ISA from native target");

        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        // Register runtime functions
        Self::register_runtime_symbols(&mut builder);

        // Register pre-compiled module functions as external symbols
        if let Some(functions) = precompiled {
            for (name, &ptr) in functions {
                builder.symbol(name, ptr);
            }
        }

        let module = JITModule::new(builder);
        let ctx = module.make_context();

        let mut jit = Self {
            module,
            ctx,
            func_ids: FxHashMap::default(),
            imported_func_ids: FxHashMap::default(),
            source_file: None,
            disasm: options.disasm,
            disasm_output: Vec::new(),
            loop_param_opt: options.loop_param_opt,
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

        // vole_f32_to_string(value: f32) -> *mut RcString
        let sig = self.create_signature(&[types::F32], Some(ptr_ty));
        self.import_function("vole_f32_to_string", &sig);

        // vole_i128_to_string(value: i128) -> *mut RcString
        let sig = self.create_signature(&[types::I128], Some(ptr_ty));
        self.import_function("vole_i128_to_string", &sig);

        // vole_bool_to_string(value: i8) -> *mut RcString
        let sig = self.create_signature(&[types::I8], Some(ptr_ty));
        self.import_function("vole_bool_to_string", &sig);

        // vole_nil_to_string() -> *mut RcString
        let sig = self.create_signature(&[], Some(ptr_ty));
        self.import_function("vole_nil_to_string", &sig);

        // vole_array_i64_to_string(arr: *const RcArray) -> *mut RcString
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_array_i64_to_string", &sig);

        // vole_flush()
        let sig = self.create_signature(&[], None);
        self.import_function("vole_flush", &sig);

        // vole_assert_fail(file_ptr: *const u8, file_len: usize, line: u32)
        let sig = self.create_signature(&[ptr_ty, types::I64, types::I32], None);
        self.import_function("vole_assert_fail", &sig);

        // vole_panic(msg: *const RcString, file_ptr: *const u8, file_len: usize, line: u32)
        let sig = self.create_signature(&[ptr_ty, ptr_ty, types::I64, types::I32], None);
        self.import_function("vole_panic", &sig);

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

        // vole_filter_iter(source: *mut RcIterator, predicate: *const Closure) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(ptr_ty));
        self.import_function("vole_filter_iter", &sig);

        // vole_filter_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_filter_iter_next", &sig);

        // vole_filter_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_filter_iter_collect", &sig);

        // vole_iter_set_elem_tag(iter: *mut RcIterator, tag: u64)
        let sig = self.create_signature(&[ptr_ty, types::I64], None);
        self.import_function("vole_iter_set_elem_tag", &sig);

        // vole_iter_set_produces_owned(iter: *mut RcIterator)
        let sig = self.create_signature(&[ptr_ty], None);
        self.import_function("vole_iter_set_produces_owned", &sig);

        // vole_iter_count(iter: *mut RcIterator) -> i64
        let sig = self.create_signature(&[ptr_ty], Some(types::I64));
        self.import_function("vole_iter_count", &sig);

        // vole_iter_sum(iter: *mut RcIterator) -> i64
        let sig = self.create_signature(&[ptr_ty], Some(types::I64));
        self.import_function("vole_iter_sum", &sig);

        // vole_iter_for_each(iter: *mut RcIterator, callback: *const Closure)
        let sig = self.create_signature(&[ptr_ty, ptr_ty], None);
        self.import_function("vole_iter_for_each", &sig);

        // vole_iter_reduce(iter: *mut RcIterator, init: i64, reducer: *const Closure) -> i64
        let sig = self.create_signature(&[ptr_ty, types::I64, ptr_ty], Some(types::I64));
        self.import_function("vole_iter_reduce", &sig);

        // vole_iter_reduce_tagged(iter, init, reducer, acc_tag, elem_tag) -> i64
        let sig = self.create_signature(
            &[ptr_ty, types::I64, ptr_ty, types::I64, types::I64],
            Some(types::I64),
        );
        self.import_function("vole_iter_reduce_tagged", &sig);

        // vole_iter_first(iter: *mut RcIterator) -> *mut u8 (optional: [tag:1][pad:7][payload:8])
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_iter_first", &sig);

        // vole_iter_last(iter: *mut RcIterator) -> *mut u8 (optional: [tag:1][pad:7][payload:8])
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_iter_last", &sig);

        // vole_iter_nth(iter: *mut RcIterator, n: i64) -> *mut u8 (optional: [tag:1][pad:7][payload:8])
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_iter_nth", &sig);

        // vole_take_iter(source: *mut RcIterator, count: i64) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_take_iter", &sig);

        // vole_take_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_take_iter_next", &sig);

        // vole_take_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_take_iter_collect", &sig);

        // vole_skip_iter(source: *mut RcIterator, count: i64) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_skip_iter", &sig);

        // vole_skip_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_skip_iter_next", &sig);

        // vole_skip_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_skip_iter_collect", &sig);

        // vole_chain_iter(first: *mut RcIterator, second: *mut RcIterator) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(ptr_ty));
        self.import_function("vole_chain_iter", &sig);

        // vole_chain_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_chain_iter_next", &sig);

        // vole_chain_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_chain_iter_collect", &sig);

        // vole_flatten_iter(source: *mut RcIterator) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_flatten_iter", &sig);

        // vole_flatten_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_flatten_iter_next", &sig);

        // vole_flatten_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_flatten_iter_collect", &sig);

        // vole_flat_map_iter(source: *mut RcIterator, transform: *const Closure) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(ptr_ty));
        self.import_function("vole_flat_map_iter", &sig);

        // vole_flat_map_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_flat_map_iter_next", &sig);

        // vole_flat_map_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_flat_map_iter_collect", &sig);

        // vole_reverse_iter(iter: *mut RcIterator) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_reverse_iter", &sig);

        // vole_sorted_iter(iter: *mut RcIterator) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_sorted_iter", &sig);

        // vole_unique_iter(iter: *mut RcIterator) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_unique_iter", &sig);

        // vole_unique_iter_next(iter: *mut UniqueIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_unique_iter_next", &sig);

        // vole_chunks_iter(source: *mut RcIterator, chunk_size: i64) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_chunks_iter", &sig);

        // vole_chunks_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_chunks_iter_next", &sig);

        // vole_chunks_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_chunks_iter_collect", &sig);

        // vole_windows_iter(source: *mut RcIterator, window_size: i64) -> *mut RcIterator
        let sig = self.create_signature(&[ptr_ty, types::I64], Some(ptr_ty));
        self.import_function("vole_windows_iter", &sig);

        // vole_windows_iter_next(iter: *mut RcIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_windows_iter_next", &sig);

        // vole_windows_iter_collect(iter: *mut RcIterator) -> *mut RcArray
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_windows_iter_collect", &sig);

        // Iterator factory functions
        // vole_repeat_iter(value: i64) -> *mut RepeatIterator
        let sig = self.create_signature(&[types::I64], Some(ptr_ty));
        self.import_function("vole_repeat_iter", &sig);

        // vole_repeat_iter_next(iter: *mut RepeatIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_repeat_iter_next", &sig);

        // vole_once_iter(value: i64) -> *mut OnceIterator
        let sig = self.create_signature(&[types::I64], Some(ptr_ty));
        self.import_function("vole_once_iter", &sig);

        // vole_once_iter_next(iter: *mut OnceIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_once_iter_next", &sig);

        // vole_empty_iter() -> *mut EmptyIterator
        let sig = self.create_signature(&[], Some(ptr_ty));
        self.import_function("vole_empty_iter", &sig);

        // vole_from_fn_iter(generator: *const Closure) -> *mut FromFnIterator
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_from_fn_iter", &sig);

        // vole_from_fn_iter_next(iter: *mut FromFnIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_from_fn_iter_next", &sig);

        // vole_range_iter(start: i64, end: i64) -> *mut RangeIterator
        let sig = self.create_signature(&[types::I64, types::I64], Some(ptr_ty));
        self.import_function("vole_range_iter", &sig);

        // vole_range_iter_next(iter: *mut RangeIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_range_iter_next", &sig);

        // vole_string_chars_iter(string: *const RcString) -> *mut StringCharsIterator
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_string_chars_iter", &sig);

        // vole_string_chars_iter_next(iter: *mut StringCharsIterator, out_value: *mut i64) -> i64
        let sig = self.create_signature(&[ptr_ty, ptr_ty], Some(types::I64));
        self.import_function("vole_string_chars_iter_next", &sig);

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

        // vole_closure_set_capture_kind(closure: *mut Closure, index: usize, kind: u8)
        let sig = self.create_signature(&[ptr_ty, types::I64, types::I8], None);
        self.import_function("vole_closure_set_capture_kind", &sig);

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

        // StringBuilder functions
        // vole_sb_new() -> *mut StringBuilder
        let sig = self.create_signature(&[], Some(ptr_ty));
        self.import_function("vole_sb_new", &sig);

        // vole_sb_push_string(sb: *mut StringBuilder, s: *const RcString)
        let sig = self.create_signature(&[ptr_ty, ptr_ty], None);
        self.import_function("vole_sb_push_string", &sig);

        // vole_sb_finish(sb: *mut StringBuilder) -> *mut RcString
        let sig = self.create_signature(&[ptr_ty], Some(ptr_ty));
        self.import_function("vole_sb_finish", &sig);

        // Unified RC functions
        // rc_inc(ptr: *mut u8)
        let sig = self.create_signature(&[ptr_ty], None);
        self.import_function("rc_inc", &sig);

        // rc_dec(ptr: *mut u8)
        let sig = self.create_signature(&[ptr_ty], None);
        self.import_function("rc_dec", &sig);
    }

    fn register_runtime_symbols(builder: &mut JITBuilder) {
        // Unified RC functions
        builder.symbol("rc_inc", vole_runtime::value::rc_inc as *const u8);
        builder.symbol("rc_dec", vole_runtime::value::rc_dec as *const u8);

        // String functions
        builder.symbol(
            "vole_string_new",
            vole_runtime::string::vole_string_new as *const u8,
        );
        builder.symbol(
            "vole_string_inc",
            vole_runtime::string::vole_string_inc as *const u8,
        );
        builder.symbol(
            "vole_string_dec",
            vole_runtime::string::vole_string_dec as *const u8,
        );
        builder.symbol(
            "vole_string_len",
            vole_runtime::string::vole_string_len as *const u8,
        );
        builder.symbol(
            "vole_string_data",
            vole_runtime::string::vole_string_data as *const u8,
        );
        builder.symbol(
            "vole_string_eq",
            vole_runtime::string::vole_string_eq as *const u8,
        );
        builder.symbol(
            "vole_string_concat",
            vole_runtime::builtins::vole_string_concat as *const u8,
        );

        // Print functions
        builder.symbol(
            "vole_println_string",
            vole_runtime::builtins::vole_println_string as *const u8,
        );
        builder.symbol(
            "vole_println_i64",
            vole_runtime::builtins::vole_println_i64 as *const u8,
        );
        builder.symbol(
            "vole_println_f64",
            vole_runtime::builtins::vole_println_f64 as *const u8,
        );
        builder.symbol(
            "vole_println_bool",
            vole_runtime::builtins::vole_println_bool as *const u8,
        );
        builder.symbol(
            "vole_print_string",
            vole_runtime::builtins::vole_print_string as *const u8,
        );
        builder.symbol(
            "vole_print_i64",
            vole_runtime::builtins::vole_print_i64 as *const u8,
        );
        builder.symbol(
            "vole_print_f64",
            vole_runtime::builtins::vole_print_f64 as *const u8,
        );
        builder.symbol(
            "vole_print_bool",
            vole_runtime::builtins::vole_print_bool as *const u8,
        );
        builder.symbol(
            "vole_print_char",
            vole_runtime::builtins::vole_print_char as *const u8,
        );
        builder.symbol(
            "vole_flush",
            vole_runtime::builtins::vole_flush as *const u8,
        );

        // Conversion functions
        builder.symbol(
            "vole_i64_to_string",
            vole_runtime::builtins::vole_i64_to_string as *const u8,
        );
        builder.symbol(
            "vole_f64_to_string",
            vole_runtime::builtins::vole_f64_to_string as *const u8,
        );
        builder.symbol(
            "vole_f32_to_string",
            vole_runtime::builtins::vole_f32_to_string as *const u8,
        );
        builder.symbol(
            "vole_i128_to_string",
            vole_runtime::builtins::vole_i128_to_string as *const u8,
        );
        builder.symbol(
            "vole_bool_to_string",
            vole_runtime::builtins::vole_bool_to_string as *const u8,
        );
        builder.symbol(
            "vole_nil_to_string",
            vole_runtime::builtins::vole_nil_to_string as *const u8,
        );
        builder.symbol(
            "vole_array_i64_to_string",
            vole_runtime::builtins::vole_array_i64_to_string as *const u8,
        );

        // Assert functions
        builder.symbol(
            "vole_assert_fail",
            vole_runtime::assert::vole_assert_fail as *const u8,
        );

        // Panic function
        builder.symbol(
            "vole_panic",
            vole_runtime::builtins::vole_panic as *const u8,
        );

        // Array functions
        builder.symbol(
            "vole_array_new",
            vole_runtime::builtins::vole_array_new as *const u8,
        );
        builder.symbol(
            "vole_array_push",
            vole_runtime::builtins::vole_array_push as *const u8,
        );
        builder.symbol(
            "vole_array_get_value",
            vole_runtime::builtins::vole_array_get_value as *const u8,
        );
        builder.symbol(
            "vole_array_len",
            vole_runtime::builtins::vole_array_len as *const u8,
        );
        builder.symbol(
            "vole_array_iter",
            vole_runtime::iterator::vole_array_iter as *const u8,
        );
        builder.symbol(
            "vole_array_iter_next",
            vole_runtime::iterator::vole_array_iter_next as *const u8,
        );
        builder.symbol(
            "vole_array_iter_collect",
            vole_runtime::iterator::vole_array_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_map_iter",
            vole_runtime::iterator::vole_map_iter as *const u8,
        );
        builder.symbol(
            "vole_map_iter_next",
            vole_runtime::iterator::vole_map_iter_next as *const u8,
        );
        builder.symbol(
            "vole_map_iter_collect",
            vole_runtime::iterator::vole_map_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_filter_iter",
            vole_runtime::iterator::vole_filter_iter as *const u8,
        );
        builder.symbol(
            "vole_filter_iter_next",
            vole_runtime::iterator::vole_filter_iter_next as *const u8,
        );
        builder.symbol(
            "vole_filter_iter_collect",
            vole_runtime::iterator::vole_filter_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_iter_count",
            vole_runtime::iterator::vole_iter_count as *const u8,
        );
        builder.symbol(
            "vole_iter_sum",
            vole_runtime::iterator::vole_iter_sum as *const u8,
        );
        builder.symbol(
            "vole_iter_set_elem_tag",
            vole_runtime::iterator::vole_iter_set_elem_tag as *const u8,
        );
        builder.symbol(
            "vole_iter_set_produces_owned",
            vole_runtime::iterator::vole_iter_set_produces_owned as *const u8,
        );
        builder.symbol(
            "vole_iter_for_each",
            vole_runtime::iterator::vole_iter_for_each as *const u8,
        );
        builder.symbol(
            "vole_iter_reduce",
            vole_runtime::iterator::vole_iter_reduce as *const u8,
        );
        builder.symbol(
            "vole_iter_reduce_tagged",
            vole_runtime::iterator::vole_iter_reduce_tagged as *const u8,
        );
        builder.symbol(
            "vole_iter_first",
            vole_runtime::iterator::vole_iter_first as *const u8,
        );
        builder.symbol(
            "vole_iter_last",
            vole_runtime::iterator::vole_iter_last as *const u8,
        );
        builder.symbol(
            "vole_iter_nth",
            vole_runtime::iterator::vole_iter_nth as *const u8,
        );
        builder.symbol(
            "vole_take_iter",
            vole_runtime::iterator::vole_take_iter as *const u8,
        );
        builder.symbol(
            "vole_take_iter_next",
            vole_runtime::iterator::vole_take_iter_next as *const u8,
        );
        builder.symbol(
            "vole_take_iter_collect",
            vole_runtime::iterator::vole_take_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_skip_iter",
            vole_runtime::iterator::vole_skip_iter as *const u8,
        );
        builder.symbol(
            "vole_skip_iter_next",
            vole_runtime::iterator::vole_skip_iter_next as *const u8,
        );
        builder.symbol(
            "vole_skip_iter_collect",
            vole_runtime::iterator::vole_skip_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_chain_iter",
            vole_runtime::iterator::vole_chain_iter as *const u8,
        );
        builder.symbol(
            "vole_chain_iter_next",
            vole_runtime::iterator::vole_chain_iter_next as *const u8,
        );
        builder.symbol(
            "vole_chain_iter_collect",
            vole_runtime::iterator::vole_chain_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_flatten_iter",
            vole_runtime::iterator::vole_flatten_iter as *const u8,
        );
        builder.symbol(
            "vole_flatten_iter_next",
            vole_runtime::iterator::vole_flatten_iter_next as *const u8,
        );
        builder.symbol(
            "vole_flatten_iter_collect",
            vole_runtime::iterator::vole_flatten_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_flat_map_iter",
            vole_runtime::iterator::vole_flat_map_iter as *const u8,
        );
        builder.symbol(
            "vole_flat_map_iter_next",
            vole_runtime::iterator::vole_flat_map_iter_next as *const u8,
        );
        builder.symbol(
            "vole_flat_map_iter_collect",
            vole_runtime::iterator::vole_flat_map_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_reverse_iter",
            vole_runtime::iterator::vole_reverse_iter as *const u8,
        );
        builder.symbol(
            "vole_sorted_iter",
            vole_runtime::iterator::vole_sorted_iter as *const u8,
        );
        builder.symbol(
            "vole_unique_iter",
            vole_runtime::iterator::vole_unique_iter as *const u8,
        );
        builder.symbol(
            "vole_unique_iter_next",
            vole_runtime::iterator::vole_unique_iter_next as *const u8,
        );
        builder.symbol(
            "vole_chunks_iter",
            vole_runtime::iterator::vole_chunks_iter as *const u8,
        );
        builder.symbol(
            "vole_chunks_iter_next",
            vole_runtime::iterator::vole_chunks_iter_next as *const u8,
        );
        builder.symbol(
            "vole_chunks_iter_collect",
            vole_runtime::iterator::vole_chunks_iter_collect as *const u8,
        );
        builder.symbol(
            "vole_windows_iter",
            vole_runtime::iterator::vole_windows_iter as *const u8,
        );
        builder.symbol(
            "vole_windows_iter_next",
            vole_runtime::iterator::vole_windows_iter_next as *const u8,
        );
        builder.symbol(
            "vole_windows_iter_collect",
            vole_runtime::iterator::vole_windows_iter_collect as *const u8,
        );

        // Iterator factory functions
        builder.symbol(
            "vole_repeat_iter",
            vole_runtime::iterator::vole_repeat_iter as *const u8,
        );
        builder.symbol(
            "vole_repeat_iter_next",
            vole_runtime::iterator::vole_repeat_iter_next as *const u8,
        );
        builder.symbol(
            "vole_once_iter",
            vole_runtime::iterator::vole_once_iter as *const u8,
        );
        builder.symbol(
            "vole_once_iter_next",
            vole_runtime::iterator::vole_once_iter_next as *const u8,
        );
        builder.symbol(
            "vole_empty_iter",
            vole_runtime::iterator::vole_empty_iter as *const u8,
        );
        builder.symbol(
            "vole_from_fn_iter",
            vole_runtime::iterator::vole_from_fn_iter as *const u8,
        );
        builder.symbol(
            "vole_from_fn_iter_next",
            vole_runtime::iterator::vole_from_fn_iter_next as *const u8,
        );
        builder.symbol(
            "vole_range_iter",
            vole_runtime::iterator::vole_range_iter as *const u8,
        );
        builder.symbol(
            "vole_range_iter_next",
            vole_runtime::iterator::vole_range_iter_next as *const u8,
        );
        builder.symbol(
            "vole_string_chars_iter",
            vole_runtime::iterator::vole_string_chars_iter as *const u8,
        );
        builder.symbol(
            "vole_string_chars_iter_next",
            vole_runtime::iterator::vole_string_chars_iter_next as *const u8,
        );

        builder.symbol(
            "vole_array_set",
            vole_runtime::builtins::vole_array_set as *const u8,
        );

        // Closure functions
        builder.symbol(
            "vole_closure_alloc",
            vole_runtime::closure::vole_closure_alloc as *const u8,
        );
        builder.symbol(
            "vole_closure_get_capture",
            vole_runtime::closure::vole_closure_get_capture as *const u8,
        );
        builder.symbol(
            "vole_closure_set_capture",
            vole_runtime::closure::vole_closure_set_capture as *const u8,
        );
        builder.symbol(
            "vole_closure_set_capture_kind",
            vole_runtime::closure::vole_closure_set_capture_kind as *const u8,
        );
        builder.symbol(
            "vole_closure_get_func",
            vole_runtime::closure::vole_closure_get_func as *const u8,
        );
        builder.symbol(
            "vole_heap_alloc",
            vole_runtime::closure::vole_heap_alloc as *const u8,
        );

        // StringBuilder functions
        builder.symbol(
            "vole_sb_new",
            vole_runtime::string_builder::vole_sb_new as *const u8,
        );
        builder.symbol(
            "vole_sb_push_string",
            vole_runtime::string_builder::vole_sb_push_string as *const u8,
        );
        builder.symbol(
            "vole_sb_finish",
            vole_runtime::string_builder::vole_sb_finish as *const u8,
        );

        // Instance functions (classes and records)
        builder.symbol(
            "vole_instance_new",
            vole_runtime::instance::vole_instance_new as *const u8,
        );
        builder.symbol(
            "vole_instance_inc",
            vole_runtime::instance::vole_instance_inc as *const u8,
        );
        builder.symbol(
            "vole_instance_dec",
            vole_runtime::instance::vole_instance_dec as *const u8,
        );
        builder.symbol(
            "vole_instance_get_field",
            vole_runtime::instance::vole_instance_get_field as *const u8,
        );
        builder.symbol(
            "vole_instance_set_field",
            vole_runtime::instance::vole_instance_set_field as *const u8,
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

    /// Create a function signature with given parameters and multiple return types.
    /// Used for fallible functions which return (tag, payload) in registers.
    pub fn create_signature_multi_return(&self, params: &[Type], returns: &[Type]) -> Signature {
        let mut sig = self.module.make_signature();
        for &param in params {
            sig.params.push(AbiParam::new(param));
        }
        for &ret_type in returns {
            sig.returns.push(AbiParam::new(ret_type));
        }
        sig
    }

    /// Declare a function in the module
    pub fn declare_function(&mut self, name: &str, sig: &Signature) -> FuncId {
        let func_id = self
            .module
            .declare_function(name, Linkage::Export, sig)
            .unwrap_or_else(|e| panic!("failed to declare function '{}': {:?}", name, e));
        self.func_ids.insert(name.to_string(), func_id);
        func_id
    }

    /// Import an external function
    /// These are stored in imported_func_ids (not func_ids) since they don't have
    /// compiled code that can be retrieved via get_finalized_function.
    pub fn import_function(&mut self, name: &str, sig: &Signature) -> FuncId {
        let func_id = self
            .module
            .declare_function(name, Linkage::Import, sig)
            .unwrap_or_else(|e| panic!("failed to import function '{}': {:?}", name, e));
        self.imported_func_ids.insert(name.to_string(), func_id);
        func_id
    }

    /// Define a function (after building IR)
    pub fn define_function(&mut self, func_id: FuncId) -> Result<(), String> {
        // Run CFG cleanup to eliminate trampoline blocks before Cranelift compilation
        crate::cfg_cleanup::cleanup_cfg(&mut self.ctx.func);

        // Run loop parameter optimization if enabled
        if self.loop_param_opt {
            crate::loop_param_opt::optimize_loop_params(&mut self.ctx.func);
        }

        // Enable disassembly if requested
        if self.disasm {
            self.ctx.set_disasm(true);
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| format!("Compilation error: {:?}", e))?;

        // Capture disassembly if enabled
        if self.disasm
            && let Some(compiled) = self.ctx.compiled_code()
            && let Some(vcode) = &compiled.vcode
        {
            // Get function name from func_ids (reverse lookup)
            let func_name = self
                .func_ids
                .iter()
                .find(|(_, id)| **id == func_id)
                .map(|(name, _)| name.clone())
                .unwrap_or_else(|| format!("func_{:?}", func_id));
            self.disasm_output.push((func_name, vcode.clone()));
        }

        Ok(())
    }

    /// Get collected disassembly output
    pub fn get_disasm(&self) -> &[(String, String)] {
        &self.disasm_output
    }

    /// Check if loop parameter optimization is enabled
    pub fn loop_param_opt_enabled(&self) -> bool {
        self.loop_param_opt
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

    /// Split into parts for compilation - allows FunctionBuilder and CodegenCtx to coexist.
    /// Returns disjoint mutable references: (func, module, func_ids)
    pub fn split_for_compile(
        &mut self,
    ) -> (
        &mut cranelift_codegen::ir::Function,
        &mut JITModule,
        &mut FxHashMap<String, FuncId>,
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
        jit.finalize().expect("finalization should succeed");

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
        jit.finalize().expect("finalization should succeed");

        let fn_ptr = jit.get_function_ptr("add").unwrap();
        let add: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(fn_ptr) };
        assert_eq!(add(10, 32), 42);
        assert_eq!(add(-5, 5), 0);
    }
}
