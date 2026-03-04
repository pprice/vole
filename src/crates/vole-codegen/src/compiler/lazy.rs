// src/codegen/compiler/lazy.rs
//
// Lazy module codegen: dispatch table and CLIF stub generation.
//
// When `lazy_modules=true`, module function bodies are not compiled during
// Phase 2 of `compile_module_functions`. Instead, small CLIF stubs are
// generated that check a "compiled" flag and, if not yet compiled, call
// `compile_trigger(module_id)` to compile the module on demand.
//
// Each stub then loads the real function pointer from the dispatch table
// and tail-calls it via `call_indirect`.

use std::sync::atomic::{AtomicBool, AtomicU64};

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};

/// Dispatch table for lazy module codegen.
///
/// Each module function gets an entry with a function pointer slot.
/// Each module gets a compiled flag. When `compile_trigger` is called,
/// it compiles all functions in the module, fills in the fn_ptr slots,
/// and sets the compiled flag to true.
///
/// The table is heap-allocated (`Box<LazyDispatchTable>`) so that
/// pointers to its fields are stable across the lifetime of the JIT.
pub struct LazyDispatchTable {
    /// Function pointer slots (one per module function).
    /// Initially 0 (null), filled by `compile_trigger`.
    pub fn_ptrs: Vec<AtomicU64>,
    /// Per-module compiled flags (one per module).
    /// Set to true after `compile_trigger` compiles the module.
    pub compiled_flags: Vec<AtomicBool>,
    /// Map from module function FuncId to dispatch table index
    /// (index into `fn_ptrs`).
    pub func_index: FxHashMap<FuncId, usize>,
    /// Map from dispatch table index to module index
    /// (index into `compiled_flags`).
    pub func_to_module: Vec<usize>,
    /// Module path to module index (index into `compiled_flags`).
    pub module_index: FxHashMap<String, usize>,
}

impl LazyDispatchTable {
    /// Create a new empty dispatch table.
    pub fn new() -> Self {
        Self {
            fn_ptrs: Vec::new(),
            compiled_flags: Vec::new(),
            func_index: FxHashMap::default(),
            func_to_module: Vec::new(),
            module_index: FxHashMap::default(),
        }
    }

    /// Register a module path, returning its module index.
    /// If the module is already registered, returns the existing index.
    pub fn register_module(&mut self, module_path: &str) -> usize {
        if let Some(&idx) = self.module_index.get(module_path) {
            return idx;
        }
        let idx = self.compiled_flags.len();
        self.compiled_flags.push(AtomicBool::new(false));
        self.module_index.insert(module_path.to_string(), idx);
        idx
    }

    /// Register a function in the dispatch table, returning its function index.
    /// `module_idx` is the index returned by `register_module`.
    pub fn register_function(&mut self, func_id: FuncId, module_idx: usize) -> usize {
        let func_idx = self.fn_ptrs.len();
        self.fn_ptrs.push(AtomicU64::new(0));
        self.func_index.insert(func_id, func_idx);
        self.func_to_module.push(module_idx);
        func_idx
    }

    /// Get a stable pointer to the compiled flag for a module index.
    /// The pointer is valid as long as the `LazyDispatchTable` is alive.
    pub fn compiled_flag_ptr(&self, module_idx: usize) -> *const AtomicBool {
        &self.compiled_flags[module_idx] as *const AtomicBool
    }

    /// Get a stable pointer to the function pointer slot for a function index.
    /// The pointer is valid as long as the `LazyDispatchTable` is alive.
    pub fn fn_ptr_slot_ptr(&self, func_idx: usize) -> *const AtomicU64 {
        &self.fn_ptrs[func_idx] as *const AtomicU64
    }
}

/// Placeholder `compile_trigger` function.
///
/// This is registered as a JIT symbol so stubs can call it. The real
/// implementation (vol-wsec) will compile the module on demand and
/// fill in the dispatch table entries.
///
/// # Safety
///
/// Called from JIT-compiled code. Panics because the real implementation
/// is not yet available.
pub extern "C" fn compile_trigger_placeholder(module_id: i64) {
    panic!(
        "INTERNAL: compile_trigger called for module_id={} but lazy compilation callback is not yet implemented (vol-wsec)",
        module_id
    );
}

/// Generate a CLIF stub function for a lazily-compiled module function.
///
/// The stub:
/// 1. Loads the "compiled" flag from the dispatch table
/// 2. If not compiled: calls `compile_trigger(module_id)`
/// 3. Loads the real function pointer from the dispatch table
/// 4. Tail-calls the real function via `call_indirect`
/// 5. Returns the result
///
/// # Arguments
///
/// * `jit_module` - The JIT module (for declaring functions, importing signatures)
/// * `jit_ctx` - The Cranelift codegen context (reused for each stub)
/// * `func_id` - The already-declared FuncId for this module function
/// * `compile_trigger_func_id` - FuncId of the `compile_trigger` extern
/// * `compiled_flag_addr` - Stable pointer to the compiled flag (AtomicBool)
/// * `fn_ptr_addr` - Stable pointer to the function pointer slot (AtomicU64)
/// * `module_idx` - Module index passed to `compile_trigger`
pub fn generate_lazy_stub(
    jit_module: &mut cranelift_jit::JITModule,
    jit_ctx: &mut codegen::Context,
    func_id: FuncId,
    compile_trigger_func_id: FuncId,
    compiled_flag_addr: u64,
    fn_ptr_addr: u64,
    module_idx: usize,
) -> CodegenResult<()> {
    // Get the signature of the target function (already declared)
    let sig = jit_module.declarations().get_function_decl(func_id).signature.clone();

    jit_ctx.func.signature = sig.clone();

    let mut builder_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut jit_ctx.func, &mut builder_ctx);

    // Create blocks
    let entry_block = builder.create_block();
    let compile_block = builder.create_block();
    let call_block = builder.create_block();

    // Entry block: check compiled flag
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Collect the original parameters
    let params: Vec<Value> = builder.block_params(entry_block).to_vec();

    // Load compiled flag: load i8 from the AtomicBool address
    let flag_addr_val = builder.ins().iconst(types::I64, compiled_flag_addr as i64);
    let flag_val = builder
        .ins()
        .load(types::I8, MemFlags::new(), flag_addr_val, 0);
    let zero = builder.ins().iconst(types::I8, 0);
    let is_compiled = builder.ins().icmp(IntCC::NotEqual, flag_val, zero);

    // Branch: if compiled, jump to call_block; else jump to compile_block
    builder.ins().brif(is_compiled, call_block, &[], compile_block, &[]);

    // Compile block: call compile_trigger(module_idx), then fall through to call_block
    builder.switch_to_block(compile_block);
    let compile_trigger_ref = jit_module.declare_func_in_func(compile_trigger_func_id, builder.func);
    let module_id_val = builder.ins().iconst(types::I64, module_idx as i64);
    builder.ins().call(compile_trigger_ref, &[module_id_val]);
    builder.ins().jump(call_block, &[]);

    // Call block: load fn_ptr from dispatch table, call_indirect with original params
    builder.switch_to_block(call_block);

    let fn_ptr_addr_val = builder.ins().iconst(types::I64, fn_ptr_addr as i64);
    let fn_ptr_raw = builder
        .ins()
        .load(types::I64, MemFlags::new(), fn_ptr_addr_val, 0);

    // Import the function signature for call_indirect
    let sig_ref = builder.import_signature(sig);

    // Call indirect with all original params
    let call_inst = builder.ins().call_indirect(sig_ref, fn_ptr_raw, &params);

    // Return the results
    let results: Vec<Value> = builder.inst_results(call_inst).to_vec();
    builder.ins().return_(&results);

    // Seal all blocks (no back-edges, so sealing at the end is fine)
    builder.seal_all_blocks();
    builder.finalize();

    // Define the function in the JIT module
    jit_module
        .define_function(func_id, jit_ctx)
        .map_err(|e| {
            CodegenError::internal_with_context(
                "failed to define lazy stub",
                format!("{:?}", e),
            )
        })?;

    jit_ctx.clear();

    Ok(())
}
