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

use std::cell::RefCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::{JitContext, JitOptions};
use vole_vir::VirProgram;

/// Dispatch table for lazy module codegen.
///
/// Each module function gets an entry with a function pointer slot.
/// Each module gets a compiled flag. When `compile_trigger` is called,
/// it compiles all functions in the module, fills in the fn_ptr slots,
/// and sets the compiled flag to true.
///
/// The table is heap-allocated (`Arc<LazyDispatchTable>`) so that
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
    /// Function display_name to dispatch table func_idx.
    /// Used by `compile_trigger` to map compiled function names back to
    /// their dispatch table slots.
    pub func_name_to_idx: FxHashMap<String, usize>,
}

impl Default for LazyDispatchTable {
    fn default() -> Self {
        Self::new()
    }
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
            func_name_to_idx: FxHashMap::default(),
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

/// Runtime state for lazy module compilation.
///
/// Holds everything `compile_trigger` needs to compile modules on demand:
/// the dispatch table, a reference to the analyzed program, JIT options,
/// and a single overflow JIT context for lazily-compiled function bodies.
///
/// # Lifecycle
///
/// 1. Built from `Compiler::take_lazy_state()` after stub generation.
/// 2. Stored in the `LAZY_STATE` thread-local via `activate()`.
/// 3. Accessed by `compile_trigger()` during JIT execution.
/// 4. Removed from thread-local via `deactivate()` after execution.
pub struct LazyCompilationState {
    /// The dispatch table (fn_ptrs and compiled_flags).
    pub dispatch_table: Arc<LazyDispatchTable>,
    /// Reference to the analyzed program (for module compilation).
    ///
    /// # Safety
    ///
    /// The caller must ensure the `VirProgram` outlives execution.
    /// This is safe in the current architecture because the `VirProgram`
    /// lives on the stack in `run_source_tests_with_modules` / `run_source`
    /// and execution happens in the same scope.
    analyzed: *const VirProgram,
    /// JIT options for creating new JitContexts during lazy compilation.
    jit_options: JitOptions,
    /// Module index -> module path (reverse of `dispatch_table.module_index`).
    module_paths: Vec<String>,
    /// Function display_name -> dispatch table func_idx.
    /// Copied from the dispatch table for quick lookup during compilation.
    func_name_to_idx: FxHashMap<String, usize>,
    /// Single overflow JitContext for all lazily-compiled function bodies.
    /// Created on first compile_trigger call; subsequent triggers define
    /// additional functions into it and call finalize_definitions() again.
    overflow_jit: Option<JitContext>,
    /// Whether the global compilation passes (array Iterable defaults,
    /// monomorphized instances, VIR monomorphs, abstract class methods)
    /// have been run. These are shared across all modules and only need
    /// to execute once — on the first compile_trigger call.
    global_passes_done: bool,
    /// Stub function pointers from the main JitContext.
    ///
    /// Maps `display_name -> stub_ptr` for all module functions that have
    /// lazy stubs in the main JitContext. These are registered as JIT symbols
    /// in the overflow JitContext so cross-module calls from a compiled module
    /// resolve to the main JitContext's stubs (which check the compiled flag
    /// and dispatch through the table).
    stub_symbols: FxHashMap<String, *const u8>,
    /// Running lambda counter across lazy compilations.
    ///
    /// Each `Compiler::new` starts with `lambda_counter=0`, but lazily-compiled
    /// modules share the same Cranelift `JITModule`, so `__lambda_0` from
    /// module A collides with `__lambda_0` from module B. This field persists
    /// across triggers so each lazy compilation picks up where the last left off.
    next_lambda_id: usize,
}

// SAFETY: LazyCompilationState contains `*const VirProgram` which is not
// Send/Sync by default. The pointer is only dereferenced on the thread that
// created it (via the thread-local LAZY_STATE), and the VirProgram is
// guaranteed to outlive execution by the caller. The overflow_jit Option
// contains a JitContext with immutable finalized machine code.
unsafe impl Send for LazyCompilationState {}

impl LazyCompilationState {
    /// Create a new `LazyCompilationState`.
    ///
    /// # Safety
    ///
    /// The caller must ensure `analyzed` outlives the execution of JIT code
    /// (i.e., until `deactivate()` is called and all JIT code has finished).
    pub unsafe fn new(
        dispatch_table: Arc<LazyDispatchTable>,
        analyzed: *const VirProgram,
        jit_options: JitOptions,
        initial_lambda_id: usize,
    ) -> Self {
        // Build module_paths: module_idx -> module_path
        let mut module_paths = vec![String::new(); dispatch_table.module_index.len()];
        for (path, &idx) in &dispatch_table.module_index {
            module_paths[idx] = path.clone();
        }

        let func_name_to_idx = dispatch_table.func_name_to_idx.clone();

        Self {
            dispatch_table,
            analyzed,
            jit_options,
            module_paths,
            func_name_to_idx,
            overflow_jit: None,
            global_passes_done: false,
            stub_symbols: FxHashMap::default(),
            next_lambda_id: initial_lambda_id,
        }
    }

    /// Populate stub symbols from the finalized main JitContext.
    ///
    /// Must be called AFTER `jit.finalize()` so that stub addresses are valid.
    /// Extracts the finalized pointer for each function in the dispatch table's
    /// `func_name_to_idx` map (these are the lazy stubs generated in Pass 2).
    /// Populate stub symbols from the finalized main JitContext.
    ///
    /// Extracts the finalized pointer for each function in the dispatch table's
    /// `func_name_to_idx` map. Must be called AFTER `jit.finalize()`.
    pub fn populate_stub_symbols(&mut self, jit: &JitContext) {
        for name in self.func_name_to_idx.keys() {
            if let Some(&func_id) = jit.func_ids.get(name) {
                // Only extract pointers for functions that were actually
                // defined (compiled as stubs) in the main JitContext.
                if jit.defined_func_ids.contains(&func_id) {
                    let ptr = jit.module.get_finalized_function(func_id);
                    self.stub_symbols.insert(name.clone(), ptr);
                }
            }
        }
        tracing::debug!(
            count = self.stub_symbols.len(),
            "populate_stub_symbols: registered from main JitContext"
        );
    }

    /// Populate stub symbols from pre-compiled module functions.
    ///
    /// Used in the module cache path: module functions are already compiled
    /// and their pointers are in the `CompiledModules.functions` map.
    /// Cross-module calls in the overflow JitContext resolve to these pointers.
    ///
    /// All cached functions are registered (not just those in the dispatch
    /// table) so that cross-module references from lazily-compiled bodies
    /// can resolve to functions added by incremental cache extensions.
    pub fn populate_stub_symbols_from_cache(&mut self, functions: &FxHashMap<String, *const u8>) {
        for (name, &ptr) in functions {
            self.stub_symbols.insert(name.clone(), ptr);
        }
        tracing::debug!(
            count = self.stub_symbols.len(),
            "populate_stub_symbols: registered from module cache"
        );
    }

    /// Store this state in the thread-local for use by `compile_trigger`.
    pub fn activate(self) {
        LAZY_STATE.with(|cell| {
            *cell.borrow_mut() = Some(self);
        });
    }

    /// Remove and return the state from the thread-local.
    /// Returns `None` if no state was active.
    pub fn deactivate() -> Option<Self> {
        LAZY_STATE.with(|cell| cell.borrow_mut().take())
    }

    /// Consume this state and return the overflow JIT context, if any.
    ///
    /// The context holds the machine code compiled by `compile_trigger`.
    /// It must be kept alive as long as the dispatch table's function
    /// pointers are in use.
    pub fn into_overflow_jit(self) -> Option<JitContext> {
        self.overflow_jit
    }
}

thread_local! {
    static LAZY_STATE: RefCell<Option<LazyCompilationState>> = const { RefCell::new(None) };
}

/// Compile-trigger callback invoked from JIT-compiled lazy stubs.
///
/// When a lazily-compiled module function is called for the first time,
/// the stub calls this function with the module index. This function:
///
/// 1. Checks if the module is already compiled (double-check after the stub's check).
/// 2. Reuses (or creates) the single overflow `JitContext`.
/// 3. Compiles ONLY the triggered module's function bodies (incremental).
/// 4. Extracts function pointers and patches the dispatch table for that module.
/// 5. Sets the triggered module's compiled flag so subsequent calls are no-ops.
///
/// Global declaration/compilation passes (type declarations, monomorphized
/// instances, array Iterable defaults) run on the first trigger only. They
/// cover all modules for cross-reference resolution. Subsequent triggers
/// re-run declarations (idempotent) but skip global compilation passes.
///
/// # Safety
///
/// Called from JIT-compiled code via `extern "C"` ABI. Assumes `LAZY_STATE`
/// has been activated via `LazyCompilationState::activate()`.
pub extern "C" fn compile_trigger(module_idx: i64) {
    LAZY_STATE.with(|cell| {
        let mut state_opt = cell.borrow_mut();
        let state = state_opt
            .as_mut()
            .expect("INTERNAL: compile_trigger called but LazyCompilationState not activated");

        let module_idx = module_idx as usize;

        // Double-check: the stub already checked, but another call may have
        // compiled this module between the stub's check and this point.
        if state.dispatch_table.compiled_flags[module_idx].load(Ordering::Acquire) {
            return;
        }

        let trigger_module = state
            .module_paths
            .get(module_idx)
            .cloned()
            .unwrap_or_else(|| "<unknown>".to_string());
        let first_trigger = !state.global_passes_done;
        tracing::debug!(
            module_idx,
            %trigger_module,
            first_trigger,
            total_modules = state.module_paths.len(),
            "compile_trigger: compiling single module"
        );
        let analyzed = unsafe { &*state.analyzed };

        // Reuse the overflow JIT context (created on first trigger), or create
        // one with lazy_modules disabled so compile_single_module_lazy compiles
        // real bodies (not stubs). The overflow JitContext is pre-seeded with
        // stub symbols from the main JitContext so cross-module calls resolve
        // to the main stubs (which dispatch through the table). Cranelift's
        // finalize_definitions() can be called multiple times — each call only
        // processes functions defined since the last finalize.
        let mut lazy_off_options = state.jit_options;
        lazy_off_options.lazy_modules = false;
        let stub_symbols = &state.stub_symbols;
        let jit = state.overflow_jit.get_or_insert_with(|| {
            JitContext::with_symbols_and_options(stub_symbols, lazy_off_options)
        });

        let mut compiler = super::Compiler::new(jit, analyzed);
        // Seed the lambda counter from the persistent state so that
        // lambda names don't collide across lazily-compiled modules.
        compiler.set_lambda_counter(state.next_lambda_id);
        compiler
            .compile_single_module_lazy(&trigger_module, first_trigger)
            .unwrap_or_else(|e| {
                panic!(
                    "INTERNAL: lazy module compilation failed for '{}': {:?}",
                    trigger_module, e
                )
            });
        // Persist the updated counter for the next trigger.
        state.next_lambda_id = compiler.lambda_counter();
        jit.finalize()
            .expect("INTERNAL: lazy module JIT finalization failed");

        state.global_passes_done = true;

        // Extract function pointers and update dispatch table slots
        // ONLY for functions belonging to the triggered module.
        for (name, &func_id) in &jit.func_ids {
            if jit.defined_func_ids.contains(&func_id)
                && let Some(&func_idx) = state.func_name_to_idx.get(name)
            {
                // Only patch entries that belong to the triggered module.
                if state.dispatch_table.func_to_module[func_idx] == module_idx {
                    let ptr = jit.module.get_finalized_function(func_id);
                    state.dispatch_table.fn_ptrs[func_idx].store(ptr as u64, Ordering::Release);
                }
            }
        }

        // Set the compiled flag ONLY for the triggered module.
        state.dispatch_table.compiled_flags[module_idx].store(true, Ordering::Release);
    });
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
    let sig = jit_module
        .declarations()
        .get_function_decl(func_id)
        .signature
        .clone();

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
    builder
        .ins()
        .brif(is_compiled, call_block, &[], compile_block, &[]);

    // Compile block: call compile_trigger(module_idx), then fall through to call_block
    builder.switch_to_block(compile_block);
    let compile_trigger_ref =
        jit_module.declare_func_in_func(compile_trigger_func_id, builder.func);
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
    jit_module.define_function(func_id, jit_ctx).map_err(|e| {
        CodegenError::internal_with_context("failed to define lazy stub", format!("{:?}", e))
    })?;

    jit_ctx.clear();

    Ok(())
}
