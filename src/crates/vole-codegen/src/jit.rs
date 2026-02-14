// src/codegen/jit.rs

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::errors::{CodegenError, CodegenResult};
use crate::runtime_registry::{
    AbiTy, SigSpec, all_linkable_symbols, codegen_symbols, signature_for,
};

/// Cache of compiled module functions that can be shared across JitContexts.
/// Supports incremental growth: new JIT contexts can be added without
/// invalidating existing function pointers.
pub struct CompiledModules {
    /// JIT contexts holding compiled module code. Function pointers in `functions`
    /// point into these contexts' compiled code, so they must remain alive.
    /// Multiple contexts accumulate as new modules are discovered across test files.
    /// Only accessed via `push` (to add new contexts); never read directly.
    jit_contexts: Vec<JitContext>,
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
    pub fn new(mut jit: JitContext, module_paths: Vec<String>) -> CodegenResult<Self> {
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
            jit_contexts: vec![jit],
            functions,
            compiled_module_paths: module_paths.into_iter().collect(),
        })
    }

    /// Add a new JIT context's compiled functions to this cache.
    /// The JIT context is kept alive so its function pointers remain valid.
    /// New functions and module paths are merged into the existing maps.
    pub fn extend(&mut self, mut jit: JitContext, module_paths: Vec<String>) -> CodegenResult<()> {
        // Finalize to get function pointers
        jit.finalize()?;

        // Extract and merge function pointers (new functions override old ones)
        for (name, &func_id) in &jit.func_ids {
            let ptr = jit.module.get_finalized_function(func_id);
            self.functions.insert(name.clone(), ptr);
        }

        // Merge module paths
        self.compiled_module_paths.extend(module_paths);

        // Keep the JIT context alive
        self.jit_contexts.push(jit);

        Ok(())
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
            .expect("INTERNAL: Cranelift config: invalid 'use_colocated_libcalls' flag");
        flag_builder
            .set("is_pic", "false")
            .expect("INTERNAL: Cranelift config: invalid 'is_pic' flag");
        // Enable LLVM ABI extensions for i128 support in function signatures
        flag_builder
            .set("enable_llvm_abi_extensions", "true")
            .expect("INTERNAL: Cranelift config: invalid 'enable_llvm_abi_extensions' flag");

        // Always enable speed optimizations for better codegen
        flag_builder
            .set("opt_level", "speed")
            .expect("INTERNAL: Cranelift config: invalid 'opt_level' flag");

        // Apply release mode settings
        if options.release {
            // Disable IR verifier for faster compilation
            flag_builder
                .set("enable_verifier", "false")
                .expect("INTERNAL: Cranelift config: invalid 'enable_verifier' flag");
        }

        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("native ISA not available: {}", msg);
        });

        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .expect("INTERNAL: Cranelift config: failed to build ISA from native target");

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
        for symbol in codegen_symbols() {
            let sig = self.create_signature_from_spec(signature_for(symbol.key));
            self.import_function(symbol.c_name, &sig);
        }
    }

    fn register_runtime_symbols(builder: &mut JITBuilder) {
        for symbol in all_linkable_symbols() {
            builder.symbol(symbol.c_name, symbol.ptr);
        }
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

    fn abi_ty_to_type(&self, ty: AbiTy) -> Type {
        match ty {
            AbiTy::Ptr => self.pointer_type(),
            AbiTy::I8 => types::I8,
            AbiTy::I32 => types::I32,
            AbiTy::I64 => types::I64,
            AbiTy::I128 => types::I128,
            AbiTy::F32 => types::F32,
            AbiTy::F64 => types::F64,
        }
    }

    fn create_signature_from_spec(&self, spec: SigSpec) -> Signature {
        let mut sig = self.module.make_signature();
        for &param in spec.params {
            sig.params.push(AbiParam::new(self.abi_ty_to_type(param)));
        }
        if let Some(ret) = spec.ret {
            sig.returns.push(AbiParam::new(self.abi_ty_to_type(ret)));
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
    pub fn define_function(&mut self, func_id: FuncId) -> CodegenResult<()> {
        // Run CFG cleanup to eliminate trampoline blocks before Cranelift compilation
        crate::control_flow::cleanup_cfg(&mut self.ctx.func);

        // Run loop parameter optimization if enabled
        if self.loop_param_opt {
            crate::control_flow::optimize_loop_params(&mut self.ctx.func);
        }

        // Enable disassembly if requested
        if self.disasm {
            self.ctx.set_disasm(true);
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(CodegenError::cranelift)?;

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
    pub fn finalize(&mut self) -> CodegenResult<()> {
        self.module.finalize_definitions().map_err(|e| {
            CodegenError::internal_with_context("finalization error", format!("{:?}", e))
        })?;

        if std::env::var_os("VOLE_DUMP_FN_PTRS").is_some() {
            for (name, &func_id) in &self.func_ids {
                let ptr = self.module.get_finalized_function(func_id);
                eprintln!("fnptr {} {:p}", name, ptr);
            }
        }

        Ok(())
    }

    /// Get a function pointer by name
    pub fn get_function_ptr(&self, name: &str) -> Option<*const u8> {
        self.func_ids
            .get(name)
            .map(|&func_id| self.module.get_finalized_function(func_id))
    }

    /// Check if a function exists by name (exported functions only).
    pub fn has_function(&self, name: &str) -> bool {
        self.func_ids.contains_key(name)
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
        jit.finalize().expect("INTERNAL: JIT finalization failed");

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
        jit.finalize().expect("INTERNAL: JIT finalization failed");

        let fn_ptr = jit.get_function_ptr("add").unwrap();
        let add: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(fn_ptr) };
        assert_eq!(add(10, 32), 42);
        assert_eq!(add(-5, 5), 0);
    }
}
