// src/codegen/compiler/mod.rs
//
// NOTE: This file contains legacy code being migrated to split impl blocks.
// The new code is in expr.rs, stmt.rs, calls.rs, ops.rs, structs.rs, lambda.rs.
// Functions here are kept for backward compatibility during migration.

#![allow(dead_code)]
mod calls;
mod fields;
mod methods;
mod ops;
mod patterns;
mod strings;

use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::stmt::compile_block;
use super::types::{
    CompileCtx, TypeMetadata, resolve_type_expr_full, resolve_type_expr_with_errors,
    type_to_cranelift,
};
use crate::codegen::JitContext;
use crate::frontend::{
    ClassDecl, Decl, FuncDecl, ImplementBlock, InterfaceDecl, InterfaceMethod, Interner, LetStmt,
    NodeId, Program, RecordDecl, Symbol, TestCase, TestsDecl, TypeExpr,
};
use crate::runtime::NativeRegistry;
use crate::sema::interface_registry::InterfaceRegistry;
use crate::sema::resolution::MethodResolutions;
use crate::sema::{ClassType, ErrorTypeInfo, RecordType, StructField, Type};

// Re-export functions from split modules

/// Metadata about a compiled test
#[derive(Debug, Clone)]
pub struct TestInfo {
    pub name: String,      // "basic math"
    pub func_name: String, // "__test_0"
    pub file: String,      // "test/unit/test_basic.vole"
    pub line: u32,
}

/// Context for control flow during compilation
pub struct ControlFlowCtx {
    /// Stack of loop exit blocks for break statements
    loop_exits: Vec<Block>,
    /// Stack of loop continue blocks for continue statements
    loop_continues: Vec<Block>,
}

impl ControlFlowCtx {
    pub fn new() -> Self {
        Self {
            loop_exits: Vec::new(),
            loop_continues: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, exit_block: Block, continue_block: Block) {
        self.loop_exits.push(exit_block);
        self.loop_continues.push(continue_block);
    }

    pub fn pop_loop(&mut self) {
        self.loop_exits.pop();
        self.loop_continues.pop();
    }

    pub fn current_loop_exit(&self) -> Option<Block> {
        self.loop_exits.last().copied()
    }

    pub fn current_loop_continue(&self) -> Option<Block> {
        self.loop_continues.last().copied()
    }
}

impl Default for ControlFlowCtx {
    fn default() -> Self {
        Self::new()
    }
}

/// Compiler for generating Cranelift IR from AST
pub struct Compiler<'a> {
    jit: &'a mut JitContext,
    interner: &'a Interner,
    pointer_type: types::Type,
    tests: Vec<TestInfo>,
    /// Global variable declarations (let statements at module level)
    globals: Vec<LetStmt>,
    /// Counter for generating unique lambda names
    lambda_counter: usize,
    /// Type aliases from semantic analysis
    type_aliases: HashMap<Symbol, Type>,
    /// Class and record metadata: name -> TypeMetadata
    type_metadata: HashMap<Symbol, TypeMetadata>,
    /// Next type ID to assign
    next_type_id: u32,
    /// Expression types from semantic analysis (includes narrowed types)
    expr_types: HashMap<NodeId, Type>,
    /// Resolved method calls from semantic analysis
    method_resolutions: MethodResolutions,
    /// Return types of compiled functions
    func_return_types: HashMap<String, Type>,
    /// Interface definitions registry
    interface_registry: InterfaceRegistry,
    /// Tracks which interfaces each type implements: type_name -> [interface_names]
    type_implements: HashMap<Symbol, Vec<Symbol>>,
    /// Error type definitions from semantic analysis
    error_types: HashMap<Symbol, ErrorTypeInfo>,
    /// Registry of native functions for external method calls
    native_registry: NativeRegistry,
    /// Module programs and their interners (for compiling pure Vole functions)
    module_programs: HashMap<String, (Program, Interner)>,
}

impl<'a> Compiler<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        jit: &'a mut JitContext,
        interner: &'a Interner,
        type_aliases: HashMap<Symbol, Type>,
        expr_types: HashMap<NodeId, Type>,
        method_resolutions: MethodResolutions,
        interface_registry: InterfaceRegistry,
        type_implements: HashMap<Symbol, Vec<Symbol>>,
        error_types: HashMap<Symbol, ErrorTypeInfo>,
        module_programs: HashMap<String, (Program, Interner)>,
    ) -> Self {
        let pointer_type = jit.pointer_type();

        // Initialize native registry with stdlib functions
        let mut native_registry = NativeRegistry::new();
        crate::runtime::stdlib::register_stdlib(&mut native_registry);

        Self {
            jit,
            interner,
            pointer_type,
            tests: Vec::new(),
            globals: Vec::new(),
            lambda_counter: 0,
            type_aliases,
            type_metadata: HashMap::new(),
            next_type_id: 0,
            expr_types,
            method_resolutions,
            func_return_types: HashMap::new(),
            interface_registry,
            type_implements,
            error_types,
            native_registry,
            module_programs,
        }
    }

    /// Set the source file path for error reporting.
    /// The string is stored in the JitContext so it lives as long as the JIT code.
    pub fn set_source_file(&mut self, file: &str) {
        self.jit.set_source_file(file);
    }

    /// Get the source file pointer and length from the JitContext.
    fn source_file_ptr(&self) -> (*const u8, usize) {
        self.jit.source_file_ptr()
    }

    /// Get the source file as a string for TestInfo metadata.
    fn source_file_str(&self) -> String {
        let (ptr, len) = self.jit.source_file_ptr();
        if ptr.is_null() || len == 0 {
            String::new()
        } else {
            unsafe {
                std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len)).to_string()
            }
        }
    }

    /// Take the compiled test metadata, leaving an empty vec
    pub fn take_tests(&mut self) -> Vec<TestInfo> {
        std::mem::take(&mut self.tests)
    }

    /// Compile a complete program
    pub fn compile_program(&mut self, program: &Program) -> Result<(), String> {
        // Compile module functions first (before main program)
        self.compile_module_functions()?;

        // Count total tests to assign unique IDs
        let mut test_count = 0usize;

        // First pass: declare all functions and tests, collect globals
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let sig = self.create_function_signature(func);
                    let name = self.interner.resolve(func.name);
                    self.jit.declare_function(name, &sig);
                    // Record return type for use in call expressions
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_with_errors(
                                t,
                                &self.type_aliases,
                                &self.interface_registry,
                                &self.error_types,
                                self.interner,
                            )
                        })
                        .unwrap_or(Type::Void);
                    self.func_return_types.insert(name.to_string(), return_type);
                }
                Decl::Tests(tests_decl) => {
                    // Declare each test as __test_N with signature () -> i64
                    for _ in &tests_decl.tests {
                        let func_name = format!("__test_{}", test_count);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        self.jit.declare_function(&func_name, &sig);
                        test_count += 1;
                    }
                }
                Decl::Let(let_stmt) => {
                    // Collect global variable declarations
                    self.globals.push(let_stmt.clone());
                }
                Decl::Class(class) => {
                    self.register_class(class, program);
                }
                Decl::Record(record) => {
                    self.register_record(record, program);
                }
                Decl::Interface(_) => {
                    // Interface declarations don't generate code directly
                }
                Decl::Implement(impl_block) => {
                    self.register_implement_block(impl_block);
                }
                Decl::Error(_) => {
                    // Error declarations don't generate code in pass 1
                }
                Decl::External(_) => {
                    // External blocks don't generate code in pass 1
                }
            }
        }

        // Reset counter for second pass
        test_count = 0;

        // Second pass: compile function bodies and tests
        // Note: Decl::Let globals are handled by inlining their initializers
        // when referenced (see compile_expr for ExprKind::Identifier)
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.compile_function(func)?;
                }
                Decl::Tests(tests_decl) => {
                    self.compile_tests(tests_decl, &mut test_count)?;
                }
                Decl::Let(_) => {
                    // Globals are handled during identifier lookup
                }
                Decl::Class(class) => {
                    self.compile_class_methods(class, program)?;
                }
                Decl::Record(record) => {
                    self.compile_record_methods(record, program)?;
                }
                Decl::Interface(_) => {
                    // Interface methods are compiled when used via implement blocks
                }
                Decl::Implement(impl_block) => {
                    self.compile_implement_block(impl_block)?;
                }
                Decl::Error(_) => {
                    // Error declarations don't generate code in pass 2
                }
                Decl::External(_) => {
                    // External blocks don't generate code in pass 2
                }
            }
        }

        Ok(())
    }

    /// Compile pure Vole functions from imported modules.
    /// These are functions defined in module files (not external FFI functions).
    fn compile_module_functions(&mut self) -> Result<(), String> {
        // Take ownership of module_programs temporarily to avoid borrow issues
        let module_programs = std::mem::take(&mut self.module_programs);

        for (module_path, (program, module_interner)) in &module_programs {
            // Extract module globals (let statements)
            let module_globals: Vec<LetStmt> = program
                .declarations
                .iter()
                .filter_map(|decl| {
                    if let Decl::Let(let_stmt) = decl {
                        Some(let_stmt.clone())
                    } else {
                        None
                    }
                })
                .collect();

            // First pass: declare pure Vole functions
            for decl in &program.declarations {
                if let Decl::Function(func) = decl {
                    let func_name = module_interner.resolve(func.name);
                    let mangled_name = format!("{}::{}", module_path, func_name);

                    // Create signature and declare function
                    let sig = self.create_function_signature(func);
                    self.jit.declare_function(&mangled_name, &sig);

                    // Record return type
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_with_errors(
                                t,
                                &self.type_aliases,
                                &self.interface_registry,
                                &self.error_types,
                                self.interner,
                            )
                        })
                        .unwrap_or(Type::Void);
                    self.func_return_types
                        .insert(mangled_name.clone(), return_type);
                }
            }

            // Second pass: compile pure Vole function bodies
            for decl in &program.declarations {
                if let Decl::Function(func) = decl {
                    let func_name = module_interner.resolve(func.name);
                    let mangled_name = format!("{}::{}", module_path, func_name);
                    self.compile_module_function(
                        module_path,
                        &mangled_name,
                        func,
                        module_interner,
                        &module_globals,
                    )?;
                }
            }
        }

        // Restore module_programs
        self.module_programs = module_programs;

        Ok(())
    }

    /// Compile a single module function with its own interner
    fn compile_module_function(
        &mut self,
        module_path: &str,
        mangled_name: &str,
        func: &FuncDecl,
        module_interner: &Interner,
        module_globals: &[LetStmt],
    ) -> Result<(), String> {
        let func_id = *self
            .jit
            .func_ids
            .get(mangled_name)
            .ok_or_else(|| format!("Module function {} not declared", mangled_name))?;

        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig;

        // Collect param types
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_with_errors(
                        &p.ty,
                        &self.type_aliases,
                        &self.interface_registry,
                        &self.error_types,
                        self.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_with_errors(
                    &p.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_with_errors(
                t,
                &self.type_aliases,
                &self.interface_registry,
                &self.error_types,
                self.interner,
            )
        });

        // Get source file pointer
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Bind parameters to variables
            let params = builder.block_params(entry_block).to_vec();
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile function body with module's interner
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: module_interner, // Use module's interner
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: module_globals, // Use module's globals
                lambda_counter: &mut self.lambda_counter,
                type_aliases: &self.type_aliases,
                type_metadata: &self.type_metadata,
                expr_types: &self.expr_types,
                method_resolutions: &self.method_resolutions,
                func_return_types: &self.func_return_types,
                interface_registry: &self.interface_registry,
                current_function_return_type: return_type,
                error_types: &self.error_types,
                native_registry: &self.native_registry,
                current_module: Some(module_path), // We're compiling module code
            };
            let terminated = compile_block(
                &mut builder,
                &func.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    fn create_function_signature(&self, func: &FuncDecl) -> Signature {
        let mut params = Vec::new();
        for param in &func.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_with_errors(
                    &param.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = func.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_with_errors(
                    t,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Create a method signature (with self as first parameter)
    fn create_method_signature(&self, method: &FuncDecl) -> Signature {
        // Methods have `self` as implicit first parameter (pointer to instance)
        let mut params = vec![self.pointer_type];
        for param in &method.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_with_errors(
                    &param.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_with_errors(
                    t,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Create a method signature for implement blocks (self type can be primitive or pointer)
    fn create_implement_method_signature(&self, method: &FuncDecl, self_type: &Type) -> Signature {
        // For implement blocks, `self` type depends on the target type
        // Primitives use their actual type, classes/records use pointer
        let self_cranelift_type = type_to_cranelift(self_type, self.pointer_type);
        let mut params = vec![self_cranelift_type];
        for param in &method.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_with_errors(
                    &param.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_with_errors(
                    t,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Create a method signature for an interface method (self as pointer + params)
    fn create_interface_method_signature(&self, method: &InterfaceMethod) -> Signature {
        // Methods have `self` as implicit first parameter (pointer to instance)
        let mut params = vec![self.pointer_type];
        for param in &method.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_with_errors(
                    &param.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_with_errors(
                    t,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Find an interface declaration by name in the program
    fn find_interface_decl<'b>(
        &self,
        program: &'b Program,
        interface_name: Symbol,
    ) -> Option<&'b InterfaceDecl> {
        for decl in &program.declarations {
            if let Decl::Interface(iface) = decl
                && iface.name == interface_name
            {
                return Some(iface);
            }
        }
        None
    }

    /// Register a class type and declare its methods
    fn register_class(&mut self, class: &ClassDecl, program: &Program) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        for (i, field) in class.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            struct_fields.push(StructField {
                name: field.name,
                ty: resolve_type_expr_full(
                    &field.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    self.interner,
                ),
                slot: i,
            });
        }

        // Create the Vole type
        let vole_type = Type::Class(ClassType {
            name: class.name,
            fields: struct_fields,
        });

        // Collect method return types
        let mut method_return_types = HashMap::new();
        for method in &class.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| {
                    resolve_type_expr_full(
                        t,
                        &self.type_aliases,
                        &self.interface_registry,
                        self.interner,
                    )
                })
                .unwrap_or(Type::Void);
            method_return_types.insert(method.name, return_type);
        }

        // Collect method names that the class directly defines
        let direct_methods: std::collections::HashSet<_> =
            class.methods.iter().map(|m| m.name).collect();

        // Also add return types for default methods from implemented interfaces
        if let Some(interfaces) = self.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let return_type = method
                                .return_type
                                .as_ref()
                                .map(|t| {
                                    resolve_type_expr_full(
                                        t,
                                        &self.type_aliases,
                                        &self.interface_registry,
                                        self.interner,
                                    )
                                })
                                .unwrap_or(Type::Void);
                            method_return_types.insert(method.name, return_type);
                        }
                    }
                }
            }
        }

        self.type_metadata.insert(
            class.name,
            TypeMetadata {
                type_id,
                field_slots,
                is_class: true,
                vole_type,
                method_return_types,
            },
        );

        // Declare methods as functions: ClassName_methodName
        let type_name = self.interner.resolve(class.name);
        for method in &class.methods {
            let method_name_str = self.interner.resolve(method.name);
            let full_name = format!("{}_{}", type_name, method_name_str);
            let sig = self.create_method_signature(method);
            self.jit.declare_function(&full_name, &sig);
        }

        // Declare default methods from implemented interfaces
        if let Some(interfaces) = self.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let method_name_str = self.interner.resolve(method.name);
                            let full_name = format!("{}_{}", type_name, method_name_str);
                            let sig = self.create_interface_method_signature(method);
                            self.jit.declare_function(&full_name, &sig);
                        }
                    }
                }
            }
        }
    }

    /// Register a record type and declare its methods
    fn register_record(&mut self, record: &RecordDecl, program: &Program) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        for (i, field) in record.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            struct_fields.push(StructField {
                name: field.name,
                ty: resolve_type_expr_full(
                    &field.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    self.interner,
                ),
                slot: i,
            });
        }

        // Create the Vole type
        let vole_type = Type::Record(RecordType {
            name: record.name,
            fields: struct_fields,
        });

        // Collect method return types
        let mut method_return_types = HashMap::new();
        for method in &record.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| {
                    resolve_type_expr_full(
                        t,
                        &self.type_aliases,
                        &self.interface_registry,
                        self.interner,
                    )
                })
                .unwrap_or(Type::Void);
            method_return_types.insert(method.name, return_type);
        }

        // Collect method names that the record directly defines
        let direct_methods: std::collections::HashSet<_> =
            record.methods.iter().map(|m| m.name).collect();

        // Also add return types for default methods from implemented interfaces
        if let Some(interfaces) = self.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let return_type = method
                                .return_type
                                .as_ref()
                                .map(|t| {
                                    resolve_type_expr_full(
                                        t,
                                        &self.type_aliases,
                                        &self.interface_registry,
                                        self.interner,
                                    )
                                })
                                .unwrap_or(Type::Void);
                            method_return_types.insert(method.name, return_type);
                        }
                    }
                }
            }
        }

        self.type_metadata.insert(
            record.name,
            TypeMetadata {
                type_id,
                field_slots,
                is_class: false,
                vole_type,
                method_return_types,
            },
        );

        // Declare methods as functions: RecordName_methodName
        let type_name = self.interner.resolve(record.name);
        for method in &record.methods {
            let method_name_str = self.interner.resolve(method.name);
            let full_name = format!("{}_{}", type_name, method_name_str);
            let sig = self.create_method_signature(method);
            self.jit.declare_function(&full_name, &sig);
        }

        // Declare default methods from implemented interfaces
        if let Some(interfaces) = self.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let method_name_str = self.interner.resolve(method.name);
                            let full_name = format!("{}_{}", type_name, method_name_str);
                            let sig = self.create_interface_method_signature(method);
                            self.jit.declare_function(&full_name, &sig);
                        }
                    }
                }
            }
        }
    }

    /// Compile methods for a class
    fn compile_class_methods(
        &mut self,
        class: &ClassDecl,
        program: &Program,
    ) -> Result<(), String> {
        let metadata = self
            .type_metadata
            .get(&class.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Internal error: class {} not registered",
                    self.interner.resolve(class.name)
                )
            })?;

        for method in &class.methods {
            self.compile_method(method, class.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            class.methods.iter().map(|m| m.name).collect();
        if let Some(interfaces) = self.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            self.compile_default_method(method, class.name, &metadata)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Compile methods for a record
    fn compile_record_methods(
        &mut self,
        record: &RecordDecl,
        program: &Program,
    ) -> Result<(), String> {
        let metadata = self
            .type_metadata
            .get(&record.name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Internal error: record {} not registered",
                    self.interner.resolve(record.name)
                )
            })?;

        for method in &record.methods {
            self.compile_method(method, record.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            record.methods.iter().map(|m| m.name).collect();
        if let Some(interfaces) = self.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            self.compile_default_method(method, record.name, &metadata)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Get the type name symbol from a TypeExpr (for implement blocks on records/classes)
    fn get_type_name_symbol(&self, ty: &TypeExpr) -> Option<Symbol> {
        match ty {
            TypeExpr::Named(sym) => Some(*sym),
            _ => None,
        }
    }

    /// Get the type name string from a TypeExpr (works for primitives and named types)
    fn get_type_name_from_expr(&self, ty: &TypeExpr) -> Option<String> {
        match ty {
            TypeExpr::Primitive(p) => Some(Type::from_primitive(*p).name().to_string()),
            TypeExpr::Named(sym) => Some(self.interner.resolve(*sym).to_string()),
            _ => None,
        }
    }

    /// Register implement block methods (first pass)
    fn register_implement_block(&mut self, impl_block: &ImplementBlock) {
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return; // Unsupported type for implement block
        };

        // Get the Vole type for the target (used for creating signature)
        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        let self_vole_type = match &impl_block.target_type {
            TypeExpr::Primitive(p) => Type::from_primitive(*p),
            TypeExpr::Named(sym) => self
                .type_metadata
                .get(sym)
                .map(|m| m.vole_type.clone())
                .unwrap_or(Type::Error),
            _ => resolve_type_expr_full(
                &impl_block.target_type,
                &self.type_aliases,
                &self.interface_registry,
                self.interner,
            ),
        };

        // For named types (records/classes), add method return types to metadata
        if let Some(type_sym) = self.get_type_name_symbol(&impl_block.target_type)
            && let Some(metadata) = self.type_metadata.get_mut(&type_sym)
        {
            for method in &impl_block.methods {
                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| {
                        resolve_type_expr_full(
                            t,
                            &self.type_aliases,
                            &self.interface_registry,
                            self.interner,
                        )
                    })
                    .unwrap_or(Type::Void);
                metadata
                    .method_return_types
                    .insert(method.name, return_type);
            }
        }

        // Declare methods as functions: TypeName::methodName (implement block convention)
        for method in &impl_block.methods {
            let method_name_str = self.interner.resolve(method.name);
            let full_name = format!("{}::{}", type_name, method_name_str);
            let sig = self.create_implement_method_signature(method, &self_vole_type);
            self.jit.declare_function(&full_name, &sig);
        }
    }

    /// Compile implement block methods (second pass)
    fn compile_implement_block(&mut self, impl_block: &ImplementBlock) -> Result<(), String> {
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return Ok(()); // Unsupported type for implement block
        };

        // Get the Vole type for `self` binding
        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        let self_vole_type = match &impl_block.target_type {
            TypeExpr::Primitive(p) => Type::from_primitive(*p),
            TypeExpr::Named(sym) => self
                .type_metadata
                .get(sym)
                .map(|m| m.vole_type.clone())
                .unwrap_or(Type::Error),
            _ => resolve_type_expr_full(
                &impl_block.target_type,
                &self.type_aliases,
                &self.interface_registry,
                self.interner,
            ),
        };

        for method in &impl_block.methods {
            self.compile_implement_method(method, &type_name, &self_vole_type)?;
        }
        Ok(())
    }

    /// Compile a method from an implement block
    fn compile_implement_method(
        &mut self,
        method: &FuncDecl,
        type_name: &str,
        self_vole_type: &Type,
    ) -> Result<(), String> {
        let method_name_str = self.interner.resolve(method.name);
        let full_name = format!("{}::{}", type_name, method_name_str);

        let func_id = *self
            .jit
            .func_ids
            .get(&full_name)
            .ok_or_else(|| format!("Internal error: method {} not declared", full_name))?;

        // Create method signature with correct self type (primitives use their type, not pointer)
        let sig = self.create_implement_method_signature(method, self_vole_type);
        self.jit.ctx.func.signature = sig;

        // Get the Cranelift type for self
        let self_cranelift_type = type_to_cranelift(self_vole_type, self.pointer_type);

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.type_aliases,
                        &self.interface_registry,
                        self.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_full(
                    &p.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    self.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Clone type for the closure
        let self_type = self_vole_type.clone();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Get entry block params (self + user params)
            let params = builder.block_params(entry_block).to_vec();

            // Bind `self` as the first parameter (using correct type for primitives)
            let self_sym = self
                .interner
                .lookup("self")
                .ok_or_else(|| "Internal error: 'self' keyword not interned".to_string())?;
            let self_var = builder.declare_var(self_cranelift_type);
            builder.def_var(self_var, params[0]);
            variables.insert(self_sym, (self_var, self_type));

            // Bind remaining parameters
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile method body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_aliases: &self.type_aliases,
                type_metadata: &self.type_metadata,
                expr_types: &self.expr_types,
                method_resolutions: &self.method_resolutions,
                func_return_types: &self.func_return_types,
                interface_registry: &self.interface_registry,
                current_function_return_type: None, // Methods don't use raise statements yet
                error_types: &self.error_types,
                native_registry: &self.native_registry,
                current_module: None,
            };
            let terminated = compile_block(
                &mut builder,
                &method.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            if !terminated {
                // Return void if no explicit return
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit
            .module
            .define_function(func_id, &mut self.jit.ctx)
            .map_err(|e| e.to_string())?;
        self.jit.module.clear_context(&mut self.jit.ctx);

        Ok(())
    }

    /// Compile a single method
    fn compile_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> Result<(), String> {
        let type_name_str = self.interner.resolve(type_name);
        let method_name_str = self.interner.resolve(method.name);
        let full_name = format!("{}_{}", type_name_str, method_name_str);

        let func_id = *self
            .jit
            .func_ids
            .get(&full_name)
            .ok_or_else(|| format!("Internal error: method {} not declared", full_name))?;

        // Create method signature (self + params)
        let sig = self.create_method_signature(method);
        self.jit.ctx.func.signature = sig;

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.type_aliases,
                        &self.interface_registry,
                        self.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_full(
                    &p.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    self.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Clone metadata for the closure
        let self_vole_type = metadata.vole_type.clone();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Get entry block params (self + user params)
            let params = builder.block_params(entry_block).to_vec();

            // Bind `self` as the first parameter
            // Note: "self" should already be interned during parsing of method bodies
            let self_sym = self
                .interner
                .lookup("self")
                .ok_or_else(|| "Internal error: 'self' keyword not interned".to_string())?;
            let self_var = builder.declare_var(self.pointer_type);
            builder.def_var(self_var, params[0]);
            variables.insert(self_sym, (self_var, self_vole_type));

            // Bind remaining parameters
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile method body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_aliases: &self.type_aliases,
                type_metadata: &self.type_metadata,
                expr_types: &self.expr_types,
                method_resolutions: &self.method_resolutions,
                func_return_types: &self.func_return_types,
                interface_registry: &self.interface_registry,
                current_function_return_type: None, // Methods don't use raise statements yet
                error_types: &self.error_types,
                native_registry: &self.native_registry,
                current_module: None,
            };
            let terminated = compile_block(
                &mut builder,
                &method.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Compile a default method from an interface, monomorphized for a concrete type
    fn compile_default_method(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> Result<(), String> {
        let type_name_str = self.interner.resolve(type_name);
        let method_name_str = self.interner.resolve(method.name);
        let full_name = format!("{}_{}", type_name_str, method_name_str);

        let func_id =
            *self.jit.func_ids.get(&full_name).ok_or_else(|| {
                format!("Internal error: default method {} not declared", full_name)
            })?;

        // Create method signature (self + params)
        let sig = self.create_interface_method_signature(method);
        self.jit.ctx.func.signature = sig;

        // Collect param types (not including self)
        let param_types: Vec<types::Type> = method
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.type_aliases,
                        &self.interface_registry,
                        self.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_full(
                    &p.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    self.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = method.params.iter().map(|p| p.name).collect();

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Clone metadata for the closure - self has the concrete type!
        let self_vole_type = metadata.vole_type.clone();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Get entry block params (self + user params)
            let params = builder.block_params(entry_block).to_vec();

            // Bind `self` as the first parameter with the concrete type
            let self_sym = self
                .interner
                .lookup("self")
                .ok_or_else(|| "Internal error: 'self' keyword not interned".to_string())?;
            let self_var = builder.declare_var(self.pointer_type);
            builder.def_var(self_var, params[0]);
            variables.insert(self_sym, (self_var, self_vole_type));

            // Bind remaining parameters
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params[1..].iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile method body (must exist for default methods)
            let body = method.body.as_ref().ok_or_else(|| {
                format!(
                    "Internal error: default method {} has no body",
                    method_name_str
                )
            })?;

            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_aliases: &self.type_aliases,
                type_metadata: &self.type_metadata,
                expr_types: &self.expr_types,
                method_resolutions: &self.method_resolutions,
                func_return_types: &self.func_return_types,
                interface_registry: &self.interface_registry,
                current_function_return_type: None, // Default methods don't use raise statements yet
                error_types: &self.error_types,
                native_registry: &self.native_registry,
                current_module: None,
            };
            let terminated =
                compile_block(&mut builder, body, &mut variables, &mut cf_ctx, &mut ctx)?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    fn compile_function(&mut self, func: &FuncDecl) -> Result<(), String> {
        let name = self.interner.resolve(func.name);
        let func_id = *self.jit.func_ids.get(name).unwrap();

        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig;

        // Collect param types before borrowing ctx.func
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_with_errors(
                        &p.ty,
                        &self.type_aliases,
                        &self.interface_registry,
                        &self.error_types,
                        self.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_with_errors(
                    &p.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_with_errors(
                t,
                &self.type_aliases,
                &self.interface_registry,
                &self.error_types,
                self.interner,
            )
        });

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Bind parameters to variables
            let params = builder.block_params(entry_block).to_vec();
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_aliases: &self.type_aliases,
                type_metadata: &self.type_metadata,
                expr_types: &self.expr_types,
                method_resolutions: &self.method_resolutions,
                func_return_types: &self.func_return_types,
                interface_registry: &self.interface_registry,
                current_function_return_type: return_type,
                error_types: &self.error_types,
                native_registry: &self.native_registry,
                current_module: None,
            };
            let terminated = compile_block(
                &mut builder,
                &func.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Compile all tests in a tests block
    fn compile_tests(
        &mut self,
        tests_decl: &TestsDecl,
        test_count: &mut usize,
    ) -> Result<(), String> {
        for test in &tests_decl.tests {
            let func_name = format!("__test_{}", *test_count);
            let func_id = *self.jit.func_ids.get(&func_name).unwrap();

            // Create function signature: () -> i64
            let sig = self.jit.create_signature(&[], Some(types::I64));
            self.jit.ctx.func.signature = sig;

            // Get source file pointer before borrowing ctx.func
            let source_file_ptr = self.source_file_ptr();

            // Create function builder
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

                let entry_block = builder.create_block();
                builder.switch_to_block(entry_block);

                // No parameters or variables for tests (they start fresh)
                let mut variables = HashMap::new();

                // Compile test body
                let mut cf_ctx = ControlFlowCtx::new();
                let mut ctx = CompileCtx {
                    interner: self.interner,
                    pointer_type: self.pointer_type,
                    module: &mut self.jit.module,
                    func_ids: &mut self.jit.func_ids,
                    source_file_ptr,
                    globals: &self.globals,
                    lambda_counter: &mut self.lambda_counter,
                    type_aliases: &self.type_aliases,
                    type_metadata: &self.type_metadata,
                    expr_types: &self.expr_types,
                    method_resolutions: &self.method_resolutions,
                    func_return_types: &self.func_return_types,
                    interface_registry: &self.interface_registry,
                    current_function_return_type: None, // Tests don't have a declared return type
                    error_types: &self.error_types,
                    native_registry: &self.native_registry,
                    current_module: None,
                };
                let terminated = compile_block(
                    &mut builder,
                    &test.body,
                    &mut variables,
                    &mut cf_ctx,
                    &mut ctx,
                )?;

                // If not already terminated, return 0 (test passed)
                if !terminated {
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().return_(&[zero]);
                }

                builder.seal_all_blocks();
                builder.finalize();
            }

            // Define the function
            self.jit.define_function(func_id)?;
            self.jit.clear();

            // Record test metadata
            let line = test.span.line;
            self.tests.push(TestInfo {
                name: test.name.clone(),
                func_name: func_name.clone(),
                file: self.source_file_str(),
                line,
            });

            *test_count += 1;
        }

        Ok(())
    }

    /// Compile program to CLIF IR and write to the given writer.
    /// Does not finalize for execution - just generates IR for inspection.
    pub fn compile_to_ir<W: std::io::Write>(
        &mut self,
        program: &Program,
        writer: &mut W,
        include_tests: bool,
    ) -> Result<(), String> {
        // First pass: declare all functions so they can reference each other
        let mut test_count = 0usize;
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let sig = self.create_function_signature(func);
                    let name = self.interner.resolve(func.name);
                    self.jit.declare_function(name, &sig);
                    // Record return type for use in call expressions
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_with_errors(
                                t,
                                &self.type_aliases,
                                &self.interface_registry,
                                &self.error_types,
                                self.interner,
                            )
                        })
                        .unwrap_or(Type::Void);
                    self.func_return_types.insert(name.to_string(), return_type);
                }
                Decl::Tests(tests_decl) if include_tests => {
                    for _ in &tests_decl.tests {
                        let func_name = format!("__test_{}", test_count);
                        let sig = self.jit.create_signature(&[], Some(types::I64));
                        self.jit.declare_function(&func_name, &sig);
                        test_count += 1;
                    }
                }
                _ => {}
            }
        }

        // Second pass: build and emit IR for each function
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let name = self.interner.resolve(func.name);
                    self.build_function_ir(func)?;
                    writeln!(writer, "// func {}", name).map_err(|e| e.to_string())?;
                    writeln!(writer, "{}", self.jit.ctx.func).map_err(|e| e.to_string())?;
                    self.jit.clear();
                }
                Decl::Tests(tests_decl) if include_tests => {
                    for test in &tests_decl.tests {
                        self.build_test_ir(test)?;
                        writeln!(writer, "// test \"{}\"", test.name).map_err(|e| e.to_string())?;
                        writeln!(writer, "{}", self.jit.ctx.func).map_err(|e| e.to_string())?;
                        self.jit.clear();
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Build IR for a single function without defining it.
    /// Similar to compile_function but doesn't call define_function.
    fn build_function_ir(&mut self, func: &FuncDecl) -> Result<(), String> {
        // Create function signature
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig;

        // Collect param types before borrowing ctx.func
        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| {
                type_to_cranelift(
                    &resolve_type_expr_with_errors(
                        &p.ty,
                        &self.type_aliases,
                        &self.interface_registry,
                        &self.error_types,
                        self.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_with_errors(
                    &p.ty,
                    &self.type_aliases,
                    &self.interface_registry,
                    &self.error_types,
                    self.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_with_errors(
                t,
                &self.type_aliases,
                &self.interface_registry,
                &self.error_types,
                self.interner,
            )
        });

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            // Build variables map
            let mut variables = HashMap::new();

            // Bind parameters to variables
            let params = builder.block_params(entry_block).to_vec();
            for (((name, ty), vole_ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(param_vole_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, (var, vole_ty.clone()));
            }

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::new();
            let empty_type_metadata = HashMap::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_aliases: &self.type_aliases,
                type_metadata: &empty_type_metadata,
                expr_types: &self.expr_types,
                method_resolutions: &self.method_resolutions,
                func_return_types: &self.func_return_types,
                interface_registry: &self.interface_registry,
                current_function_return_type: return_type,
                error_types: &self.error_types,
                native_registry: &self.native_registry,
                current_module: None,
            };
            let terminated = compile_block(
                &mut builder,
                &func.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // Add implicit return if no explicit return
            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // NOTE: We intentionally do NOT call define_function here.
        // This method is for IR inspection only.

        Ok(())
    }

    /// Build IR for a single test case without defining it.
    /// Similar to test compilation in compile_tests but doesn't call define_function.
    fn build_test_ir(&mut self, test: &TestCase) -> Result<(), String> {
        // Create function signature: () -> i64
        let sig = self.jit.create_signature(&[], Some(types::I64));
        self.jit.ctx.func.signature = sig;

        // Get source file pointer before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();

        // Create function builder
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.switch_to_block(entry_block);

            // No parameters or variables for tests (they start fresh)
            let mut variables = HashMap::new();

            // Compile test body
            let mut cf_ctx = ControlFlowCtx::new();
            let empty_type_metadata = HashMap::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_aliases: &self.type_aliases,
                type_metadata: &empty_type_metadata,
                expr_types: &self.expr_types,
                method_resolutions: &self.method_resolutions,
                func_return_types: &self.func_return_types,
                interface_registry: &self.interface_registry,
                current_function_return_type: None, // Tests don't have a declared return type
                error_types: &self.error_types,
                native_registry: &self.native_registry,
                current_module: None,
            };
            let terminated = compile_block(
                &mut builder,
                &test.body,
                &mut variables,
                &mut cf_ctx,
                &mut ctx,
            )?;

            // If not already terminated, return 0 (test passed)
            if !terminated {
                let zero = builder.ins().iconst(types::I64, 0);
                builder.ins().return_(&[zero]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        // NOTE: We intentionally do NOT call define_function here.
        // This method is for IR inspection only.

        Ok(())
    }
}

#[cfg(test)]
mod tests;
