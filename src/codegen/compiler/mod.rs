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
use super::types::{CompileCtx, TypeMetadata, resolve_type_expr_full, type_to_cranelift};
use crate::codegen::JitContext;
use crate::commands::common::AnalyzedProgram;
use crate::frontend::{
    ClassDecl, Decl, FuncDecl, ImplementBlock, InterfaceDecl, InterfaceMethod, Interner, LetStmt,
    Program, RecordDecl, Symbol, TestCase, TestsDecl, TypeExpr,
};
use crate::runtime::NativeRegistry;
use crate::sema::generic::MonomorphInstance;
use crate::sema::{ClassType, RecordType, StructField, Type};

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
    /// Reference to analyzed program (types, methods, etc.)
    analyzed: &'a AnalyzedProgram,
    pointer_type: types::Type,
    tests: Vec<TestInfo>,
    /// Global variable declarations (let statements at module level)
    globals: Vec<LetStmt>,
    /// Counter for generating unique lambda names
    lambda_counter: usize,
    /// Class and record metadata: name -> TypeMetadata
    type_metadata: HashMap<Symbol, TypeMetadata>,
    /// Next type ID to assign
    next_type_id: u32,
    /// Return types of compiled functions
    func_return_types: HashMap<String, Type>,
    /// Registry of native functions for external method calls
    native_registry: NativeRegistry,
}

impl<'a> Compiler<'a> {
    pub fn new(jit: &'a mut JitContext, analyzed: &'a AnalyzedProgram) -> Self {
        let pointer_type = jit.pointer_type();

        // Initialize native registry with stdlib functions
        let mut native_registry = NativeRegistry::new();
        crate::runtime::stdlib::register_stdlib(&mut native_registry);

        Self {
            jit,
            analyzed,
            pointer_type,
            tests: Vec::new(),
            globals: Vec::new(),
            lambda_counter: 0,
            type_metadata: HashMap::new(),
            next_type_id: 0,
            func_return_types: HashMap::new(),
            native_registry,
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

        // Pre-pass: Register all record/class names first so they're available for field type resolution
        // This allows records to reference each other (e.g., Company.ceo: Person?)
        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    self.pre_register_class(class);
                }
                Decl::Record(record) => {
                    self.pre_register_record(record);
                }
                _ => {}
            }
        }

        // First pass: declare all functions and tests, collect globals, finalize type metadata
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Skip generic functions - they're templates, not actual functions
                    if !func.type_params.is_empty() {
                        continue;
                    }
                    let sig = self.create_function_signature(func);
                    let name = self.analyzed.interner.resolve(func.name);
                    self.jit.declare_function(name, &sig);
                    // Record return type for use in call expressions
                    // Note: Use resolve_type_with_metadata so that record types (like
                    // generated generator records) are properly resolved from type_metadata
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type_with_metadata(t))
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
                    self.finalize_class(class, program);
                }
                Decl::Record(record) => {
                    self.finalize_record(record, program);
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

        // Declare monomorphized function instances before second pass
        self.declare_monomorphized_instances()?;

        // Second pass: compile function bodies and tests
        // Note: Decl::Let globals are handled by inlining their initializers
        // when referenced (see compile_expr for ExprKind::Identifier)
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    // Skip generic functions - they're compiled via monomorphized instances
                    if !func.type_params.is_empty() {
                        continue;
                    }
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

        // Compile monomorphized instances
        self.compile_monomorphized_instances(program)?;

        Ok(())
    }

    /// Compile pure Vole functions from imported modules.
    /// These are functions defined in module files (not external FFI functions).
    fn compile_module_functions(&mut self) -> Result<(), String> {
        // Collect module paths first to avoid borrow issues
        let module_paths: Vec<_> = self.analyzed.module_programs.keys().cloned().collect();

        for module_path in &module_paths {
            let (program, module_interner) = &self.analyzed.module_programs[module_path];
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
                            resolve_type_expr_full(
                                t,
                                &self.analyzed.type_aliases,
                                &self.analyzed.interface_registry,
                                &self.analyzed.interner,
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
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_full(
                    &p.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_full(
                t,
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
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
                analyzed: self.analyzed,
                interner: module_interner, // Use module's interner
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: module_globals, // Use module's globals
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: Some(module_path), // We're compiling module code
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = func.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
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
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
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
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
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
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
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

    /// Resolve a type expression using type_metadata (for record/class field types)
    /// This allows resolving types like `Person?` where Person is another record/class
    fn resolve_type_with_metadata(&self, ty: &TypeExpr) -> Type {
        use super::types::resolve_type_expr_with_metadata;
        let empty_error_types = HashMap::new();
        resolve_type_expr_with_metadata(
            ty,
            &self.analyzed.type_aliases,
            &self.analyzed.interface_registry,
            &empty_error_types,
            &self.type_metadata,
            &self.analyzed.interner,
        )
    }

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    fn pre_register_class(&mut self, class: &ClassDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Create a placeholder vole_type (will be replaced in finalize_class)
        let placeholder_type = Type::Class(ClassType {
            name: class.name,
            fields: vec![],
        });

        self.type_metadata.insert(
            class.name,
            TypeMetadata {
                type_id,
                field_slots: HashMap::new(),
                is_class: true,
                vole_type: placeholder_type,
                method_return_types: HashMap::new(),
            },
        );
    }

    /// Finalize a class type: fill in field types and declare methods
    fn finalize_class(&mut self, class: &ClassDecl, program: &Program) {
        // Get the pre-registered type_id
        let type_id = self
            .type_metadata
            .get(&class.name)
            .expect("class should be pre-registered")
            .type_id;

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        for (i, field) in class.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            struct_fields.push(StructField {
                name: field.name,
                ty: self.resolve_type_with_metadata(&field.ty),
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
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            method_return_types.insert(method.name, return_type);
        }

        // Collect method names that the class directly defines
        let direct_methods: std::collections::HashSet<_> =
            class.methods.iter().map(|m| m.name).collect();

        // Also add return types for default methods from implemented interfaces
        if let Some(interfaces) = self.analyzed.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let return_type = method
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type_with_metadata(t))
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
        let type_name = self.analyzed.interner.resolve(class.name);
        for method in &class.methods {
            let method_name_str = self.analyzed.interner.resolve(method.name);
            let full_name = format!("{}_{}", type_name, method_name_str);
            let sig = self.create_method_signature(method);
            self.jit.declare_function(&full_name, &sig);
        }

        // Declare default methods from implemented interfaces
        if let Some(interfaces) = self.analyzed.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let method_name_str = self.analyzed.interner.resolve(method.name);
                            let full_name = format!("{}_{}", type_name, method_name_str);
                            let sig = self.create_interface_method_signature(method);
                            self.jit.declare_function(&full_name, &sig);
                        }
                    }
                }
            }
        }
    }

    /// Pre-register a record type (just the name and type_id)
    /// This is called first so that field type resolution can find other records
    fn pre_register_record(&mut self, record: &RecordDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Create a placeholder vole_type (will be replaced in finalize_record)
        let placeholder_type = Type::Record(RecordType {
            name: record.name,
            fields: vec![],
        });

        self.type_metadata.insert(
            record.name,
            TypeMetadata {
                type_id,
                field_slots: HashMap::new(),
                is_class: false,
                vole_type: placeholder_type,
                method_return_types: HashMap::new(),
            },
        );
    }

    /// Finalize a record type: fill in field types and declare methods
    fn finalize_record(&mut self, record: &RecordDecl, program: &Program) {
        // Get the pre-registered type_id
        let type_id = self
            .type_metadata
            .get(&record.name)
            .expect("record should be pre-registered")
            .type_id;

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        for (i, field) in record.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            struct_fields.push(StructField {
                name: field.name,
                ty: self.resolve_type_with_metadata(&field.ty),
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
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            method_return_types.insert(method.name, return_type);
        }

        // Collect method names that the record directly defines
        let direct_methods: std::collections::HashSet<_> =
            record.methods.iter().map(|m| m.name).collect();

        // Also add return types for default methods from implemented interfaces
        if let Some(interfaces) = self.analyzed.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let return_type = method
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type_with_metadata(t))
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
        let type_name = self.analyzed.interner.resolve(record.name);
        for method in &record.methods {
            let method_name_str = self.analyzed.interner.resolve(method.name);
            let full_name = format!("{}_{}", type_name, method_name_str);
            let sig = self.create_method_signature(method);
            self.jit.declare_function(&full_name, &sig);
        }

        // Declare default methods from implemented interfaces
        if let Some(interfaces) = self.analyzed.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let method_name_str = self.analyzed.interner.resolve(method.name);
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
                    self.analyzed.interner.resolve(class.name)
                )
            })?;

        for method in &class.methods {
            self.compile_method(method, class.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            class.methods.iter().map(|m| m.name).collect();
        if let Some(interfaces) = self.analyzed.type_implements.get(&class.name).cloned() {
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
                    self.analyzed.interner.resolve(record.name)
                )
            })?;

        for method in &record.methods {
            self.compile_method(method, record.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            record.methods.iter().map(|m| m.name).collect();
        if let Some(interfaces) = self.analyzed.type_implements.get(&record.name).cloned() {
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
            TypeExpr::Named(sym) => Some(self.analyzed.interner.resolve(*sym).to_string()),
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
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
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
                            &self.analyzed.type_aliases,
                            &self.analyzed.interface_registry,
                            &self.analyzed.interner,
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
            let method_name_str = self.analyzed.interner.resolve(method.name);
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
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
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
        let method_name_str = self.analyzed.interner.resolve(method.name);
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
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
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
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
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
                .analyzed
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

            // Compute the method's return type for proper union wrapping
            let method_return_type = method.return_type.as_ref().map(|t| {
                resolve_type_expr_full(
                    t,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            });

            // Compile method body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: method_return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
        let type_name_str = self.analyzed.interner.resolve(type_name);
        let method_name_str = self.analyzed.interner.resolve(method.name);
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
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
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
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
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
                .analyzed
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
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: None, // Methods don't use raise statements yet
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
        let type_name_str = self.analyzed.interner.resolve(type_name);
        let method_name_str = self.analyzed.interner.resolve(method.name);
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
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
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
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
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
                .analyzed
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
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: None, // Default methods don't use raise statements yet
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
        let name = self.analyzed.interner.resolve(func.name);
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
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_full(
                    &p.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_full(
                t,
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
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
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
                    analyzed: self.analyzed,
                    interner: &self.analyzed.interner,
                    pointer_type: self.pointer_type,
                    module: &mut self.jit.module,
                    func_ids: &mut self.jit.func_ids,
                    source_file_ptr,
                    globals: &self.globals,
                    lambda_counter: &mut self.lambda_counter,
                    type_metadata: &self.type_metadata,
                    func_return_types: &self.func_return_types,
                    current_function_return_type: None, // Tests don't have a declared return type
                    native_registry: &self.native_registry,
                    current_module: None,
                    generic_calls: &self.analyzed.generic_calls,
                    monomorph_cache: &self.analyzed.monomorph_cache,
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
                    let name = self.analyzed.interner.resolve(func.name);
                    self.jit.declare_function(name, &sig);
                    // Record return type for use in call expressions
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| {
                            resolve_type_expr_full(
                                t,
                                &self.analyzed.type_aliases,
                                &self.analyzed.interface_registry,
                                &self.analyzed.interner,
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
                    let name = self.analyzed.interner.resolve(func.name);
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
                    &resolve_type_expr_full(
                        &p.ty,
                        &self.analyzed.type_aliases,
                        &self.analyzed.interface_registry,
                        &self.analyzed.interner,
                    ),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = func
            .params
            .iter()
            .map(|p| {
                resolve_type_expr_full(
                    &p.ty,
                    &self.analyzed.type_aliases,
                    &self.analyzed.interface_registry,
                    &self.analyzed.interner,
                )
            })
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();

        // Get function return type (needed for raise statements in fallible functions)
        let return_type = func.return_type.as_ref().map(|t| {
            resolve_type_expr_full(
                t,
                &self.analyzed.type_aliases,
                &self.analyzed.interface_registry,
                &self.analyzed.interner,
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
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &empty_type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &[],
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &empty_type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: None, // Tests don't have a declared return type
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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

    /// Declare all monomorphized function instances
    fn declare_monomorphized_instances(&mut self) -> Result<(), String> {
        // Collect instances to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .monomorph_cache
            .instances()
            .map(|(key, instance)| (key.clone(), instance.clone()))
            .collect();

        for (_key, instance) in instances {
            let mangled_name =
                self.mangle_monomorph_name(instance.original_name, instance.instance_id);

            // Create signature from the concrete function type
            let mut params = Vec::new();
            for param_type in &instance.func_type.params {
                params.push(type_to_cranelift(param_type, self.pointer_type));
            }
            let ret = if *instance.func_type.return_type == Type::Void {
                None
            } else {
                Some(type_to_cranelift(
                    &instance.func_type.return_type,
                    self.pointer_type,
                ))
            };
            let sig = self.jit.create_signature(&params, ret);
            self.jit.declare_function(&mangled_name, &sig);

            // Record return type for call expressions
            self.func_return_types
                .insert(mangled_name, (*instance.func_type.return_type).clone());
        }

        Ok(())
    }

    /// Compile all monomorphized function instances
    fn compile_monomorphized_instances(&mut self, program: &Program) -> Result<(), String> {
        // Build a map of generic function names to their ASTs
        let generic_func_asts: HashMap<Symbol, &FuncDecl> = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Function(func) = decl
                    && !func.type_params.is_empty()
                {
                    return Some((func.name, func));
                }
                None
            })
            .collect();

        // Collect instances to avoid borrow issues
        let instances: Vec<_> = self
            .analyzed
            .monomorph_cache
            .instances()
            .map(|(key, instance)| (key.clone(), instance.clone()))
            .collect();

        for (_key, instance) in instances {
            let func = generic_func_asts
                .get(&instance.original_name)
                .ok_or_else(|| {
                    format!(
                        "Internal error: generic function AST not found for {:?}",
                        instance.original_name
                    )
                })?;

            self.compile_monomorphized_function(func, &instance)?;
        }

        Ok(())
    }

    /// Compile a single monomorphized function instance
    fn compile_monomorphized_function(
        &mut self,
        func: &FuncDecl,
        instance: &MonomorphInstance,
    ) -> Result<(), String> {
        let mangled_name = self.mangle_monomorph_name(instance.original_name, instance.instance_id);

        let func_id = *self
            .jit
            .func_ids
            .get(&mangled_name)
            .ok_or_else(|| format!("Monomorphized function {} not declared", mangled_name))?;

        // Create function signature from concrete types
        let mut params = Vec::new();
        for param_type in &instance.func_type.params {
            params.push(type_to_cranelift(param_type, self.pointer_type));
        }
        let ret = if *instance.func_type.return_type == Type::Void {
            None
        } else {
            Some(type_to_cranelift(
                &instance.func_type.return_type,
                self.pointer_type,
            ))
        };
        let sig = self.jit.create_signature(&params, ret);
        self.jit.ctx.func.signature = sig;

        // Get parameter names and concrete types
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();
        let param_types: Vec<types::Type> = instance
            .func_type
            .params
            .iter()
            .map(|t| type_to_cranelift(t, self.pointer_type))
            .collect();
        let param_vole_types: Vec<Type> = instance.func_type.params.clone();

        // Get return type
        let return_type = Some((*instance.func_type.return_type).clone());

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

            // Compile function body
            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                analyzed: self.analyzed,
                interner: &self.analyzed.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &mut self.jit.func_ids,
                source_file_ptr,
                globals: &self.globals,
                lambda_counter: &mut self.lambda_counter,
                type_metadata: &self.type_metadata,
                func_return_types: &self.func_return_types,
                current_function_return_type: return_type,
                native_registry: &self.native_registry,
                current_module: None,
                generic_calls: &self.analyzed.generic_calls,
                monomorph_cache: &self.analyzed.monomorph_cache,
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

    /// Generate a mangled name for a monomorphized function instance
    fn mangle_monomorph_name(&self, original_name: Symbol, instance_id: u32) -> String {
        let name = self.analyzed.interner.resolve(original_name);
        format!("{}__mono_{}", name, instance_id)
    }
}

#[cfg(test)]
mod tests;
