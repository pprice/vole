// src/codegen/compiler.rs
//
// NOTE: This file contains legacy code being migrated to split impl blocks.
// The new code is in expr.rs, stmt.rs, calls.rs, ops.rs, structs.rs, lambda.rs.
// Functions here are kept for backward compatibility during migration.

#![allow(dead_code)]

use cranelift::codegen::ir::{BlockArg, TrapCode};
use cranelift::prelude::*;
use cranelift_module::Module;
use std::collections::HashMap;

use super::calls::{compile_string_literal, value_to_string};
use super::lambda::{CaptureBinding, compile_lambda};
use super::stmt::{compile_block, construct_union};
use super::structs::{
    convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type, get_type_name_symbol,
};
use super::types::{
    CompileCtx, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, FALLIBLE_TAG_OFFSET, TypeMetadata,
    convert_to_type, cranelift_to_vole_type, fallible_error_tag, resolve_type_expr,
    resolve_type_expr_full, resolve_type_expr_with_errors, type_to_cranelift,
};
use crate::codegen::{CompiledValue, JitContext};
use crate::frontend::{
    self, AssignTarget, BinaryOp, ClassDecl, Decl, ErrorPattern, Expr, ExprKind, FuncDecl,
    ImplementBlock, InterfaceDecl, InterfaceMethod, Interner, LetStmt, NodeId, Pattern, Program,
    RecordDecl, StringPart, Symbol, TestCase, TestsDecl, TryCatchExpr, TypeExpr, UnaryOp,
};
use crate::sema::implement_registry::TypeId;
use crate::sema::interface_registry::InterfaceRegistry;
use crate::sema::resolution::{MethodResolutions, ResolvedMethod};
use crate::sema::{ClassType, ErrorTypeInfo, FunctionType, RecordType, StructField, Type};

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
    ) -> Self {
        let pointer_type = jit.pointer_type();
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
            }
        }

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
                ty: resolve_type_expr_full(&field.ty, &self.type_aliases, &self.interface_registry),
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
                .map(|t| resolve_type_expr_full(t, &self.type_aliases, &self.interface_registry))
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
                ty: resolve_type_expr_full(&field.ty, &self.type_aliases, &self.interface_registry),
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
                .map(|t| resolve_type_expr_full(t, &self.type_aliases, &self.interface_registry))
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
                        resolve_type_expr_full(t, &self.type_aliases, &self.interface_registry)
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
                    &resolve_type_expr_full(&p.ty, &self.type_aliases, &self.interface_registry),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| resolve_type_expr_full(&p.ty, &self.type_aliases, &self.interface_registry))
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
                    &resolve_type_expr_full(&p.ty, &self.type_aliases, &self.interface_registry),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| resolve_type_expr_full(&p.ty, &self.type_aliases, &self.interface_registry))
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
                    &resolve_type_expr_full(&p.ty, &self.type_aliases, &self.interface_registry),
                    self.pointer_type,
                )
            })
            .collect();
        let param_vole_types: Vec<Type> = method
            .params
            .iter()
            .map(|p| resolve_type_expr_full(&p.ty, &self.type_aliases, &self.interface_registry))
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

/// Compile a type pattern check for match expressions
/// Returns Some(comparison_value) if a runtime check is needed, None if always matches
fn compile_type_pattern_check(
    builder: &mut FunctionBuilder,
    scrutinee: &CompiledValue,
    pattern_type: &Type,
) -> Option<Value> {
    if let Type::Union(variants) = &scrutinee.vole_type {
        let expected_tag = variants
            .iter()
            .position(|v| v == pattern_type)
            .unwrap_or(usize::MAX);

        if expected_tag == usize::MAX {
            // Pattern type not in union - will never match
            let never_match = builder.ins().iconst(types::I8, 0);
            return Some(never_match);
        }

        let tag = builder
            .ins()
            .load(types::I8, MemFlags::new(), scrutinee.value, 0);
        let expected = builder.ins().iconst(types::I8, expected_tag as i64);
        let result = builder.ins().icmp(IntCC::Equal, tag, expected);

        Some(result)
    } else {
        // Non-union scrutinee - pattern matches if types are equal
        if scrutinee.vole_type == *pattern_type {
            None // Always matches
        } else {
            // Never matches
            let never_match = builder.ins().iconst(types::I8, 0);
            Some(never_match)
        }
    }
}

pub(super) fn compile_expr(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    match &expr.kind {
        ExprKind::IntLiteral(n) => {
            let val = builder.ins().iconst(types::I64, *n);
            Ok(CompiledValue {
                value: val,
                ty: types::I64,
                vole_type: Type::I64,
            })
        }
        ExprKind::FloatLiteral(n) => {
            let val = builder.ins().f64const(*n);
            Ok(CompiledValue {
                value: val,
                ty: types::F64,
                vole_type: Type::F64,
            })
        }
        ExprKind::BoolLiteral(b) => {
            let val = builder.ins().iconst(types::I8, if *b { 1 } else { 0 });
            Ok(CompiledValue {
                value: val,
                ty: types::I8,
                vole_type: Type::Bool,
            })
        }
        ExprKind::Identifier(sym) => {
            if let Some((var, vole_type)) = variables.get(sym) {
                let val = builder.use_var(*var);
                // Get the type from the variable declaration
                let ty = builder.func.dfg.value_type(val);

                // Check if this expression has a narrowed type from semantic analysis
                // (e.g., inside `if x is i64 { ... }`, x's type is narrowed from i64|nil to i64)
                if let Some(narrowed_type) = ctx.expr_types.get(&expr.id) {
                    // If variable is a union but narrowed type is not, extract the payload
                    if matches!(vole_type, Type::Union(_))
                        && !matches!(narrowed_type, Type::Union(_))
                    {
                        // Union layout: [tag:1][padding:7][payload]
                        // Load the payload at offset 8
                        let payload_ty = type_to_cranelift(narrowed_type, ctx.pointer_type);
                        let payload = builder.ins().load(payload_ty, MemFlags::new(), val, 8);
                        return Ok(CompiledValue {
                            value: payload,
                            ty: payload_ty,
                            vole_type: narrowed_type.clone(),
                        });
                    }
                }

                Ok(CompiledValue {
                    value: val,
                    ty,
                    vole_type: vole_type.clone(),
                })
            } else {
                // Check if this is a global variable
                if let Some(global) = ctx.globals.iter().find(|g| g.name == *sym) {
                    // Compile the global's initializer expression inline
                    // This works for constant expressions; for complex expressions,
                    // a more sophisticated approach would be needed
                    compile_expr(builder, &global.init, variables, ctx)
                } else {
                    Err(format!(
                        "undefined variable: {}",
                        ctx.interner.resolve(*sym)
                    ))
                }
            }
        }
        ExprKind::Binary(bin) => {
            // Handle short-circuit evaluation for And/Or before evaluating both sides
            match bin.op {
                BinaryOp::And => {
                    // Short-circuit AND: if left is false, return false without evaluating right
                    let left = compile_expr(builder, &bin.left, variables, ctx)?;

                    let then_block = builder.create_block();
                    let else_block = builder.create_block();
                    let merge_block = builder.create_block();
                    builder.append_block_param(merge_block, types::I8);

                    builder
                        .ins()
                        .brif(left.value, then_block, &[], else_block, &[]);

                    // Then block: left was true, evaluate right side
                    builder.switch_to_block(then_block);
                    builder.seal_block(then_block);
                    let right = compile_expr(builder, &bin.right, variables, ctx)?;
                    let right_arg = BlockArg::from(right.value);
                    builder.ins().jump(merge_block, &[right_arg]);

                    // Else block: left was false, short-circuit with false
                    builder.switch_to_block(else_block);
                    builder.seal_block(else_block);
                    let false_val = builder.ins().iconst(types::I8, 0);
                    let false_arg = BlockArg::from(false_val);
                    builder.ins().jump(merge_block, &[false_arg]);

                    // Merge block
                    builder.switch_to_block(merge_block);
                    builder.seal_block(merge_block);
                    let result = builder.block_params(merge_block)[0];

                    return Ok(CompiledValue {
                        value: result,
                        ty: types::I8,
                        vole_type: Type::Bool,
                    });
                }
                BinaryOp::Or => {
                    // Short-circuit OR: if left is true, return true without evaluating right
                    let left = compile_expr(builder, &bin.left, variables, ctx)?;

                    let then_block = builder.create_block();
                    let else_block = builder.create_block();
                    let merge_block = builder.create_block();
                    builder.append_block_param(merge_block, types::I8);

                    builder
                        .ins()
                        .brif(left.value, then_block, &[], else_block, &[]);

                    // Then block: left was true, short-circuit with true
                    builder.switch_to_block(then_block);
                    builder.seal_block(then_block);
                    let true_val = builder.ins().iconst(types::I8, 1);
                    let true_arg = BlockArg::from(true_val);
                    builder.ins().jump(merge_block, &[true_arg]);

                    // Else block: left was false, evaluate right side
                    builder.switch_to_block(else_block);
                    builder.seal_block(else_block);
                    let right = compile_expr(builder, &bin.right, variables, ctx)?;
                    let right_arg = BlockArg::from(right.value);
                    builder.ins().jump(merge_block, &[right_arg]);

                    // Merge block
                    builder.switch_to_block(merge_block);
                    builder.seal_block(merge_block);
                    let result = builder.block_params(merge_block)[0];

                    return Ok(CompiledValue {
                        value: result,
                        ty: types::I8,
                        vole_type: Type::Bool,
                    });
                }
                _ => {} // Fall through to regular binary handling
            }

            let left = compile_expr(builder, &bin.left, variables, ctx)?;
            let right = compile_expr(builder, &bin.right, variables, ctx)?;

            // Determine result type (promote to wider type)
            let result_ty = if left.ty == types::F64 || right.ty == types::F64 {
                types::F64
            } else if left.ty == types::F32 || right.ty == types::F32 {
                types::F32
            } else {
                left.ty
            };

            // Save the left operand's vole_type before conversion (for signed/unsigned op selection)
            let left_vole_type = left.vole_type.clone();

            // Convert operands if needed
            let left_val = convert_to_type(builder, left, result_ty);
            let right_val = convert_to_type(builder, right, result_ty);

            let result = match bin.op {
                BinaryOp::Add => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fadd(left_val, right_val)
                    } else {
                        builder.ins().iadd(left_val, right_val)
                    }
                }
                BinaryOp::Sub => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fsub(left_val, right_val)
                    } else {
                        builder.ins().isub(left_val, right_val)
                    }
                }
                BinaryOp::Mul => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fmul(left_val, right_val)
                    } else {
                        builder.ins().imul(left_val, right_val)
                    }
                }
                BinaryOp::Div => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fdiv(left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder.ins().udiv(left_val, right_val)
                    } else {
                        builder.ins().sdiv(left_val, right_val)
                    }
                }
                BinaryOp::Mod => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        // Floating-point modulo: a - (a/b).floor() * b
                        let div = builder.ins().fdiv(left_val, right_val);
                        let floor = builder.ins().floor(div);
                        let mul = builder.ins().fmul(floor, right_val);
                        builder.ins().fsub(left_val, mul)
                    } else if left_vole_type.is_unsigned() {
                        builder.ins().urem(left_val, right_val)
                    } else {
                        builder.ins().srem(left_val, right_val)
                    }
                }
                BinaryOp::Eq => {
                    if matches!(left_vole_type, Type::String) {
                        // String comparison
                        if let Some(cmp_id) = ctx.func_ids.get("vole_string_eq") {
                            let cmp_ref = ctx.module.declare_func_in_func(*cmp_id, builder.func);
                            let call = builder.ins().call(cmp_ref, &[left_val, right_val]);
                            builder.inst_results(call)[0]
                        } else {
                            builder.ins().icmp(IntCC::Equal, left_val, right_val)
                        }
                    } else if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::Equal, left_val, right_val)
                    }
                }
                BinaryOp::Ne => {
                    if matches!(left_vole_type, Type::String) {
                        // String comparison (negate the result of eq)
                        if let Some(cmp_id) = ctx.func_ids.get("vole_string_eq") {
                            let cmp_ref = ctx.module.declare_func_in_func(*cmp_id, builder.func);
                            let call = builder.ins().call(cmp_ref, &[left_val, right_val]);
                            let eq_result = builder.inst_results(call)[0];
                            // Negate: 1 - eq_result (since bool is 0 or 1)
                            let one = builder.ins().iconst(types::I8, 1);
                            builder.ins().isub(one, eq_result)
                        } else {
                            builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
                        }
                    } else if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val)
                    } else {
                        builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
                    }
                }
                BinaryOp::Lt => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder.ins().fcmp(FloatCC::LessThan, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedLessThan, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedLessThan, left_val, right_val)
                    }
                }
                BinaryOp::Gt => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder
                            .ins()
                            .fcmp(FloatCC::GreaterThan, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedGreaterThan, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThan, left_val, right_val)
                    }
                }
                BinaryOp::Le => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder
                            .ins()
                            .fcmp(FloatCC::LessThanOrEqual, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedLessThanOrEqual, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
                    }
                }
                BinaryOp::Ge => {
                    if result_ty == types::F64 || result_ty == types::F32 {
                        builder
                            .ins()
                            .fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val)
                    } else if left_vole_type.is_unsigned() {
                        builder
                            .ins()
                            .icmp(IntCC::UnsignedGreaterThanOrEqual, left_val, right_val)
                    } else {
                        builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
                    }
                }
                // And/Or are handled above with short-circuit evaluation
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                // Bitwise operators
                BinaryOp::BitAnd => builder.ins().band(left_val, right_val),
                BinaryOp::BitOr => builder.ins().bor(left_val, right_val),
                BinaryOp::BitXor => builder.ins().bxor(left_val, right_val),
                BinaryOp::Shl => builder.ins().ishl(left_val, right_val),
                BinaryOp::Shr => {
                    if left_vole_type.is_unsigned() {
                        builder.ins().ushr(left_val, right_val)
                    } else {
                        builder.ins().sshr(left_val, right_val)
                    }
                }
            };

            // Comparison operators return I8 (bool)
            let final_ty = match bin.op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Gt
                | BinaryOp::Le
                | BinaryOp::Ge => types::I8,
                // And/Or are handled above with early return
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                _ => result_ty,
            };

            // Determine vole_type for result
            let vole_type = match bin.op {
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Gt
                | BinaryOp::Le
                | BinaryOp::Ge => Type::Bool,
                BinaryOp::And | BinaryOp::Or => unreachable!(),
                _ => left_vole_type,
            };

            Ok(CompiledValue {
                value: result,
                ty: final_ty,
                vole_type,
            })
        }
        ExprKind::Unary(un) => {
            let operand = compile_expr(builder, &un.operand, variables, ctx)?;
            let result = match un.op {
                UnaryOp::Neg => {
                    if operand.ty == types::F64 {
                        builder.ins().fneg(operand.value)
                    } else {
                        builder.ins().ineg(operand.value)
                    }
                }
                UnaryOp::Not => {
                    // Logical not: 1 - x for boolean
                    let one = builder.ins().iconst(types::I8, 1);
                    builder.ins().isub(one, operand.value)
                }
                UnaryOp::BitNot => builder.ins().bnot(operand.value),
            };
            Ok(CompiledValue {
                value: result,
                ty: operand.ty,
                vole_type: operand.vole_type,
            })
        }
        ExprKind::Assign(assign) => {
            match &assign.target {
                AssignTarget::Variable(sym) => {
                    let value = compile_expr(builder, &assign.value, variables, ctx)?;
                    if let Some((var, var_type)) = variables.get(sym) {
                        // If variable is a union and value is not, wrap the value
                        let final_value = if matches!(var_type, Type::Union(_))
                            && !matches!(&value.vole_type, Type::Union(_))
                        {
                            let wrapped = construct_union(
                                builder,
                                value.clone(),
                                var_type,
                                ctx.pointer_type,
                            )?;
                            wrapped.value
                        } else {
                            value.value
                        };
                        builder.def_var(*var, final_value);
                        Ok(value)
                    } else {
                        Err(format!(
                            "undefined variable: {}",
                            ctx.interner.resolve(*sym)
                        ))
                    }
                }
                AssignTarget::Field { object, field, .. } => {
                    compile_field_assign(builder, object, *field, &assign.value, variables, ctx)
                }
                AssignTarget::Index { object, index } => {
                    compile_index_assign(builder, object, index, &assign.value, variables, ctx)
                }
            }
        }
        ExprKind::CompoundAssign(compound) => {
            compile_compound_assign(builder, compound, variables, ctx)
        }
        ExprKind::Grouping(inner) => compile_expr(builder, inner, variables, ctx),
        ExprKind::StringLiteral(s) => {
            compile_string_literal(builder, s, ctx.pointer_type, ctx.module, ctx.func_ids)
        }
        ExprKind::Call(call) => compile_call(builder, call, expr.span.line, variables, ctx),
        ExprKind::InterpolatedString(parts) => {
            compile_interpolated_string(builder, parts, variables, ctx)
        }
        ExprKind::Range(_) => {
            // Range expressions are only supported in for-in context
            Err("Range expressions only supported in for-in context".to_string())
        }
        ExprKind::ArrayLiteral(elements) => {
            // Call vole_array_new()
            let array_new_id = ctx
                .func_ids
                .get("vole_array_new")
                .ok_or_else(|| "vole_array_new not found".to_string())?;
            let array_new_ref = ctx.module.declare_func_in_func(*array_new_id, builder.func);

            let call = builder.ins().call(array_new_ref, &[]);
            let arr_ptr = builder.inst_results(call)[0];

            // Push each element
            let array_push_id = ctx
                .func_ids
                .get("vole_array_push")
                .ok_or_else(|| "vole_array_push not found".to_string())?;
            let array_push_ref = ctx
                .module
                .declare_func_in_func(*array_push_id, builder.func);

            // Track element type from first element
            let mut elem_type = Type::Unknown;

            for (i, elem) in elements.iter().enumerate() {
                let compiled = compile_expr(builder, elem, variables, ctx)?;

                // Track element type from first element
                if i == 0 {
                    elem_type = compiled.vole_type.clone();
                }

                // Determine tag based on type
                let tag = match &compiled.vole_type {
                    Type::I64 | Type::I32 => 2i64, // TYPE_I64
                    Type::F64 => 3i64,             // TYPE_F64
                    Type::Bool => 4i64,            // TYPE_BOOL
                    Type::String => 1i64,          // TYPE_STRING
                    Type::Array(_) => 5i64,        // TYPE_ARRAY
                    _ => 2i64,                     // default to I64
                };

                let tag_val = builder.ins().iconst(types::I64, tag);

                // Convert value to u64 bits
                let value_bits = if compiled.ty == types::F64 {
                    builder
                        .ins()
                        .bitcast(types::I64, MemFlags::new(), compiled.value)
                } else if compiled.ty == types::I8 {
                    // Bool: zero-extend to i64
                    builder.ins().uextend(types::I64, compiled.value)
                } else {
                    compiled.value
                };

                builder
                    .ins()
                    .call(array_push_ref, &[arr_ptr, tag_val, value_bits]);
            }

            Ok(CompiledValue {
                value: arr_ptr,
                ty: ctx.pointer_type,
                vole_type: Type::Array(Box::new(elem_type)),
            })
        }
        ExprKind::Index(idx) => {
            let arr = compile_expr(builder, &idx.object, variables, ctx)?;
            let index = compile_expr(builder, &idx.index, variables, ctx)?;

            // Get element type from array type
            let elem_type = match &arr.vole_type {
                Type::Array(elem) => elem.as_ref().clone(),
                _ => Type::I64, // Default to I64 if type unknown
            };

            // Call vole_array_get_value(arr, index)
            let get_value_id = ctx
                .func_ids
                .get("vole_array_get_value")
                .ok_or_else(|| "vole_array_get_value not found".to_string())?;
            let get_value_ref = ctx.module.declare_func_in_func(*get_value_id, builder.func);

            let call = builder.ins().call(get_value_ref, &[arr.value, index.value]);
            let value = builder.inst_results(call)[0];

            // Convert value based on element type
            let (result_value, result_ty) = match &elem_type {
                Type::F64 => {
                    let fval = builder.ins().bitcast(types::F64, MemFlags::new(), value);
                    (fval, types::F64)
                }
                Type::Bool => {
                    let bval = builder.ins().ireduce(types::I8, value);
                    (bval, types::I8)
                }
                _ => (value, types::I64), // i64, strings, arrays stay as i64/pointer
            };

            Ok(CompiledValue {
                value: result_value,
                ty: result_ty,
                vole_type: elem_type,
            })
        }

        ExprKind::Match(match_expr) => {
            // Compile the scrutinee (value being matched)
            let scrutinee = compile_expr(builder, &match_expr.scrutinee, variables, ctx)?;

            // Create merge block that collects results
            // Use I64 as the result type since it can hold both integers and pointers
            let merge_block = builder.create_block();
            builder.append_block_param(merge_block, types::I64);

            // Create a trap block for non-exhaustive match (should be unreachable)
            let trap_block = builder.create_block();

            // Create blocks for each arm
            let arm_blocks: Vec<Block> = match_expr
                .arms
                .iter()
                .map(|_| builder.create_block())
                .collect();

            // Jump to first arm
            if !arm_blocks.is_empty() {
                builder.ins().jump(arm_blocks[0], &[]);
            } else {
                // No arms - should not happen after sema, but handle gracefully
                let default_val = builder.ins().iconst(types::I64, 0);
                let default_arg = BlockArg::from(default_val);
                builder.ins().jump(merge_block, &[default_arg]);
            }

            // Track the result type from the first arm body
            let mut result_vole_type = Type::Void;

            // Compile each arm
            for (i, arm) in match_expr.arms.iter().enumerate() {
                let arm_block = arm_blocks[i];
                // For the last arm, if pattern fails, go to trap (should be unreachable)
                let next_block = arm_blocks.get(i + 1).copied().unwrap_or(trap_block);

                builder.switch_to_block(arm_block);

                // Create a new variables scope for this arm
                let mut arm_variables = variables.clone();

                // Check pattern
                let pattern_matches = match &arm.pattern {
                    Pattern::Wildcard(_) => {
                        // Always matches
                        None
                    }
                    Pattern::Identifier { name, .. } => {
                        // Check if this identifier is a type name (class/record)
                        if let Some(type_meta) = ctx.type_metadata.get(name) {
                            // Type pattern - compare against union variant tag
                            compile_type_pattern_check(builder, &scrutinee, &type_meta.vole_type)
                        } else {
                            // Bind the scrutinee value to the identifier
                            let var = builder.declare_var(scrutinee.ty);
                            builder.def_var(var, scrutinee.value);
                            arm_variables.insert(*name, (var, scrutinee.vole_type.clone()));
                            None // Always matches
                        }
                    }
                    Pattern::Type { type_expr, .. } => {
                        let pattern_type = resolve_type_expr(type_expr, ctx);
                        compile_type_pattern_check(builder, &scrutinee, &pattern_type)
                    }
                    Pattern::Literal(lit_expr) => {
                        // Compile literal and compare
                        let lit_val = compile_expr(builder, lit_expr, &mut arm_variables, ctx)?;
                        let cmp = match scrutinee.ty {
                            types::I64 | types::I32 | types::I8 => {
                                builder
                                    .ins()
                                    .icmp(IntCC::Equal, scrutinee.value, lit_val.value)
                            }
                            types::F64 => {
                                builder
                                    .ins()
                                    .fcmp(FloatCC::Equal, scrutinee.value, lit_val.value)
                            }
                            _ => {
                                // For strings, need to call comparison function
                                if let Some(cmp_id) = ctx.func_ids.get("vole_string_eq") {
                                    let cmp_ref =
                                        ctx.module.declare_func_in_func(*cmp_id, builder.func);
                                    let call = builder
                                        .ins()
                                        .call(cmp_ref, &[scrutinee.value, lit_val.value]);
                                    builder.inst_results(call)[0]
                                } else {
                                    builder
                                        .ins()
                                        .icmp(IntCC::Equal, scrutinee.value, lit_val.value)
                                }
                            }
                        };
                        Some(cmp)
                    }
                    Pattern::Val { name, .. } => {
                        // Val pattern - compare against existing variable's value
                        let (var, var_type) = arm_variables
                            .get(name)
                            .ok_or_else(|| "undefined variable in val pattern".to_string())?
                            .clone();
                        let var_val = builder.use_var(var);

                        let cmp = match var_type {
                            Type::F64 => {
                                builder.ins().fcmp(FloatCC::Equal, scrutinee.value, var_val)
                            }
                            Type::String => {
                                if let Some(cmp_id) = ctx.func_ids.get("vole_string_eq") {
                                    let cmp_ref =
                                        ctx.module.declare_func_in_func(*cmp_id, builder.func);
                                    let call =
                                        builder.ins().call(cmp_ref, &[scrutinee.value, var_val]);
                                    builder.inst_results(call)[0]
                                } else {
                                    builder.ins().icmp(IntCC::Equal, scrutinee.value, var_val)
                                }
                            }
                            _ => builder.ins().icmp(IntCC::Equal, scrutinee.value, var_val),
                        };
                        Some(cmp)
                    }
                };

                // Check guard if present
                let guard_result = if let Some(guard) = &arm.guard {
                    let guard_val = compile_expr(builder, guard, &mut arm_variables, ctx)?;
                    // Guard must be bool (i8)
                    Some(guard_val.value)
                } else {
                    None
                };

                // Combine pattern match and guard
                let should_execute = match (pattern_matches, guard_result) {
                    (None, None) => None, // Always execute (wildcard/identifier, no guard)
                    (Some(p), None) => Some(p),
                    (None, Some(g)) => Some(g),
                    (Some(p), Some(g)) => {
                        // Both must be true: p AND g
                        // icmp returns i8 (bool), guard is also i8
                        Some(builder.ins().band(p, g))
                    }
                };

                // Create body block and skip block
                let body_block = builder.create_block();

                if let Some(cond) = should_execute {
                    // Conditional: branch to body if true, next arm if false
                    let cond_i32 = builder.ins().uextend(types::I32, cond);
                    builder
                        .ins()
                        .brif(cond_i32, body_block, &[], next_block, &[]);
                } else {
                    // Unconditional: always go to body
                    builder.ins().jump(body_block, &[]);
                }

                builder.seal_block(arm_block);

                // Compile body
                builder.switch_to_block(body_block);
                let body_val = compile_expr(builder, &arm.body, &mut arm_variables, ctx)?;

                // Track result type from first arm
                if i == 0 {
                    result_vole_type = body_val.vole_type.clone();
                }

                // Convert body value to I64 if needed (merge block uses I64)
                let result_val = if body_val.ty != types::I64 {
                    match body_val.ty {
                        types::I8 => builder.ins().sextend(types::I64, body_val.value),
                        types::I32 => builder.ins().sextend(types::I64, body_val.value),
                        _ => body_val.value, // Pointers are already I64
                    }
                } else {
                    body_val.value
                };

                let result_arg = BlockArg::from(result_val);
                builder.ins().jump(merge_block, &[result_arg]);
                builder.seal_block(body_block);
            }

            // Note: arm_blocks are sealed inside the loop after their predecessors are known

            // Fill in trap block (should be unreachable if match is exhaustive)
            builder.switch_to_block(trap_block);
            builder.seal_block(trap_block);
            builder.ins().trap(TrapCode::unwrap_user(1));

            // Switch to merge block and get result
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);

            let result = builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: result_vole_type,
            })
        }

        ExprKind::Nil => {
            // Nil has no runtime value - return a zero constant
            // The actual type will be determined by context (union wrapping)
            let zero = builder.ins().iconst(types::I8, 0);
            Ok(CompiledValue {
                value: zero,
                ty: types::I8,
                vole_type: Type::Nil,
            })
        }

        ExprKind::Is(is_expr) => {
            let value = compile_expr(builder, &is_expr.value, variables, ctx)?;
            let tested_type = resolve_type_expr(&is_expr.type_expr, ctx);

            // If value is a union, check the tag
            if let Type::Union(variants) = &value.vole_type {
                let expected_tag = variants
                    .iter()
                    .position(|v| v == &tested_type)
                    .unwrap_or(usize::MAX);

                // Load tag from union (at offset 0)
                let tag = builder
                    .ins()
                    .load(types::I8, MemFlags::new(), value.value, 0);
                let expected = builder.ins().iconst(types::I8, expected_tag as i64);
                let result = builder.ins().icmp(IntCC::Equal, tag, expected);

                Ok(CompiledValue {
                    value: result,
                    ty: types::I8,
                    vole_type: Type::Bool,
                })
            } else {
                // Not a union, always true if types match, false otherwise
                let result = if value.vole_type == tested_type {
                    1i64
                } else {
                    0i64
                };
                let result_val = builder.ins().iconst(types::I8, result);
                Ok(CompiledValue {
                    value: result_val,
                    ty: types::I8,
                    vole_type: Type::Bool,
                })
            }
        }

        ExprKind::NullCoalesce(nc) => {
            let value = compile_expr(builder, &nc.value, variables, ctx)?;

            // Get nil tag for this union
            let Type::Union(variants) = &value.vole_type else {
                return Err("Expected union for ??".to_string());
            };
            let nil_tag = variants
                .iter()
                .position(|v| v == &Type::Nil)
                .unwrap_or(usize::MAX);

            // Load tag
            let tag = builder
                .ins()
                .load(types::I8, MemFlags::new(), value.value, 0);
            let nil_tag_val = builder.ins().iconst(types::I8, nil_tag as i64);
            let is_nil = builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

            // Create blocks
            let nil_block = builder.create_block();
            let not_nil_block = builder.create_block();
            let merge_block = builder.create_block();

            // Determine result type (unwrapped)
            let result_vole_type = value.vole_type.unwrap_optional().unwrap_or(Type::Error);
            let cranelift_type = type_to_cranelift(&result_vole_type, ctx.pointer_type);
            builder.append_block_param(merge_block, cranelift_type);

            builder
                .ins()
                .brif(is_nil, nil_block, &[], not_nil_block, &[]);

            // Nil block: evaluate default
            builder.switch_to_block(nil_block);
            builder.seal_block(nil_block);
            let default_val = compile_expr(builder, &nc.default, variables, ctx)?;
            // Coerce default value to the expected result type if needed
            let default_coerced = if default_val.ty != cranelift_type {
                if default_val.ty.is_int() && cranelift_type.is_int() {
                    if cranelift_type.bytes() < default_val.ty.bytes() {
                        builder.ins().ireduce(cranelift_type, default_val.value)
                    } else {
                        builder.ins().sextend(cranelift_type, default_val.value)
                    }
                } else {
                    default_val.value
                }
            } else {
                default_val.value
            };
            let default_arg = BlockArg::from(default_coerced);
            builder.ins().jump(merge_block, &[default_arg]);

            // Not nil block: extract payload
            builder.switch_to_block(not_nil_block);
            builder.seal_block(not_nil_block);
            let payload = builder
                .ins()
                .load(cranelift_type, MemFlags::new(), value.value, 8);
            let payload_arg = BlockArg::from(payload);
            builder.ins().jump(merge_block, &[payload_arg]);

            // Merge
            builder.switch_to_block(merge_block);
            builder.seal_block(merge_block);

            let result = builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: cranelift_type,
                vole_type: result_vole_type,
            })
        }

        ExprKind::Lambda(lambda) => compile_lambda(builder, lambda, variables, ctx),

        ExprKind::TypeLiteral(_) => {
            // Type values are compile-time only and have no runtime representation.
            // If we reach here, the semantic analyzer should have caught this.
            Err("type expressions cannot be used as runtime values".to_string())
        }

        ExprKind::StructLiteral(sl) => compile_struct_literal(builder, sl, variables, ctx),

        ExprKind::FieldAccess(fa) => compile_field_access(builder, fa, variables, ctx),

        ExprKind::MethodCall(mc) => compile_method_call(builder, mc, expr.id, variables, ctx),

        ExprKind::TryCatch(try_catch) => compile_try_catch(builder, try_catch, variables, ctx),
    }
}

/// Compile an expression with capture awareness
pub(super) fn compile_expr_with_captures(
    builder: &mut FunctionBuilder,
    expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    capture_bindings: &HashMap<Symbol, CaptureBinding>,
    closure_var: Option<Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    match &expr.kind {
        ExprKind::Identifier(sym) => {
            // First check if this is a captured variable
            if let Some(binding) = capture_bindings.get(sym) {
                // Access via closure
                let closure_var = closure_var.ok_or_else(|| {
                    "Closure variable not available for capture access".to_string()
                })?;
                let closure_ptr = builder.use_var(closure_var);

                // Call vole_closure_get_capture(closure, index) -> *mut u8
                let get_capture_id = ctx
                    .func_ids
                    .get("vole_closure_get_capture")
                    .ok_or_else(|| "vole_closure_get_capture not found".to_string())?;
                let get_capture_ref = ctx
                    .module
                    .declare_func_in_func(*get_capture_id, builder.func);
                let index_val = builder.ins().iconst(types::I64, binding.index as i64);
                let call = builder
                    .ins()
                    .call(get_capture_ref, &[closure_ptr, index_val]);
                let heap_ptr = builder.inst_results(call)[0];

                // Load value from heap pointer
                let cranelift_ty = type_to_cranelift(&binding.vole_type, ctx.pointer_type);
                let value = builder
                    .ins()
                    .load(cranelift_ty, MemFlags::new(), heap_ptr, 0);

                return Ok(CompiledValue {
                    value,
                    ty: cranelift_ty,
                    vole_type: binding.vole_type.clone(),
                });
            }

            // Otherwise, regular variable lookup
            if let Some((var, vole_type)) = variables.get(sym) {
                let val = builder.use_var(*var);
                let ty = builder.func.dfg.value_type(val);
                Ok(CompiledValue {
                    value: val,
                    ty,
                    vole_type: vole_type.clone(),
                })
            } else {
                // Check globals
                if let Some(global) = ctx.globals.iter().find(|g| g.name == *sym) {
                    compile_expr_with_captures(
                        builder,
                        &global.init,
                        variables,
                        capture_bindings,
                        closure_var,
                        ctx,
                    )
                } else {
                    Err(format!(
                        "undefined variable: {}",
                        ctx.interner.resolve(*sym)
                    ))
                }
            }
        }
        ExprKind::Assign(assign) => {
            match &assign.target {
                AssignTarget::Variable(sym) => {
                    // Check if assigning to a captured variable
                    if let Some(binding) = capture_bindings.get(sym) {
                        let value = compile_expr_with_captures(
                            builder,
                            &assign.value,
                            variables,
                            capture_bindings,
                            closure_var,
                            ctx,
                        )?;

                        // Get the capture pointer
                        let closure_var = closure_var.ok_or_else(|| {
                            "Closure variable not available for capture access".to_string()
                        })?;
                        let closure_ptr = builder.use_var(closure_var);

                        let get_capture_id = ctx
                            .func_ids
                            .get("vole_closure_get_capture")
                            .ok_or_else(|| "vole_closure_get_capture not found".to_string())?;
                        let get_capture_ref = ctx
                            .module
                            .declare_func_in_func(*get_capture_id, builder.func);
                        let index_val = builder.ins().iconst(types::I64, binding.index as i64);
                        let call = builder
                            .ins()
                            .call(get_capture_ref, &[closure_ptr, index_val]);
                        let heap_ptr = builder.inst_results(call)[0];

                        // Store the new value
                        builder
                            .ins()
                            .store(MemFlags::new(), value.value, heap_ptr, 0);

                        return Ok(value);
                    }

                    // Otherwise, regular assignment
                    let value = compile_expr_with_captures(
                        builder,
                        &assign.value,
                        variables,
                        capture_bindings,
                        closure_var,
                        ctx,
                    )?;
                    if let Some((var, _)) = variables.get(sym) {
                        builder.def_var(*var, value.value);
                        Ok(value)
                    } else {
                        Err(format!(
                            "undefined variable: {}",
                            ctx.interner.resolve(*sym)
                        ))
                    }
                }
                AssignTarget::Field { object, field, .. } => {
                    compile_field_assign(builder, object, *field, &assign.value, variables, ctx)
                }
                AssignTarget::Index { object, index } => {
                    compile_index_assign(builder, object, index, &assign.value, variables, ctx)
                }
            }
        }
        ExprKind::Binary(bin) => {
            // Compile left and right with capture awareness
            let left = compile_expr_with_captures(
                builder,
                &bin.left,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )?;
            let right = compile_expr_with_captures(
                builder,
                &bin.right,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )?;

            // Use the existing binary operation logic
            compile_binary_op(builder, left, right, bin.op, ctx)
        }
        ExprKind::Call(call) => {
            // For calls, we need to compile with capture awareness
            compile_call_with_captures(
                builder,
                call,
                expr.span.line,
                variables,
                capture_bindings,
                closure_var,
                ctx,
            )
        }
        // For other expression types, delegate to regular compilation
        // They may contain nested expressions that need capture handling
        _ => compile_expr(builder, expr, variables, ctx),
    }
}

/// Helper to compile binary operations (extracted from compile_expr)
fn compile_binary_op(
    builder: &mut FunctionBuilder,
    left: CompiledValue,
    right: CompiledValue,
    op: BinaryOp,
    _ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Determine result type (promote to wider type)
    let result_ty = if left.ty == types::F64 || right.ty == types::F64 {
        types::F64
    } else if left.ty == types::F32 || right.ty == types::F32 {
        types::F32
    } else {
        left.ty
    };

    let left_vole_type = left.vole_type.clone();
    let left_val = convert_to_type(builder, left, result_ty);
    let right_val = convert_to_type(builder, right, result_ty);

    let result = match op {
        BinaryOp::Add => {
            if result_ty == types::F64 {
                builder.ins().fadd(left_val, right_val)
            } else {
                builder.ins().iadd(left_val, right_val)
            }
        }
        BinaryOp::Sub => {
            if result_ty == types::F64 {
                builder.ins().fsub(left_val, right_val)
            } else {
                builder.ins().isub(left_val, right_val)
            }
        }
        BinaryOp::Mul => {
            if result_ty == types::F64 {
                builder.ins().fmul(left_val, right_val)
            } else {
                builder.ins().imul(left_val, right_val)
            }
        }
        BinaryOp::Div => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder.ins().fdiv(left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder.ins().udiv(left_val, right_val)
            } else {
                builder.ins().sdiv(left_val, right_val)
            }
        }
        BinaryOp::Mod => {
            if result_ty == types::F64 || result_ty == types::F32 {
                let div = builder.ins().fdiv(left_val, right_val);
                let floor = builder.ins().floor(div);
                let mul = builder.ins().fmul(floor, right_val);
                builder.ins().fsub(left_val, mul)
            } else if left_vole_type.is_unsigned() {
                builder.ins().urem(left_val, right_val)
            } else {
                builder.ins().srem(left_val, right_val)
            }
        }
        BinaryOp::Eq => {
            if result_ty == types::F64 {
                builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
            } else {
                builder.ins().icmp(IntCC::Equal, left_val, right_val)
            }
        }
        BinaryOp::Ne => {
            if result_ty == types::F64 {
                builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val)
            } else {
                builder.ins().icmp(IntCC::NotEqual, left_val, right_val)
            }
        }
        BinaryOp::Lt => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder.ins().fcmp(FloatCC::LessThan, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThan, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, left_val, right_val)
            }
        }
        BinaryOp::Gt => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder
                    .ins()
                    .fcmp(FloatCC::GreaterThan, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThan, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, left_val, right_val)
            }
        }
        BinaryOp::Le => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder
                    .ins()
                    .fcmp(FloatCC::LessThanOrEqual, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThanOrEqual, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
            }
        }
        BinaryOp::Ge => {
            if result_ty == types::F64 || result_ty == types::F32 {
                builder
                    .ins()
                    .fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val)
            } else if left_vole_type.is_unsigned() {
                builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThanOrEqual, left_val, right_val)
            } else {
                builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
            }
        }
        BinaryOp::And | BinaryOp::Or => {
            return Err("And/Or should be handled with short-circuit evaluation".to_string());
        }
        BinaryOp::BitAnd => builder.ins().band(left_val, right_val),
        BinaryOp::BitOr => builder.ins().bor(left_val, right_val),
        BinaryOp::BitXor => builder.ins().bxor(left_val, right_val),
        BinaryOp::Shl => builder.ins().ishl(left_val, right_val),
        BinaryOp::Shr => {
            if left_vole_type.is_unsigned() {
                builder.ins().ushr(left_val, right_val)
            } else {
                builder.ins().sshr(left_val, right_val)
            }
        }
    };

    let final_ty = match op {
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
            types::I8
        }
        _ => result_ty,
    };

    let vole_type = match op {
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
            Type::Bool
        }
        _ => left_vole_type,
    };

    Ok(CompiledValue {
        value: result,
        ty: final_ty,
        vole_type,
    })
}

/// Compile compound assignment expression: x += 1, arr[i] -= 2
fn compile_compound_assign(
    builder: &mut FunctionBuilder,
    compound: &frontend::CompoundAssignExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    use crate::frontend::AssignTarget;

    match &compound.target {
        AssignTarget::Variable(sym) => {
            // 1. Get current value
            let (var, var_type) = variables
                .get(sym)
                .ok_or_else(|| format!("undefined variable: {}", ctx.interner.resolve(*sym)))?;
            let var = *var;
            let var_type = var_type.clone();
            let current_val = builder.use_var(var);

            let current = CompiledValue {
                value: current_val,
                ty: type_to_cranelift(&var_type, ctx.pointer_type),
                vole_type: var_type.clone(),
            };

            // 2. Compile RHS value
            let rhs = compile_expr(builder, &compound.value, variables, ctx)?;

            // 3. Apply the binary operation
            let binary_op = compound.op.to_binary_op();
            let result = compile_binary_op(builder, current, rhs, binary_op, ctx)?;

            // 4. Store back to variable
            builder.def_var(var, result.value);

            Ok(result)
        }
        AssignTarget::Index { object, index } => {
            // 1. Compile array and index ONCE
            let arr = compile_expr(builder, object, variables, ctx)?;
            let idx = compile_expr(builder, index, variables, ctx)?;

            // Get element type from array type
            let elem_type = match &arr.vole_type {
                Type::Array(elem) => elem.as_ref().clone(),
                _ => Type::I64,
            };

            // 2. Load current element value
            let get_value_id = ctx
                .func_ids
                .get("vole_array_get_value")
                .ok_or_else(|| "vole_array_get_value not found".to_string())?;
            let get_value_ref = ctx.module.declare_func_in_func(*get_value_id, builder.func);
            let call = builder.ins().call(get_value_ref, &[arr.value, idx.value]);
            let raw_value = builder.inst_results(call)[0];

            // Convert to proper type
            let (current_val, current_ty) = match &elem_type {
                Type::F64 => {
                    let fval = builder
                        .ins()
                        .bitcast(types::F64, MemFlags::new(), raw_value);
                    (fval, types::F64)
                }
                Type::Bool => {
                    let bval = builder.ins().ireduce(types::I8, raw_value);
                    (bval, types::I8)
                }
                _ => (raw_value, types::I64),
            };

            let current = CompiledValue {
                value: current_val,
                ty: current_ty,
                vole_type: elem_type.clone(),
            };

            // 3. Compile RHS and apply operation
            let rhs = compile_expr(builder, &compound.value, variables, ctx)?;
            let binary_op = compound.op.to_binary_op();
            let result = compile_binary_op(builder, current, rhs, binary_op, ctx)?;

            // 4. Store back to array
            let array_set_id = ctx
                .func_ids
                .get("vole_array_set")
                .ok_or_else(|| "vole_array_set not found".to_string())?;
            let array_set_ref = ctx.module.declare_func_in_func(*array_set_id, builder.func);

            // Convert result to i64 for storage
            let store_value = match result.ty {
                types::F64 => builder
                    .ins()
                    .bitcast(types::I64, MemFlags::new(), result.value),
                types::I8 => builder.ins().uextend(types::I64, result.value),
                _ => result.value,
            };

            // Compute tag based on element type
            let tag = match &elem_type {
                Type::I64 | Type::I32 => 2i64, // TYPE_I64
                Type::F64 => 3i64,             // TYPE_F64
                Type::Bool => 4i64,            // TYPE_BOOL
                Type::String => 1i64,          // TYPE_STRING
                Type::Array(_) => 5i64,        // TYPE_ARRAY
                _ => 2i64,                     // default to I64
            };
            let tag_val = builder.ins().iconst(types::I64, tag);

            builder
                .ins()
                .call(array_set_ref, &[arr.value, idx.value, tag_val, store_value]);

            Ok(result)
        }
        AssignTarget::Field { object, field, .. } => {
            // 1. Compile object to get the instance pointer
            let obj = compile_expr(builder, object, variables, ctx)?;

            // 2. Get field slot and type from the object's type
            let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, *field, ctx)?;

            // 3. Load current field value
            let get_field_id = ctx
                .func_ids
                .get("vole_instance_get_field")
                .ok_or_else(|| "vole_instance_get_field not found".to_string())?;
            let get_field_ref = ctx.module.declare_func_in_func(*get_field_id, builder.func);
            let slot_val = builder.ins().iconst(types::I32, slot as i64);
            let call = builder.ins().call(get_field_ref, &[obj.value, slot_val]);
            let current_raw = builder.inst_results(call)[0];

            // Convert value based on field type
            let (current_val, cranelift_ty) =
                convert_field_value(builder, current_raw, &field_type);

            let current = CompiledValue {
                value: current_val,
                ty: cranelift_ty,
                vole_type: field_type.clone(),
            };

            // 4. Compile RHS value
            let rhs = compile_expr(builder, &compound.value, variables, ctx)?;

            // 5. Apply the binary operation
            let binary_op = compound.op.to_binary_op();
            let result = compile_binary_op(builder, current, rhs, binary_op, ctx)?;

            // 6. Store back to field
            let set_field_id = ctx
                .func_ids
                .get("vole_instance_set_field")
                .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
            let set_field_ref = ctx.module.declare_func_in_func(*set_field_id, builder.func);

            // Convert result to i64 for storage
            let store_value = convert_to_i64_for_storage(builder, &result);

            builder
                .ins()
                .call(set_field_ref, &[obj.value, slot_val, store_value]);

            Ok(result)
        }
    }
}

/// Compile a function call with capture awareness
fn compile_call_with_captures(
    builder: &mut FunctionBuilder,
    call: &frontend::CallExpr,
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    _capture_bindings: &HashMap<Symbol, CaptureBinding>,
    _closure_var: Option<Variable>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // For now, delegate to regular call compilation
    // The callee might be a closure, but we handle that in compile_indirect_call_value
    compile_call(builder, call, call_line, variables, ctx)
}

/// Compile a function call expression
fn compile_call(
    builder: &mut FunctionBuilder,
    call: &frontend::CallExpr,
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Get the callee symbol - must be an identifier for now
    let callee_sym = match &call.callee.kind {
        ExprKind::Identifier(sym) => *sym,
        _ => return Err("only simple function calls are supported".to_string()),
    };

    let callee_name = ctx.interner.resolve(callee_sym);

    // Handle builtin functions first
    match callee_name {
        "println" => return compile_println(builder, &call.args, variables, ctx),
        "print_char" => return compile_print_char(builder, &call.args, variables, ctx),
        "assert" => return compile_assert(builder, &call.args, call_line, variables, ctx),
        _ => {}
    }

    // Check if callee is a variable with function type (for indirect calls)
    if let Some((var, Type::Function(ft))) = variables.get(&callee_sym) {
        // Clone what we need to avoid borrow conflicts
        let var = *var;
        let ft = ft.clone();
        return compile_indirect_call(builder, var, &ft, &call.args, variables, ctx);
    }

    // Check if callee is a variable with interface type (functional interface)
    if let Some((var, Type::Interface(iface))) = variables.get(&callee_sym) {
        // Look up the functional interface's function type
        if let Some(method_def) = ctx.interface_registry.is_functional(iface.name) {
            let ft = FunctionType {
                params: method_def.params.clone(),
                return_type: Box::new(method_def.return_type.clone()),
                is_closure: true, // Interface variables hold closures
            };
            let var = *var;
            return compile_indirect_call(builder, var, &ft, &call.args, variables, ctx);
        }
    }

    // Check if callee is a global variable with function type
    if let Some(global) = ctx.globals.iter().find(|g| g.name == callee_sym) {
        // Compile the global's initializer to get the function pointer
        let callee_value = compile_expr(builder, &global.init, variables, ctx)?;
        if let Type::Function(ft) = &callee_value.vole_type {
            return compile_indirect_call_value(
                builder,
                callee_value.value,
                ft,
                &call.args,
                variables,
                ctx,
            );
        }
        // Check if global is a functional interface
        if let Type::Interface(iface) = &callee_value.vole_type
            && let Some(method_def) = ctx.interface_registry.is_functional(iface.name)
        {
            let ft = FunctionType {
                params: method_def.params.clone(),
                return_type: Box::new(method_def.return_type.clone()),
                is_closure: true,
            };
            return compile_indirect_call_value(
                builder,
                callee_value.value,
                &ft,
                &call.args,
                variables,
                ctx,
            );
        }
    }

    // Fall back to named function call
    compile_user_function_call(builder, callee_name, &call.args, variables, ctx)
}

/// Compile an indirect call through a function pointer variable
fn compile_indirect_call(
    builder: &mut FunctionBuilder,
    var: Variable,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let func_ptr_or_closure = builder.use_var(var);
    compile_indirect_call_value(builder, func_ptr_or_closure, ft, args, variables, ctx)
}

/// Compile an indirect call through a function pointer value or closure pointer
fn compile_indirect_call_value(
    builder: &mut FunctionBuilder,
    func_ptr_or_closure: Value,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if ft.is_closure {
        // This is a closure - we need to extract the function pointer and pass the closure
        compile_closure_call(builder, func_ptr_or_closure, ft, args, variables, ctx)
    } else {
        // Pure function pointer - call directly
        compile_pure_function_call(builder, func_ptr_or_closure, ft, args, variables, ctx)
    }
}

/// Compile a call to a pure function (no closure)
fn compile_pure_function_call(
    builder: &mut FunctionBuilder,
    func_ptr: Value,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Build the Cranelift signature for the indirect call
    let mut sig = ctx.module.make_signature();
    for param_type in &ft.params {
        sig.params.push(AbiParam::new(type_to_cranelift(
            param_type,
            ctx.pointer_type,
        )));
    }
    sig.returns.push(AbiParam::new(type_to_cranelift(
        &ft.return_type,
        ctx.pointer_type,
    )));

    let sig_ref = builder.import_signature(sig);

    // Compile arguments
    let mut arg_values = Vec::new();
    for arg in args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        arg_values.push(compiled.value);
    }

    // Perform the indirect call
    let call_inst = builder.ins().call_indirect(sig_ref, func_ptr, &arg_values);
    let results = builder.inst_results(call_inst);

    if results.is_empty() {
        // Void function
        let zero = builder.ins().iconst(types::I64, 0);
        Ok(CompiledValue {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        Ok(CompiledValue {
            value: result,
            ty,
            vole_type: (*ft.return_type).clone(),
        })
    }
}

/// Compile a call to a closure (lambda with captures)
fn compile_closure_call(
    builder: &mut FunctionBuilder,
    closure_ptr: Value,
    ft: &FunctionType,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Extract the function pointer from the closure
    let get_func_id = ctx
        .func_ids
        .get("vole_closure_get_func")
        .ok_or_else(|| "vole_closure_get_func not found".to_string())?;
    let get_func_ref = ctx.module.declare_func_in_func(*get_func_id, builder.func);
    let get_func_call = builder.ins().call(get_func_ref, &[closure_ptr]);
    let func_ptr = builder.inst_results(get_func_call)[0];

    // Build the Cranelift signature for the closure call
    // First param is the closure pointer, then the user params
    let mut sig = ctx.module.make_signature();
    sig.params.push(AbiParam::new(ctx.pointer_type)); // Closure pointer
    for param_type in &ft.params {
        sig.params.push(AbiParam::new(type_to_cranelift(
            param_type,
            ctx.pointer_type,
        )));
    }
    sig.returns.push(AbiParam::new(type_to_cranelift(
        &ft.return_type,
        ctx.pointer_type,
    )));

    let sig_ref = builder.import_signature(sig);

    // Compile arguments - closure pointer first, then user args
    let mut arg_values = vec![closure_ptr];
    for arg in args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        arg_values.push(compiled.value);
    }

    // Perform the indirect call
    let call_inst = builder.ins().call_indirect(sig_ref, func_ptr, &arg_values);
    let results = builder.inst_results(call_inst);

    if results.is_empty() {
        // Void function
        let zero = builder.ins().iconst(types::I64, 0);
        Ok(CompiledValue {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        Ok(CompiledValue {
            value: result,
            ty,
            vole_type: (*ft.return_type).clone(),
        })
    }
}

/// Compile println builtin - dispatches to correct vole_println_* based on argument type
fn compile_println(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("println expects exactly one argument".to_string());
    }

    let arg = compile_expr(builder, &args[0], variables, ctx)?;

    // Dispatch based on argument type
    // We use vole_type to distinguish strings from regular I64 values
    let (func_name, call_arg) = if matches!(arg.vole_type, Type::String) {
        ("vole_println_string", arg.value)
    } else if arg.ty == types::F64 {
        ("vole_println_f64", arg.value)
    } else if arg.ty == types::I8 {
        ("vole_println_bool", arg.value)
    } else {
        // Extend smaller integer types to I64
        let extended = if arg.ty.is_int() && arg.ty != types::I64 {
            builder.ins().sextend(types::I64, arg.value)
        } else {
            arg.value
        };
        ("vole_println_i64", extended)
    };

    let func_id = ctx
        .func_ids
        .get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder.ins().call(func_ref, &[call_arg]);

    // println returns void, but we need to return something
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile print_char builtin for mandelbrot ASCII output
fn compile_print_char(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("print_char expects exactly one argument".to_string());
    }

    let arg = compile_expr(builder, &args[0], variables, ctx)?;

    // Convert to u8 if needed (truncate from i64)
    let char_val = if arg.ty == types::I64 {
        builder.ins().ireduce(types::I8, arg.value)
    } else if arg.ty == types::I8 {
        arg.value
    } else {
        return Err("print_char expects an integer argument".to_string());
    };

    let func_id = ctx
        .func_ids
        .get("vole_print_char")
        .ok_or_else(|| "vole_print_char not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder.ins().call(func_ref, &[char_val]);

    // Return void (as i64 zero)
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile assert builtin - checks condition and calls vole_assert_fail if false
fn compile_assert(
    builder: &mut FunctionBuilder,
    args: &[Expr],
    call_line: u32,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if args.len() != 1 {
        return Err("assert expects exactly one argument".to_string());
    }

    // Compile the condition
    let cond = compile_expr(builder, &args[0], variables, ctx)?;

    // Create pass and fail blocks
    let pass_block = builder.create_block();
    let fail_block = builder.create_block();

    // Branch on condition (extend bool to i32 for brif)
    let cond_i32 = builder.ins().uextend(types::I32, cond.value);
    builder
        .ins()
        .brif(cond_i32, pass_block, &[], fail_block, &[]);

    // Fail block: call vole_assert_fail and trap
    builder.switch_to_block(fail_block);
    {
        // Get vole_assert_fail function
        let func_id = ctx
            .func_ids
            .get("vole_assert_fail")
            .ok_or_else(|| "vole_assert_fail not found".to_string())?;
        let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

        // Pass source file pointer and length from JitContext
        // The source_file_ptr points to memory in JitContext that lives as long as the JIT code
        let (file_ptr, file_len) = ctx.source_file_ptr;
        let line = call_line as i32;

        let file_ptr_val = builder.ins().iconst(ctx.pointer_type, file_ptr as i64);
        let file_len_val = builder.ins().iconst(types::I64, file_len as i64);
        let line_val = builder.ins().iconst(types::I32, line as i64);

        builder
            .ins()
            .call(func_ref, &[file_ptr_val, file_len_val, line_val]);

        // Trap after calling assert_fail (this should not be reached due to longjmp, but
        // we need to terminate the block)
        // Note: TrapCode::user(0) returns None because TrapCode uses NonZeroU8, so we use 1
        builder.ins().trap(TrapCode::unwrap_user(1));
    }

    // Seal fail block
    builder.seal_block(fail_block);

    // Pass block: continue execution
    builder.switch_to_block(pass_block);
    builder.seal_block(pass_block);

    // Assert returns void (as i64 zero)
    let zero = builder.ins().iconst(types::I64, 0);
    Ok(CompiledValue {
        value: zero,
        ty: types::I64,
        vole_type: Type::Void,
    })
}

/// Compile a call to a user-defined function
fn compile_user_function_call(
    builder: &mut FunctionBuilder,
    name: &str,
    args: &[Expr],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let func_id = ctx
        .func_ids
        .get(name)
        .ok_or_else(|| format!("undefined function: {}", name))?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    // Get expected parameter types from the function's signature
    let sig_ref = builder.func.dfg.ext_funcs[func_ref].signature;
    let sig = &builder.func.dfg.signatures[sig_ref];
    let expected_types: Vec<types::Type> = sig.params.iter().map(|p| p.value_type).collect();

    // Compile arguments with type narrowing
    let mut arg_values = Vec::new();
    for (i, arg) in args.iter().enumerate() {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        let expected_ty = expected_types.get(i).copied();

        // Narrow integer types if needed
        let arg_value = if let Some(expected) = expected_ty {
            if compiled.ty.is_int() && expected.is_int() && expected.bits() < compiled.ty.bits() {
                // Truncate to narrower type
                builder.ins().ireduce(expected, compiled.value)
            } else if compiled.ty.is_int()
                && expected.is_int()
                && expected.bits() > compiled.ty.bits()
            {
                // Extend to wider type
                builder.ins().sextend(expected, compiled.value)
            } else {
                compiled.value
            }
        } else {
            compiled.value
        };
        arg_values.push(arg_value);
    }

    let call = builder.ins().call(func_ref, &arg_values);
    let results = builder.inst_results(call);

    if results.is_empty() {
        // Void function
        let zero = builder.ins().iconst(types::I64, 0);
        Ok(CompiledValue {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        let result = results[0];
        let ty = builder.func.dfg.value_type(result);
        // Infer vole_type from Cranelift type
        let vole_type = cranelift_to_vole_type(ty);
        Ok(CompiledValue {
            value: result,
            ty,
            vole_type,
        })
    }
}

/// Compile an interpolated string by converting parts and concatenating
fn compile_interpolated_string(
    builder: &mut FunctionBuilder,
    parts: &[StringPart],
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    if parts.is_empty() {
        // Empty interpolated string - return empty string
        return compile_string_literal(builder, "", ctx.pointer_type, ctx.module, ctx.func_ids);
    }

    // Convert each part to a string value
    let mut string_values: Vec<Value> = Vec::new();
    for part in parts {
        let str_val = match part {
            StringPart::Literal(s) => {
                compile_string_literal(builder, s, ctx.pointer_type, ctx.module, ctx.func_ids)?
                    .value
            }
            StringPart::Expr(expr) => {
                let compiled = compile_expr(builder, expr, variables, ctx)?;
                value_to_string(
                    builder,
                    compiled,
                    ctx.pointer_type,
                    ctx.module,
                    ctx.func_ids,
                )?
            }
        };
        string_values.push(str_val);
    }

    // Concatenate all parts
    if string_values.len() == 1 {
        return Ok(CompiledValue {
            value: string_values[0],
            ty: ctx.pointer_type,
            vole_type: Type::String,
        });
    }

    let concat_func_id = ctx
        .func_ids
        .get("vole_string_concat")
        .ok_or_else(|| "vole_string_concat not found".to_string())?;
    let concat_func_ref = ctx
        .module
        .declare_func_in_func(*concat_func_id, builder.func);

    let mut result = string_values[0];
    for &next in &string_values[1..] {
        let call = builder.ins().call(concat_func_ref, &[result, next]);
        result = builder.inst_results(call)[0];
    }

    Ok(CompiledValue {
        value: result,
        ty: ctx.pointer_type,
        vole_type: Type::String,
    })
}

// ============================================================================
// Struct literal, field access, and method call compilation
// ============================================================================

use crate::frontend::{FieldAccessExpr, MethodCallExpr, StructLiteralExpr};

/// Compile a struct literal: Point { x: 10, y: 20 }
fn compile_struct_literal(
    builder: &mut FunctionBuilder,
    sl: &StructLiteralExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Look up class or record metadata
    let metadata = ctx
        .type_metadata
        .get(&sl.name)
        .ok_or_else(|| format!("Unknown type: {}", ctx.interner.resolve(sl.name)))?;

    let type_id = metadata.type_id;
    let field_count = metadata.field_slots.len() as u32;
    let vole_type = metadata.vole_type.clone();
    let field_slots = metadata.field_slots.clone();

    // Call vole_instance_new(type_id, field_count, TYPE_INSTANCE)
    let new_func_id = ctx
        .func_ids
        .get("vole_instance_new")
        .ok_or_else(|| "vole_instance_new not found".to_string())?;
    let new_func_ref = ctx.module.declare_func_in_func(*new_func_id, builder.func);

    let type_id_val = builder.ins().iconst(types::I32, type_id as i64);
    let field_count_val = builder.ins().iconst(types::I32, field_count as i64);
    let runtime_type = builder.ins().iconst(types::I32, 7); // TYPE_INSTANCE

    let call = builder
        .ins()
        .call(new_func_ref, &[type_id_val, field_count_val, runtime_type]);
    let instance_ptr = builder.inst_results(call)[0];

    // Initialize each field
    let set_func_id = ctx
        .func_ids
        .get("vole_instance_set_field")
        .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
    let set_func_ref = ctx.module.declare_func_in_func(*set_func_id, builder.func);

    for init in &sl.fields {
        let slot = *field_slots.get(&init.name).ok_or_else(|| {
            format!(
                "Unknown field: {} in type {}",
                ctx.interner.resolve(init.name),
                ctx.interner.resolve(sl.name)
            )
        })?;

        let value = compile_expr(builder, &init.value, variables, ctx)?;
        let slot_val = builder.ins().iconst(types::I32, slot as i64);

        // Convert value to i64 for storage
        let store_value = convert_to_i64_for_storage(builder, &value);

        builder
            .ins()
            .call(set_func_ref, &[instance_ptr, slot_val, store_value]);
    }

    Ok(CompiledValue {
        value: instance_ptr,
        ty: ctx.pointer_type,
        vole_type,
    })
}

/// Compile field access: point.x
fn compile_field_access(
    builder: &mut FunctionBuilder,
    fa: &FieldAccessExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let obj = compile_expr(builder, &fa.object, variables, ctx)?;

    // Get slot and type from object's type
    let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, fa.field, ctx)?;

    let get_func_id = ctx
        .func_ids
        .get("vole_instance_get_field")
        .ok_or_else(|| "vole_instance_get_field not found".to_string())?;
    let get_func_ref = ctx.module.declare_func_in_func(*get_func_id, builder.func);

    let slot_val = builder.ins().iconst(types::I32, slot as i64);
    let call = builder.ins().call(get_func_ref, &[obj.value, slot_val]);
    let result_raw = builder.inst_results(call)[0];

    // Convert the raw i64 value to the appropriate type
    let (result_val, cranelift_ty) = convert_field_value(builder, result_raw, &field_type);

    Ok(CompiledValue {
        value: result_val,
        ty: cranelift_ty,
        vole_type: field_type,
    })
}

/// Compile field assignment: obj.field = value
fn compile_field_assign(
    builder: &mut FunctionBuilder,
    object: &Expr,
    field: Symbol,
    value_expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let obj = compile_expr(builder, object, variables, ctx)?;
    let value = compile_expr(builder, value_expr, variables, ctx)?;

    // Get slot from object's type
    let (slot, _field_type) = get_field_slot_and_type(&obj.vole_type, field, ctx)?;

    let set_func_id = ctx
        .func_ids
        .get("vole_instance_set_field")
        .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
    let set_func_ref = ctx.module.declare_func_in_func(*set_func_id, builder.func);

    let slot_val = builder.ins().iconst(types::I32, slot as i64);

    // Convert value to i64 for storage
    let store_value = convert_to_i64_for_storage(builder, &value);

    builder
        .ins()
        .call(set_func_ref, &[obj.value, slot_val, store_value]);

    Ok(value)
}

/// Compile index assignment: arr[i] = value
fn compile_index_assign(
    builder: &mut FunctionBuilder,
    object: &Expr,
    index: &Expr,
    value_expr: &Expr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let arr = compile_expr(builder, object, variables, ctx)?;
    let idx = compile_expr(builder, index, variables, ctx)?;
    let value = compile_expr(builder, value_expr, variables, ctx)?;

    // Get element type from array type
    let elem_type = match &arr.vole_type {
        Type::Array(elem) => elem.as_ref().clone(),
        _ => Type::I64,
    };

    // Call vole_array_set(arr, index, tag, value)
    let array_set_id = ctx
        .func_ids
        .get("vole_array_set")
        .ok_or_else(|| "vole_array_set not found".to_string())?;
    let array_set_ref = ctx.module.declare_func_in_func(*array_set_id, builder.func);

    // Convert value to i64 for storage
    let store_value = convert_to_i64_for_storage(builder, &value);

    // Determine tag based on type
    let tag = match &elem_type {
        Type::I64 | Type::I32 => 2i64, // TYPE_I64
        Type::F64 => 3i64,             // TYPE_F64
        Type::Bool => 4i64,            // TYPE_BOOL
        Type::String => 1i64,          // TYPE_STRING
        Type::Array(_) => 5i64,        // TYPE_ARRAY
        _ => 2i64,                     // default to I64
    };
    let tag_val = builder.ins().iconst(types::I64, tag);

    builder
        .ins()
        .call(array_set_ref, &[arr.value, idx.value, tag_val, store_value]);

    Ok(value)
}

/// Compile a try-catch expression
///
/// Layout of a fallible value (returned by the try_expr):
/// - Offset 0: tag (i64) - 0 for success, 1+ for error types
/// - Offset 8: payload - success value or error fields
///
/// Control flow:
/// 1. Compile try_expr to get fallible pointer
/// 2. Load tag
/// 3. Branch: if tag == 0, go to success block
/// 4. Otherwise, check each catch arm's pattern
/// 5. Merge all paths with block parameter
fn compile_try_catch(
    builder: &mut FunctionBuilder,
    try_catch: &TryCatchExpr,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    // Compile the try expression - should return a pointer to a fallible value
    let try_result = compile_expr(builder, &try_catch.try_expr, variables, ctx)?;

    // The try_result should be a Fallible type - get the inner types
    let (success_type, error_type) = match &try_result.vole_type {
        Type::Fallible(ft) => ((*ft.success_type).clone(), (*ft.error_type).clone()),
        _ => {
            return Err(format!(
                "try expression must have fallible type, got {:?}",
                try_result.vole_type
            ));
        }
    };

    // Extract the FallibleType for tag lookups
    let fallible_type = match &try_result.vole_type {
        Type::Fallible(ft) => ft.clone(),
        _ => unreachable!(),
    };

    // Load the tag from the fallible value (at offset 0, i64)
    let tag = builder.ins().load(
        types::I64,
        MemFlags::new(),
        try_result.value,
        FALLIBLE_TAG_OFFSET,
    );

    // Create blocks for control flow
    let success_block = builder.create_block();
    let first_catch_block = builder.create_block();
    let merge_block = builder.create_block();

    // Result type is the success type (after unwrapping fallible)
    let result_cranelift_type = type_to_cranelift(&success_type, ctx.pointer_type);
    builder.append_block_param(merge_block, result_cranelift_type);

    // Branch: if tag == 0 (success), go to success_block, else to first catch
    let success_tag = builder.ins().iconst(types::I64, FALLIBLE_SUCCESS_TAG);
    let is_success = builder.ins().icmp(IntCC::Equal, tag, success_tag);
    builder
        .ins()
        .brif(is_success, success_block, &[], first_catch_block, &[]);

    // === Success block ===
    builder.switch_to_block(success_block);
    builder.seal_block(success_block);

    // Load the success value from the payload (at offset 8)
    let success_value = builder.ins().load(
        result_cranelift_type,
        MemFlags::new(),
        try_result.value,
        FALLIBLE_PAYLOAD_OFFSET,
    );
    let success_arg = BlockArg::from(success_value);
    builder.ins().jump(merge_block, &[success_arg]);

    // === Catch blocks ===
    // Create blocks for each catch arm
    let catch_blocks: Vec<Block> = try_catch
        .catch_arms
        .iter()
        .map(|_| builder.create_block())
        .collect();

    // First catch block is where we jump from the initial branch
    builder.switch_to_block(first_catch_block);

    // Jump to the first catch arm's block
    if !catch_blocks.is_empty() {
        builder.ins().jump(catch_blocks[0], &[]);
    } else {
        // No catch arms - should not happen after sema, but handle gracefully
        let default_val = builder.ins().iconst(result_cranelift_type, 0);
        let default_arg = BlockArg::from(default_val);
        builder.ins().jump(merge_block, &[default_arg]);
    }
    builder.seal_block(first_catch_block);

    // Compile each catch arm
    for (i, arm) in try_catch.catch_arms.iter().enumerate() {
        let arm_block = catch_blocks[i];
        let next_block = catch_blocks.get(i + 1).copied().unwrap_or(merge_block);

        builder.switch_to_block(arm_block);

        // Create a new variables scope for this arm's bindings
        let mut arm_variables = variables.clone();

        // Check pattern and bind variables
        match &arm.pattern {
            ErrorPattern::Wildcard(_) => {
                // Wildcard always matches - go directly to body
                let body_val = compile_expr(builder, &arm.body, &mut arm_variables, ctx)?;
                let result_val = convert_to_result_type(builder, &body_val, result_cranelift_type);
                let result_arg = BlockArg::from(result_val);
                builder.ins().jump(merge_block, &[result_arg]);
            }

            ErrorPattern::NamedEmpty { name, .. } => {
                // Get the error tag for this error type
                let error_tag = fallible_error_tag(&fallible_type, *name).ok_or_else(|| {
                    format!(
                        "Error type not found in fallible: {}",
                        ctx.interner.resolve(*name)
                    )
                })?;

                // Compare tag
                let expected_tag = builder.ins().iconst(types::I64, error_tag);
                let matches = builder.ins().icmp(IntCC::Equal, tag, expected_tag);

                // Create body block
                let body_block = builder.create_block();

                // Branch: if matches, go to body, else go to next arm
                builder
                    .ins()
                    .brif(matches, body_block, &[], next_block, &[]);

                // Compile body
                builder.switch_to_block(body_block);
                let body_val = compile_expr(builder, &arm.body, &mut arm_variables, ctx)?;
                let result_val = convert_to_result_type(builder, &body_val, result_cranelift_type);
                let result_arg = BlockArg::from(result_val);
                builder.ins().jump(merge_block, &[result_arg]);
                builder.seal_block(body_block);
            }

            ErrorPattern::Named { name, bindings, .. } => {
                // Get the error tag for this error type
                let error_tag = fallible_error_tag(&fallible_type, *name).ok_or_else(|| {
                    format!(
                        "Error type not found in fallible: {}",
                        ctx.interner.resolve(*name)
                    )
                })?;

                // Compare tag
                let expected_tag = builder.ins().iconst(types::I64, error_tag);
                let matches = builder.ins().icmp(IntCC::Equal, tag, expected_tag);

                // Create body block
                let body_block = builder.create_block();

                // Branch: if matches, go to body, else go to next arm
                builder
                    .ins()
                    .brif(matches, body_block, &[], next_block, &[]);

                // Compile body with field bindings
                builder.switch_to_block(body_block);

                // Get the error type info to find field types and offsets
                let error_info = get_error_type_info(&error_type, *name).ok_or_else(|| {
                    format!(
                        "Error type info not found for: {}",
                        ctx.interner.resolve(*name)
                    )
                })?;

                // Bind each destructured field
                for (field_name, binding_name) in bindings {
                    // Find the field in the error type
                    let (field_idx, field_type) = error_info
                        .fields
                        .iter()
                        .enumerate()
                        .find(|(_, f)| f.name == *field_name)
                        .map(|(idx, f)| (idx, f.ty.clone()))
                        .ok_or_else(|| {
                            format!(
                                "Field {} not found in error type {}",
                                ctx.interner.resolve(*field_name),
                                ctx.interner.resolve(*name)
                            )
                        })?;

                    // Calculate field offset: payload starts at offset 8, each field is 8 bytes
                    let field_offset = FALLIBLE_PAYLOAD_OFFSET + (field_idx as i32 * 8);

                    // Load the field value
                    let field_cranelift_type = type_to_cranelift(&field_type, ctx.pointer_type);
                    let field_value = builder.ins().load(
                        field_cranelift_type,
                        MemFlags::new(),
                        try_result.value,
                        field_offset,
                    );

                    // Bind to variable
                    let var = builder.declare_var(field_cranelift_type);
                    builder.def_var(var, field_value);
                    arm_variables.insert(*binding_name, (var, field_type));
                }

                let body_val = compile_expr(builder, &arm.body, &mut arm_variables, ctx)?;
                let result_val = convert_to_result_type(builder, &body_val, result_cranelift_type);
                let result_arg = BlockArg::from(result_val);
                builder.ins().jump(merge_block, &[result_arg]);
                builder.seal_block(body_block);
            }
        }

        builder.seal_block(arm_block);
    }

    // === Merge block ===
    builder.switch_to_block(merge_block);
    builder.seal_block(merge_block);

    let result = builder.block_params(merge_block)[0];
    Ok(CompiledValue {
        value: result,
        ty: result_cranelift_type,
        vole_type: success_type,
    })
}

/// Convert a compiled value to the expected result type for merge block
fn convert_to_result_type(
    builder: &mut FunctionBuilder,
    val: &CompiledValue,
    target: types::Type,
) -> Value {
    if val.ty == target {
        return val.value;
    }

    // Integer widening
    if target.is_int() && val.ty.is_int() && target.bits() > val.ty.bits() {
        return builder.ins().sextend(target, val.value);
    }

    // Integer narrowing
    if target.is_int() && val.ty.is_int() && target.bits() < val.ty.bits() {
        return builder.ins().ireduce(target, val.value);
    }

    val.value
}

/// Get error type info from an error type or union of error types
fn get_error_type_info(error_type: &Type, name: Symbol) -> Option<ErrorTypeInfo> {
    match error_type {
        Type::ErrorType(info) if info.name == name => Some(info.clone()),
        Type::Union(variants) => variants.iter().find_map(|v| match v {
            Type::ErrorType(info) if info.name == name => Some(info.clone()),
            _ => None,
        }),
        _ => None,
    }
}

/// Compile a method call: point.distance()
fn compile_method_call(
    builder: &mut FunctionBuilder,
    mc: &MethodCallExpr,
    expr_id: NodeId,
    variables: &mut HashMap<Symbol, (Variable, Type)>,
    ctx: &mut CompileCtx,
) -> Result<CompiledValue, String> {
    let obj = compile_expr(builder, &mc.object, variables, ctx)?;
    let method_name_str = ctx.interner.resolve(mc.method);

    // Handle built-in methods for primitive types
    if let Some(result) = compile_builtin_method(builder, &obj, method_name_str, ctx)? {
        return Ok(result);
    }

    // Look up method resolution to determine naming convention and return type
    // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
    let resolution = ctx.method_resolutions.get(expr_id);

    // Determine the method function name based on resolution type
    let (full_name, return_type) = if let Some(resolution) = resolution {
        match resolution {
            ResolvedMethod::Direct { func_type } => {
                // Direct method on class/record: use TypeName_methodName
                let type_name = get_type_name_symbol(&obj.vole_type)?;
                let type_name_str = ctx.interner.resolve(type_name);
                let name = format!("{}_{}", type_name_str, method_name_str);
                (name, (*func_type.return_type).clone())
            }
            ResolvedMethod::Implemented {
                func_type,
                is_builtin,
                ..
            } => {
                if *is_builtin {
                    // Built-in methods should have been handled above
                    return Err(format!("Unhandled builtin method: {}", method_name_str));
                }
                // Implement block method: use TypeName::methodName
                let type_id = TypeId::from_type(&obj.vole_type)
                    .ok_or_else(|| format!("Cannot get TypeId for {:?}", obj.vole_type))?;
                let type_name_str = type_id.type_name(ctx.interner);
                let name = format!("{}::{}", type_name_str, method_name_str);
                (name, (*func_type.return_type).clone())
            }
            ResolvedMethod::FunctionalInterface { func_type } => {
                // For functional interfaces, the object IS the closure pointer
                // Call it as a closure
                return compile_closure_call(
                    builder, obj.value, func_type, &mc.args, variables, ctx,
                );
            }
            ResolvedMethod::DefaultMethod {
                type_name,
                func_type,
                ..
            } => {
                // Default method from interface, monomorphized for the concrete type
                // Name format is TypeName_methodName (same as direct methods)
                let type_name_str = ctx.interner.resolve(*type_name);
                let name = format!("{}_{}", type_name_str, method_name_str);
                (name, (*func_type.return_type).clone())
            }
        }
    } else {
        // No resolution found - try to resolve directly from object type
        // This handles method calls inside default method bodies where sema
        // doesn't analyze the interface body
        let type_name = get_type_name_symbol(&obj.vole_type)?;
        let type_name_str = ctx.interner.resolve(type_name);

        // Look up method return type from type metadata
        let return_type = ctx
            .type_metadata
            .get(&type_name)
            .and_then(|meta| meta.method_return_types.get(&mc.method).cloned())
            .ok_or_else(|| {
                format!(
                    "Method {} not found on type {}",
                    method_name_str, type_name_str
                )
            })?;

        let name = format!("{}_{}", type_name_str, method_name_str);
        (name, return_type)
    };

    let method_func_id = ctx
        .func_ids
        .get(&full_name)
        .ok_or_else(|| format!("Unknown method: {}", full_name))?;
    let method_func_ref = ctx
        .module
        .declare_func_in_func(*method_func_id, builder.func);

    // Args: self first, then user args
    let mut args = vec![obj.value];
    for arg in &mc.args {
        let compiled = compile_expr(builder, arg, variables, ctx)?;
        args.push(compiled.value);
    }

    let call = builder.ins().call(method_func_ref, &args);
    let results = builder.inst_results(call);

    if results.is_empty() {
        Ok(CompiledValue {
            value: builder.ins().iconst(types::I64, 0),
            ty: types::I64,
            vole_type: Type::Void,
        })
    } else {
        Ok(CompiledValue {
            value: results[0],
            ty: type_to_cranelift(&return_type, ctx.pointer_type),
            vole_type: return_type,
        })
    }
}

/// Compile a built-in method call for primitive types
/// Returns Some(CompiledValue) if handled, None if not a built-in
fn compile_builtin_method(
    builder: &mut FunctionBuilder,
    obj: &CompiledValue,
    method_name: &str,
    ctx: &mut CompileCtx,
) -> Result<Option<CompiledValue>, String> {
    match (&obj.vole_type, method_name) {
        // Array.length() -> i64
        (Type::Array(_), "length") => {
            let func_id = ctx
                .func_ids
                .get("vole_array_len")
                .ok_or_else(|| "vole_array_len not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
            }))
        }
        // String.length() -> i64
        (Type::String, "length") => {
            let func_id = ctx
                .func_ids
                .get("vole_string_len")
                .ok_or_else(|| "vole_string_len not found".to_string())?;
            let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
            let call = builder.ins().call(func_ref, &[obj.value]);
            let result = builder.inst_results(call)[0];
            Ok(Some(CompiledValue {
                value: result,
                ty: types::I64,
                vole_type: Type::I64,
            }))
        }
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Parser;

    fn compile_and_run(source: &str) -> i64 {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();

        let mut jit = JitContext::new();
        {
            let mut compiler = Compiler::new(
                &mut jit,
                &interner,
                HashMap::new(),
                HashMap::new(),
                MethodResolutions::new(),
                InterfaceRegistry::new(),
                HashMap::new(),
                HashMap::new(), // error_types
            );
            compiler.compile_program(&program).unwrap();
        }
        jit.finalize();

        let fn_ptr = jit.get_function_ptr("main").unwrap();
        let main: extern "C" fn() -> i64 = unsafe { std::mem::transmute(fn_ptr) };
        main()
    }

    #[test]
    fn compile_return_literal() {
        let result = compile_and_run("func main() -> i64 { return 42 }");
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_arithmetic() {
        let result = compile_and_run("func main() -> i64 { return 10 + 32 }");
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_let_and_return() {
        let result = compile_and_run("func main() -> i64 { let x = 40\n return x + 2 }");
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_multiple_ops() {
        let result = compile_and_run("func main() -> i64 { return 2 + 3 * 10 }");
        assert_eq!(result, 32); // 2 + 30
    }

    #[test]
    fn compile_while_loop() {
        let source = r#"
func main() -> i64 {
    let mut x = 0
    while x < 10 {
        x = x + 1
    }
    return x
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 10);
    }

    #[test]
    fn compile_if_else() {
        let source = r#"
func main() -> i64 {
    let x = 10
    if x > 5 {
        return 1
    } else {
        return 0
    }
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 1);
    }

    #[test]
    fn compile_nested_while_with_break() {
        let source = r#"
func main() -> i64 {
    let mut sum = 0
    let mut i = 0
    while i < 100 {
        if i == 5 {
            break
        }
        sum = sum + i
        i = i + 1
    }
    return sum
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 10); // 0+1+2+3+4 = 10
    }

    #[test]
    fn compile_user_function_call() {
        let source = r#"
func add(a: i64, b: i64) -> i64 {
    return a + b
}

func main() -> i64 {
    return add(10, 32)
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_user_function_call_no_args() {
        let source = r#"
func get_answer() -> i64 {
    return 42
}

func main() -> i64 {
    return get_answer()
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 42);
    }

    #[test]
    fn compile_recursive_function() {
        let source = r#"
func factorial(n: i64) -> i64 {
    if n <= 1 {
        return 1
    }
    return n * factorial(n - 1)
}

func main() -> i64 {
    return factorial(5)
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 120); // 5! = 120
    }

    #[test]
    fn compile_println_i64() {
        // Test that println compiles and runs without crashing
        let source = r#"
func main() -> i64 {
    println(42)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_println_bool() {
        let source = r#"
func main() -> i64 {
    println(true)
    println(false)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_println_f64() {
        let source = r#"
func main() -> i64 {
    println(3.14)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_println_string() {
        let source = r#"
func main() -> i64 {
    println("Hello, World!")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_print_char() {
        let source = r#"
func main() -> i64 {
    print_char(65)
    print_char(10)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_string_literal_in_let() {
        let source = r#"
func main() -> i64 {
    let s = "test"
    println(s)
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string() {
        let source = r#"
func main() -> i64 {
    let x = 42
    println("The answer is {x}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string_multiple() {
        let source = r#"
func main() -> i64 {
    let a = 1
    let b = 2
    println("{a} + {b} = {a + b}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string_with_bool() {
        let source = r#"
func main() -> i64 {
    let flag = true
    println("flag is {flag}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }

    #[test]
    fn compile_interpolated_string_with_float() {
        let source = r#"
func main() -> i64 {
    let pi = 3.14159
    println("pi = {pi}")
    return 0
}
"#;
        let result = compile_and_run(source);
        assert_eq!(result, 0);
    }
}
