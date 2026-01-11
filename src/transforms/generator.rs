// src/transforms/generator.rs
//! Generator-to-state-machine transformation.
//!
//! Transforms generator functions (functions containing `yield`) into
//! state machine records with a `next()` method.
//!
//! ## Example transformation
//!
//! Input:
//! ```vole
//! func simple() -> Iterator<i64> {
//!     yield 1
//!     yield 2
//!     yield 3
//! }
//! ```
//!
//! Output (conceptual):
//! ```vole
//! record __Generator_simple {
//!     __state: i64,
//! }
//!
//! implement __Generator_simple {
//!     func next(self) -> i64 | Done {
//!         if self.__state == 0 {
//!             self.__state = 1
//!             return 1
//!         }
//!         if self.__state == 1 {
//!             self.__state = 2
//!             return 2
//!         }
//!         if self.__state == 2 {
//!             self.__state = 3
//!             return 3
//!         }
//!         return Done {}
//!     }
//! }
//!
//! func simple() -> Iterator<i64> {
//!     return __Generator_simple { __state: 0 }
//! }
//! ```

use crate::errors::SemanticError;
use crate::frontend::ast::*;
use crate::frontend::{Interner, Span};
use crate::sema::TypeError;

/// Transform all generator functions in a program to state machines.
///
/// This function:
/// 1. Identifies functions with `yield` expressions
/// 2. Generates a state machine record for each generator
/// 3. Generates an implement block with a `next()` method
/// 4. Replaces the original function body with record instantiation
///
/// Returns the number of generators transformed and any type errors found.
pub fn transform_generators(
    program: &mut Program,
    interner: &mut Interner,
) -> (usize, Vec<TypeError>) {
    let mut transformer = GeneratorTransformer::new(interner);
    transformer.transform(program)
}

struct GeneratorTransformer<'a> {
    interner: &'a mut Interner,
    /// Counter for generating unique state machine names
    generator_count: u32,
    /// Counter for generating unique NodeIds for generated AST nodes
    next_node_id: u32,
    /// Type errors found during transformation
    errors: Vec<TypeError>,
}

impl<'a> GeneratorTransformer<'a> {
    fn new(interner: &'a mut Interner) -> Self {
        Self {
            interner,
            generator_count: 0,
            next_node_id: 0, // Will be set in transform()
            errors: Vec::new(),
        }
    }

    /// Generate a unique NodeId for generated AST nodes
    fn next_id(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }

    fn transform(&mut self, program: &mut Program) -> (usize, Vec<TypeError>) {
        // Use the program's next_node_id to avoid collisions with existing nodes
        self.next_node_id = program.next_node_id;

        // Collect indices of generator functions and their info
        let mut generators_info = Vec::new();

        for (i, decl) in program.declarations.iter().enumerate() {
            if let Decl::Function(func) = decl
                && self.contains_yield(&func.body)
            {
                generators_info.push((i, func.clone()));
            }
        }

        let count = generators_info.len();

        // Generate new declarations for each generator
        let mut new_declarations = Vec::new();

        for (idx, func) in generators_info {
            // Generate state machine record and implement block
            if let Some((record_decl, impl_block, new_func)) = self.transform_generator(&func) {
                // Add implement block FIRST (will be inserted second = comes after record)
                new_declarations.push((idx, Decl::Implement(impl_block)));
                // Add record declaration SECOND (will be inserted first = comes before impl)
                new_declarations.push((idx, Decl::Record(record_decl)));
                // Replace original function
                program.declarations[idx] = Decl::Function(new_func);
            }
        }

        // Insert new declarations before their corresponding functions
        // We need to insert in reverse order to preserve indices
        // Since we insert at the same index, later inserts come before earlier ones
        // So we push Implement first, Record second -> Record comes before Implement
        new_declarations.sort_by_key(|(idx, _)| std::cmp::Reverse(*idx));
        for (idx, decl) in new_declarations {
            program.declarations.insert(idx, decl);
        }

        // Update program's next_node_id to reflect nodes created during transform
        program.next_node_id = self.next_node_id;

        (count, std::mem::take(&mut self.errors))
    }

    /// Check if a block contains any yield expressions
    fn contains_yield(&self, block: &Block) -> bool {
        for stmt in &block.stmts {
            if self.stmt_contains_yield(stmt) {
                return true;
            }
        }
        false
    }

    fn stmt_contains_yield(&self, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Expr(expr_stmt) => self.expr_contains_yield(&expr_stmt.expr),
            Stmt::Let(let_stmt) => match &let_stmt.init {
                LetInit::Expr(e) => self.expr_contains_yield(e),
                LetInit::TypeAlias(_) => false,
            },
            Stmt::While(while_stmt) => {
                self.expr_contains_yield(&while_stmt.condition)
                    || self.contains_yield(&while_stmt.body)
            }
            Stmt::For(for_stmt) => {
                self.expr_contains_yield(&for_stmt.iterable) || self.contains_yield(&for_stmt.body)
            }
            Stmt::If(if_stmt) => {
                self.expr_contains_yield(&if_stmt.condition)
                    || self.contains_yield(&if_stmt.then_branch)
                    || if_stmt
                        .else_branch
                        .as_ref()
                        .is_some_and(|b| self.contains_yield(b))
            }
            Stmt::Return(ret_stmt) => ret_stmt
                .value
                .as_ref()
                .is_some_and(|e| self.expr_contains_yield(e)),
            Stmt::LetTuple(lt) => self.expr_contains_yield(&lt.init),
            Stmt::Raise(_) | Stmt::Break(_) | Stmt::Continue(_) => false,
        }
    }

    fn expr_contains_yield(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Yield(_) => true,
            ExprKind::Binary(bin) => {
                self.expr_contains_yield(&bin.left) || self.expr_contains_yield(&bin.right)
            }
            ExprKind::Unary(un) => self.expr_contains_yield(&un.operand),
            ExprKind::Call(call) => {
                self.expr_contains_yield(&call.callee)
                    || call.args.iter().any(|a| self.expr_contains_yield(a))
            }
            ExprKind::Grouping(inner) => self.expr_contains_yield(inner),
            ExprKind::ArrayLiteral(elems) => elems.iter().any(|e| self.expr_contains_yield(e)),
            ExprKind::RepeatLiteral { element, .. } => self.expr_contains_yield(element),
            ExprKind::Index(idx) => {
                self.expr_contains_yield(&idx.object) || self.expr_contains_yield(&idx.index)
            }
            ExprKind::Match(m) => {
                self.expr_contains_yield(&m.scrutinee)
                    || m.arms.iter().any(|arm| self.expr_contains_yield(&arm.body))
            }
            ExprKind::NullCoalesce(nc) => {
                self.expr_contains_yield(&nc.value) || self.expr_contains_yield(&nc.default)
            }
            ExprKind::Is(is_expr) => self.expr_contains_yield(&is_expr.value),
            ExprKind::FieldAccess(fa) => self.expr_contains_yield(&fa.object),
            ExprKind::OptionalChain(oc) => self.expr_contains_yield(&oc.object),
            ExprKind::MethodCall(mc) => {
                self.expr_contains_yield(&mc.object)
                    || mc.args.iter().any(|a| self.expr_contains_yield(a))
            }
            ExprKind::StructLiteral(sl) => {
                sl.fields.iter().any(|f| self.expr_contains_yield(&f.value))
            }
            ExprKind::Assign(assign) => self.expr_contains_yield(&assign.value),
            ExprKind::CompoundAssign(ca) => self.expr_contains_yield(&ca.value),
            ExprKind::Range(range) => {
                self.expr_contains_yield(&range.start) || self.expr_contains_yield(&range.end)
            }
            ExprKind::Lambda(lambda) => match &lambda.body {
                LambdaBody::Expr(e) => self.expr_contains_yield(e),
                LambdaBody::Block(b) => self.contains_yield(b),
            },
            ExprKind::Try(inner) => self.expr_contains_yield(inner),
            ExprKind::InterpolatedString(parts) => parts.iter().any(|p| match p {
                StringPart::Literal(_) => false,
                StringPart::Expr(e) => self.expr_contains_yield(e),
            }),
            ExprKind::Block(block) => {
                block.stmts.iter().any(|s| self.stmt_contains_yield(s))
                    || block
                        .trailing_expr
                        .as_ref()
                        .is_some_and(|e| self.expr_contains_yield(e))
            }
            ExprKind::If(if_expr) => {
                self.expr_contains_yield(&if_expr.condition)
                    || self.expr_contains_yield(&if_expr.then_branch)
                    || if_expr
                        .else_branch
                        .as_ref()
                        .is_some_and(|e| self.expr_contains_yield(e))
            }
            // Leaf expressions that can't contain yield
            ExprKind::IntLiteral(_)
            | ExprKind::FloatLiteral(_)
            | ExprKind::BoolLiteral(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::Identifier(_)
            | ExprKind::Nil
            | ExprKind::Done
            | ExprKind::TypeLiteral(_)
            | ExprKind::Import(_) => false,
        }
    }

    /// Transform a generator function into a state machine.
    /// Returns (record declaration, implement block, new function declaration).
    fn transform_generator(
        &mut self,
        func: &FuncDecl,
    ) -> Option<(RecordDecl, ImplementBlock, FuncDecl)> {
        // Extract the element type from Iterator<T>
        let element_type = match &func.return_type {
            Some(TypeExpr::Generic { name, args })
                if self.interner.resolve(*name) == "Iterator" && args.len() == 1 =>
            {
                args[0].clone()
            }
            _ => return None, // Not a generator function (should have been caught earlier)
        };

        // Generate unique name for the state machine record
        let record_name = self.interner.intern_with_prefix("__Generator_", func.name);
        self.generator_count += 1;

        // Collect yields to determine states
        let yields = self.collect_yields(&func.body);
        if yields.is_empty() {
            return None; // No yields, not actually a generator
        }

        // Validate yield types against the expected element type
        self.validate_yield_types(&yields, &element_type);

        // Find local variables that need to be hoisted to the record
        let hoisted_locals = self.find_hoisted_locals(func);

        // Create record fields:
        // - __state: i64 (state machine state)
        // - captured parameters
        // - hoisted local variables
        let mut fields = Vec::new();
        let dummy_span = Span::default();

        // State field
        let state_sym = self.interner.intern("__state");
        fields.push(FieldDef {
            name: state_sym,
            ty: TypeExpr::Primitive(PrimitiveType::I64),
            span: dummy_span,
        });

        // Captured parameters
        for param in &func.params {
            fields.push(FieldDef {
                name: param.name,
                ty: param.ty.clone(),
                span: dummy_span,
            });
        }

        // Hoisted local variables
        for (name, ty) in &hoisted_locals {
            fields.push(FieldDef {
                name: *name,
                ty: ty.clone(),
                span: dummy_span,
            });
        }

        // Create the record declaration
        // Note: implements uses TypeExpr - for Iterator<T>, we use the element type
        let iterator_sym = self.interner.intern("Iterator");
        let iterator_type = TypeExpr::Generic {
            name: iterator_sym,
            args: vec![element_type.clone()],
        };
        let record_decl = RecordDecl {
            name: record_name,
            type_params: Vec::new(),
            implements: vec![iterator_type.clone()],
            fields,
            external: None,
            methods: Vec::new(),
            statics: None,
            span: func.span,
        };

        // Create the next() method
        let next_method = self.create_next_method(
            &yields,
            &element_type,
            &func.params,
            &hoisted_locals,
            func.span,
        );

        // Create the implement block for Iterator<T>
        let impl_block = ImplementBlock {
            trait_type: Some(iterator_type),
            target_type: TypeExpr::Named(record_name),
            external: None,
            methods: vec![next_method],
            statics: None,
            span: func.span,
        };

        // Create the new function that returns the record
        let new_func = self.create_wrapper_function(func, record_name, &hoisted_locals);

        Some((record_decl, impl_block, new_func))
    }

    /// Collect all yield expressions from a function body (in order).
    fn collect_yields(&self, block: &Block) -> Vec<Expr> {
        let mut yields = Vec::new();
        self.collect_yields_from_block(block, &mut yields);
        yields
    }

    fn collect_yields_from_block(&self, block: &Block, yields: &mut Vec<Expr>) {
        for stmt in &block.stmts {
            self.collect_yields_from_stmt(stmt, yields);
        }
    }

    fn collect_yields_from_stmt(&self, stmt: &Stmt, yields: &mut Vec<Expr>) {
        match stmt {
            Stmt::Expr(expr_stmt) => self.collect_yields_from_expr(&expr_stmt.expr, yields),
            Stmt::Let(let_stmt) => {
                if let LetInit::Expr(e) = &let_stmt.init {
                    self.collect_yields_from_expr(e, yields);
                }
            }
            Stmt::While(while_stmt) => {
                self.collect_yields_from_expr(&while_stmt.condition, yields);
                self.collect_yields_from_block(&while_stmt.body, yields);
            }
            Stmt::For(for_stmt) => {
                self.collect_yields_from_expr(&for_stmt.iterable, yields);
                self.collect_yields_from_block(&for_stmt.body, yields);
            }
            Stmt::If(if_stmt) => {
                self.collect_yields_from_expr(&if_stmt.condition, yields);
                self.collect_yields_from_block(&if_stmt.then_branch, yields);
                if let Some(else_branch) = &if_stmt.else_branch {
                    self.collect_yields_from_block(else_branch, yields);
                }
            }
            Stmt::Return(ret_stmt) => {
                if let Some(value) = &ret_stmt.value {
                    self.collect_yields_from_expr(value, yields);
                }
            }
            Stmt::LetTuple(lt) => {
                self.collect_yields_from_expr(&lt.init, yields);
            }
            Stmt::Raise(_) | Stmt::Break(_) | Stmt::Continue(_) => {}
        }
    }

    fn collect_yields_from_expr(&self, expr: &Expr, yields: &mut Vec<Expr>) {
        match &expr.kind {
            ExprKind::Yield(yield_expr) => {
                // Clone the yielded value expression
                yields.push(yield_expr.value.clone());
            }
            ExprKind::Binary(bin) => {
                self.collect_yields_from_expr(&bin.left, yields);
                self.collect_yields_from_expr(&bin.right, yields);
            }
            ExprKind::Unary(un) => {
                self.collect_yields_from_expr(&un.operand, yields);
            }
            ExprKind::Call(call) => {
                self.collect_yields_from_expr(&call.callee, yields);
                for arg in &call.args {
                    self.collect_yields_from_expr(arg, yields);
                }
            }
            ExprKind::Grouping(inner) => {
                self.collect_yields_from_expr(inner, yields);
            }
            ExprKind::ArrayLiteral(elems) => {
                for elem in elems {
                    self.collect_yields_from_expr(elem, yields);
                }
            }
            ExprKind::RepeatLiteral { element, .. } => {
                self.collect_yields_from_expr(element, yields);
            }
            ExprKind::Index(idx) => {
                self.collect_yields_from_expr(&idx.object, yields);
                self.collect_yields_from_expr(&idx.index, yields);
            }
            ExprKind::Match(m) => {
                self.collect_yields_from_expr(&m.scrutinee, yields);
                for arm in &m.arms {
                    self.collect_yields_from_expr(&arm.body, yields);
                }
            }
            ExprKind::NullCoalesce(nc) => {
                self.collect_yields_from_expr(&nc.value, yields);
                self.collect_yields_from_expr(&nc.default, yields);
            }
            ExprKind::Is(is_expr) => {
                self.collect_yields_from_expr(&is_expr.value, yields);
            }
            ExprKind::FieldAccess(fa) => {
                self.collect_yields_from_expr(&fa.object, yields);
            }
            ExprKind::OptionalChain(oc) => {
                self.collect_yields_from_expr(&oc.object, yields);
            }
            ExprKind::MethodCall(mc) => {
                self.collect_yields_from_expr(&mc.object, yields);
                for arg in &mc.args {
                    self.collect_yields_from_expr(arg, yields);
                }
            }
            ExprKind::StructLiteral(sl) => {
                for field in &sl.fields {
                    self.collect_yields_from_expr(&field.value, yields);
                }
            }
            ExprKind::Assign(assign) => {
                self.collect_yields_from_expr(&assign.value, yields);
            }
            ExprKind::CompoundAssign(ca) => {
                self.collect_yields_from_expr(&ca.value, yields);
            }
            ExprKind::Range(range) => {
                self.collect_yields_from_expr(&range.start, yields);
                self.collect_yields_from_expr(&range.end, yields);
            }
            ExprKind::Lambda(lambda) => match &lambda.body {
                LambdaBody::Expr(e) => self.collect_yields_from_expr(e, yields),
                LambdaBody::Block(b) => self.collect_yields_from_block(b, yields),
            },
            ExprKind::Try(inner) => {
                self.collect_yields_from_expr(inner, yields);
            }
            ExprKind::InterpolatedString(parts) => {
                for part in parts {
                    if let StringPart::Expr(e) = part {
                        self.collect_yields_from_expr(e, yields);
                    }
                }
            }
            ExprKind::Block(block) => {
                for stmt in &block.stmts {
                    self.collect_yields_from_stmt(stmt, yields);
                }
                if let Some(trailing) = &block.trailing_expr {
                    self.collect_yields_from_expr(trailing, yields);
                }
            }
            ExprKind::If(if_expr) => {
                self.collect_yields_from_expr(&if_expr.condition, yields);
                self.collect_yields_from_expr(&if_expr.then_branch, yields);
                if let Some(else_branch) = &if_expr.else_branch {
                    self.collect_yields_from_expr(else_branch, yields);
                }
            }
            // Leaf expressions
            ExprKind::IntLiteral(_)
            | ExprKind::FloatLiteral(_)
            | ExprKind::BoolLiteral(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::Identifier(_)
            | ExprKind::Nil
            | ExprKind::Done
            | ExprKind::TypeLiteral(_)
            | ExprKind::Import(_) => {}
        }
    }

    /// Validate that yield expression types match the expected Iterator element type.
    /// This performs basic literal type checking to catch obvious mismatches early.
    fn validate_yield_types(&mut self, yields: &[Expr], expected_type: &TypeExpr) {
        for yield_expr in yields {
            if let Some((inferred_type, type_name)) = self.infer_literal_type(yield_expr)
                && !self.type_expr_matches(&inferred_type, expected_type)
            {
                let expected_name = self.type_expr_to_string(expected_type);
                // Add E2001-style type mismatch error
                self.errors.push(TypeError::new(
                    SemanticError::TypeMismatch {
                        expected: expected_name.clone(),
                        found: type_name.clone(),
                        span: yield_expr.span.into(),
                    },
                    yield_expr.span,
                ));
                // Add E2071-style yield type mismatch error
                self.errors.push(TypeError::new(
                    SemanticError::YieldTypeMismatch {
                        expected: expected_name,
                        found: type_name,
                        span: yield_expr.span.into(),
                    },
                    yield_expr.span,
                ));
            }
        }
    }

    /// Try to infer the type of a literal expression.
    /// Returns (TypeExpr, type_name_string) if successful.
    fn infer_literal_type(&self, expr: &Expr) -> Option<(TypeExpr, String)> {
        match &expr.kind {
            ExprKind::IntLiteral(_) => {
                Some((TypeExpr::Primitive(PrimitiveType::I64), "i64".to_string()))
            }
            ExprKind::FloatLiteral(_) => {
                Some((TypeExpr::Primitive(PrimitiveType::F64), "f64".to_string()))
            }
            ExprKind::BoolLiteral(_) => {
                Some((TypeExpr::Primitive(PrimitiveType::Bool), "bool".to_string()))
            }
            ExprKind::StringLiteral(_) | ExprKind::InterpolatedString(_) => Some((
                TypeExpr::Primitive(PrimitiveType::String),
                "string".to_string(),
            )),
            ExprKind::Nil => Some((TypeExpr::Nil, "nil".to_string())),
            ExprKind::Done => Some((TypeExpr::Done, "Done".to_string())),
            // For non-literals, we can't infer the type without full semantic analysis
            _ => None,
        }
    }

    /// Check if two TypeExpr are compatible (for basic literal checking).
    fn type_expr_matches(&self, actual: &TypeExpr, expected: &TypeExpr) -> bool {
        match (actual, expected) {
            (TypeExpr::Primitive(a), TypeExpr::Primitive(b)) => a == b,
            (TypeExpr::Nil, TypeExpr::Nil) => true,
            (TypeExpr::Done, TypeExpr::Done) => true,
            (TypeExpr::Named(a), TypeExpr::Named(b)) => a == b,
            // For complex types or optionals, assume compatible and let sema handle it
            _ => true,
        }
    }

    /// Convert a TypeExpr to a string for error messages.
    fn type_expr_to_string(&self, ty: &TypeExpr) -> String {
        match ty {
            TypeExpr::Primitive(p) => match p {
                PrimitiveType::I8 => "i8".to_string(),
                PrimitiveType::I16 => "i16".to_string(),
                PrimitiveType::I32 => "i32".to_string(),
                PrimitiveType::I64 => "i64".to_string(),
                PrimitiveType::I128 => "i128".to_string(),
                PrimitiveType::U8 => "u8".to_string(),
                PrimitiveType::U16 => "u16".to_string(),
                PrimitiveType::U32 => "u32".to_string(),
                PrimitiveType::U64 => "u64".to_string(),
                PrimitiveType::F32 => "f32".to_string(),
                PrimitiveType::F64 => "f64".to_string(),
                PrimitiveType::Bool => "bool".to_string(),
                PrimitiveType::String => "string".to_string(),
            },
            TypeExpr::Named(sym) => self.interner.resolve(*sym).to_string(),
            TypeExpr::Nil => "nil".to_string(),
            TypeExpr::Done => "Done".to_string(),
            TypeExpr::Optional(inner) => format!("{}?", self.type_expr_to_string(inner)),
            TypeExpr::Array(inner) => format!("[{}]", self.type_expr_to_string(inner)),
            TypeExpr::Union(variants) => variants
                .iter()
                .map(|v| self.type_expr_to_string(v))
                .collect::<Vec<_>>()
                .join(" | "),
            TypeExpr::Function {
                params,
                return_type,
            } => {
                let params_str = params
                    .iter()
                    .map(|p| self.type_expr_to_string(p))
                    .collect::<Vec<_>>()
                    .join(", ");
                let ret = self.type_expr_to_string(return_type);
                format!("({}) -> {}", params_str, ret)
            }
            TypeExpr::SelfType => "Self".to_string(),
            TypeExpr::Fallible {
                success_type,
                error_type,
            } => format!(
                "fallible({}, {})",
                self.type_expr_to_string(success_type),
                self.type_expr_to_string(error_type)
            ),
            TypeExpr::Generic { name, args } => {
                let args_str = args
                    .iter()
                    .map(|a| self.type_expr_to_string(a))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{}>", self.interner.resolve(*name), args_str)
            }
            TypeExpr::Tuple(elements) => {
                let elems_str = elements
                    .iter()
                    .map(|e| self.type_expr_to_string(e))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("[{}]", elems_str)
            }
            TypeExpr::FixedArray { element, size } => {
                format!("[{}; {}]", self.type_expr_to_string(element), size)
            }
        }
    }

    /// Find local variables that are live across yields and need to be hoisted.
    /// For now, we hoist all `let mut` bindings to be safe.
    fn find_hoisted_locals(&self, func: &FuncDecl) -> Vec<(Symbol, TypeExpr)> {
        let mut locals = Vec::new();
        self.find_locals_in_block(&func.body, &mut locals);
        locals
    }

    fn find_locals_in_block(&self, block: &Block, locals: &mut Vec<(Symbol, TypeExpr)>) {
        for stmt in &block.stmts {
            if let Stmt::Let(let_stmt) = stmt {
                // Only hoist mutable locals (they may change between yields)
                // For immutable locals, we'd need dataflow analysis to see if they're
                // live across yields. For simplicity, hoist all with explicit types.
                if let_stmt.mutable {
                    if let Some(ty) = &let_stmt.ty {
                        locals.push((let_stmt.name, ty.clone()));
                    } else {
                        // For now, assume i64 for untyped mutable locals
                        // A more complete solution would infer types or require annotations
                        locals.push((let_stmt.name, TypeExpr::Primitive(PrimitiveType::I64)));
                    }
                }
            }
            // Recurse into nested blocks
            match stmt {
                Stmt::While(while_stmt) => self.find_locals_in_block(&while_stmt.body, locals),
                Stmt::For(for_stmt) => self.find_locals_in_block(&for_stmt.body, locals),
                Stmt::If(if_stmt) => {
                    self.find_locals_in_block(&if_stmt.then_branch, locals);
                    if let Some(else_branch) = &if_stmt.else_branch {
                        self.find_locals_in_block(else_branch, locals);
                    }
                }
                _ => {}
            }
        }
    }

    /// Create the next() method for the state machine.
    ///
    /// For simple sequential yields:
    /// ```vole
    /// func next(self) -> T | Done {
    ///     if self.__state == 0 {
    ///         self.__state = 1
    ///         return <yield_0_value>
    ///     }
    ///     if self.__state == 1 {
    ///         self.__state = 2
    ///         return <yield_1_value>
    ///     }
    ///     // ... etc
    ///     return Done {}
    /// }
    /// ```
    fn create_next_method(
        &mut self,
        yields: &[Expr],
        element_type: &TypeExpr,
        _params: &[Param],
        _hoisted_locals: &[(Symbol, TypeExpr)],
        span: Span,
    ) -> FuncDecl {
        let self_sym = self.interner.intern("self");
        let state_sym = self.interner.intern("__state");
        let next_sym = self.interner.intern("next");

        let mut stmts = Vec::new();
        let dummy_span = Span::default();

        // Generate state branches
        for (i, yield_value) in yields.iter().enumerate() {
            // if self.__state == i {
            //     self.__state = i + 1
            //     return <yield_value>
            // }

            // Create: self.__state
            let self_expr = Expr {
                id: self.next_id(),
                kind: ExprKind::Identifier(self_sym),
                span: dummy_span,
            };
            let state_access = Expr {
                id: self.next_id(),
                kind: ExprKind::FieldAccess(Box::new(FieldAccessExpr {
                    object: self_expr.clone(),
                    field: state_sym,
                    field_span: dummy_span,
                })),
                span: dummy_span,
            };

            // Create: self.__state == i
            let condition = Expr {
                id: self.next_id(),
                kind: ExprKind::Binary(Box::new(BinaryExpr {
                    left: state_access.clone(),
                    op: BinaryOp::Eq,
                    right: Expr {
                        id: self.next_id(),
                        kind: ExprKind::IntLiteral(i as i64),
                        span: dummy_span,
                    },
                })),
                span: dummy_span,
            };

            // Create: self.__state = i + 1
            let state_assign = Stmt::Expr(ExprStmt {
                expr: Expr {
                    id: self.next_id(),
                    kind: ExprKind::Assign(Box::new(AssignExpr {
                        target: AssignTarget::Field {
                            object: Box::new(self_expr.clone()),
                            field: state_sym,
                            field_span: dummy_span,
                        },
                        value: Expr {
                            id: self.next_id(),
                            kind: ExprKind::IntLiteral((i + 1) as i64),
                            span: dummy_span,
                        },
                    })),
                    span: dummy_span,
                },
                span: dummy_span,
            });

            // Create: return <yield_value>
            let return_stmt = Stmt::Return(ReturnStmt {
                value: Some(yield_value.clone()),
                span: dummy_span,
            });

            // Create the if statement
            let if_stmt = Stmt::If(IfStmt {
                condition,
                then_branch: Block {
                    stmts: vec![state_assign, return_stmt],
                    span: dummy_span,
                },
                else_branch: None,
                span: dummy_span,
            });

            stmts.push(if_stmt);
        }

        // Final: return Done
        let done_return = Stmt::Return(ReturnStmt {
            value: Some(Expr {
                id: self.next_id(),
                kind: ExprKind::Done,
                span: dummy_span,
            }),
            span: dummy_span,
        });
        stmts.push(done_return);

        // Return type: T | Done
        let return_type = TypeExpr::Union(vec![element_type.clone(), TypeExpr::Done]);

        FuncDecl {
            name: next_sym,
            type_params: Vec::new(),
            // Note: Methods in implement blocks don't list `self` explicitly;
            // it's added implicitly by codegen
            params: vec![],
            return_type: Some(return_type),
            body: Block {
                stmts,
                span: dummy_span,
            },
            span,
        }
    }

    /// Create the wrapper function that instantiates the state machine.
    fn create_wrapper_function(
        &mut self,
        original: &FuncDecl,
        record_name: Symbol,
        hoisted_locals: &[(Symbol, TypeExpr)],
    ) -> FuncDecl {
        let state_sym = self.interner.intern("__state");
        let dummy_span = Span::default();

        // Build field initializers
        let mut fields = Vec::new();

        // __state: 0
        fields.push(StructFieldInit {
            name: state_sym,
            value: Expr {
                id: self.next_id(),
                kind: ExprKind::IntLiteral(0),
                span: dummy_span,
            },
            span: dummy_span,
        });

        // Captured parameters: name: name
        for param in &original.params {
            fields.push(StructFieldInit {
                name: param.name,
                value: Expr {
                    id: self.next_id(),
                    kind: ExprKind::Identifier(param.name),
                    span: dummy_span,
                },
                span: dummy_span,
            });
        }

        // Hoisted locals with default values
        for (name, ty) in hoisted_locals {
            let default_value = self.default_value_for_type(ty);
            fields.push(StructFieldInit {
                name: *name,
                value: default_value,
                span: dummy_span,
            });
        }

        // return RecordName { fields }
        let return_stmt = Stmt::Return(ReturnStmt {
            value: Some(Expr {
                id: self.next_id(),
                kind: ExprKind::StructLiteral(Box::new(StructLiteralExpr {
                    name: record_name,
                    fields,
                })),
                span: dummy_span,
            }),
            span: dummy_span,
        });

        FuncDecl {
            name: original.name,
            type_params: Vec::new(),
            params: original.params.clone(),
            // Return type is the original Iterator<T> - codegen will box the record
            return_type: original.return_type.clone(),
            body: Block {
                stmts: vec![return_stmt],
                span: original.body.span,
            },
            span: original.span,
        }
    }

    /// Get a default value expression for a type.
    fn default_value_for_type(&mut self, ty: &TypeExpr) -> Expr {
        let dummy_span = Span::default();
        match ty {
            TypeExpr::Primitive(PrimitiveType::I8)
            | TypeExpr::Primitive(PrimitiveType::I16)
            | TypeExpr::Primitive(PrimitiveType::I32)
            | TypeExpr::Primitive(PrimitiveType::I64)
            | TypeExpr::Primitive(PrimitiveType::I128)
            | TypeExpr::Primitive(PrimitiveType::U8)
            | TypeExpr::Primitive(PrimitiveType::U16)
            | TypeExpr::Primitive(PrimitiveType::U32)
            | TypeExpr::Primitive(PrimitiveType::U64) => Expr {
                id: self.next_id(),
                kind: ExprKind::IntLiteral(0),
                span: dummy_span,
            },
            TypeExpr::Primitive(PrimitiveType::F32) | TypeExpr::Primitive(PrimitiveType::F64) => {
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::FloatLiteral(0.0),
                    span: dummy_span,
                }
            }
            TypeExpr::Primitive(PrimitiveType::Bool) => Expr {
                id: self.next_id(),
                kind: ExprKind::BoolLiteral(false),
                span: dummy_span,
            },
            TypeExpr::Primitive(PrimitiveType::String) => Expr {
                id: self.next_id(),
                kind: ExprKind::StringLiteral(String::new()),
                span: dummy_span,
            },
            _ => Expr {
                id: self.next_id(),
                kind: ExprKind::IntLiteral(0),
                span: dummy_span,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Parser;

    #[test]
    fn test_contains_yield() {
        let source = r#"
            func gen() -> Iterator<i64> {
                yield 1
                yield 2
            }
        "#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().expect("parse failed");
        let interner = parser.into_interner();

        if let Decl::Function(func) = &program.declarations[0] {
            let mut interner_copy = interner.clone();
            let transformer = GeneratorTransformer::new(&mut interner_copy);
            assert!(transformer.contains_yield(&func.body));
        }
    }

    #[test]
    fn test_no_yield() {
        let source = r#"
            func regular() -> i64 {
                return 42
            }
        "#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().expect("parse failed");
        let interner = parser.into_interner();

        if let Decl::Function(func) = &program.declarations[0] {
            let mut interner_copy = interner.clone();
            let transformer = GeneratorTransformer::new(&mut interner_copy);
            assert!(!transformer.contains_yield(&func.body));
        }
    }

    #[test]
    fn test_transform_simple_generator() {
        let source = r#"
            func simple() -> Iterator<i64> {
                yield 1
                yield 2
                yield 3
            }
        "#;
        let mut parser = Parser::new(source);
        let mut program = parser.parse_program().expect("parse failed");
        let mut interner = parser.into_interner();

        let (count, errors) = transform_generators(&mut program, &mut interner);
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
        assert_eq!(count, 1);

        // Should have: record, implement, function (3 declarations total)
        assert_eq!(program.declarations.len(), 3);

        // First should be the record
        assert!(matches!(program.declarations[0], Decl::Record(_)));

        // Second should be the implement block
        assert!(matches!(program.declarations[1], Decl::Implement(_)));

        // Third should be the function
        assert!(matches!(program.declarations[2], Decl::Function(_)));
    }
}
