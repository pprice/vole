# Inspect Command Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add `vole inspect` command that dumps AST and Cranelift IR for debugging.

**Architecture:** CLI command with two modes (ast/ir). AST uses custom `AstPrinter` with interner resolution. IR uses new `compile_to_ir` method that builds Cranelift IR without JIT finalization.

**Tech Stack:** Rust, clap (CLI), glob (file patterns), Cranelift (IR display)

---

## Task 1: Add CLI Arguments

**Files:**
- Modify: `src/cli/args.rs`

**Step 1: Add InspectType enum and Inspect command**

Add after the `Commands` enum:

```rust
#[derive(Clone, ValueEnum)]
pub enum InspectType {
    Ast,
    Ir,
}
```

Add to `Commands` enum:

```rust
    /// Inspect compilation output (AST, IR)
    Inspect {
        /// What to inspect: ast, ir
        #[arg(value_name = "TYPE")]
        inspect_type: InspectType,

        /// Paths to inspect (files or glob patterns)
        #[arg(value_name = "FILES", required = true)]
        files: Vec<String>,

        /// Exclude test blocks from output
        #[arg(long)]
        no_tests: bool,

        /// Include imports: "project" or "all" (not yet implemented)
        #[arg(long)]
        imports: Option<String>,
    },
```

**Step 2: Verify it compiles**

Run: `cargo build 2>&1 | head -20`
Expected: Compiles (with unused warnings)

**Step 3: Commit**

```bash
git add src/cli/args.rs
git commit -m "feat(cli): add inspect command arguments"
```

---

## Task 2: Wire Up Command Entry Point

**Files:**
- Modify: `src/bin/vole.rs`
- Modify: `src/commands/mod.rs`
- Create: `src/commands/inspect.rs`

**Step 1: Create stub inspect module**

Create `src/commands/inspect.rs`:

```rust
// src/commands/inspect.rs

use std::process::ExitCode;

use crate::cli::InspectType;

/// Inspect compilation output for the given files
pub fn inspect_files(
    files: &[String],
    inspect_type: InspectType,
    no_tests: bool,
    _imports: Option<&str>,
) -> ExitCode {
    eprintln!(
        "inspect {:?} files={:?} no_tests={}",
        inspect_type, files, no_tests
    );
    ExitCode::SUCCESS
}
```

**Step 2: Add module to mod.rs**

Add to `src/commands/mod.rs`:

```rust
pub mod inspect;
```

**Step 3: Wire up in main**

Add import to `src/bin/vole.rs`:

```rust
use vole::commands::inspect::inspect_files;
```

Add match arm:

```rust
        Commands::Inspect {
            inspect_type,
            files,
            no_tests,
            imports,
        } => inspect_files(&files, inspect_type, no_tests, imports.as_deref()),
```

**Step 4: Test the stub**

Run: `cargo run -- inspect ast test/snapshot/run/hello.vole`
Expected: Prints debug output with file path

**Step 5: Commit**

```bash
git add src/commands/mod.rs src/commands/inspect.rs src/bin/vole.rs
git commit -m "feat(cli): wire up inspect command entry point"
```

---

## Task 3: Implement Glob Expansion and File Loop

**Files:**
- Modify: `src/commands/inspect.rs`

**Step 1: Add glob expansion and file processing loop**

Replace `src/commands/inspect.rs`:

```rust
// src/commands/inspect.rs

use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use glob::glob;

use crate::cli::InspectType;

/// Inspect compilation output for the given files
pub fn inspect_files(
    patterns: &[String],
    inspect_type: InspectType,
    no_tests: bool,
    _imports: Option<&str>,
) -> ExitCode {
    // Expand globs and collect unique files
    let mut files: Vec<PathBuf> = Vec::new();
    let mut seen: HashSet<PathBuf> = HashSet::new();

    for pattern in patterns {
        match glob(pattern) {
            Ok(paths) => {
                for entry in paths.flatten() {
                    if let Ok(canonical) = entry.canonicalize() {
                        if seen.insert(canonical.clone()) {
                            files.push(entry);
                        }
                    } else if seen.insert(entry.clone()) {
                        files.push(entry);
                    }
                }
            }
            Err(e) => {
                eprintln!("error: invalid glob pattern '{}': {}", pattern, e);
            }
        }
    }

    if files.is_empty() {
        eprintln!("error: no matching files found");
        return ExitCode::FAILURE;
    }

    let mut had_error = false;

    for (i, path) in files.iter().enumerate() {
        // Print separator between files
        if i > 0 {
            println!();
        }

        // Print file header to stderr
        eprintln!("// {}", path.display());

        // Read source
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: could not read '{}': {}", path.display(), e);
                had_error = true;
                continue;
            }
        };

        let file_path = path.to_string_lossy();

        // TODO: Process based on inspect_type
        match inspect_type {
            InspectType::Ast => {
                println!("TODO: AST for {} (no_tests={})", file_path, no_tests);
            }
            InspectType::Ir => {
                println!("TODO: IR for {} (no_tests={})", file_path, no_tests);
            }
        }
    }

    if had_error {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
```

**Step 2: Test glob expansion**

Run: `cargo run -- inspect ast "test/snapshot/**/*.vole"`
Expected: Lists multiple files with headers

Run: `cargo run -- inspect ast nonexistent.vole`
Expected: "error: no matching files found"

**Step 3: Commit**

```bash
git add src/commands/inspect.rs
git commit -m "feat(inspect): implement glob expansion and file loop"
```

---

## Task 4: Create AstPrinter Module

**Files:**
- Create: `src/frontend/ast_display.rs`
- Modify: `src/frontend/mod.rs`

**Step 1: Create ast_display module with basic structure**

Create `src/frontend/ast_display.rs`:

```rust
// src/frontend/ast_display.rs
//! Pretty-printing for AST nodes with symbol resolution.

use std::fmt::Write;

use crate::frontend::{
    BinaryOp, Block, Decl, Expr, ExprKind, FuncDecl, Interner, LetStmt, Param, PrimitiveType,
    Program, Stmt, StringPart, TestCase, TestsDecl, TypeExpr, UnaryOp,
};

/// Pretty-printer for AST nodes that resolves symbols via an Interner.
pub struct AstPrinter<'a> {
    interner: &'a Interner,
    indent: usize,
    no_tests: bool,
}

impl<'a> AstPrinter<'a> {
    /// Create a new AstPrinter.
    pub fn new(interner: &'a Interner, no_tests: bool) -> Self {
        Self {
            interner,
            indent: 0,
            no_tests,
        }
    }

    /// Print an entire program to a String.
    pub fn print_program(&self, program: &Program) -> String {
        let mut out = String::new();
        self.write_program(&mut out, program);
        out
    }

    fn write_indent(&self, out: &mut String) {
        for _ in 0..self.indent {
            out.push_str("  ");
        }
    }

    fn indented(&self) -> Self {
        Self {
            interner: self.interner,
            indent: self.indent + 1,
            no_tests: self.no_tests,
        }
    }

    fn write_program(&self, out: &mut String, program: &Program) {
        out.push_str("Program\n");
        let inner = self.indented();
        for decl in &program.declarations {
            if self.no_tests && matches!(decl, Decl::Tests(_)) {
                continue;
            }
            inner.write_decl(out, decl);
        }
    }

    fn write_decl(&self, out: &mut String, decl: &Decl) {
        match decl {
            Decl::Function(f) => self.write_func_decl(out, f),
            Decl::Tests(t) => self.write_tests_decl(out, t),
        }
    }

    fn write_func_decl(&self, out: &mut String, func: &FuncDecl) {
        self.write_indent(out);
        let name = self.interner.resolve(func.name);
        writeln!(out, "FunctionDecl \"{}\"", name).unwrap();

        let inner = self.indented();

        // Params
        if !func.params.is_empty() {
            inner.write_indent(out);
            out.push_str("params: [");
            for (i, param) in func.params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                inner.write_param_inline(out, param);
            }
            out.push_str("]\n");
        }

        // Return type
        if let Some(ret) = &func.return_type {
            inner.write_indent(out);
            write!(out, "return_type: ").unwrap();
            inner.write_type_inline(out, ret);
            out.push('\n');
        }

        // Body
        inner.write_indent(out);
        out.push_str("body:\n");
        inner.indented().write_block(out, &func.body);
    }

    fn write_tests_decl(&self, out: &mut String, tests: &TestsDecl) {
        self.write_indent(out);
        if let Some(label) = &tests.label {
            writeln!(out, "Tests \"{}\"", label).unwrap();
        } else {
            out.push_str("Tests\n");
        }

        let inner = self.indented();
        for test in &tests.tests {
            inner.write_test_case(out, test);
        }
    }

    fn write_test_case(&self, out: &mut String, test: &TestCase) {
        self.write_indent(out);
        writeln!(out, "Test \"{}\"", test.name).unwrap();
        self.indented().write_block(out, &test.body);
    }

    fn write_param_inline(&self, out: &mut String, param: &Param) {
        let name = self.interner.resolve(param.name);
        write!(out, "({}: ", name).unwrap();
        self.write_type_inline(out, &param.ty);
        out.push(')');
    }

    fn write_type_inline(&self, out: &mut String, ty: &TypeExpr) {
        match ty {
            TypeExpr::Primitive(p) => {
                let s = match p {
                    PrimitiveType::I32 => "i32",
                    PrimitiveType::I64 => "i64",
                    PrimitiveType::F64 => "f64",
                    PrimitiveType::Bool => "bool",
                    PrimitiveType::String => "string",
                };
                out.push_str(s);
            }
            TypeExpr::Named(sym) => {
                let name = self.interner.resolve(*sym);
                out.push_str(name);
            }
        }
    }

    fn write_block(&self, out: &mut String, block: &Block) {
        for stmt in &block.stmts {
            self.write_stmt(out, stmt);
        }
    }

    fn write_stmt(&self, out: &mut String, stmt: &Stmt) {
        match stmt {
            Stmt::Let(l) => self.write_let(out, l),
            Stmt::Expr(e) => self.write_expr_stmt(out, &e.expr),
            Stmt::Return(r) => {
                self.write_indent(out);
                out.push_str("Return\n");
                if let Some(val) = &r.value {
                    self.indented().write_expr(out, val);
                }
            }
            Stmt::While(w) => {
                self.write_indent(out);
                out.push_str("While\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("condition:\n");
                inner.indented().write_expr(out, &w.condition);
                inner.write_indent(out);
                out.push_str("body:\n");
                inner.indented().write_block(out, &w.body);
            }
            Stmt::If(i) => {
                self.write_indent(out);
                out.push_str("If\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("condition:\n");
                inner.indented().write_expr(out, &i.condition);
                inner.write_indent(out);
                out.push_str("then:\n");
                inner.indented().write_block(out, &i.then_branch);
                if let Some(else_branch) = &i.else_branch {
                    inner.write_indent(out);
                    out.push_str("else:\n");
                    inner.indented().write_block(out, else_branch);
                }
            }
            Stmt::Break(_) => {
                self.write_indent(out);
                out.push_str("Break\n");
            }
        }
    }

    fn write_let(&self, out: &mut String, l: &LetStmt) {
        self.write_indent(out);
        let name = self.interner.resolve(l.name);
        if l.mutable {
            writeln!(out, "LetMut \"{}\"", name).unwrap();
        } else {
            writeln!(out, "Let \"{}\"", name).unwrap();
        }
        let inner = self.indented();
        if let Some(ty) = &l.ty {
            inner.write_indent(out);
            write!(out, "type: ").unwrap();
            inner.write_type_inline(out, ty);
            out.push('\n');
        }
        inner.write_indent(out);
        out.push_str("init:\n");
        inner.indented().write_expr(out, &l.init);
    }

    fn write_expr_stmt(&self, out: &mut String, expr: &Expr) {
        self.write_expr(out, expr);
    }

    fn write_expr(&self, out: &mut String, expr: &Expr) {
        match &expr.kind {
            ExprKind::IntLiteral(n) => {
                self.write_indent(out);
                writeln!(out, "Int {}", n).unwrap();
            }
            ExprKind::FloatLiteral(n) => {
                self.write_indent(out);
                writeln!(out, "Float {}", n).unwrap();
            }
            ExprKind::BoolLiteral(b) => {
                self.write_indent(out);
                writeln!(out, "Bool {}", b).unwrap();
            }
            ExprKind::StringLiteral(s) => {
                self.write_indent(out);
                writeln!(out, "String {:?}", s).unwrap();
            }
            ExprKind::InterpolatedString(parts) => {
                self.write_indent(out);
                out.push_str("InterpolatedString\n");
                let inner = self.indented();
                for part in parts {
                    match part {
                        StringPart::Literal(s) => {
                            inner.write_indent(out);
                            writeln!(out, "Literal {:?}", s).unwrap();
                        }
                        StringPart::Expr(e) => {
                            inner.write_indent(out);
                            out.push_str("Expr:\n");
                            inner.indented().write_expr(out, e);
                        }
                    }
                }
            }
            ExprKind::Identifier(sym) => {
                self.write_indent(out);
                let name = self.interner.resolve(*sym);
                writeln!(out, "Ident \"{}\"", name).unwrap();
            }
            ExprKind::Binary(b) => {
                self.write_indent(out);
                let op = match b.op {
                    BinaryOp::Add => "Add",
                    BinaryOp::Sub => "Sub",
                    BinaryOp::Mul => "Mul",
                    BinaryOp::Div => "Div",
                    BinaryOp::Mod => "Mod",
                    BinaryOp::Eq => "Eq",
                    BinaryOp::Ne => "Ne",
                    BinaryOp::Lt => "Lt",
                    BinaryOp::Gt => "Gt",
                    BinaryOp::Le => "Le",
                    BinaryOp::Ge => "Ge",
                    BinaryOp::And => "And",
                    BinaryOp::Or => "Or",
                };
                writeln!(out, "BinaryOp {}", op).unwrap();
                let inner = self.indented();
                inner.write_expr(out, &b.left);
                inner.write_expr(out, &b.right);
            }
            ExprKind::Unary(u) => {
                self.write_indent(out);
                let op = match u.op {
                    UnaryOp::Neg => "Neg",
                    UnaryOp::Not => "Not",
                };
                writeln!(out, "UnaryOp {}", op).unwrap();
                self.indented().write_expr(out, &u.operand);
            }
            ExprKind::Call(c) => {
                self.write_indent(out);
                out.push_str("Call\n");
                let inner = self.indented();
                inner.write_indent(out);
                out.push_str("callee:\n");
                inner.indented().write_expr(out, &c.callee);
                if !c.args.is_empty() {
                    inner.write_indent(out);
                    out.push_str("args:\n");
                    let args_inner = inner.indented();
                    for arg in &c.args {
                        args_inner.write_expr(out, arg);
                    }
                }
            }
            ExprKind::Assign(a) => {
                self.write_indent(out);
                let name = self.interner.resolve(a.target);
                writeln!(out, "Assign \"{}\"", name).unwrap();
                self.indented().write_expr(out, &a.value);
            }
            ExprKind::Grouping(inner) => {
                // Skip grouping node, just print inner
                self.write_expr(out, inner);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Parser;

    #[test]
    fn print_simple_function() {
        let source = r#"
func add(a: i64, b: i64) -> i64 {
    return a + b
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();

        let printer = AstPrinter::new(&interner, false);
        let output = printer.print_program(&program);

        assert!(output.contains("FunctionDecl \"add\""));
        assert!(output.contains("params: [(a: i64), (b: i64)]"));
        assert!(output.contains("return_type: i64"));
        assert!(output.contains("BinaryOp Add"));
    }

    #[test]
    fn print_filters_tests_when_no_tests() {
        let source = r#"
func main() { }

tests {
    test "example" {
        assert(true)
    }
}
"#;
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();

        let with_tests = AstPrinter::new(&interner, false).print_program(&program);
        let without_tests = AstPrinter::new(&interner, true).print_program(&program);

        assert!(with_tests.contains("Tests"));
        assert!(!without_tests.contains("Tests"));
    }
}
```

**Step 2: Add to frontend mod.rs**

Add to `src/frontend/mod.rs`:

```rust
pub mod ast_display;

pub use ast_display::AstPrinter;
```

**Step 3: Run tests**

Run: `cargo test ast_display -v`
Expected: 2 tests pass

**Step 4: Commit**

```bash
git add src/frontend/ast_display.rs src/frontend/mod.rs
git commit -m "feat(frontend): add AstPrinter for pretty-printing AST"
```

---

## Task 5: Implement AST Inspection

**Files:**
- Modify: `src/commands/inspect.rs`

**Step 1: Add AST inspection**

Update the `InspectType::Ast` arm in `inspect_files`:

```rust
            InspectType::Ast => {
                // Parse
                let mut parser = Parser::with_file(&source, &file_path);
                let program = match parser.parse_program() {
                    Ok(p) => p,
                    Err(e) => {
                        let report = miette::Report::new(e.error.clone())
                            .with_source_code(NamedSource::new(
                                file_path.to_string(),
                                source.clone(),
                            ));
                        render_to_stderr(report.as_ref());
                        had_error = true;
                        continue;
                    }
                };

                let interner = parser.into_interner();
                let printer = AstPrinter::new(&interner, no_tests);
                print!("{}", printer.print_program(&program));
            }
```

Add imports at top:

```rust
use miette::NamedSource;

use crate::errors::render_to_stderr;
use crate::frontend::{AstPrinter, Parser};
```

**Step 2: Test AST output**

Run: `cargo run -- inspect ast test/snapshot/run/hello.vole`
Expected: Pretty-printed AST with "FunctionDecl \"main\""

**Step 3: Commit**

```bash
git add src/commands/inspect.rs
git commit -m "feat(inspect): implement AST inspection mode"
```

---

## Task 6: Add compile_to_ir Method

**Files:**
- Modify: `src/codegen/compiler.rs`

**Step 1: Add compile_to_ir method**

Add this method to `impl<'a> Compiler<'a>`:

```rust
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

        // Reset for second pass
        test_count = 0;

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
                        let func_name = format!("__test_{}", test_count);
                        self.build_test_ir(test)?;
                        writeln!(writer, "// test \"{}\"", test.name).map_err(|e| e.to_string())?;
                        writeln!(writer, "{}", self.jit.ctx.func).map_err(|e| e.to_string())?;
                        self.jit.clear();
                        test_count += 1;
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Build IR for a function without defining it
    fn build_function_ir(&mut self, func: &FuncDecl) -> Result<(), String> {
        let sig = self.create_function_signature(func);
        self.jit.ctx.func.signature = sig;

        let param_types: Vec<types::Type> = func
            .params
            .iter()
            .map(|p| type_to_cranelift(&resolve_type_expr(&p.ty), self.pointer_type))
            .collect();
        let param_names: Vec<Symbol> = func.params.iter().map(|p| p.name).collect();
        let source_file_ptr = self.source_file_ptr();

        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            let mut variables = HashMap::new();
            let params = builder.block_params(entry_block).to_vec();
            for ((name, ty), val) in param_names
                .iter()
                .zip(param_types.iter())
                .zip(params.iter())
            {
                let var = builder.declare_var(*ty);
                builder.def_var(var, *val);
                variables.insert(*name, var);
            }

            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &self.jit.func_ids,
                source_file_ptr,
            };
            let terminated =
                compile_block(&mut builder, &func.body, &mut variables, &mut cf_ctx, &mut ctx)?;

            if !terminated {
                builder.ins().return_(&[]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        Ok(())
    }

    /// Build IR for a test case without defining it
    fn build_test_ir(&mut self, test: &TestCase) -> Result<(), String> {
        let sig = self.jit.create_signature(&[], Some(types::I64));
        self.jit.ctx.func.signature = sig;

        let source_file_ptr = self.source_file_ptr();

        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            let entry_block = builder.create_block();
            builder.switch_to_block(entry_block);

            let mut variables = HashMap::new();

            let mut cf_ctx = ControlFlowCtx::new();
            let mut ctx = CompileCtx {
                interner: self.interner,
                pointer_type: self.pointer_type,
                module: &mut self.jit.module,
                func_ids: &self.jit.func_ids,
                source_file_ptr,
            };
            let terminated =
                compile_block(&mut builder, &test.body, &mut variables, &mut cf_ctx, &mut ctx)?;

            if !terminated {
                let zero = builder.ins().iconst(types::I64, 0);
                builder.ins().return_(&[zero]);
            }

            builder.seal_all_blocks();
            builder.finalize();
        }

        Ok(())
    }
```

**Step 2: Verify it compiles**

Run: `cargo build 2>&1 | head -20`
Expected: Compiles

**Step 3: Commit**

```bash
git add src/codegen/compiler.rs
git commit -m "feat(codegen): add compile_to_ir for IR inspection"
```

---

## Task 7: Implement IR Inspection

**Files:**
- Modify: `src/commands/inspect.rs`

**Step 1: Add IR inspection**

Add imports:

```rust
use crate::codegen::{Compiler, JitContext};
use crate::sema::Analyzer;
```

Update the `InspectType::Ir` arm:

```rust
            InspectType::Ir => {
                // Parse
                let mut parser = Parser::with_file(&source, &file_path);
                let program = match parser.parse_program() {
                    Ok(p) => p,
                    Err(e) => {
                        let report = miette::Report::new(e.error.clone())
                            .with_source_code(NamedSource::new(
                                file_path.to_string(),
                                source.clone(),
                            ));
                        render_to_stderr(report.as_ref());
                        had_error = true;
                        continue;
                    }
                };

                let interner = parser.into_interner();

                // Type check
                let mut analyzer = Analyzer::new(&file_path, &source);
                if let Err(errors) = analyzer.analyze(&program, &interner) {
                    for err in &errors {
                        let report = miette::Report::new(err.error.clone())
                            .with_source_code(NamedSource::new(
                                file_path.to_string(),
                                source.clone(),
                            ));
                        render_to_stderr(report.as_ref());
                    }
                    had_error = true;
                    continue;
                }

                // Generate IR
                let mut jit = JitContext::new();
                let mut compiler = Compiler::new(&mut jit, &interner);
                let include_tests = !no_tests;

                if let Err(e) = compiler.compile_to_ir(&program, &mut std::io::stdout(), include_tests) {
                    eprintln!("error: {}", e);
                    had_error = true;
                }
            }
```

**Step 2: Test IR output**

Run: `cargo run -- inspect ir test/snapshot/run/hello.vole`
Expected: CLIF IR output with `function u0:0()` etc.

**Step 3: Commit**

```bash
git add src/commands/inspect.rs
git commit -m "feat(inspect): implement IR inspection mode"
```

---

## Task 8: Add Integration Tests

**Files:**
- Create: `test/snapshot/inspect/` directory
- Create test fixtures and snapshots

**Step 1: Create test fixture**

Create `test/snapshot/inspect/simple.vole`:

```vole
func add(a: i64, b: i64) -> i64 {
    return a + b
}

func main() {
    println(add(1, 2))
}
```

**Step 2: Create AST snapshot**

Run: `cargo run -- inspect ast test/snapshot/inspect/simple.vole > test/snapshot/inspect/simple_ast.snap.stdout`

Create `test/snapshot/inspect/simple_ast.snap`:
```
[stdout]
<contents of simple_ast.snap.stdout>

[stderr]
// test/snapshot/inspect/simple.vole
```

**Step 3: Create IR snapshot**

Run: `cargo run -- inspect ir test/snapshot/inspect/simple.vole > test/snapshot/inspect/simple_ir.snap.stdout`

(IR snapshots may be fragile due to block/value numbering - consider whether to include)

**Step 4: Commit**

```bash
git add test/snapshot/inspect/
git commit -m "test(inspect): add integration test fixtures"
```

---

## Task 9: Final Verification

**Step 1: Run all checks**

Run: `just ci`
Expected: All tests pass, clippy clean, fmt clean

**Step 2: Manual testing**

```bash
# Test AST with glob
cargo run -- inspect ast "test/unit/**/*.vole" | head -50

# Test IR
cargo run -- inspect ir test/snapshot/run/hello.vole

# Test --no-tests
cargo run -- inspect ast test/unit/test_basic.vole --no-tests

# Test error handling
cargo run -- inspect ast nonexistent.vole
```

**Step 3: Commit any fixes**

```bash
git add -A
git commit -m "fix: address CI feedback"
```

---

## Summary

| Task | Description | Files |
|------|-------------|-------|
| 1 | CLI arguments | `src/cli/args.rs` |
| 2 | Entry point wiring | `src/bin/vole.rs`, `src/commands/mod.rs`, `src/commands/inspect.rs` |
| 3 | Glob expansion | `src/commands/inspect.rs` |
| 4 | AstPrinter | `src/frontend/ast_display.rs`, `src/frontend/mod.rs` |
| 5 | AST inspection | `src/commands/inspect.rs` |
| 6 | compile_to_ir | `src/codegen/compiler.rs` |
| 7 | IR inspection | `src/commands/inspect.rs` |
| 8 | Integration tests | `test/snapshot/inspect/` |
| 9 | Final verification | - |
