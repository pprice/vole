use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};

use super::common::{DefaultReturn, finalize_function_body};
use super::{Compiler, TestInfo};

use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CodegenCtx;
use vole_vir::func::VirTest;

impl Compiler<'_> {
    /// Compile all tests from VirProgram's flat test list.
    pub(super) fn compile_all_tests(&mut self, vir_tests: &[VirTest]) -> CodegenResult<()> {
        for (i, vir_test) in vir_tests.iter().enumerate() {
            self.compile_single_test(vir_test, i)?;
        }
        Ok(())
    }

    /// Compile a single test case into a JIT function.
    fn compile_single_test(&mut self, vir_test: &VirTest, test_index: usize) -> CodegenResult<()> {
        let func_key = self.test_function_key(test_index);
        let func_name = self.test_display_name(func_key);
        let func_id = self
            .func_registry
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("test function", &func_name))?;

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

            // Create split contexts
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            // Compile test body from VIR.
            let mut cg = Cg::new(&mut builder, &mut codegen_ctx, &env)
                .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline);

            // Push function-level RC scope for test body
            cg.push_rc_scope();

            // Compile test body via VIR.
            // Note: For FuncBody::Expr, terminated=true but the block isn't actually
            // terminated (no return instruction). For FuncBody::Block, terminated=true
            // only if there's an explicit return/break. So we check both.
            let (block_terminated, expr_value) = cg.compile_vir_body(&vir_test.body)?;

            // Tests always return 0. Add return if block didn't explicitly terminate
            // or if it's an expression body.
            let terminated = block_terminated && expr_value.is_none();

            // Emit RC cleanup for test-level scope
            if !terminated {
                cg.pop_rc_scope_with_cleanup(None)?;
            } else {
                cg.rc_scopes.pop_scope();
            }

            finalize_function_body(builder, None, terminated, DefaultReturn::Zero);
        }

        // Define the function
        self.finalize_function(func_id)?;

        // Record test metadata
        let line = vir_test.span.line;
        self.tests.push(TestInfo {
            name: vir_test.name.clone(),
            func_key,
            func_id,
            file: self.source_file_str(),
            line,
        });

        Ok(())
    }
}
