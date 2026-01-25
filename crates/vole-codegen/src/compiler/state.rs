use cranelift::prelude::Block;
use cranelift_module::FuncId;

use crate::FunctionKey;

/// Metadata about a compiled test
#[derive(Debug, Clone)]
pub struct TestInfo {
    pub name: String, // "basic math"
    pub func_key: FunctionKey,
    pub func_id: FuncId,
    pub file: String, // "test/unit/test_basic.vole"
    pub line: u32,
}

/// Context for control flow during compilation
#[derive(Default)]
pub struct ControlFlowCtx {
    /// Stack of loop exit blocks for break statements
    loop_exits: Vec<Block>,
    /// Stack of loop continue blocks for continue statements
    loop_continues: Vec<Block>,
}

impl ControlFlowCtx {
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
