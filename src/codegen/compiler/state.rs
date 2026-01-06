use cranelift::prelude::Block;

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
