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
