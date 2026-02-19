// Block fusion pass: merge single-predecessor blocks.
//
// When block A ends with `jump blockB(args...)` and blockB has exactly one
// predecessor (block A), the two blocks can be merged. This eliminates the
// jump overhead and creates larger basic blocks that are better for
// register allocation and instruction scheduling.
//
// Runs after trampoline elimination and unreachable block removal since
// those phases change predecessor counts.

use cranelift_codegen::ir::{Block, Function, Opcode, Value};
use rustc_hash::{FxHashMap, FxHashSet};

/// Build a map from each block to the set of unique predecessor blocks.
///
/// A predecessor of block B is any block whose terminator has a branch
/// destination targeting B. Each predecessor block is counted once even
/// if it branches to B multiple times (e.g. `brif v, B, B`).
pub(super) fn build_predecessor_map(func: &Function) -> FxHashMap<Block, FxHashSet<Block>> {
    let mut preds: FxHashMap<Block, FxHashSet<Block>> = FxHashMap::default();

    for block in func.layout.blocks() {
        // Ensure every block has an entry (even if no predecessors)
        preds.entry(block).or_default();

        let Some(inst) = func.layout.last_inst(block) else {
            continue;
        };
        for dest in func.dfg.insts[inst]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables)
        {
            let target = dest.block(&func.dfg.value_lists);
            preds.entry(target).or_default().insert(block);
        }
    }

    preds
}

/// Fuse single-predecessor blocks into their predecessor, iterating to fixpoint.
///
/// When block A ends with `jump blockB(args...)` and blockB has exactly one
/// predecessor (block A), and blockB is not the entry block, the two blocks
/// can be merged: alias blockB's params to the jump args, remove the jump,
/// move blockB's instructions into A, and remove blockB from the layout.
pub(super) fn fuse_single_predecessor_blocks(func: &mut Function) {
    loop {
        let preds = build_predecessor_map(func);
        let entry = match func.layout.entry_block() {
            Some(b) => b,
            None => return,
        };

        let fused = fuse_one_pass(func, &preds, entry);
        if fused == 0 {
            break;
        }
    }
}

/// Run one pass of block fusion, returning the number of fused pairs.
fn fuse_one_pass(
    func: &mut Function,
    preds: &FxHashMap<Block, FxHashSet<Block>>,
    entry: Block,
) -> usize {
    // Collect fusible pairs: (block_a, block_b)
    let pairs: Vec<(Block, Block)> = func
        .layout
        .blocks()
        .filter_map(|block_a| {
            let inst = func.layout.last_inst(block_a)?;
            if func.dfg.insts[inst].opcode() != Opcode::Jump {
                return None;
            }
            let dests = func.dfg.insts[inst]
                .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
            if dests.len() != 1 {
                return None;
            }
            let block_b = dests[0].block(&func.dfg.value_lists);

            // Don't fuse if B is the entry block
            if block_b == entry {
                return None;
            }
            // Don't fuse self-loops
            if block_a == block_b {
                return None;
            }
            // B must have exactly one unique predecessor
            let b_preds = preds.get(&block_b)?;
            if b_preds.len() != 1 {
                return None;
            }
            Some((block_a, block_b))
        })
        .collect();

    // Track which blocks have been consumed as targets in this pass to
    // avoid double-fusing (e.g. if A->B and B->C, don't also fuse B->C
    // in the same pass — the next iteration will catch it)
    let mut consumed: FxHashSet<Block> = FxHashSet::default();
    let mut count = 0;

    for (block_a, block_b) in pairs {
        if consumed.contains(&block_a) || consumed.contains(&block_b) {
            continue;
        }
        fuse_pair(func, block_a, block_b);
        consumed.insert(block_b);
        count += 1;
    }

    count
}

/// Fuse block_b into block_a: alias params, move instructions, remove block_b.
fn fuse_pair(func: &mut Function, block_a: Block, block_b: Block) {
    // Read and remove the jump terminator from block_a
    let jump_inst = func.layout.last_inst(block_a).unwrap();
    let jump_args: Vec<Value> = {
        let dests = func.dfg.insts[jump_inst]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
        dests[0]
            .args(&func.dfg.value_lists)
            .filter_map(|arg| arg.as_value())
            .collect()
    };
    func.layout.remove_inst(jump_inst);

    // Alias block_b's params to the jump args
    let b_params: Vec<Value> = func.dfg.block_params(block_b).to_vec();
    func.dfg.detach_block_params(block_b);
    for (&param, &arg) in b_params.iter().zip(jump_args.iter()) {
        func.dfg.change_to_alias(param, arg);
    }

    // Move all instructions from block_b to block_a
    let insts: Vec<cranelift_codegen::ir::Inst> = func.layout.block_insts(block_b).collect();
    for inst in insts {
        func.layout.remove_inst(inst);
        func.layout.append_inst(inst, block_a);
    }

    // Remove the now-empty block_b from the layout
    func.layout.remove_block(block_b);
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelift::prelude::*;

    fn create_test_function() -> Function {
        let mut func = Function::new();
        func.signature.returns.push(AbiParam::new(types::I64));
        func
    }

    /// Basic fusion: block0 has instructions + jump block1, block1 has instructions + return.
    /// After fusion, block0 should contain all instructions and block1 should be gone.
    ///
    ///   block0:
    ///       v0 = iconst 42
    ///       jump block1
    ///   block1:
    ///       return v0
    ///
    /// After: block0 contains both iconst and return.
    #[test]
    fn test_fusion_basic() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let block0 = builder.create_block();
        let block1 = builder.create_block();

        builder.switch_to_block(block0);
        builder.seal_block(block0);
        let v0 = builder.ins().iconst(types::I64, 42);
        builder.ins().jump(block1, &[]);

        builder.switch_to_block(block1);
        builder.seal_block(block1);
        builder.ins().return_(&[v0]);

        builder.finalize();

        // block1 should have exactly 1 predecessor (block0)
        let preds = build_predecessor_map(&func);
        assert_eq!(preds[&block1].len(), 1);

        fuse_single_predecessor_blocks(&mut func);

        // block1 should be gone — only block0 remains
        let blocks: Vec<Block> = func.layout.blocks().collect();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0], block0);

        // block0's terminator should now be a return
        let last = func.layout.last_inst(block0).unwrap();
        assert_eq!(func.dfg.insts[last].opcode(), Opcode::Return);
    }

    /// Fusion with block params: block0 jumps to block1 passing an arg,
    /// block1 uses the param. After fusion, the param should be aliased.
    ///
    ///   block0:
    ///       v0 = iconst 42
    ///       jump block1(v0)
    ///   block1(v1: i64):
    ///       return v1
    ///
    /// After: block0 contains `return v0` (v1 aliased to v0).
    #[test]
    fn test_fusion_with_block_params() {
        use cranelift::codegen::ir::BlockArg;

        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let block0 = builder.create_block();
        let block1 = builder.create_block();

        builder.switch_to_block(block0);
        builder.seal_block(block0);
        let v0 = builder.ins().iconst(types::I64, 42);
        builder.ins().jump(block1, &[BlockArg::from(v0)]);

        builder.switch_to_block(block1);
        builder.append_block_param(block1, types::I64);
        builder.seal_block(block1);
        let v1 = builder.block_params(block1)[0];
        builder.ins().return_(&[v1]);

        builder.finalize();

        fuse_single_predecessor_blocks(&mut func);

        // Only block0 should remain
        let blocks: Vec<Block> = func.layout.blocks().collect();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0], block0);

        // block0's terminator should be a return
        let last = func.layout.last_inst(block0).unwrap();
        assert_eq!(func.dfg.insts[last].opcode(), Opcode::Return);

        // The return value should resolve to v0 (v1 aliased to v0)
        let ret_args = func.dfg.inst_args(last);
        assert_eq!(func.dfg.resolve_aliases(ret_args[0]), v0);
    }

    /// No fusion when a block has multiple predecessors.
    ///
    ///   entry:
    ///       v0 = iconst 1
    ///       brif v0, block_a, [], block_b, []
    ///   block_a:
    ///       jump merge
    ///   block_b:
    ///       jump merge
    ///   merge:
    ///       v1 = iconst 99
    ///       return v1
    ///
    /// merge has TWO predecessors (block_a and block_b) — no fusion for merge.
    #[test]
    fn test_no_fusion_multiple_predecessors() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        let block_a = builder.create_block();
        let block_b = builder.create_block();
        let merge = builder.create_block();

        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let cond = builder.ins().iconst(types::I64, 1);
        builder.ins().brif(cond, block_a, &[], block_b, &[]);

        builder.switch_to_block(block_a);
        builder.seal_block(block_a);
        builder.ins().jump(merge, &[]);

        builder.switch_to_block(block_b);
        builder.seal_block(block_b);
        builder.ins().jump(merge, &[]);

        builder.switch_to_block(merge);
        builder.seal_block(merge);
        let v1 = builder.ins().iconst(types::I64, 99);
        builder.ins().return_(&[v1]);

        builder.finalize();

        let preds = build_predecessor_map(&func);
        assert_eq!(preds[&merge].len(), 2);

        fuse_single_predecessor_blocks(&mut func);

        // merge should still exist as a separate block (2 predecessors).
        // block_a and block_b each have 1 predecessor (entry), but entry
        // ends with brif (not jump), so they can't be fused into entry.
        let blocks: Vec<Block> = func.layout.blocks().collect();
        assert!(blocks.contains(&merge), "merge block should still exist");
        assert_eq!(blocks.len(), 4, "all 4 blocks should remain");
    }

    /// Chain fusion: A -> B -> C should merge into A containing all instructions.
    ///
    ///   block_a:
    ///       v0 = iconst 1
    ///       jump block_b
    ///   block_b:
    ///       v1 = iconst 2
    ///       jump block_c
    ///   block_c:
    ///       v2 = iconst 3
    ///       return v2
    ///
    /// After fusion (two iterations): block_a contains all three iconsts + return.
    #[test]
    fn test_fusion_chain() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let block_a = builder.create_block();
        let block_b = builder.create_block();
        let block_c = builder.create_block();

        builder.switch_to_block(block_a);
        builder.seal_block(block_a);
        let _v0 = builder.ins().iconst(types::I64, 1);
        builder.ins().jump(block_b, &[]);

        builder.switch_to_block(block_b);
        builder.seal_block(block_b);
        let _v1 = builder.ins().iconst(types::I64, 2);
        builder.ins().jump(block_c, &[]);

        builder.switch_to_block(block_c);
        builder.seal_block(block_c);
        let v2 = builder.ins().iconst(types::I64, 3);
        builder.ins().return_(&[v2]);

        builder.finalize();

        fuse_single_predecessor_blocks(&mut func);

        // All blocks should be fused into block_a
        let blocks: Vec<Block> = func.layout.blocks().collect();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0], block_a);

        // block_a should have 4 instructions: 3 iconsts + 1 return
        let inst_count = func.layout.block_insts(block_a).count();
        assert_eq!(inst_count, 4);

        // Last instruction should be a return
        let last = func.layout.last_inst(block_a).unwrap();
        assert_eq!(func.dfg.insts[last].opcode(), Opcode::Return);
    }
}
