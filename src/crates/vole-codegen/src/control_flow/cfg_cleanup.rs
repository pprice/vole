// src/codegen/cfg_cleanup.rs
//
// CFG cleanup pass to eliminate trampoline blocks.
//
// Handles three kinds of trampolines:
//
// 1. Simple trampolines: no params, jump passes no args (e.g. `block5: jump block6`)
//    - Chains are resolved (A->B->C becomes A->C)
//
// 2. Forward-arg trampolines: no params, jump passes args (e.g. `block5: jump block6(v3)`)
//    - Common in optional/nil-check paths where brif branches to a block that
//      forwards a default value to a merge block
//
// 3. Pass-through trampolines: has params, jump forwards them unchanged
//    (e.g. `block38(v1, v2, v3): jump block18(v1, v2, v3)`)
//    - Common in when/match merge chains where control flow funnels through
//      intermediate merge blocks. Callers already provide the right args,
//      so we just redirect them to the final target.
//    - Chains are resolved (A->B->C becomes A->C)
//
// All are eliminated by rewriting references to jump directly to the final
// target. Dead blocks are cleaned up by Cranelift's unreachable code elimination.

use cranelift_codegen::ir::{Block, Function, Opcode, Value};
use rustc_hash::{FxHashMap, FxHashSet};

use super::block_fusion::fuse_single_predecessor_blocks;

/// Clean up trampoline blocks in the function.
///
/// Phase 1: Rewrites branch targets to bypass simple trampolines (no params,
/// jump with no args), resolving chains.
///
/// Phase 2: Rewrites branch targets to bypass forward-arg trampolines (no
/// params, jump that passes args to its target).
///
/// Phase 3: Rewrites branch targets to bypass pass-through trampolines (has
/// params, jump forwards them unchanged to another block), resolving chains.
///
/// Phase 4: Remove unreachable blocks from the layout.
///
/// Phase 5: Fuse single-predecessor blocks — when block A ends with
/// `jump blockB` and blockB has exactly one predecessor, merge B into A.
pub(crate) fn cleanup_cfg(func: &mut Function) {
    // Phase 1: Eliminate simple trampolines (no params, jump with no args)
    let trampolines = find_trampolines(func);
    if !trampolines.is_empty() {
        let resolved = resolve_trampoline_chains(&trampolines);
        rewrite_terminators(func, &resolved);
    }

    // Phase 2: Eliminate forward-arg trampolines (no params, jump WITH args)
    let fwd_trampolines = find_forward_arg_trampolines(func);
    if !fwd_trampolines.is_empty() {
        rewrite_forward_arg_terminators(func, &fwd_trampolines);
    }

    // Phase 3: Eliminate pass-through trampolines (has params, jump forwards them)
    let passthrough = find_passthrough_trampolines(func);
    if !passthrough.is_empty() {
        let resolved = resolve_trampoline_chains(&passthrough);
        rewrite_terminators(func, &resolved);
    }

    // Phase 4: Remove unreachable blocks from the layout
    remove_unreachable_blocks(func);

    // Phase 5: Fuse single-predecessor blocks (runs after trampoline elimination
    // and dead block removal since those change predecessor counts)
    fuse_single_predecessor_blocks(func);
}

/// Find all trampoline blocks in the function.
///
/// A trampoline block is one that:
/// - Has no block parameters
/// - Contains exactly one instruction
/// - That instruction is an unconditional jump
fn find_trampolines(func: &Function) -> FxHashMap<Block, Block> {
    let mut trampolines = FxHashMap::default();

    for block in func.layout.blocks() {
        // Skip blocks with parameters - they're not simple trampolines
        if !func.dfg.block_params(block).is_empty() {
            continue;
        }

        // Check if block has exactly one instruction
        let first_inst = func.layout.first_inst(block);
        let last_inst = func.layout.last_inst(block);

        if first_inst != last_inst {
            // More than one instruction
            continue;
        }

        let Some(inst) = first_inst else {
            // Empty block (shouldn't happen in valid IR)
            continue;
        };

        // Check if it's a simple unconditional jump
        let opcode = func.dfg.insts[inst].opcode();
        if opcode != Opcode::Jump {
            continue;
        }

        // Get the jump target
        let destinations = func.dfg.insts[inst]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
        if destinations.len() != 1 {
            continue;
        }

        let target = destinations[0].block(&func.dfg.value_lists);

        // Check that the jump has no arguments (no phi values to pass)
        if destinations[0].len(&func.dfg.value_lists) > 0 {
            continue;
        }

        trampolines.insert(block, target);
    }

    trampolines
}

/// Find forward-arg trampoline blocks in the function.
///
/// A forward-arg trampoline is a block that:
/// - Has no block parameters
/// - Contains exactly one instruction (an unconditional jump)
/// - The jump passes arguments to its target
///
/// These arise from optional/nil check paths where a `brif` branches to a block
/// that just forwards a default value to a merge block.
fn find_forward_arg_trampolines(func: &Function) -> FxHashMap<Block, (Block, Vec<Value>)> {
    let mut trampolines = FxHashMap::default();

    for block in func.layout.blocks() {
        if !func.dfg.block_params(block).is_empty() {
            continue;
        }

        let first_inst = func.layout.first_inst(block);
        let last_inst = func.layout.last_inst(block);
        if first_inst != last_inst {
            continue;
        }

        let Some(inst) = first_inst else {
            continue;
        };

        if func.dfg.insts[inst].opcode() != Opcode::Jump {
            continue;
        }

        let destinations = func.dfg.insts[inst]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
        if destinations.len() != 1 {
            continue;
        }

        // Only interested in jumps that DO pass arguments
        if destinations[0].len(&func.dfg.value_lists) == 0 {
            continue;
        }

        let target = destinations[0].block(&func.dfg.value_lists);
        let args: Vec<Value> = destinations[0]
            .args(&func.dfg.value_lists)
            .filter_map(|arg| arg.as_value())
            .collect();

        trampolines.insert(block, (target, args));
    }

    trampolines
}

/// Find pass-through trampoline blocks in the function.
///
/// A pass-through trampoline is a block that:
/// - Has one or more block parameters
/// - Contains exactly one instruction (an unconditional jump)
/// - The jump passes exactly those block parameters as arguments, in the same order
///
/// These arise from when/match merge chains where control flow funnels through
/// intermediate merge blocks. Since callers already supply the right argument
/// values, we can redirect them to the jump target directly.
fn find_passthrough_trampolines(func: &Function) -> FxHashMap<Block, Block> {
    let mut trampolines = FxHashMap::default();

    for block in func.layout.blocks() {
        let params = func.dfg.block_params(block);
        if params.is_empty() {
            continue;
        }

        // Check if block has exactly one instruction
        let first_inst = func.layout.first_inst(block);
        let last_inst = func.layout.last_inst(block);
        if first_inst != last_inst {
            continue;
        }

        let Some(inst) = first_inst else {
            continue;
        };

        if func.dfg.insts[inst].opcode() != Opcode::Jump {
            continue;
        }

        let destinations = func.dfg.insts[inst]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
        if destinations.len() != 1 {
            continue;
        }

        // Check that the jump args are exactly the block params in the same order
        let args: Vec<Value> = destinations[0]
            .args(&func.dfg.value_lists)
            .filter_map(|arg| arg.as_value())
            .collect();

        if args.len() != params.len() {
            continue;
        }

        if args.iter().zip(params).all(|(&arg, &param)| arg == param) {
            let target = destinations[0].block(&func.dfg.value_lists);
            trampolines.insert(block, target);
        }
    }

    trampolines
}

/// Resolve trampoline chains to their final targets.
///
/// If block A jumps to B and B jumps to C, we want A to jump directly to C.
/// Cycles are detected and those trampolines are not included in the result.
fn resolve_trampoline_chains(trampolines: &FxHashMap<Block, Block>) -> FxHashMap<Block, Block> {
    let mut resolved = FxHashMap::default();

    for (&trampoline, &initial_target) in trampolines {
        let mut target = initial_target;
        let mut visited = vec![trampoline];
        let mut is_cycle = false;

        // Follow the chain until we hit a non-trampoline or a cycle
        while let Some(&next) = trampolines.get(&target) {
            if visited.contains(&target) {
                // Cycle detected - don't rewrite this trampoline
                is_cycle = true;
                break;
            }
            visited.push(target);
            target = next;
        }

        // Only add to resolved if we found a valid final target (not a cycle)
        if !is_cycle {
            resolved.insert(trampoline, target);
        }
    }

    resolved
}

/// Rewrite all terminator instructions to bypass trampolines.
fn rewrite_terminators(func: &mut Function, trampolines: &FxHashMap<Block, Block>) {
    // Collect all instructions with their rewrite targets first
    let rewrites: Vec<(cranelift_codegen::ir::Inst, Vec<(Block, Block)>)> = func
        .layout
        .blocks()
        .filter_map(|block| {
            let inst = func.layout.last_inst(block)?;
            let destinations = func.dfg.insts[inst]
                .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
            let block_rewrites: Vec<_> = destinations
                .iter()
                .filter_map(|dest| {
                    let current = dest.block(&func.dfg.value_lists);
                    trampolines.get(&current).map(|&new| (current, new))
                })
                .collect();
            if block_rewrites.is_empty() {
                None
            } else {
                Some((inst, block_rewrites))
            }
        })
        .collect();

    // Apply rewrites using the DFG's fields directly
    for (inst, block_rewrites) in rewrites {
        let dfg = &mut func.dfg;
        for (old_block, new_block) in block_rewrites {
            for dest in dfg.insts[inst]
                .branch_destination_mut(&mut dfg.jump_tables, &mut dfg.exception_tables)
            {
                if dest.block(&dfg.value_lists) == old_block {
                    dest.set_block(new_block, &mut dfg.value_lists);
                }
            }
        }
    }
}

/// Rewrite all terminator instructions to bypass forward-arg trampolines.
///
/// For each branch destination that targets a forward-arg trampoline, rewrite
/// it to point to the trampoline's target block and carry the same arguments.
fn rewrite_forward_arg_terminators(
    func: &mut Function,
    trampolines: &FxHashMap<Block, (Block, Vec<Value>)>,
) {
    // Collect rewrites: (inst, dest_index, new_block, args_to_set)
    let rewrites: Vec<(cranelift_codegen::ir::Inst, usize, Block, Vec<Value>)> = func
        .layout
        .blocks()
        .filter_map(|block| {
            let inst = func.layout.last_inst(block)?;
            let destinations = func.dfg.insts[inst]
                .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
            let mut inst_rewrites = Vec::new();
            for (i, dest) in destinations.iter().enumerate() {
                let current = dest.block(&func.dfg.value_lists);
                if let Some((target, args)) = trampolines.get(&current) {
                    inst_rewrites.push((inst, i, *target, args.clone()));
                }
            }
            if inst_rewrites.is_empty() {
                None
            } else {
                Some(inst_rewrites)
            }
        })
        .flatten()
        .collect();

    // Apply rewrites
    for (inst, dest_idx, new_block, args) in rewrites {
        let dfg = &mut func.dfg;
        let destinations =
            dfg.insts[inst].branch_destination_mut(&mut dfg.jump_tables, &mut dfg.exception_tables);
        let dest = &mut destinations[dest_idx];
        dest.set_block(new_block, &mut dfg.value_lists);
        // Clear any existing args and set the trampoline's args
        dest.clear(&mut dfg.value_lists);
        for val in args {
            dest.append_argument(val, &mut dfg.value_lists);
        }
    }
}

/// Remove blocks not reachable from the entry block.
///
/// After trampoline rewrites, many blocks become unreachable dead code.
/// Removing them keeps the IR clean and avoids wasted work in Cranelift's
/// later passes (legalization, register allocation, code emission).
fn remove_unreachable_blocks(func: &mut Function) {
    let entry = match func.layout.entry_block() {
        Some(b) => b,
        None => return,
    };

    // BFS from entry to find all reachable blocks
    let mut reachable = FxHashSet::default();
    let mut queue = vec![entry];
    while let Some(block) = queue.pop() {
        if !reachable.insert(block) {
            continue;
        }
        // Follow all branch destinations from the block's terminator
        if let Some(inst) = func.layout.last_inst(block) {
            for dest in func.dfg.insts[inst]
                .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables)
            {
                let target = dest.block(&func.dfg.value_lists);
                if !reachable.contains(&target) {
                    queue.push(target);
                }
            }
        }
    }

    // Collect unreachable blocks (can't modify layout while iterating)
    let dead: Vec<Block> = func
        .layout
        .blocks()
        .filter(|b| !reachable.contains(b))
        .collect();

    // Remove instructions then blocks
    for block in dead {
        // Drain all instructions from the block
        while let Some(inst) = func.layout.first_inst(block) {
            func.layout.remove_inst(inst);
        }
        func.layout.remove_block(block);
    }
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

    #[test]
    fn test_find_no_trampolines() {
        let func = create_test_function();
        let trampolines = find_trampolines(&func);
        assert!(trampolines.is_empty());
    }

    #[test]
    fn test_resolve_simple_chain() {
        let mut trampolines = FxHashMap::default();
        // Simulate: block0 -> block1 -> block2 (final)
        let b0 = Block::from_u32(0);
        let b1 = Block::from_u32(1);
        let b2 = Block::from_u32(2);
        trampolines.insert(b0, b1);
        trampolines.insert(b1, b2);

        let resolved = resolve_trampoline_chains(&trampolines);

        // Both should resolve to block2
        assert_eq!(resolved.get(&b0), Some(&b2));
        assert_eq!(resolved.get(&b1), Some(&b2));
    }

    #[test]
    fn test_resolve_cycle_detection() {
        let mut trampolines = FxHashMap::default();
        // Simulate a cycle: block0 -> block1 -> block0
        let b0 = Block::from_u32(0);
        let b1 = Block::from_u32(1);
        trampolines.insert(b0, b1);
        trampolines.insert(b1, b0);

        let resolved = resolve_trampoline_chains(&trampolines);

        // Cycles should not be rewritten (would cause infinite loops)
        assert_eq!(resolved.get(&b0), None);
        assert_eq!(resolved.get(&b1), None);
    }

    /// Build IR with a forward-arg trampoline (brif -> trampoline -> merge):
    ///
    ///   entry:
    ///       v0 = iconst 1
    ///       v1 = iconst 42
    ///       brif v0, trampoline, [], exit, []
    ///   trampoline:           // no params
    ///       jump merge(v1)    // passes arg
    ///   exit:
    ///       v2 = iconst 0
    ///       return v2
    ///   merge(v3):
    ///       return v3
    ///
    /// After cleanup, entry should branch directly to merge with the arg:
    ///       brif v0, merge, [v1], exit, []
    #[test]
    fn test_forward_arg_trampoline_brif() {
        use cranelift::codegen::ir::BlockArg;

        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        let trampoline = builder.create_block();
        let exit = builder.create_block();
        let merge = builder.create_block();

        // entry: brif v0, trampoline, [], exit, []
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let cond = builder.ins().iconst(types::I64, 1);
        let default_val = builder.ins().iconst(types::I64, 42);
        builder.ins().brif(cond, trampoline, &[], exit, &[]);

        // trampoline: jump merge(default_val)
        builder.switch_to_block(trampoline);
        builder.seal_block(trampoline);
        builder.ins().jump(merge, &[BlockArg::from(default_val)]);

        // exit: return 0
        builder.switch_to_block(exit);
        builder.seal_block(exit);
        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[zero]);

        // merge(param): return param
        builder.switch_to_block(merge);
        builder.append_block_param(merge, types::I64);
        builder.seal_block(merge);
        let merge_param = builder.block_params(merge)[0];
        builder.ins().return_(&[merge_param]);

        builder.finalize();

        // Verify: trampoline is detected as a forward-arg trampoline
        let fwd = find_forward_arg_trampolines(&func);
        assert_eq!(fwd.len(), 1);
        assert!(fwd.contains_key(&trampoline));
        let (target, args) = &fwd[&trampoline];
        assert_eq!(*target, merge);
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], default_val);

        // Run full cleanup
        cleanup_cfg(&mut func);

        // Verify: entry's brif now targets merge directly with args
        let entry_last = func.layout.last_inst(entry).unwrap();
        let dests = func.dfg.insts[entry_last]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
        // brif has two destinations: then-branch and else-branch
        let then_dest = &dests[0];
        assert_eq!(then_dest.block(&func.dfg.value_lists), merge);
        assert_eq!(then_dest.len(&func.dfg.value_lists), 1);
    }

    /// Test that a jump (not brif) to a forward-arg trampoline is also rewritten.
    ///
    ///   entry:
    ///       v0 = iconst 99
    ///       jump trampoline
    ///   trampoline:           // no params
    ///       jump target(v0)   // passes arg
    ///   target(v1):
    ///       return v1
    ///
    /// After cleanup, trampoline elimination rewrites entry to jump to target,
    /// then block fusion merges target into entry (single predecessor).
    /// Final result: entry contains iconst + return.
    #[test]
    fn test_forward_arg_trampoline_jump() {
        use cranelift::codegen::ir::BlockArg;

        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        let trampoline = builder.create_block();
        let target = builder.create_block();

        // entry: jump trampoline
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let val = builder.ins().iconst(types::I64, 99);
        builder.ins().jump(trampoline, &[]);

        // trampoline: jump target(val)
        builder.switch_to_block(trampoline);
        builder.seal_block(trampoline);
        builder.ins().jump(target, &[BlockArg::from(val)]);

        // target(param): return param
        builder.switch_to_block(target);
        builder.append_block_param(target, types::I64);
        builder.seal_block(target);
        let param = builder.block_params(target)[0];
        builder.ins().return_(&[param]);

        builder.finalize();

        // Verify trampoline detection before full cleanup
        let fwd = find_forward_arg_trampolines(&func);
        assert_eq!(fwd.len(), 1);
        assert!(fwd.contains_key(&trampoline));

        cleanup_cfg(&mut func);

        // After trampoline elimination + block fusion, target (single pred from
        // entry) gets merged into entry. Only entry remains.
        let blocks: Vec<Block> = func.layout.blocks().collect();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0], entry);

        // entry's terminator should now be a return
        let entry_last = func.layout.last_inst(entry).unwrap();
        assert_eq!(func.dfg.insts[entry_last].opcode(), Opcode::Return);

        // The return value should resolve to val (param aliased to val)
        let ret_args = func.dfg.inst_args(entry_last);
        assert_eq!(func.dfg.resolve_aliases(ret_args[0]), val);
    }

    /// Build IR with a pass-through trampoline (brif -> trampoline -> target):
    ///
    ///   entry:
    ///       v0 = iconst 1
    ///       v1 = iconst 42
    ///       v2 = iconst 7
    ///       brif v0, passthrough, [v1, v2], exit, []
    ///   passthrough(v3: i64, v4: i64):
    ///       jump target(v3, v4)     // forwards params unchanged
    ///   exit:
    ///       v5 = iconst 0
    ///       return v5
    ///   target(v6: i64, v7: i64):
    ///       return v6
    ///
    /// After cleanup, entry should branch directly to target:
    ///       brif v0, target, [v1, v2], exit, []
    #[test]
    fn test_passthrough_trampoline_brif() {
        use cranelift::codegen::ir::BlockArg;

        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        let passthrough = builder.create_block();
        let exit = builder.create_block();
        let target = builder.create_block();

        // entry: brif v0, passthrough, [v1, v2], exit, []
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let cond = builder.ins().iconst(types::I64, 1);
        let val1 = builder.ins().iconst(types::I64, 42);
        let val2 = builder.ins().iconst(types::I64, 7);
        builder.ins().brif(
            cond,
            passthrough,
            &[BlockArg::from(val1), BlockArg::from(val2)],
            exit,
            &[],
        );

        // passthrough(v3, v4): jump target(v3, v4)
        builder.switch_to_block(passthrough);
        builder.append_block_param(passthrough, types::I64);
        builder.append_block_param(passthrough, types::I64);
        builder.seal_block(passthrough);
        let p0 = builder.block_params(passthrough)[0];
        let p1 = builder.block_params(passthrough)[1];
        builder
            .ins()
            .jump(target, &[BlockArg::from(p0), BlockArg::from(p1)]);

        // exit: return 0
        builder.switch_to_block(exit);
        builder.seal_block(exit);
        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[zero]);

        // target(v6, v7): return v6
        builder.switch_to_block(target);
        builder.append_block_param(target, types::I64);
        builder.append_block_param(target, types::I64);
        builder.seal_block(target);
        let target_p0 = builder.block_params(target)[0];
        builder.ins().return_(&[target_p0]);

        builder.finalize();

        // Verify detection
        let pt = find_passthrough_trampolines(&func);
        assert_eq!(pt.len(), 1);
        assert!(pt.contains_key(&passthrough));
        assert_eq!(pt[&passthrough], target);

        // Run full cleanup
        cleanup_cfg(&mut func);

        // Verify: entry's brif now targets target directly with same args
        let entry_last = func.layout.last_inst(entry).unwrap();
        let dests = func.dfg.insts[entry_last]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
        let then_dest = &dests[0];
        assert_eq!(then_dest.block(&func.dfg.value_lists), target);
        assert_eq!(then_dest.len(&func.dfg.value_lists), 2);
    }

    /// Test pass-through trampoline chain resolution:
    ///
    ///   entry:
    ///       v0 = iconst 10
    ///       jump pt1(v0)
    ///   pt1(v1: i64):
    ///       jump pt2(v1)
    ///   pt2(v2: i64):
    ///       jump final(v2)
    ///   final(v3: i64):
    ///       return v3
    ///
    /// After cleanup, trampoline chain resolution redirects entry to final_block,
    /// then block fusion merges final_block into entry (single predecessor).
    /// Final result: entry contains iconst + return.
    #[test]
    fn test_passthrough_trampoline_chain() {
        use cranelift::codegen::ir::BlockArg;

        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        let pt1 = builder.create_block();
        let pt2 = builder.create_block();
        let final_block = builder.create_block();

        // entry: jump pt1(v0)
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let val = builder.ins().iconst(types::I64, 10);
        builder.ins().jump(pt1, &[BlockArg::from(val)]);

        // pt1(v1): jump pt2(v1)
        builder.switch_to_block(pt1);
        builder.append_block_param(pt1, types::I64);
        builder.seal_block(pt1);
        let pt1_p = builder.block_params(pt1)[0];
        builder.ins().jump(pt2, &[BlockArg::from(pt1_p)]);

        // pt2(v2): jump final(v2)
        builder.switch_to_block(pt2);
        builder.append_block_param(pt2, types::I64);
        builder.seal_block(pt2);
        let pt2_p = builder.block_params(pt2)[0];
        builder.ins().jump(final_block, &[BlockArg::from(pt2_p)]);

        // final(v3): return v3
        builder.switch_to_block(final_block);
        builder.append_block_param(final_block, types::I64);
        builder.seal_block(final_block);
        let final_p = builder.block_params(final_block)[0];
        builder.ins().return_(&[final_p]);

        builder.finalize();

        // Verify chain detection
        let pt = find_passthrough_trampolines(&func);
        assert_eq!(pt.len(), 2);
        assert_eq!(pt[&pt1], pt2);
        assert_eq!(pt[&pt2], final_block);

        // Chain resolution
        let resolved = resolve_trampoline_chains(&pt);
        assert_eq!(resolved[&pt1], final_block);
        assert_eq!(resolved[&pt2], final_block);

        // Run full cleanup
        cleanup_cfg(&mut func);

        // After trampoline elimination + block fusion, final_block (single pred
        // from entry) gets merged into entry. Only entry remains.
        let blocks: Vec<Block> = func.layout.blocks().collect();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0], entry);

        // entry's terminator should now be a return
        let entry_last = func.layout.last_inst(entry).unwrap();
        assert_eq!(func.dfg.insts[entry_last].opcode(), Opcode::Return);

        // The return value should resolve to val (through the alias chain)
        let ret_args = func.dfg.inst_args(entry_last);
        assert_eq!(func.dfg.resolve_aliases(ret_args[0]), val);
    }

    /// Test that a block with params but reordered args is NOT a pass-through trampoline:
    ///
    ///   block(v1: i64, v2: i64):
    ///       jump target(v2, v1)     // swapped — not a pass-through
    #[test]
    fn test_reordered_args_not_passthrough() {
        use cranelift::codegen::ir::BlockArg;

        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        let reorder = builder.create_block();
        let target = builder.create_block();

        // entry: jump reorder(v0, v1)
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let v0 = builder.ins().iconst(types::I64, 1);
        let v1 = builder.ins().iconst(types::I64, 2);
        builder
            .ins()
            .jump(reorder, &[BlockArg::from(v0), BlockArg::from(v1)]);

        // reorder(p0, p1): jump target(p1, p0) — swapped
        builder.switch_to_block(reorder);
        builder.append_block_param(reorder, types::I64);
        builder.append_block_param(reorder, types::I64);
        builder.seal_block(reorder);
        let rp0 = builder.block_params(reorder)[0];
        let rp1 = builder.block_params(reorder)[1];
        builder
            .ins()
            .jump(target, &[BlockArg::from(rp1), BlockArg::from(rp0)]);

        // target(t0, t1): return t0
        builder.switch_to_block(target);
        builder.append_block_param(target, types::I64);
        builder.append_block_param(target, types::I64);
        builder.seal_block(target);
        let tp0 = builder.block_params(target)[0];
        builder.ins().return_(&[tp0]);

        builder.finalize();

        let pt = find_passthrough_trampolines(&func);
        assert!(pt.is_empty(), "reordered args should not be detected");
    }

    /// Test that a block with params that drops one is NOT a pass-through trampoline:
    ///
    ///   block(v1: i64, v2: i64):
    ///       jump target(v1)     // drops v2 — not a pass-through
    #[test]
    fn test_fewer_args_not_passthrough() {
        use cranelift::codegen::ir::BlockArg;

        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        let dropper = builder.create_block();
        let target = builder.create_block();

        // entry: jump dropper(v0, v1)
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let v0 = builder.ins().iconst(types::I64, 1);
        let v1 = builder.ins().iconst(types::I64, 2);
        builder
            .ins()
            .jump(dropper, &[BlockArg::from(v0), BlockArg::from(v1)]);

        // dropper(p0, p1): jump target(p0) — drops p1
        builder.switch_to_block(dropper);
        builder.append_block_param(dropper, types::I64);
        builder.append_block_param(dropper, types::I64);
        builder.seal_block(dropper);
        let dp0 = builder.block_params(dropper)[0];
        builder.ins().jump(target, &[BlockArg::from(dp0)]);

        // target(t0): return t0
        builder.switch_to_block(target);
        builder.append_block_param(target, types::I64);
        builder.seal_block(target);
        let tp0 = builder.block_params(target)[0];
        builder.ins().return_(&[tp0]);

        builder.finalize();

        let pt = find_passthrough_trampolines(&func);
        assert!(pt.is_empty(), "dropping args should not be detected");
    }
}
