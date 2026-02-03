// src/codegen/loop_param_opt.rs
//
// Loop parameter optimization pass.
//
// This pass removes unnecessary block parameters from loop headers.
// When a value is passed unchanged through a loop back-edge (e.g., loop-invariant
// values like limits or constants), we can remove it from the block parameters
// and use the original value directly.
//
// Example transformation:
//
// Before:
//   block1(v4: i64, v5: i64):  ; v4 = counter, v5 = limit (invariant)
//     ...
//     jump block1(v12, v5)     ; v5 passed unchanged
//
// After:
//   block1(v4: i64):           ; only counter
//     ; uses of v5 replaced with v1 (original definition)
//     ...
//     jump block1(v12)

use cranelift_codegen::ir::{Block, Function, Opcode, Value};
use rustc_hash::{FxHashMap, FxHashSet};

use super::loop_analysis::FunctionLoopInfo;

/// Statistics for the loop parameter optimization pass.
#[derive(Debug, Default)]
pub struct LoopParamOptStats {
    /// Number of loops processed
    pub loops_processed: usize,
    /// Number of parameters removed
    pub params_removed: usize,
}

/// Run the loop parameter optimization pass.
///
/// Returns statistics about the optimization performed.
pub fn optimize_loop_params(func: &mut Function) -> LoopParamOptStats {
    let mut stats = LoopParamOptStats::default();

    // Analyze loops in the function
    let mut loop_info = FunctionLoopInfo::new();
    loop_info.analyze(func);

    if loop_info.num_loops() == 0 {
        return stats;
    }

    // Collect optimization opportunities for each loop
    let optimizations = collect_optimizations(func, &loop_info);

    if optimizations.is_empty() {
        return stats;
    }

    // Apply optimizations
    for opt in &optimizations {
        apply_optimization(func, opt);
        stats.loops_processed += 1;
        stats.params_removed += opt.params_to_remove.len();
    }

    stats
}

/// Information about a parameter to be removed from a loop header.
#[derive(Debug)]
struct ParamRemoval {
    /// The block parameter being removed
    param: Value,
    /// Index of the parameter in the block parameter list
    param_idx: usize,
    /// The value to use instead (the original value from outside the loop)
    replacement: Value,
}

/// Optimization plan for a single loop.
#[derive(Debug)]
struct LoopOptimization {
    /// The loop header block
    header: Block,
    /// Parameters to remove, with their replacements
    params_to_remove: Vec<ParamRemoval>,
}

/// Collect optimization opportunities from analyzed loops.
fn collect_optimizations(func: &Function, loop_info: &FunctionLoopInfo) -> Vec<LoopOptimization> {
    let mut optimizations = Vec::new();

    for lp in loop_info.loops() {
        let params_to_remove = find_removable_params(func, loop_info, lp);

        if !params_to_remove.is_empty() {
            optimizations.push(LoopOptimization {
                header: lp.header,
                params_to_remove,
            });
        }
    }

    // Post-process: if any replacement value is itself a parameter that will be removed,
    // transitively resolve it to the ultimate replacement. This handles nested loops where
    // an inner loop passes through an outer loop's invariant parameter.
    resolve_transitive_replacements(&mut optimizations);

    optimizations
}

/// Transitively resolve replacements through the optimization chain.
///
/// When multiple loops are optimized, an inner loop's invariant parameter might come from
/// an outer loop's parameter that is also being removed. For example:
///
/// - Loop 1 (block1): remove param v13 -> replacement v0
/// - Loop 2 (block4): remove param v36 -> replacement v13
///
/// After this function, Loop 2's replacement will be v0 (following the chain v36 -> v13 -> v0).
fn resolve_transitive_replacements(optimizations: &mut [LoopOptimization]) {
    // Build a map from parameter being removed -> its replacement
    let mut param_to_replacement: FxHashMap<Value, Value> = FxHashMap::default();
    for opt in optimizations.iter() {
        for removal in &opt.params_to_remove {
            param_to_replacement.insert(removal.param, removal.replacement);
        }
    }

    // Transitively resolve each replacement
    for opt in optimizations.iter_mut() {
        for removal in &mut opt.params_to_remove {
            // Follow the chain until we reach a value that's not being removed
            let mut current = removal.replacement;
            let mut iterations = 0;
            while let Some(&next) = param_to_replacement.get(&current) {
                current = next;
                iterations += 1;
                // Safety: prevent infinite loops (shouldn't happen with valid IR)
                if iterations > 100 {
                    break;
                }
            }
            removal.replacement = current;
        }
    }
}

/// Find parameters that can be removed from a loop header.
fn find_removable_params(
    func: &Function,
    loop_info: &FunctionLoopInfo,
    lp: &super::loop_analysis::LoopInfo,
) -> Vec<ParamRemoval> {
    let mut removals = Vec::new();
    let header = lp.header;
    let params: Vec<Value> = func.dfg.block_params(header).to_vec();

    // For each invariant parameter, find the replacement value
    for (param_idx, &param) in params.iter().enumerate() {
        if !lp.invariant_params.contains(&param) {
            continue;
        }

        // Find the value passed from outside the loop (entry edge)
        if let Some(replacement) = find_entry_value(func, loop_info, lp, param_idx) {
            removals.push(ParamRemoval {
                param,
                param_idx,
                replacement,
            });
        }
    }

    removals
}

/// Find the value passed to a parameter from the loop entry (non-back-edge).
///
/// Returns the resolved (de-aliased) value to ensure it's valid in all contexts.
/// Aliases may reference block parameters that are only valid in specific blocks,
/// so we resolve them to the underlying value.
fn find_entry_value(
    func: &Function,
    _loop_info: &FunctionLoopInfo,
    lp: &super::loop_analysis::LoopInfo,
    param_idx: usize,
) -> Option<Value> {
    let header = lp.header;

    // Build CFG to find predecessors
    let mut cfg = cranelift_codegen::flowgraph::ControlFlowGraph::new();
    cfg.compute(func);

    // Look for entry edges (predecessors not in the loop)
    for pred in cfg.pred_iter(header) {
        if lp.blocks.contains(&pred.block) {
            // Back-edge, skip
            continue;
        }

        // This is an entry edge - get the value passed
        let Some(term_inst) = func.layout.last_inst(pred.block) else {
            continue;
        };

        let destinations = func.dfg.insts[term_inst]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);

        for dest in destinations {
            if dest.block(&func.dfg.value_lists) != header {
                continue;
            }

            let args: Vec<_> = dest.args(&func.dfg.value_lists).collect();
            if param_idx < args.len()
                && let Some(val) = args[param_idx].as_value()
            {
                // Resolve aliases to get the underlying value.
                // This is important because the entry value might be an alias
                // to a block parameter (e.g., from an outer loop), and we need
                // the original value to use as a replacement.
                let resolved = func.dfg.resolve_aliases(val);
                return Some(resolved);
            }
        }
    }

    None
}

/// Apply an optimization to remove invariant parameters from a loop header.
fn apply_optimization(func: &mut Function, opt: &LoopOptimization) {
    if opt.params_to_remove.is_empty() {
        return;
    }

    // Build set of parameter indices to remove
    let indices_to_remove: FxHashSet<usize> =
        opt.params_to_remove.iter().map(|r| r.param_idx).collect();

    // Build replacement map: old param -> replacement value
    // Also include any values that are aliased to the parameters being removed
    let mut replacements: FxHashMap<Value, Value> = opt
        .params_to_remove
        .iter()
        .map(|r| (r.param, r.replacement))
        .collect();

    // Find all values that are aliased to parameters we're removing
    // A value v is an alias to param p if resolve_aliases(v) == p
    let params_to_remove: FxHashSet<Value> = opt.params_to_remove.iter().map(|r| r.param).collect();

    // Scan ALL values in the DFG to find aliases (not just block params and inst results)
    // This catches "free" aliases created by change_to_alias during variable assignments
    for value in func.dfg.values() {
        if replacements.contains_key(&value) {
            continue;
        }
        let resolved = func.dfg.resolve_aliases(value);
        if params_to_remove.contains(&resolved)
            && let Some(removal) = opt.params_to_remove.iter().find(|r| r.param == resolved)
        {
            replacements.insert(value, removal.replacement);
        }
    }

    // Step 1: Replace uses of removed parameters (and their aliases) with their replacements
    replace_value_uses(func, &replacements);

    // Step 2: Remove parameters from header block and update all jumps
    remove_block_params(func, opt.header, &indices_to_remove);
}

/// Replace all uses of values in the replacement map.
fn replace_value_uses(func: &mut Function, replacements: &FxHashMap<Value, Value>) {
    // Collect instructions that use values we need to replace
    let mut inst_replacements: Vec<(cranelift_codegen::ir::Inst, Vec<(usize, Value)>)> = Vec::new();

    // Collect branch destination replacements: (inst, dest_idx, new_args)
    let mut branch_replacements: Vec<(cranelift_codegen::ir::Inst, usize, Vec<Value>)> = Vec::new();

    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            let mut arg_updates = Vec::new();

            // Check instruction arguments (for non-branch instructions)
            for (idx, &arg) in func.dfg.inst_args(inst).iter().enumerate() {
                if let Some(&replacement) = replacements.get(&arg) {
                    arg_updates.push((idx, replacement));
                }
            }

            if !arg_updates.is_empty() {
                inst_replacements.push((inst, arg_updates));
            }

            // Check branch destination arguments (for jumps/branches)
            let opcode = func.dfg.insts[inst].opcode();
            if opcode == Opcode::Jump || opcode == Opcode::Brif || opcode == Opcode::BrTable {
                let destinations = func.dfg.insts[inst]
                    .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
                for (dest_idx, dest) in destinations.iter().enumerate() {
                    let mut any_replaced = false;
                    let new_args: Vec<Value> = dest
                        .args(&func.dfg.value_lists)
                        .filter_map(|arg| arg.as_value())
                        .map(|val| {
                            if let Some(&replacement) = replacements.get(&val) {
                                any_replaced = true;
                                replacement
                            } else {
                                val
                            }
                        })
                        .collect();
                    if any_replaced {
                        branch_replacements.push((inst, dest_idx, new_args));
                    }
                }
            }
        }
    }

    // Apply instruction argument replacements
    for (inst, updates) in inst_replacements {
        let args = func.dfg.inst_args_mut(inst);
        for (idx, replacement) in updates {
            args[idx] = replacement;
        }
    }

    // Apply branch destination argument replacements (clear and repopulate)
    for (inst, dest_idx, new_args) in branch_replacements {
        let dfg = &mut func.dfg;
        let destinations_mut =
            dfg.insts[inst].branch_destination_mut(&mut dfg.jump_tables, &mut dfg.exception_tables);
        let dest_mut = &mut destinations_mut[dest_idx];
        dest_mut.clear(&mut dfg.value_lists);
        for val in new_args {
            dest_mut.append_argument(val, &mut dfg.value_lists);
        }
    }
}

/// Remove block parameters at specified indices and update all jumps to that block.
fn remove_block_params(func: &mut Function, block: Block, indices_to_remove: &FxHashSet<usize>) {
    // Collect all jump/branch instructions that target this block
    let mut jumps_to_update: Vec<cranelift_codegen::ir::Inst> = Vec::new();

    for blk in func.layout.blocks() {
        if let Some(inst) = func.layout.last_inst(blk) {
            let opcode = func.dfg.insts[inst].opcode();
            if opcode == Opcode::Jump || opcode == Opcode::Brif || opcode == Opcode::BrTable {
                let destinations = func.dfg.insts[inst]
                    .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
                for dest in destinations {
                    if dest.block(&func.dfg.value_lists) == block {
                        jumps_to_update.push(inst);
                        break;
                    }
                }
            }
        }
    }

    // Update each jump instruction to remove the arguments at specified indices
    for inst in jumps_to_update {
        update_jump_args(func, inst, block, indices_to_remove);
    }

    // Remove the block parameters themselves
    // We need the parameter Values, which we collect from the optimization data
    // remove_block_param takes a Value (the parameter itself), not an index
    let params: Vec<Value> = func.dfg.block_params(block).to_vec();

    // Remove from highest index to lowest to preserve indices
    let mut sorted_indices: Vec<usize> = indices_to_remove.iter().copied().collect();
    sorted_indices.sort_by(|a, b| b.cmp(a)); // Descending order

    for idx in sorted_indices {
        let param = params[idx];
        func.dfg.remove_block_param(param);
    }
}

/// Update jump arguments to remove values at specified indices.
fn update_jump_args(
    func: &mut Function,
    inst: cranelift_codegen::ir::Inst,
    target_block: Block,
    indices_to_remove: &FxHashSet<usize>,
) {
    let dfg = &mut func.dfg;

    // Get current arguments for the target block
    let destinations = dfg.insts[inst].branch_destination(&dfg.jump_tables, &dfg.exception_tables);

    // Find which destination targets our block and collect its args
    let mut dest_idx = None;
    let mut new_args: Vec<Value> = Vec::new();

    for (i, dest) in destinations.iter().enumerate() {
        if dest.block(&dfg.value_lists) == target_block {
            dest_idx = Some(i);
            // Collect args, filtering out removed indices
            new_args = dest
                .args(&dfg.value_lists)
                .enumerate()
                .filter(|(idx, _)| !indices_to_remove.contains(idx))
                .filter_map(|(_, arg)| arg.as_value())
                .collect();
            break;
        }
    }

    let Some(dest_idx) = dest_idx else {
        return;
    };

    // Now mutate: clear and repopulate args for this destination
    let destinations_mut =
        dfg.insts[inst].branch_destination_mut(&mut dfg.jump_tables, &mut dfg.exception_tables);
    let dest_mut = &mut destinations_mut[dest_idx];

    dest_mut.clear(&mut dfg.value_lists);
    for val in new_args {
        dest_mut.append_argument(val, &mut dfg.value_lists);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelift::codegen::ir::BlockArg;
    use cranelift::prelude::*;

    fn create_test_function() -> Function {
        let mut func = Function::new();
        func.signature.returns.push(AbiParam::new(types::I64));
        func
    }

    #[test]
    fn test_no_loops_no_change() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let val = builder.ins().iconst(types::I64, 42);
        builder.ins().return_(&[val]);
        builder.finalize();

        let stats = optimize_loop_params(&mut func);
        assert_eq!(stats.loops_processed, 0);
        assert_eq!(stats.params_removed, 0);
    }

    #[test]
    fn test_loop_with_invariant_param() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        // Create a loop where one parameter changes (counter) but another doesn't (limit)
        let entry = builder.create_block();
        let header = builder.create_block();
        let body = builder.create_block();
        let exit = builder.create_block();

        // Entry: jump to header with (counter=0, limit=100)
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let init_counter = builder.ins().iconst(types::I64, 0);
        let init_limit = builder.ins().iconst(types::I64, 100);
        builder.ins().jump(
            header,
            &[BlockArg::from(init_counter), BlockArg::from(init_limit)],
        );

        // Header: (counter, limit) -> check counter < limit
        builder.switch_to_block(header);
        builder.append_block_param(header, types::I64); // counter
        builder.append_block_param(header, types::I64); // limit (invariant)
        let counter = builder.block_params(header)[0];
        let limit = builder.block_params(header)[1];
        let cond = builder.ins().icmp(IntCC::SignedLessThan, counter, limit);
        builder.ins().brif(cond, body, &[], exit, &[]);

        // Body: increment counter, pass same limit back
        builder.switch_to_block(body);
        let one = builder.ins().iconst(types::I64, 1);
        let new_counter = builder.ins().iadd(counter, one);
        builder.ins().jump(
            header,
            &[BlockArg::from(new_counter), BlockArg::from(limit)],
        );

        // Exit: return counter
        builder.switch_to_block(exit);
        let result = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[result]);

        builder.seal_block(header);
        builder.seal_block(body);
        builder.seal_block(exit);
        builder.finalize();

        // Verify initial state: header has 2 parameters
        assert_eq!(func.dfg.block_params(header).len(), 2);

        // Run optimization
        let stats = optimize_loop_params(&mut func);

        // Should have removed 1 parameter (limit)
        assert_eq!(stats.loops_processed, 1);
        assert_eq!(stats.params_removed, 1);

        // Header should now have only 1 parameter
        assert_eq!(func.dfg.block_params(header).len(), 1);
    }

    #[test]
    fn test_loop_all_params_modified() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        // Create a loop where all parameters change
        let entry = builder.create_block();
        let header = builder.create_block();
        let body = builder.create_block();
        let exit = builder.create_block();

        // Entry
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let init_a = builder.ins().iconst(types::I64, 0);
        let init_b = builder.ins().iconst(types::I64, 0);
        builder
            .ins()
            .jump(header, &[BlockArg::from(init_a), BlockArg::from(init_b)]);

        // Header with two parameters that both change
        builder.switch_to_block(header);
        builder.append_block_param(header, types::I64);
        builder.append_block_param(header, types::I64);
        let a = builder.block_params(header)[0];
        let b = builder.block_params(header)[1];
        let limit = builder.ins().iconst(types::I64, 10);
        let cond = builder.ins().icmp(IntCC::SignedLessThan, a, limit);
        builder.ins().brif(cond, body, &[], exit, &[]);

        // Body: both a and b change
        builder.switch_to_block(body);
        let one = builder.ins().iconst(types::I64, 1);
        let new_a = builder.ins().iadd(a, one);
        let new_b = builder.ins().iadd(b, a); // b changes too
        builder
            .ins()
            .jump(header, &[BlockArg::from(new_a), BlockArg::from(new_b)]);

        // Exit
        builder.switch_to_block(exit);
        let result = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[result]);

        builder.seal_block(header);
        builder.seal_block(body);
        builder.seal_block(exit);
        builder.finalize();

        // Verify initial state
        assert_eq!(func.dfg.block_params(header).len(), 2);

        // Run optimization - should find nothing to remove
        let stats = optimize_loop_params(&mut func);

        assert_eq!(stats.params_removed, 0);
        // Header should still have 2 parameters
        assert_eq!(func.dfg.block_params(header).len(), 2);
    }
}
