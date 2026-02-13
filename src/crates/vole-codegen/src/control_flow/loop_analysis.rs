// src/codegen/loop_analysis.rs
//
// Loop analysis pass for optimization.
//
// This module provides infrastructure to analyze loops in Cranelift IR:
// - Identify loop headers, bodies, and exit blocks
// - Find loop-invariant values (values that don't change within the loop)
// - Identify induction variables (variables that change predictably each iteration)
//
// This analysis is used by optimization passes like reducing unnecessary
// block parameters in loops (LICM - Loop Invariant Code Motion).

use cranelift_codegen::dominator_tree::DominatorTree;
use cranelift_codegen::flowgraph::ControlFlowGraph;
use cranelift_codegen::ir::{Block, Function, Inst, Opcode, Value};
use cranelift_codegen::loop_analysis::{Loop, LoopAnalysis as CraneliftLoopAnalysis};
use rustc_hash::{FxHashMap, FxHashSet};

/// Information about a single loop.
#[derive(Debug, Clone)]
pub struct LoopInfo {
    /// The loop handle from Cranelift's analysis
    pub loop_id: Loop,
    /// The header block (entry point with back-edge)
    pub header: Block,
    /// All blocks that belong to this loop (including nested loops)
    pub blocks: FxHashSet<Block>,
    /// Values that are loop-invariant (defined outside, unchanged inside)
    pub invariant_values: FxHashSet<Value>,
    /// Induction variables: values that change by a constant amount each iteration
    pub induction_vars: FxHashMap<Value, InductionInfo>,
    /// Block parameters of the header that are actually modified in the loop
    pub modified_params: FxHashSet<Value>,
    /// Block parameters of the header that are NOT modified (loop-invariant)
    pub invariant_params: FxHashSet<Value>,
}

/// Information about an induction variable.
#[derive(Debug, Clone)]
pub struct InductionInfo {
    /// The base value (initial value before the loop)
    pub base: Value,
    /// The step/stride (how much it changes each iteration)
    pub step: InductionStep,
}

/// The step/stride of an induction variable.
#[derive(Debug, Clone)]
pub enum InductionStep {
    /// Constant integer step (e.g., i += 1)
    ConstInt(i64),
    /// Constant float step (e.g., x += 0.5)
    ConstFloat(f64),
    /// Variable step (not a simple induction variable)
    Variable(Value),
}

/// Complete loop analysis results for a function.
pub struct FunctionLoopInfo {
    /// The underlying Cranelift loop analysis
    cranelift_analysis: CraneliftLoopAnalysis,
    /// Control flow graph (needed for queries)
    cfg: ControlFlowGraph,
    /// Dominator tree (needed for queries)
    domtree: DominatorTree,
    /// Detailed info for each loop
    loops: FxHashMap<Loop, LoopInfo>,
    /// Whether analysis has been computed
    valid: bool,
}

impl FunctionLoopInfo {
    /// Create a new, empty loop analysis.
    pub fn new() -> Self {
        Self {
            cranelift_analysis: CraneliftLoopAnalysis::new(),
            cfg: ControlFlowGraph::new(),
            domtree: DominatorTree::new(),
            loops: FxHashMap::default(),
            valid: false,
        }
    }

    /// Analyze the loops in a function.
    ///
    /// This computes:
    /// 1. Basic loop structure (headers, blocks, nesting)
    /// 2. Loop-invariant values
    /// 3. Induction variables
    /// 4. Block parameter classification
    pub fn analyze(&mut self, func: &Function) {
        // First, compute control flow graph and dominator tree
        self.cfg.compute(func);
        self.domtree.compute(func, &self.cfg);

        // Then compute Cranelift's loop analysis
        self.cranelift_analysis
            .compute(func, &self.cfg, &self.domtree);

        // Build detailed info for each loop
        self.loops.clear();
        for lp in self.cranelift_analysis.loops() {
            let info = self.analyze_single_loop(func, lp);
            self.loops.insert(lp, info);
        }

        self.valid = true;
    }

    /// Analyze a single loop and return its LoopInfo.
    fn analyze_single_loop(&self, func: &Function, lp: Loop) -> LoopInfo {
        let header = self.cranelift_analysis.loop_header(lp);

        // Collect all blocks in this loop
        let blocks = self.collect_loop_blocks(func, lp);

        // Find values defined inside the loop
        let defined_in_loop = self.values_defined_in_blocks(func, &blocks);

        // Find values used in the loop but defined outside (candidates for invariance)
        let used_in_loop = self.values_used_in_blocks(func, &blocks);
        let invariant_values: FxHashSet<Value> =
            used_in_loop.difference(&defined_in_loop).copied().collect();

        // Analyze block parameters
        let header_params: FxHashSet<Value> =
            func.dfg.block_params(header).iter().copied().collect();

        // Find which header params are actually modified in the loop
        let (modified_params, invariant_params) =
            self.classify_block_params(func, header, &blocks, &header_params);

        // Find induction variables
        let induction_vars = self.find_induction_vars(func, header, &blocks, &modified_params);

        LoopInfo {
            loop_id: lp,
            header,
            blocks,
            invariant_values,
            induction_vars,
            modified_params,
            invariant_params,
        }
    }

    /// Collect all blocks that belong to a loop.
    fn collect_loop_blocks(&self, func: &Function, lp: Loop) -> FxHashSet<Block> {
        let mut blocks = FxHashSet::default();
        for block in func.layout.blocks() {
            if self.cranelift_analysis.is_in_loop(block, lp) {
                blocks.insert(block);
            }
        }
        blocks
    }

    /// Find all values defined in a set of blocks.
    fn values_defined_in_blocks(
        &self,
        func: &Function,
        blocks: &FxHashSet<Block>,
    ) -> FxHashSet<Value> {
        let mut defined = FxHashSet::default();

        for &block in blocks {
            // Block parameters are defined in this block
            for &param in func.dfg.block_params(block) {
                defined.insert(param);
            }

            // Instruction results are defined in this block
            for inst in func.layout.block_insts(block) {
                for &result in func.dfg.inst_results(inst) {
                    defined.insert(result);
                }
            }
        }

        defined
    }

    /// Find all values used in a set of blocks.
    fn values_used_in_blocks(
        &self,
        func: &Function,
        blocks: &FxHashSet<Block>,
    ) -> FxHashSet<Value> {
        let mut used = FxHashSet::default();

        for &block in blocks {
            for inst in func.layout.block_insts(block) {
                // Collect all value arguments to this instruction
                for &arg in func.dfg.inst_args(inst) {
                    used.insert(arg);
                }

                // Also collect values passed to branch destinations
                let destinations = func.dfg.insts[inst]
                    .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);
                for dest in destinations {
                    for arg in dest.args(&func.dfg.value_lists) {
                        if let Some(val) = arg.as_value() {
                            used.insert(val);
                        }
                    }
                }
            }
        }

        used
    }

    /// Classify header block parameters as modified or invariant.
    ///
    /// A parameter is modified if any back-edge to the header passes a different
    /// value for that parameter position than what was received.
    fn classify_block_params(
        &self,
        func: &Function,
        header: Block,
        loop_blocks: &FxHashSet<Block>,
        _header_params: &FxHashSet<Value>,
    ) -> (FxHashSet<Value>, FxHashSet<Value>) {
        let mut modified = FxHashSet::default();
        let mut invariant = FxHashSet::default();

        let params: Vec<Value> = func.dfg.block_params(header).to_vec();
        if params.is_empty() {
            return (modified, invariant);
        }

        // For each parameter, check if any predecessor inside the loop passes
        // a value different from the parameter itself
        for (param_idx, &param) in params.iter().enumerate() {
            let mut is_modified = false;

            // Check all predecessors of the header that are inside the loop (back-edges)
            for pred in self.cfg.pred_iter(header) {
                if !loop_blocks.contains(&pred.block) {
                    // Entry edge from outside - skip
                    continue;
                }

                // Get the terminator instruction
                let Some(term_inst) = func.layout.last_inst(pred.block) else {
                    continue;
                };

                // Check what value is passed for this parameter position
                if let Some(passed_value) = self.get_jump_arg(func, term_inst, header, param_idx) {
                    // Resolve aliases before comparing - a value might be an alias for the param
                    let resolved_passed = func.dfg.resolve_aliases(passed_value);
                    let resolved_param = func.dfg.resolve_aliases(param);
                    // If the passed value is different from the parameter, it's modified
                    if resolved_passed != resolved_param {
                        is_modified = true;
                        break;
                    }
                }
            }

            if is_modified {
                modified.insert(param);
            } else {
                invariant.insert(param);
            }
        }

        (modified, invariant)
    }

    /// Get the argument passed to a specific block parameter position in a jump/branch.
    fn get_jump_arg(
        &self,
        func: &Function,
        inst: Inst,
        target_block: Block,
        param_idx: usize,
    ) -> Option<Value> {
        let destinations = func.dfg.insts[inst]
            .branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables);

        for dest in destinations {
            if dest.block(&func.dfg.value_lists) == target_block
                && param_idx < dest.len(&func.dfg.value_lists)
            {
                let arg = dest.args(&func.dfg.value_lists).nth(param_idx)?;
                return arg.as_value();
            }
        }

        None
    }

    /// Find induction variables among the modified block parameters.
    ///
    /// An induction variable is a value that changes by a constant amount each iteration.
    /// For example: `i = i + 1` or `x = x + 0.01`
    fn find_induction_vars(
        &self,
        func: &Function,
        header: Block,
        loop_blocks: &FxHashSet<Block>,
        modified_params: &FxHashSet<Value>,
    ) -> FxHashMap<Value, InductionInfo> {
        let mut induction_vars = FxHashMap::default();
        let params: Vec<Value> = func.dfg.block_params(header).to_vec();

        for (param_idx, &param) in params.iter().enumerate() {
            if !modified_params.contains(&param) {
                continue;
            }

            // Look for a pattern: param' = param + constant (or similar)
            if let Some(info) =
                self.detect_induction_pattern(func, header, loop_blocks, param, param_idx)
            {
                induction_vars.insert(param, info);
            }
        }

        induction_vars
    }

    /// Detect if a modified parameter follows an induction pattern.
    fn detect_induction_pattern(
        &self,
        func: &Function,
        header: Block,
        loop_blocks: &FxHashSet<Block>,
        param: Value,
        param_idx: usize,
    ) -> Option<InductionInfo> {
        // Find the value passed back to this parameter on the back-edge
        for pred in self.cfg.pred_iter(header) {
            if !loop_blocks.contains(&pred.block) {
                continue; // Skip entry edges
            }

            let Some(term_inst) = func.layout.last_inst(pred.block) else {
                continue;
            };

            let Some(passed_value) = self.get_jump_arg(func, term_inst, header, param_idx) else {
                continue;
            };

            // Check if passed_value = param + constant
            if let Some(step) = self.is_additive_update(func, passed_value, param) {
                return Some(InductionInfo { base: param, step });
            }
        }

        None
    }

    /// Check if `result` is computed as `base + constant` or `base - constant`.
    fn is_additive_update(
        &self,
        func: &Function,
        result: Value,
        base: Value,
    ) -> Option<InductionStep> {
        // Find the instruction that defines `result`
        let inst = func.dfg.value_def(result).inst()?;
        let opcode = func.dfg.insts[inst].opcode();

        // Check for iadd, isub, fadd, fsub patterns
        match opcode {
            Opcode::Iadd | Opcode::IaddImm => {
                let args = func.dfg.inst_args(inst);
                if args.len() == 2 {
                    // iadd v1, v2
                    let (arg0, arg1) = (args[0], args[1]);
                    if arg0 == base {
                        return self.get_const_int(func, arg1).map(InductionStep::ConstInt);
                    } else if arg1 == base {
                        return self.get_const_int(func, arg0).map(InductionStep::ConstInt);
                    }
                } else if args.len() == 1 && opcode == Opcode::IaddImm {
                    // iadd_imm v1, const
                    if args[0] == base
                        && let Some(imm) = self.get_iadd_imm(func, inst)
                    {
                        return Some(InductionStep::ConstInt(imm));
                    }
                }
            }
            Opcode::Isub => {
                let args = func.dfg.inst_args(inst);
                if args.len() == 2 && args[0] == base {
                    // isub base, const -> base + (-const)
                    if let Some(c) = self.get_const_int(func, args[1]) {
                        return Some(InductionStep::ConstInt(-c));
                    }
                }
            }
            Opcode::Fadd => {
                let args = func.dfg.inst_args(inst);
                if args.len() == 2 {
                    let (arg0, arg1) = (args[0], args[1]);
                    if arg0 == base {
                        return self
                            .get_const_float(func, arg1)
                            .map(InductionStep::ConstFloat);
                    } else if arg1 == base {
                        return self
                            .get_const_float(func, arg0)
                            .map(InductionStep::ConstFloat);
                    }
                }
            }
            Opcode::Fsub => {
                let args = func.dfg.inst_args(inst);
                if args.len() == 2
                    && args[0] == base
                    && let Some(c) = self.get_const_float(func, args[1])
                {
                    return Some(InductionStep::ConstFloat(-c));
                }
            }
            _ => {}
        }

        None
    }

    /// Get the constant integer value if `v` is defined by iconst.
    fn get_const_int(&self, func: &Function, v: Value) -> Option<i64> {
        let inst = func.dfg.value_def(v).inst()?;
        if func.dfg.insts[inst].opcode() == Opcode::Iconst {
            // Get the immediate value
            if let cranelift_codegen::ir::InstructionData::UnaryImm { imm, .. } =
                func.dfg.insts[inst]
            {
                return Some(imm.bits());
            }
        }
        None
    }

    /// Get the immediate value from an iadd_imm instruction.
    fn get_iadd_imm(&self, func: &Function, inst: Inst) -> Option<i64> {
        if let cranelift_codegen::ir::InstructionData::BinaryImm64 { imm, .. } =
            func.dfg.insts[inst]
        {
            return Some(imm.bits());
        }
        None
    }

    /// Get the constant float value if `v` is defined by f32const or f64const.
    fn get_const_float(&self, func: &Function, v: Value) -> Option<f64> {
        let inst = func.dfg.value_def(v).inst()?;
        let opcode = func.dfg.insts[inst].opcode();
        match opcode {
            Opcode::F32const => {
                if let cranelift_codegen::ir::InstructionData::UnaryIeee32 { imm, .. } =
                    func.dfg.insts[inst]
                {
                    return Some(f32::from_bits(imm.bits()) as f64);
                }
            }
            Opcode::F64const => {
                if let cranelift_codegen::ir::InstructionData::UnaryIeee64 { imm, .. } =
                    func.dfg.insts[inst]
                {
                    return Some(f64::from_bits(imm.bits()));
                }
            }
            _ => {}
        }
        None
    }

    /// Get a reference to the computed control flow graph.
    pub fn cfg(&self) -> &ControlFlowGraph {
        &self.cfg
    }

    /// Check if analysis is valid.
    pub fn is_valid(&self) -> bool {
        self.valid
    }

    /// Clear the analysis.
    pub fn clear(&mut self) {
        self.cranelift_analysis.clear();
        self.cfg.clear();
        self.domtree.clear();
        self.loops.clear();
        self.valid = false;
    }

    /// Get the number of loops in the function.
    pub fn num_loops(&self) -> usize {
        self.loops.len()
    }

    /// Iterate over all loops.
    pub fn loops(&self) -> impl Iterator<Item = &LoopInfo> {
        self.loops.values()
    }

    /// Get info for a specific loop.
    pub fn get_loop(&self, lp: Loop) -> Option<&LoopInfo> {
        self.loops.get(&lp)
    }

    /// Get the innermost loop containing a block.
    pub fn innermost_loop(&self, block: Block) -> Option<&LoopInfo> {
        let lp = self.cranelift_analysis.innermost_loop(block)?;
        self.loops.get(&lp)
    }

    /// Check if a block is inside any loop.
    pub fn is_in_loop(&self, block: Block) -> bool {
        self.cranelift_analysis.innermost_loop(block).is_some()
    }

    /// Get the loop nesting level of a block (0 = not in loop).
    pub fn loop_level(&self, block: Block) -> usize {
        self.cranelift_analysis.loop_level(block).level()
    }
}

impl Default for FunctionLoopInfo {
    fn default() -> Self {
        Self::new()
    }
}

/// Perform loop analysis on a function and return the results.
///
/// This is a convenience function for one-shot analysis.
pub fn analyze_loops(func: &Function) -> FunctionLoopInfo {
    let mut info = FunctionLoopInfo::new();
    info.analyze(func);
    info
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
    fn test_no_loops() {
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

        let info = analyze_loops(&func);
        assert!(info.is_valid());
        assert_eq!(info.num_loops(), 0);
        assert!(!info.is_in_loop(entry));
    }

    #[test]
    fn test_simple_loop() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        // entry -> header <-> body -> exit
        let entry = builder.create_block();
        let header = builder.create_block();
        let body = builder.create_block();
        let exit = builder.create_block();

        // Entry block
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let init = builder.ins().iconst(types::I64, 0);
        let init_arg = BlockArg::from(init);
        builder.ins().jump(header, &[init_arg]);

        // Header block with counter parameter
        builder.switch_to_block(header);
        builder.append_block_param(header, types::I64);
        let counter = builder.block_params(header)[0];
        let limit = builder.ins().iconst(types::I64, 10);
        let cond = builder.ins().icmp(IntCC::SignedLessThan, counter, limit);
        builder.ins().brif(cond, body, &[], exit, &[]);

        // Body block - increment counter and loop back
        builder.switch_to_block(body);
        let one = builder.ins().iconst(types::I64, 1);
        let new_counter = builder.ins().iadd(counter, one);
        let new_counter_arg = BlockArg::from(new_counter);
        builder.ins().jump(header, &[new_counter_arg]);

        // Exit block
        builder.switch_to_block(exit);
        let result = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[result]);

        // Seal blocks after all predecessors are known
        builder.seal_block(header);
        builder.seal_block(body);
        builder.seal_block(exit);

        builder.finalize();

        let info = analyze_loops(&func);
        assert!(info.is_valid());
        assert_eq!(info.num_loops(), 1);

        // Header and body should be in the loop
        assert!(info.is_in_loop(header));
        assert!(info.is_in_loop(body));
        assert!(!info.is_in_loop(entry));
        assert!(!info.is_in_loop(exit));

        // Check loop info
        let loop_info = info.innermost_loop(header).unwrap();
        assert_eq!(loop_info.header, header);
        assert!(loop_info.blocks.contains(&header));
        assert!(loop_info.blocks.contains(&body));

        // The counter should be identified as modified (it changes each iteration)
        assert!(loop_info.modified_params.contains(&counter));

        // The counter should be identified as an induction variable
        assert!(loop_info.induction_vars.contains_key(&counter));
        if let Some(ind_info) = loop_info.induction_vars.get(&counter) {
            match ind_info.step {
                InductionStep::ConstInt(1) => {} // Expected
                _ => panic!("Expected constant int step of 1"),
            }
        }
    }

    #[test]
    fn test_loop_with_invariant_param() {
        let mut func = create_test_function();
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        // Loop where one parameter changes (counter) but another doesn't (limit)
        let entry = builder.create_block();
        let header = builder.create_block();
        let body = builder.create_block();
        let exit = builder.create_block();

        // Entry
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let init_counter = builder.ins().iconst(types::I64, 0);
        let init_limit = builder.ins().iconst(types::I64, 100);
        let init_counter_arg = BlockArg::from(init_counter);
        let init_limit_arg = BlockArg::from(init_limit);
        builder
            .ins()
            .jump(header, &[init_counter_arg, init_limit_arg]);

        // Header with counter and limit params
        builder.switch_to_block(header);
        builder.append_block_param(header, types::I64); // counter
        builder.append_block_param(header, types::I64); // limit (invariant)
        let counter = builder.block_params(header)[0];
        let limit = builder.block_params(header)[1];
        let cond = builder.ins().icmp(IntCC::SignedLessThan, counter, limit);
        builder.ins().brif(cond, body, &[], exit, &[]);

        // Body - increment counter, pass same limit
        builder.switch_to_block(body);
        let one = builder.ins().iconst(types::I64, 1);
        let new_counter = builder.ins().iadd(counter, one);
        let new_counter_arg = BlockArg::from(new_counter);
        let limit_arg = BlockArg::from(limit);
        builder.ins().jump(header, &[new_counter_arg, limit_arg]); // limit unchanged

        // Exit
        builder.switch_to_block(exit);
        let result = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[result]);

        builder.seal_block(header);
        builder.seal_block(body);
        builder.seal_block(exit);
        builder.finalize();

        let info = analyze_loops(&func);
        let loop_info = info.innermost_loop(header).unwrap();

        // Counter should be modified, limit should be invariant
        assert!(loop_info.modified_params.contains(&counter));
        assert!(!loop_info.modified_params.contains(&limit));
        assert!(loop_info.invariant_params.contains(&limit));
        assert!(!loop_info.invariant_params.contains(&counter));
    }
}
