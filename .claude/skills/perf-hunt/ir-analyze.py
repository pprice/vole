#!/usr/bin/env python3
"""
IR / MIR analyzer for Vole's Cranelift output.

Usage:
    # Analyze IR from stdin
    vole inspect ir test/ 2>/dev/null | python3 ir-analyze.py

    # Analyze IR from file
    python3 ir-analyze.py /tmp/ir-dump.txt

    # Analyze MIR
    vole inspect mir test/ 2>/dev/null | python3 ir-analyze.py --mir

    # Specific analyses (default: summary)
    python3 ir-analyze.py /tmp/ir.txt --analysis summary
    python3 ir-analyze.py /tmp/ir.txt --analysis opcodes
    python3 ir-analyze.py /tmp/ir.txt --analysis blocks
    python3 ir-analyze.py /tmp/ir.txt --analysis constants
    python3 ir-analyze.py /tmp/ir.txt --analysis patterns
    python3 ir-analyze.py /tmp/ir.txt --analysis dead-values
    python3 ir-analyze.py /tmp/ir.txt --analysis redundant-iconst
    python3 ir-analyze.py /tmp/ir.txt --analysis diamonds
    python3 ir-analyze.py /tmp/ir.txt --analysis all

    # JSON output for scripting
    python3 ir-analyze.py /tmp/ir.txt --json

    # Top N results (default 20)
    python3 ir-analyze.py /tmp/ir.txt --analysis opcodes --top 50

Output: human-readable tables by default, JSON with --json.
"""

import sys
import re
import json
import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from typing import Optional


# ── IR Parsing ────────────────────────────────────────────────────────────────

@dataclass
class Instruction:
    """A single IR instruction."""
    results: list[str]           # e.g. ["v3"] or ["v3", "v4"] or []
    opcode: str                  # e.g. "iconst", "call", "brif"
    type_suffix: Optional[str]   # e.g. "i64", "i8", None
    operands: str                # raw operand string
    raw: str                     # full original line (stripped)

@dataclass
class Alias:
    """A value alias: vN -> vM."""
    alias: str    # vN
    target: str   # vM

@dataclass
class Block:
    """A basic block."""
    name: str                            # e.g. "block0"
    params: list[tuple[str, str]]        # [(value, type), ...] e.g. [("v0", "i64")]
    instructions: list[Instruction]
    aliases: list[Alias]

@dataclass
class Function:
    """A function definition."""
    vole_name: str                       # e.g. "double", "std:prelude/i16::u16::default_value"
    blocks: list[Block]
    signatures: list[str]                # raw sig lines
    fn_decls: list[str]                  # raw fn decl lines
    stack_slots: list[str]               # raw ss lines
    global_values: list[str]             # raw gv lines
    param_types: list[str]               # function parameter types
    return_types: list[str]              # function return types

@dataclass
class IRFile:
    """Complete parsed IR file."""
    source_path: str
    functions: list[Function]


# Regex patterns for IR parsing
RE_FILE_COMMENT = re.compile(r'^// (.+\.vole)$')
RE_FUNC_COMMENT = re.compile(r'^// func (.+)$')
RE_FUNC_DECL = re.compile(
    r'^function u0:\d+\(([^)]*)\)\s*(?:->\s*(.+?))?\s*system_v\s*\{$'
)
RE_BLOCK_HEADER = re.compile(r'^(block\d+)(?:\(([^)]*)\))?:$')
RE_INSTRUCTION = re.compile(
    r'^((?:v\d+(?:,\s*v\d+)*)\s*=\s*)?'  # optional results
    r'([a-z_]+)'                           # opcode
    r'(?:\.([a-z]\w+))?'                   # optional type suffix
    r'(?:\s+(.*))?$'                       # optional operands
)
RE_ALIAS = re.compile(r'^(v\d+)\s*->\s*(v\d+)$')
RE_SIG = re.compile(r'^sig\d+\s*=')
RE_FN_DECL = re.compile(r'^fn\d+\s*=')
RE_SS = re.compile(r'^ss\d+\s*=')
RE_GV = re.compile(r'^gv\d+\s*=')
RE_TRAILING_COMMENT = re.compile(r'\s*;[^;].*$')

# For extracting values referenced in operands
RE_VALUE_REF = re.compile(r'\bv(\d+)\b')


def parse_ir(text: str) -> IRFile:
    """Parse Cranelift IR text into structured data."""
    lines = text.splitlines()
    source_path = ""
    functions = []

    i = 0
    while i < len(lines):
        line = lines[i].strip()

        # File comment
        m = RE_FILE_COMMENT.match(line)
        if m and not source_path:
            source_path = m.group(1)
            i += 1
            continue

        # Function comment
        m = RE_FUNC_COMMENT.match(line)
        if m:
            vole_name = m.group(1)
            i += 1
            # Find function declaration
            while i < len(lines):
                fline = lines[i].strip()
                m2 = RE_FUNC_DECL.match(fline)
                if m2:
                    param_str = m2.group(1).strip()
                    ret_str = m2.group(2)
                    param_types = [p.strip() for p in param_str.split(',') if p.strip()] if param_str else []
                    return_types = [r.strip() for r in ret_str.split(',') if r.strip()] if ret_str else []
                    i += 1
                    break
                i += 1
            else:
                i += 1
                continue

            # Parse preamble and blocks
            sigs, fn_decls, ss_decls, gv_decls = [], [], [], []
            blocks = []
            current_block = None

            while i < len(lines):
                fline = lines[i]
                stripped = fline.strip()

                # End of function
                if stripped == '}':
                    if current_block:
                        blocks.append(current_block)
                    i += 1
                    break

                # Skip empty lines
                if not stripped:
                    i += 1
                    continue

                # Preamble declarations
                if RE_SIG.match(stripped):
                    sigs.append(stripped)
                    i += 1
                    continue
                if RE_FN_DECL.match(stripped):
                    fn_decls.append(stripped)
                    i += 1
                    continue
                if RE_SS.match(stripped):
                    ss_decls.append(stripped)
                    i += 1
                    continue
                if RE_GV.match(stripped):
                    gv_decls.append(stripped)
                    i += 1
                    continue

                # Block header
                m3 = RE_BLOCK_HEADER.match(stripped)
                if m3:
                    if current_block:
                        blocks.append(current_block)
                    block_name = m3.group(1)
                    params_str = m3.group(2)
                    params = []
                    if params_str:
                        for p in params_str.split(','):
                            p = p.strip()
                            parts = p.split(':')
                            if len(parts) == 2:
                                params.append((parts[0].strip(), parts[1].strip()))
                    current_block = Block(
                        name=block_name, params=params,
                        instructions=[], aliases=[]
                    )
                    i += 1
                    continue

                # Inside a block
                if current_block is not None:
                    # Strip trailing comments for parsing
                    clean = RE_TRAILING_COMMENT.sub('', stripped).strip()

                    # Value alias
                    ma = RE_ALIAS.match(clean)
                    if ma:
                        current_block.aliases.append(
                            Alias(alias=ma.group(1), target=ma.group(2))
                        )
                        i += 1
                        continue

                    # Instruction
                    mi = RE_INSTRUCTION.match(clean)
                    if mi:
                        results_str = mi.group(1)
                        opcode = mi.group(2)
                        type_suffix = mi.group(3)
                        operands = mi.group(4) or ""

                        results = []
                        if results_str:
                            results_str = results_str.replace('=', '').strip()
                            results = [r.strip() for r in results_str.split(',')]

                        current_block.instructions.append(Instruction(
                            results=results,
                            opcode=opcode,
                            type_suffix=type_suffix,
                            operands=operands,
                            raw=stripped
                        ))
                        i += 1
                        continue

                i += 1

            functions.append(Function(
                vole_name=vole_name,
                blocks=blocks,
                signatures=sigs,
                fn_decls=fn_decls,
                stack_slots=ss_decls,
                global_values=gv_decls,
                param_types=param_types,
                return_types=return_types,
            ))
            continue

        i += 1

    return IRFile(source_path=source_path, functions=functions)


# ── Analysis Functions ────────────────────────────────────────────────────────

def analyze_summary(ir: IRFile) -> dict:
    """High-level summary statistics."""
    total_funcs = len(ir.functions)
    total_blocks = sum(len(f.blocks) for f in ir.functions)
    total_insts = sum(
        len(b.instructions) for f in ir.functions for b in f.blocks
    )
    total_aliases = sum(
        len(b.aliases) for f in ir.functions for b in f.blocks
    )
    total_block_params = sum(
        len(b.params) for f in ir.functions for b in f.blocks
    )

    # Block param types
    param_type_counts = Counter()
    for f in ir.functions:
        for b in f.blocks:
            for _, ty in b.params:
                param_type_counts[ty] += 1

    # Blocks per function distribution
    blocks_per_func = [len(f.blocks) for f in ir.functions]
    insts_per_func = [
        sum(len(b.instructions) for b in f.blocks) for f in ir.functions
    ]

    return {
        "total_functions": total_funcs,
        "total_blocks": total_blocks,
        "total_instructions": total_insts,
        "total_aliases": total_aliases,
        "total_block_params": total_block_params,
        "block_param_types": dict(param_type_counts.most_common()),
        "avg_blocks_per_func": round(total_blocks / max(total_funcs, 1), 1),
        "avg_insts_per_func": round(total_insts / max(total_funcs, 1), 1),
        "avg_insts_per_block": round(total_insts / max(total_blocks, 1), 1),
        "max_blocks_in_func": max(blocks_per_func) if blocks_per_func else 0,
        "max_insts_in_func": max(insts_per_func) if insts_per_func else 0,
    }


def analyze_opcodes(ir: IRFile, top_n: int = 20) -> dict:
    """Instruction opcode frequency distribution."""
    opcode_counts = Counter()
    opcode_type_counts = Counter()

    for f in ir.functions:
        for b in f.blocks:
            for inst in b.instructions:
                opcode_counts[inst.opcode] += 1
                key = f"{inst.opcode}.{inst.type_suffix}" if inst.type_suffix else inst.opcode
                opcode_type_counts[key] += 1

    total = sum(opcode_counts.values())

    ranked = []
    for op, count in opcode_counts.most_common(top_n):
        ranked.append({
            "opcode": op,
            "count": count,
            "pct": round(100.0 * count / max(total, 1), 1),
        })

    typed_ranked = []
    for op, count in opcode_type_counts.most_common(top_n):
        typed_ranked.append({
            "opcode": op,
            "count": count,
            "pct": round(100.0 * count / max(total, 1), 1),
        })

    return {
        "total_instructions": total,
        "unique_opcodes": len(opcode_counts),
        "top_opcodes": ranked,
        "top_typed_opcodes": typed_ranked,
    }


def analyze_blocks(ir: IRFile, top_n: int = 20) -> dict:
    """Block size distribution and single-instruction block analysis."""
    size_dist = Counter()
    single_inst_opcodes = Counter()
    two_inst_patterns = Counter()
    three_inst_patterns = Counter()

    for f in ir.functions:
        for b in f.blocks:
            n = len(b.instructions)
            size_dist[n] += 1

            if n == 1:
                single_inst_opcodes[b.instructions[0].opcode] += 1
            elif n == 2:
                pattern = f"{b.instructions[0].opcode}+{b.instructions[1].opcode}"
                two_inst_patterns[pattern] += 1
            elif n == 3:
                pattern = "+".join(i.opcode for i in b.instructions[:3])
                three_inst_patterns[pattern] += 1

    total_blocks = sum(size_dist.values())

    return {
        "total_blocks": total_blocks,
        "size_distribution": [
            {"size": s, "count": c, "pct": round(100.0 * c / max(total_blocks, 1), 1)}
            for s, c in sorted(size_dist.items())[:30]
        ],
        "single_instruction_blocks": {
            "total": size_dist.get(1, 0),
            "by_opcode": [
                {"opcode": op, "count": c}
                for op, c in single_inst_opcodes.most_common(top_n)
            ],
        },
        "two_instruction_blocks": {
            "total": size_dist.get(2, 0),
            "top_patterns": [
                {"pattern": p, "count": c}
                for p, c in two_inst_patterns.most_common(top_n)
            ],
        },
        "three_instruction_blocks": {
            "total": size_dist.get(3, 0),
            "top_patterns": [
                {"pattern": p, "count": c}
                for p, c in three_inst_patterns.most_common(top_n)
            ],
        },
    }


def analyze_constants(ir: IRFile, top_n: int = 20) -> dict:
    """Constant value distribution and analysis."""
    iconst_values = Counter()
    iconst_types = Counter()
    f64const_values = Counter()

    for f in ir.functions:
        for b in f.blocks:
            for inst in b.instructions:
                if inst.opcode == "iconst":
                    val_str = inst.operands.strip()
                    iconst_types[inst.type_suffix or "untyped"] += 1
                    try:
                        if val_str.startswith('0x') or val_str.startswith('-0x'):
                            val = int(val_str.replace('_', ''), 16)
                        else:
                            val = int(val_str)
                        iconst_values[val] += 1
                    except ValueError:
                        iconst_values[val_str] += 1
                elif inst.opcode == "f64const":
                    f64const_values[inst.operands.strip()] += 1

    total_iconst = sum(iconst_values.values())

    # Small value breakdown
    small = sum(c for v, c in iconst_values.items() if isinstance(v, int) and abs(v) <= 10)

    return {
        "total_iconst": total_iconst,
        "total_f64const": sum(f64const_values.values()),
        "unique_iconst_values": len(iconst_values),
        "small_values_pct": round(100.0 * small / max(total_iconst, 1), 1),
        "iconst_by_type": dict(iconst_types.most_common()),
        "top_iconst_values": [
            {"value": v, "count": c, "pct": round(100.0 * c / max(total_iconst, 1), 1)}
            for v, c in iconst_values.most_common(top_n)
        ],
        "top_f64const_values": [
            {"value": v, "count": c}
            for v, c in f64const_values.most_common(top_n)
        ],
    }


def _parse_iconst_value(operands: str) -> Optional[int]:
    """Parse the integer value from an iconst operand string."""
    val_str = operands.strip()
    try:
        if val_str.startswith('0x') or val_str.startswith('-0x'):
            return int(val_str.replace('_', ''), 16)
        return int(val_str)
    except ValueError:
        return None


def analyze_redundant_iconst(ir: IRFile) -> dict:
    """Find iconst instructions that duplicate a value already defined in the same block."""
    total_redundant = 0
    redundant_by_value = Counter()

    for f in ir.functions:
        for b in f.blocks:
            seen = {}  # (type, value) -> first instruction index
            for idx, inst in enumerate(b.instructions):
                if inst.opcode == "iconst":
                    val = _parse_iconst_value(inst.operands)
                    ty = inst.type_suffix or "i64"
                    key = (ty, val)
                    if key in seen:
                        total_redundant += 1
                        redundant_by_value[val] += 1
                    else:
                        seen[key] = idx

    return {
        "total_redundant": total_redundant,
        "top_redundant_values": [
            {"value": v, "count": c}
            for v, c in redundant_by_value.most_common(20)
        ],
    }


def analyze_dead_values(ir: IRFile) -> dict:
    """Find values that are defined but never referenced in their function."""
    total_dead = 0
    dead_by_opcode = Counter()
    dead_by_value = Counter()  # for iconst

    for f in ir.functions:
        # Collect all defined values and all referenced values
        defined = {}  # value_name -> (opcode, block_name, operands)
        referenced = set()

        # Block params are defined
        for b in f.blocks:
            for val, _ in b.params:
                defined[val] = ("block_param", b.name, "")

            # Aliases: the alias value is defined, and references the target
            for a in b.aliases:
                defined[a.alias] = ("alias", b.name, a.target)
                referenced.add(a.target)

            for inst in b.instructions:
                # Results are defined
                for r in inst.results:
                    defined[r] = (inst.opcode, b.name, inst.operands)

                # Find all value references in operands + raw line
                # We look at operands, but also need to check block args
                for m in RE_VALUE_REF.finditer(inst.operands):
                    referenced.add(f"v{m.group(1)}")

                # For instructions without results (side effects), the operands
                # reference values. Also check raw for brif/jump block args.
                # Parse vN references from the raw line but exclude the result values
                for m in RE_VALUE_REF.finditer(inst.raw):
                    vname = f"v{m.group(1)}"
                    if vname not in inst.results:
                        referenced.add(vname)

        # Find dead values (defined but not referenced)
        for val, (opcode, block, operands) in defined.items():
            if val not in referenced and opcode not in ("block_param", "alias"):
                total_dead += 1
                dead_by_opcode[opcode] += 1
                if opcode == "iconst":
                    v = _parse_iconst_value(operands)
                    dead_by_value[v] += 1

    return {
        "total_dead": total_dead,
        "dead_by_opcode": [
            {"opcode": op, "count": c}
            for op, c in dead_by_opcode.most_common(20)
        ],
        "dead_iconst_by_value": [
            {"value": v, "count": c}
            for v, c in dead_by_value.most_common(20)
        ],
    }


def analyze_patterns(ir: IRFile, top_n: int = 20) -> dict:
    """Find repeated multi-instruction patterns within blocks."""
    # N-gram analysis (2, 3, 4, 5 instruction sequences)
    results = {}

    for n in [2, 3, 4, 5]:
        pattern_counts = Counter()
        for f in ir.functions:
            for b in f.blocks:
                opcodes = [i.opcode for i in b.instructions]
                for i in range(len(opcodes) - n + 1):
                    pattern = "+".join(opcodes[i:i+n])
                    pattern_counts[pattern] += 1

        results[f"{n}-gram"] = [
            {"pattern": p, "count": c}
            for p, c in pattern_counts.most_common(top_n)
        ]

    # Full-block patterns (the entire block as an opcode sequence)
    full_block_patterns = Counter()
    for f in ir.functions:
        for b in f.blocks:
            pattern = "+".join(i.opcode for i in b.instructions)
            full_block_patterns[pattern] += 1

    results["full_block_patterns"] = [
        {"pattern": p, "count": c, "num_insts": p.count('+') + 1}
        for p, c in full_block_patterns.most_common(top_n)
    ]

    return results


def analyze_diamonds(ir: IRFile) -> dict:
    """Find diamond patterns: brif -> two arms -> merge block."""
    diamonds = []

    for f in ir.functions:
        block_map = {b.name: b for b in f.blocks}

        for b in f.blocks:
            if not b.instructions:
                continue
            last = b.instructions[-1]
            if last.opcode != "brif":
                continue

            # Parse brif targets
            # brif vN, blockA(args), blockB(args)
            brif_raw = last.raw
            # Remove trailing comment
            brif_clean = RE_TRAILING_COMMENT.sub('', brif_raw).strip()

            # Extract block references from brif
            # Pattern: brif vN, blockA[(args)], blockB[(args)]
            m = re.match(
                r'brif\s+v\d+,\s*(block\d+)(?:\([^)]*\))?,\s*(block\d+)(?:\([^)]*\))?',
                brif_clean
            )
            if not m:
                continue

            true_name = m.group(1)
            false_name = m.group(2)

            true_block = block_map.get(true_name)
            false_block = block_map.get(false_name)

            if not true_block or not false_block:
                continue

            # Check if both arms jump to the same merge block
            if (len(true_block.instructions) >= 1 and
                true_block.instructions[-1].opcode == "jump" and
                len(false_block.instructions) >= 1 and
                false_block.instructions[-1].opcode == "jump"):

                true_target = re.match(r'(block\d+)', true_block.instructions[-1].operands)
                false_target = re.match(r'(block\d+)', false_block.instructions[-1].operands)

                if true_target and false_target and true_target.group(1) == false_target.group(1):
                    merge_block = true_target.group(1)
                    true_size = len(true_block.instructions)
                    false_size = len(false_block.instructions)

                    # Check if both arms are just iconst+jump (perfect diamond)
                    is_perfect = (
                        true_size == 2 and false_size == 2 and
                        true_block.instructions[0].opcode == "iconst" and
                        false_block.instructions[0].opcode == "iconst"
                    )

                    # Check if arms are all-constant+jump
                    true_all_const = all(
                        i.opcode in ("iconst", "f64const", "jump")
                        for i in true_block.instructions
                    )
                    false_all_const = all(
                        i.opcode in ("iconst", "f64const", "jump")
                        for i in false_block.instructions
                    )

                    diamonds.append({
                        "source": b.name,
                        "true_arm": true_name,
                        "false_arm": false_name,
                        "merge": merge_block,
                        "true_size": true_size,
                        "false_size": false_size,
                        "is_perfect": is_perfect,
                        "all_constant": true_all_const and false_all_const,
                        "func": f.vole_name,
                    })

    perfect = [d for d in diamonds if d["is_perfect"]]
    all_const = [d for d in diamonds if d["all_constant"] and not d["is_perfect"]]
    other = [d for d in diamonds if not d["all_constant"]]

    return {
        "total_diamonds": len(diamonds),
        "perfect_diamonds": len(perfect),
        "all_constant_diamonds": len(all_const),
        "other_diamonds": len(other),
        "sample_perfect": perfect[:5],
        "sample_other": other[:5],
    }


def analyze_bool_truthiness(ir: IRFile) -> dict:
    """Find icmp_imm ne vN, 0 followed by brif — redundant bool check."""
    count = 0
    in_two_inst_blocks = 0
    sources = Counter()  # which types are being compared
    examples = []

    for f in ir.functions:
        for b in f.blocks:
            insts = b.instructions
            for i in range(len(insts) - 1):
                curr = insts[i]
                nxt = insts[i + 1]
                if (curr.opcode == "icmp_imm" and nxt.opcode == "brif" and
                    "ne" in curr.operands.split()[0:1] and
                    curr.operands.strip().endswith("0")):
                    # Check if the result of icmp_imm feeds brif
                    if curr.results and nxt.operands.strip().startswith(curr.results[0]):
                        count += 1
                        ty = curr.type_suffix or "untyped"
                        sources[ty] += 1
                        if len(insts) == 2:
                            in_two_inst_blocks += 1
                        if len(examples) < 5:
                            examples.append({
                                "func": f.vole_name,
                                "block": b.name,
                                "icmp": curr.raw,
                                "brif": nxt.raw,
                            })

    return {
        "total": count,
        "in_two_inst_blocks": in_two_inst_blocks,
        "by_type": dict(sources.most_common()),
        "examples": examples,
    }


def analyze_call_indirect(ir: IRFile) -> dict:
    """Find call_indirect with constant function pointers."""
    total_call_indirect = 0
    const_ptr_call_indirect = 0
    unique_ptrs = set()

    for f in ir.functions:
        for b in f.blocks:
            # Build a map of values defined as iconst in this block
            iconst_vals = set()
            for inst in b.instructions:
                if inst.opcode == "iconst" and inst.results:
                    iconst_vals.add(inst.results[0])

                if inst.opcode == "call_indirect":
                    total_call_indirect += 1
                    # call_indirect sigN, vPtr(args)
                    m = re.match(r'sig\d+,\s*(v\d+)', inst.operands)
                    if m and m.group(1) in iconst_vals:
                        const_ptr_call_indirect += 1

    # Also check func_addr pattern
    func_addr_indirect = 0
    for f in ir.functions:
        for b in f.blocks:
            func_addr_vals = set()
            for inst in b.instructions:
                if inst.opcode == "func_addr" and inst.results:
                    func_addr_vals.add(inst.results[0])
                if inst.opcode == "call_indirect":
                    m = re.match(r'sig\d+,\s*(v\d+)', inst.operands)
                    if m and m.group(1) in func_addr_vals:
                        func_addr_indirect += 1

    return {
        "total_call_indirect": total_call_indirect,
        "with_constant_ptr": const_ptr_call_indirect,
        "with_func_addr": func_addr_indirect,
        "devirtualizable_pct": round(
            100.0 * const_ptr_call_indirect / max(total_call_indirect, 1), 1
        ),
    }


def analyze_trampolines(ir: IRFile) -> dict:
    """Check for remaining trampoline blocks (should be 0 after cleanup_cfg)."""
    no_arg = 0        # jump blockN (no block params on this block, no args on jump)
    forward_arg = 0   # jump blockN(args) where args match block params
    passthrough = 0   # jump blockN(args) with block params, args don't match

    for f in ir.functions:
        for b in f.blocks:
            if len(b.instructions) != 1:
                continue
            inst = b.instructions[0]
            if inst.opcode != "jump":
                continue

            # Parse jump target and args
            m = re.match(r'(block\d+)(?:\(([^)]*)\))?', inst.operands)
            if not m:
                continue

            args_str = m.group(2)
            has_args = bool(args_str and args_str.strip())
            has_params = len(b.params) > 0

            if not has_args and not has_params:
                no_arg += 1
            elif has_args and not has_params:
                forward_arg += 1
            elif has_args and has_params:
                # Check if it's identity passthrough
                if args_str:
                    args = [a.strip() for a in args_str.split(',')]
                    param_vals = [p[0] for p in b.params]
                    if args == param_vals:
                        passthrough += 1

    return {
        "no_arg_trampolines": no_arg,
        "forward_arg_trampolines": forward_arg,
        "passthrough_trampolines": passthrough,
        "total_remaining": no_arg + forward_arg + passthrough,
    }


# ── MIR Parsing ──────────────────────────────────────────────────────────────

@dataclass
class MIRInstruction:
    """A single MIR (assembly) instruction."""
    mnemonic: str
    operands: str
    raw: str
    comment: str = ""

@dataclass
class MIRBlock:
    """A MIR basic block."""
    label: str
    instructions: list[MIRInstruction]

@dataclass
class MIRFunction:
    """A MIR function."""
    vole_name: str
    blocks: list[MIRBlock]

@dataclass
class MIRFile:
    """Complete parsed MIR file."""
    source_path: str
    functions: list[MIRFunction]


RE_MIR_LABEL = re.compile(r'^\.L(\d+):$')
RE_MIR_INST = re.compile(r'^\s+(\w+)\s*(.*)$')


def parse_mir(text: str) -> MIRFile:
    """Parse MIR (machine IR / assembly) text."""
    lines = text.splitlines()
    source_path = ""
    functions = []

    i = 0
    while i < len(lines):
        line = lines[i].strip()

        m = RE_FILE_COMMENT.match(line)
        if m and not source_path:
            source_path = m.group(1)
            i += 1
            continue

        m = RE_FUNC_COMMENT.match(line)
        if m:
            vole_name = m.group(1)
            i += 1
            blocks = []
            current_block = None

            while i < len(lines):
                raw = lines[i]
                stripped = raw.strip()

                # Next function or end
                if RE_FUNC_COMMENT.match(stripped) or RE_FILE_COMMENT.match(stripped):
                    break

                if not stripped:
                    i += 1
                    continue

                # Label
                ml = RE_MIR_LABEL.match(stripped)
                if ml:
                    if current_block:
                        blocks.append(current_block)
                    current_block = MIRBlock(label=f".L{ml.group(1)}", instructions=[])
                    i += 1
                    continue

                # Instruction
                mi = RE_MIR_INST.match(raw)
                if mi:
                    mnemonic = mi.group(1)
                    rest = mi.group(2).strip()

                    # Split off comment
                    comment = ""
                    if ";;" in rest:
                        parts = rest.split(";;", 1)
                        rest = parts[0].strip()
                        comment = parts[1].strip()
                    elif ";" in rest:
                        parts = rest.split(";", 1)
                        rest = parts[0].strip()
                        comment = parts[1].strip()

                    if current_block is None:
                        # Instructions before any label (prologue)
                        current_block = MIRBlock(label=".Lprologue", instructions=[])

                    current_block.instructions.append(MIRInstruction(
                        mnemonic=mnemonic, operands=rest, raw=stripped, comment=comment
                    ))

                i += 1

            if current_block:
                blocks.append(current_block)
            functions.append(MIRFunction(vole_name=vole_name, blocks=blocks))
            continue

        i += 1

    return MIRFile(source_path=source_path, functions=functions)


def analyze_mir_summary(mir: MIRFile) -> dict:
    """MIR summary statistics."""
    total_funcs = len(mir.functions)
    total_blocks = sum(len(f.blocks) for f in mir.functions)
    total_insts = sum(
        len(b.instructions) for f in mir.functions for b in f.blocks
    )

    mnemonic_counts = Counter()
    for f in mir.functions:
        for b in f.blocks:
            for inst in b.instructions:
                mnemonic_counts[inst.mnemonic] += 1

    return {
        "total_functions": total_funcs,
        "total_blocks": total_blocks,
        "total_instructions": total_insts,
        "top_mnemonics": [
            {"mnemonic": m, "count": c, "pct": round(100.0 * c / max(total_insts, 1), 1)}
            for m, c in mnemonic_counts.most_common(20)
        ],
    }


# ── Output Formatting ────────────────────────────────────────────────────────

def format_table(headers: list[str], rows: list[list], align: list[str] = None):
    """Format data as an aligned text table."""
    if not rows:
        return "(no data)\n"

    # Convert all cells to strings
    str_rows = [[str(c) for c in row] for row in rows]

    # Calculate column widths
    widths = [len(h) for h in headers]
    for row in str_rows:
        for i, cell in enumerate(row):
            if i < len(widths):
                widths[i] = max(widths[i], len(cell))

    if align is None:
        align = ['l'] * len(headers)

    def fmt_cell(cell, width, a):
        if a == 'r':
            return cell.rjust(width)
        return cell.ljust(width)

    lines = []
    header_line = "  ".join(fmt_cell(h, widths[i], align[i]) for i, h in enumerate(headers))
    lines.append(header_line)
    lines.append("  ".join("-" * w for w in widths))
    for row in str_rows:
        line = "  ".join(
            fmt_cell(row[i] if i < len(row) else "", widths[i], align[i])
            for i in range(len(headers))
        )
        lines.append(line)

    return "\n".join(lines) + "\n"


def print_summary(data: dict):
    print("=== IR Summary ===\n")
    rows = [
        ["Functions", f"{data['total_functions']:,}"],
        ["Blocks", f"{data['total_blocks']:,}"],
        ["Instructions", f"{data['total_instructions']:,}"],
        ["Aliases", f"{data['total_aliases']:,}"],
        ["Block Params", f"{data['total_block_params']:,}"],
        ["Avg Blocks/Func", str(data['avg_blocks_per_func'])],
        ["Avg Insts/Func", str(data['avg_insts_per_func'])],
        ["Avg Insts/Block", str(data['avg_insts_per_block'])],
        ["Max Blocks in Func", f"{data['max_blocks_in_func']:,}"],
        ["Max Insts in Func", f"{data['max_insts_in_func']:,}"],
    ]
    print(format_table(["Metric", "Value"], rows, ['l', 'r']))

    if data['block_param_types']:
        print("Block param types:")
        for ty, count in sorted(data['block_param_types'].items(), key=lambda x: -x[1]):
            print(f"  {ty}: {count:,}")
        print()


def print_opcodes(data: dict):
    print("=== Opcode Distribution ===\n")
    print(f"Total instructions: {data['total_instructions']:,}")
    print(f"Unique opcodes: {data['unique_opcodes']}\n")

    rows = [[d['opcode'], f"{d['count']:,}", f"{d['pct']}%"] for d in data['top_opcodes']]
    print(format_table(["Opcode", "Count", "%"], rows, ['l', 'r', 'r']))

    print("\nWith type suffixes:\n")
    rows = [[d['opcode'], f"{d['count']:,}", f"{d['pct']}%"] for d in data['top_typed_opcodes']]
    print(format_table(["Opcode.Type", "Count", "%"], rows, ['l', 'r', 'r']))


def print_blocks(data: dict):
    print("=== Block Analysis ===\n")
    print(f"Total blocks: {data['total_blocks']:,}\n")

    print("Size distribution:")
    rows = [[str(d['size']), f"{d['count']:,}", f"{d['pct']}%"] for d in data['size_distribution']]
    print(format_table(["Size", "Count", "%"], rows, ['r', 'r', 'r']))

    s1 = data['single_instruction_blocks']
    print(f"\nSingle-instruction blocks: {s1['total']:,}")
    rows = [[d['opcode'], f"{d['count']:,}"] for d in s1['by_opcode']]
    print(format_table(["Opcode", "Count"], rows, ['l', 'r']))

    s2 = data['two_instruction_blocks']
    print(f"\nTwo-instruction blocks: {s2['total']:,}")
    rows = [[d['pattern'], f"{d['count']:,}"] for d in s2['top_patterns']]
    print(format_table(["Pattern", "Count"], rows, ['l', 'r']))

    s3 = data['three_instruction_blocks']
    print(f"\nThree-instruction blocks: {s3['total']:,}")
    rows = [[d['pattern'], f"{d['count']:,}"] for d in s3['top_patterns']]
    print(format_table(["Pattern", "Count"], rows, ['l', 'r']))


def print_constants(data: dict):
    print("=== Constant Analysis ===\n")
    print(f"Total iconst: {data['total_iconst']:,}")
    print(f"Total f64const: {data['total_f64const']:,}")
    print(f"Unique iconst values: {data['unique_iconst_values']:,}")
    print(f"Small values (|v| <= 10): {data['small_values_pct']}%\n")

    print("By type:")
    for ty, count in sorted(data['iconst_by_type'].items(), key=lambda x: -x[1]):
        print(f"  {ty}: {count:,}")
    print()

    rows = [[str(d['value']), f"{d['count']:,}", f"{d['pct']}%"] for d in data['top_iconst_values']]
    print("Top iconst values:")
    print(format_table(["Value", "Count", "%"], rows, ['r', 'r', 'r']))


def print_analysis(name: str, data: dict):
    print(f"=== {name} ===\n")
    for key, val in data.items():
        if isinstance(val, list):
            print(f"{key}:")
            if val and isinstance(val[0], dict):
                headers = list(val[0].keys())
                rows = [[str(d.get(h, "")) for h in headers] for d in val]
                print(format_table(headers, rows))
            else:
                for item in val:
                    print(f"  {item}")
            print()
        elif isinstance(val, dict):
            print(f"{key}:")
            for k2, v2 in val.items():
                print(f"  {k2}: {v2}")
            print()
        else:
            print(f"{key}: {val}")
    print()


# ── Main ──────────────────────────────────────────────────────────────────────

ANALYSES = {
    "summary": ("Summary", analyze_summary, print_summary),
    "opcodes": ("Opcode Distribution", analyze_opcodes, print_opcodes),
    "blocks": ("Block Analysis", analyze_blocks, print_blocks),
    "constants": ("Constant Analysis", analyze_constants, print_constants),
    "patterns": ("Pattern Analysis", analyze_patterns, None),
    "dead-values": ("Dead Value Analysis", analyze_dead_values, None),
    "redundant-iconst": ("Redundant iconst", analyze_redundant_iconst, None),
    "diamonds": ("Diamond Patterns", analyze_diamonds, None),
    "bool-truthiness": ("Bool Truthiness", analyze_bool_truthiness, None),
    "call-indirect": ("call_indirect Analysis", analyze_call_indirect, None),
    "trampolines": ("Trampoline Check", analyze_trampolines, None),
}


def main():
    parser = argparse.ArgumentParser(description="Analyze Vole Cranelift IR / MIR output")
    parser.add_argument("input", nargs="?", help="IR/MIR file (default: stdin)")
    parser.add_argument("--mir", action="store_true", help="Parse as MIR instead of IR")
    parser.add_argument("--analysis", "-a", default="summary",
                        help=f"Analysis to run: {', '.join(ANALYSES.keys())}, all")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    parser.add_argument("--top", type=int, default=20, help="Top N results (default: 20)")
    args = parser.parse_args()

    # Read input
    if args.input:
        with open(args.input) as f:
            text = f.read()
    else:
        text = sys.stdin.read()

    if args.mir:
        mir = parse_mir(text)
        data = analyze_mir_summary(mir)
        if args.json:
            print(json.dumps(data, indent=2))
        else:
            print_analysis("MIR Summary", data)
        return

    # Parse IR
    ir = parse_ir(text)

    # Run analyses
    if args.analysis == "all":
        to_run = list(ANALYSES.keys())
    else:
        to_run = [a.strip() for a in args.analysis.split(",")]

    all_results = {}
    for name in to_run:
        if name not in ANALYSES:
            print(f"Unknown analysis: {name}", file=sys.stderr)
            print(f"Available: {', '.join(ANALYSES.keys())}", file=sys.stderr)
            sys.exit(1)

        label, func, printer = ANALYSES[name]

        # Some analyses accept top_n
        import inspect
        sig = inspect.signature(func)
        if "top_n" in sig.parameters:
            result = func(ir, top_n=args.top)
        else:
            result = func(ir)

        all_results[name] = result

        if not args.json:
            if printer:
                printer(result)
            else:
                print_analysis(label, result)

    if args.json:
        if len(to_run) == 1:
            print(json.dumps(all_results[to_run[0]], indent=2))
        else:
            print(json.dumps(all_results, indent=2))


if __name__ == "__main__":
    main()
