#!/usr/bin/env python3
"""
Compare IR (pre-Cranelift) and MIR (post-Cranelift) output to understand
what Cranelift's optimizer handles vs what we should optimize ourselves.

Usage:
    python3 ir-mir-compare.py <ir-file> <mir-file>
    python3 ir-mir-compare.py <ir-file> <mir-file> --json

Produces a side-by-side comparison showing:
- Function count and size changes
- Block elimination rate
- Instruction reduction
- Per-function analysis of what Cranelift optimizes away
"""

import sys
import re
import json
import argparse
from collections import Counter, defaultdict


# ── Lightweight IR parsing (just counts, not full AST) ────────────────────────

def parse_ir_functions(text: str) -> dict:
    """Parse IR into per-function stats."""
    functions = {}
    current_func = None
    current_blocks = 0
    current_insts = 0
    current_opcodes = Counter()
    current_block_sizes = []
    current_block_insts = 0
    in_block = False

    for line in text.splitlines():
        stripped = line.strip()

        m = re.match(r'^// func (.+)$', stripped)
        if m:
            if current_func:
                if in_block:
                    current_block_sizes.append(current_block_insts)
                functions[current_func] = {
                    'blocks': current_blocks,
                    'instructions': current_insts,
                    'opcodes': dict(current_opcodes),
                    'block_sizes': current_block_sizes,
                }
            current_func = m.group(1)
            current_blocks = 0
            current_insts = 0
            current_opcodes = Counter()
            current_block_sizes = []
            current_block_insts = 0
            in_block = False
            continue

        if re.match(r'^block\d+', stripped):
            if in_block:
                current_block_sizes.append(current_block_insts)
            current_blocks += 1
            current_block_insts = 0
            in_block = True
            continue

        if stripped == '}':
            if in_block:
                current_block_sizes.append(current_block_insts)
                in_block = False
            continue

        # Instructions (indented, not aliases, not preamble)
        if in_block and stripped and not stripped.startswith('//'):
            # Skip aliases (vN -> vM)
            if re.match(r'^v\d+\s*->\s*v\d+$', stripped):
                continue
            # Skip preamble
            if re.match(r'^(sig|fn|ss|gv)\d+\s*=', stripped):
                continue

            # Strip trailing comment
            clean = re.sub(r'\s*;[^;].*$', '', stripped).strip()
            if not clean:
                continue

            # Extract opcode
            m2 = re.match(r'(?:(?:v\d+(?:,\s*v\d+)*)\s*=\s*)?([a-z_]+)', clean)
            if m2:
                current_insts += 1
                current_block_insts += 1
                current_opcodes[m2.group(1)] += 1

    if current_func:
        if in_block:
            current_block_sizes.append(current_block_insts)
        functions[current_func] = {
            'blocks': current_blocks,
            'instructions': current_insts,
            'opcodes': dict(current_opcodes),
            'block_sizes': current_block_sizes,
        }

    return functions


def parse_mir_functions(text: str) -> dict:
    """Parse MIR into per-function stats."""
    functions = {}
    current_func = None
    current_blocks = 0
    current_insts = 0
    current_mnemonics = Counter()
    current_block_insts = 0
    current_block_sizes = []

    for line in text.splitlines():
        stripped = line.strip()

        m = re.match(r'^// func (.+)$', stripped)
        if m:
            if current_func:
                if current_block_insts > 0:
                    current_block_sizes.append(current_block_insts)
                functions[current_func] = {
                    'blocks': current_blocks,
                    'instructions': current_insts,
                    'mnemonics': dict(current_mnemonics),
                    'block_sizes': current_block_sizes,
                }
            current_func = m.group(1)
            current_blocks = 0
            current_insts = 0
            current_mnemonics = Counter()
            current_block_sizes = []
            current_block_insts = 0
            continue

        if not current_func:
            continue

        # Label
        if re.match(r'^\.\w+:', stripped):
            if current_block_insts > 0:
                current_block_sizes.append(current_block_insts)
            current_blocks += 1
            current_block_insts = 0
            continue

        # MIR instruction (indented)
        if line.startswith('  ') and stripped and not stripped.startswith('//'):
            m2 = re.match(r'^(\w+)', stripped)
            if m2:
                mnemonic = m2.group(1)
                current_insts += 1
                current_block_insts += 1
                current_mnemonics[mnemonic] += 1
                # Count the first block (prologue before any label)
                if current_blocks == 0:
                    current_blocks = 1

    if current_func:
        if current_block_insts > 0:
            current_block_sizes.append(current_block_insts)
        functions[current_func] = {
            'blocks': current_blocks,
            'instructions': current_insts,
            'mnemonics': dict(current_mnemonics),
            'block_sizes': current_block_sizes,
        }

    return functions


# ── Comparison ────────────────────────────────────────────────────────────────

def compare(ir_funcs: dict, mir_funcs: dict) -> dict:
    """Compare IR and MIR stats."""

    # Match functions between IR and MIR
    common = set(ir_funcs.keys()) & set(mir_funcs.keys())
    ir_only = set(ir_funcs.keys()) - set(mir_funcs.keys())
    mir_only = set(mir_funcs.keys()) - set(ir_funcs.keys())

    # Aggregate stats
    ir_total_blocks = sum(f['blocks'] for f in ir_funcs.values())
    ir_total_insts = sum(f['instructions'] for f in ir_funcs.values())
    mir_total_blocks = sum(f['blocks'] for f in mir_funcs.values())
    mir_total_insts = sum(f['instructions'] for f in mir_funcs.values())

    # Per-function comparison
    func_comparisons = []
    for name in sorted(common):
        ir = ir_funcs[name]
        mir = mir_funcs[name]
        block_reduction = ir['blocks'] - mir['blocks']
        inst_reduction = ir['instructions'] - mir['instructions']

        func_comparisons.append({
            'name': name,
            'ir_blocks': ir['blocks'],
            'mir_blocks': mir['blocks'],
            'block_reduction': block_reduction,
            'block_reduction_pct': round(100.0 * block_reduction / max(ir['blocks'], 1), 1),
            'ir_insts': ir['instructions'],
            'mir_insts': mir['instructions'],
            'inst_reduction': inst_reduction,
            'inst_reduction_pct': round(100.0 * inst_reduction / max(ir['instructions'], 1), 1),
        })

    # Sort by absolute instruction reduction (biggest savings first)
    func_comparisons.sort(key=lambda x: -x['inst_reduction'])

    # IR opcode aggregation
    ir_opcodes = Counter()
    for f in ir_funcs.values():
        for op, count in f.get('opcodes', {}).items():
            ir_opcodes[op] += count

    # MIR mnemonic aggregation
    mir_mnemonics = Counter()
    for f in mir_funcs.values():
        for m, count in f.get('mnemonics', {}).items():
            mir_mnemonics[m] += count

    # Block size distributions
    ir_block_sizes = Counter()
    mir_block_sizes = Counter()
    for f in ir_funcs.values():
        for s in f.get('block_sizes', []):
            ir_block_sizes[s] += 1
    for f in mir_funcs.values():
        for s in f.get('block_sizes', []):
            mir_block_sizes[s] += 1

    # Compute what Cranelift eliminated
    # Single-inst IR blocks that become zero blocks in MIR
    ir_single_blocks = ir_block_sizes.get(1, 0)
    mir_single_blocks = mir_block_sizes.get(1, 0)

    return {
        'summary': {
            'ir_functions': len(ir_funcs),
            'mir_functions': len(mir_funcs),
            'common_functions': len(common),
            'ir_only_functions': len(ir_only),
            'mir_only_functions': len(mir_only),
            'ir_total_blocks': ir_total_blocks,
            'mir_total_blocks': mir_total_blocks,
            'block_reduction': ir_total_blocks - mir_total_blocks,
            'block_reduction_pct': round(100.0 * (ir_total_blocks - mir_total_blocks) / max(ir_total_blocks, 1), 1),
            'ir_total_instructions': ir_total_insts,
            'mir_total_instructions': mir_total_insts,
            'inst_reduction': ir_total_insts - mir_total_insts,
            'inst_reduction_pct': round(100.0 * (ir_total_insts - mir_total_insts) / max(ir_total_insts, 1), 1),
            'avg_ir_insts_per_func': round(ir_total_insts / max(len(ir_funcs), 1), 1),
            'avg_mir_insts_per_func': round(mir_total_insts / max(len(mir_funcs), 1), 1),
        },
        'block_size_comparison': {
            'ir_single_inst_blocks': ir_single_blocks,
            'mir_single_inst_blocks': mir_single_blocks,
            'ir_size_dist': {str(k): v for k, v in sorted(ir_block_sizes.items())[:15]},
            'mir_size_dist': {str(k): v for k, v in sorted(mir_block_sizes.items())[:15]},
        },
        'ir_top_opcodes': [
            {'opcode': op, 'count': c, 'pct': round(100.0 * c / max(ir_total_insts, 1), 1)}
            for op, c in ir_opcodes.most_common(15)
        ],
        'mir_top_mnemonics': [
            {'mnemonic': m, 'count': c, 'pct': round(100.0 * c / max(mir_total_insts, 1), 1)}
            for m, c in mir_mnemonics.most_common(15)
        ],
        'top_reductions': func_comparisons[:20],
        'bottom_reductions': func_comparisons[-10:] if len(func_comparisons) > 10 else [],
        'functions_that_grew': [
            f for f in func_comparisons if f['inst_reduction'] < 0
        ][:10],
    }


# ── Output ────────────────────────────────────────────────────────────────────

def fmt_table(headers, rows, align=None):
    if not rows:
        return "(no data)\n"
    str_rows = [[str(c) for c in row] for row in rows]
    widths = [len(h) for h in headers]
    for row in str_rows:
        for i, cell in enumerate(row):
            if i < len(widths):
                widths[i] = max(widths[i], len(cell))
    if align is None:
        align = ['l'] * len(headers)

    def fmt(cell, w, a):
        return cell.rjust(w) if a == 'r' else cell.ljust(w)

    lines = []
    lines.append("  ".join(fmt(h, widths[i], align[i]) for i, h in enumerate(headers)))
    lines.append("  ".join("-" * w for w in widths))
    for row in str_rows:
        lines.append("  ".join(fmt(row[i] if i < len(row) else "", widths[i], align[i]) for i in range(len(headers))))
    return "\n".join(lines) + "\n"


def print_comparison(data: dict):
    s = data['summary']

    print("=== IR vs MIR Comparison ===\n")
    rows = [
        ["Functions (IR)", f"{s['ir_functions']:,}"],
        ["Functions (MIR)", f"{s['mir_functions']:,}"],
        ["Common functions", f"{s['common_functions']:,}"],
        ["", ""],
        ["Blocks (IR)", f"{s['ir_total_blocks']:,}"],
        ["Blocks (MIR)", f"{s['mir_total_blocks']:,}"],
        ["Block reduction", f"{s['block_reduction']:,} ({s['block_reduction_pct']}%)"],
        ["", ""],
        ["Instructions (IR)", f"{s['ir_total_instructions']:,}"],
        ["Instructions (MIR)", f"{s['mir_total_instructions']:,}"],
        ["Instruction reduction", f"{s['inst_reduction']:,} ({s['inst_reduction_pct']}%)"],
        ["", ""],
        ["Avg insts/func (IR)", str(s['avg_ir_insts_per_func'])],
        ["Avg insts/func (MIR)", str(s['avg_mir_insts_per_func'])],
    ]
    print(fmt_table(["Metric", "Value"], rows, ['l', 'r']))

    # Block size comparison
    bs = data['block_size_comparison']
    print(f"Single-instruction blocks: IR={bs['ir_single_inst_blocks']}, MIR={bs['mir_single_inst_blocks']}\n")

    print("Block size distribution (IR vs MIR):")
    all_sizes = sorted(set(list(bs['ir_size_dist'].keys()) + list(bs['mir_size_dist'].keys())), key=lambda x: int(x))
    rows = []
    for size in all_sizes[:20]:
        ir_count = bs['ir_size_dist'].get(size, 0)
        mir_count = bs['mir_size_dist'].get(size, 0)
        rows.append([size, f"{ir_count:,}", f"{mir_count:,}"])
    print(fmt_table(["Size", "IR", "MIR"], rows, ['r', 'r', 'r']))

    # Top IR opcodes
    print("Top IR opcodes:")
    rows = [[d['opcode'], f"{d['count']:,}", f"{d['pct']}%"] for d in data['ir_top_opcodes']]
    print(fmt_table(["Opcode", "Count", "%"], rows, ['l', 'r', 'r']))

    # Top MIR mnemonics
    print("Top MIR mnemonics:")
    rows = [[d['mnemonic'], f"{d['count']:,}", f"{d['pct']}%"] for d in data['mir_top_mnemonics']]
    print(fmt_table(["Mnemonic", "Count", "%"], rows, ['l', 'r', 'r']))

    # Top reductions
    print("Functions with biggest instruction reduction (IR → MIR):")
    rows = []
    for f in data['top_reductions'][:15]:
        name = f['name']
        if len(name) > 60:
            name = "..." + name[-57:]
        rows.append([
            name,
            str(f['ir_blocks']), str(f['mir_blocks']),
            str(f['ir_insts']), str(f['mir_insts']),
            f"-{f['inst_reduction']} ({f['inst_reduction_pct']}%)",
        ])
    print(fmt_table(
        ["Function", "IR Blk", "MIR Blk", "IR Inst", "MIR Inst", "Reduction"],
        rows, ['l', 'r', 'r', 'r', 'r', 'r']
    ))

    # Functions that grew
    grew = data['functions_that_grew']
    if grew:
        print(f"Functions that GREW ({len(grew)} total):")
        rows = []
        for f in grew[:10]:
            name = f['name']
            if len(name) > 60:
                name = "..." + name[-57:]
            rows.append([
                name,
                str(f['ir_insts']), str(f['mir_insts']),
                f"+{-f['inst_reduction']}",
            ])
        print(fmt_table(["Function", "IR Inst", "MIR Inst", "Growth"], rows, ['l', 'r', 'r', 'r']))


def main():
    parser = argparse.ArgumentParser(description="Compare Vole IR and MIR output")
    parser.add_argument("ir_file", help="IR file (from vole inspect ir)")
    parser.add_argument("mir_file", help="MIR file (from vole inspect mir)")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    with open(args.ir_file) as f:
        ir_text = f.read()
    with open(args.mir_file) as f:
        mir_text = f.read()

    ir_funcs = parse_ir_functions(ir_text)
    mir_funcs = parse_mir_functions(mir_text)
    result = compare(ir_funcs, mir_funcs)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_comparison(result)


if __name__ == "__main__":
    main()
