// src/commands/mir_format.rs
//! Post-processor for Cranelift MIR (VCode) output.
//!
//! Cleans up the raw disassembly for better readability:
//! - Normalizes instruction spacing
//! - Compresses verbose unwind directives
//! - Fixes conditional jump formatting

use std::fmt::Write;

/// Format raw Cranelift VCode output for better readability.
pub fn format_mir(raw: &str) -> String {
    let mut output = String::with_capacity(raw.len());

    for line in raw.lines() {
        let formatted = format_line(line);
        // Skip empty lines (from stripped annotations)
        if !formatted.is_empty() {
            writeln!(output, "{}", formatted).unwrap();
        }
    }

    output
}

fn format_line(line: &str) -> String {
    let trimmed = line.trim();

    // Skip empty lines
    if trimmed.is_empty() {
        return String::new();
    }

    // Handle block labels - rename to .LN format
    if trimmed.starts_with("block") && trimmed.ends_with(':') {
        let num = trimmed
            .strip_prefix("block")
            .and_then(|s| s.strip_suffix(':'))
            .unwrap_or("?");
        return format!(".L{}:", num);
    }

    // Strip unwind directives (metadata only, no instructions)
    if trimmed.starts_with("unwind ") {
        return String::new();
    }

    // Handle conditional jumps with semicolon (e.g., "jl label6; j label5")
    if trimmed.contains("; j ") {
        return format_conditional_jump(trimmed);
    }

    // Handle regular instructions - normalize spacing and fix label refs
    format_instruction(trimmed)
}

/// Format conditional jumps.
/// "jl label6; j label5" -> "jl label6\n  j  label5"
fn format_conditional_jump(line: &str) -> String {
    if let Some((taken, fallthrough)) = line.split_once("; ") {
        let taken_fmt = format_instruction(taken.trim());
        let fallthrough_fmt = format_instruction(fallthrough.trim());
        format!(
            "{:<28} ; taken\n{:<28} ; fallthrough",
            taken_fmt, fallthrough_fmt
        )
    } else {
        format_instruction(line)
    }
}

/// Normalize instruction spacing.
/// "movq %rax, %rdi" -> "  movq    %rax, %rdi"
fn format_instruction(line: &str) -> String {
    let trimmed = line.trim();

    // Strip uninit annotations (no instructions generated)
    if trimmed.starts_with("uninit") {
        return String::new();
    }

    if trimmed.starts_with("load_ext_name") {
        // "load_ext_name userextname0+0, %rax" -> "  lea         [userextname0], %rax"
        if let Some((name_part, reg)) = trimmed
            .strip_prefix("load_ext_name ")
            .and_then(|s| s.split_once(", "))
        {
            return format!("  {:<11} [{}], {}", "lea", name_part, reg);
        }
    }

    // Parse instruction and operands
    let parts: Vec<&str> = trimmed.splitn(2, char::is_whitespace).collect();

    match parts.as_slice() {
        [mnemonic] => {
            // No operands (e.g., "retq")
            format!("  {}", mnemonic)
        }
        [mnemonic, operands] => {
            // Has operands - align to 12 chars for mnemonic (vfmsub213sd is 11)
            // Also normalize label references (labelN -> .LN)
            let operands = normalize_labels(operands.trim());
            format!("  {:<11} {}", mnemonic, operands)
        }
        _ => format!("  {}", trimmed),
    }
}

/// Convert labelN references to .LN format
fn normalize_labels(operands: &str) -> String {
    let mut result = operands.to_string();
    // Find and replace all labelN patterns
    let mut i = 0;
    while let Some(pos) = result[i..].find("label") {
        let start = i + pos;
        let after_label = start + 5; // len("label")
        if after_label < result.len() {
            // Find where the number ends
            let num_end = result[after_label..]
                .find(|c: char| !c.is_ascii_digit())
                .map(|p| after_label + p)
                .unwrap_or(result.len());
            if num_end > after_label {
                let num = &result[after_label..num_end];
                let replacement = format!(".L{}", num);
                result.replace_range(start..num_end, &replacement);
                i = start + replacement.len();
                continue;
            }
        }
        i = after_label;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_conditional_jump() {
        let input = "jl      label6; j label5";
        let output = format_conditional_jump(input);
        assert!(output.contains("jl"));
        assert!(output.contains("taken"));
        assert!(output.contains("fallthrough"));
    }

    #[test]
    fn test_format_instruction() {
        assert_eq!(
            format_instruction("movq %rax, %rdi"),
            "  movq        %rax, %rdi"
        );
        assert_eq!(format_instruction("retq"), "  retq");
        assert_eq!(
            format_instruction("vfmsub213sd (%rip), %xmm2, %xmm6"),
            "  vfmsub213sd (%rip), %xmm2, %xmm6"
        );
    }

    #[test]
    fn test_strips_unwind() {
        assert_eq!(format_line("unwind PushFrameRegs { offset: 16 }"), "");
    }

    #[test]
    fn test_strips_uninit() {
        assert_eq!(format_line("uninit  %rax"), "");
    }
}
