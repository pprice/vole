// src/diff.rs
//! Unified diff formatting using the `similar` crate.

use similar::{ChangeTag, TextDiff};

/// Generate a unified diff between expected and actual content.
/// Returns None if there are no differences.
pub fn unified_diff(expected: &str, actual: &str, label: &str) -> Option<String> {
    if expected == actual {
        return None;
    }

    let diff = TextDiff::from_lines(expected, actual);
    let mut output = String::new();

    // Check if there are any changes
    let has_changes = diff.ops().iter().any(|op| {
        !matches!(
            diff.iter_changes(op).next().map(|c| c.tag()),
            Some(ChangeTag::Equal) | None
        )
    });

    if !has_changes {
        return None;
    }

    output.push_str(&format!("  [{}]\n", label));

    for op in diff.ops() {
        for change in diff.iter_changes(op) {
            let line = change.value().trim_end_matches('\n');
            match change.tag() {
                ChangeTag::Delete => {
                    output.push_str(&format!("  - {}\n", line));
                }
                ChangeTag::Insert => {
                    output.push_str(&format!("  + {}\n", line));
                }
                ChangeTag::Equal => {
                    output.push_str(&format!("    {}\n", line));
                }
            }
        }
    }

    Some(output)
}

/// Generate colored unified diff for terminal output.
pub fn unified_diff_colored(expected: &str, actual: &str, label: &str) -> Option<String> {
    if expected == actual {
        return None;
    }

    let diff = TextDiff::from_lines(expected, actual);
    let mut output = String::new();

    let has_changes = diff
        .ops()
        .iter()
        .any(|op| diff.iter_changes(op).any(|c| c.tag() != ChangeTag::Equal));

    if !has_changes {
        return None;
    }

    output.push_str(&format!("  [{}]\n", label));

    for op in diff.ops() {
        for change in diff.iter_changes(op) {
            let line = change.value().trim_end_matches('\n');
            match change.tag() {
                ChangeTag::Delete => {
                    output.push_str(&format!("  \x1b[31m- {}\x1b[0m\n", line));
                }
                ChangeTag::Insert => {
                    output.push_str(&format!("  \x1b[32m+ {}\x1b[0m\n", line));
                }
                ChangeTag::Equal => {
                    output.push_str(&format!("    {}\n", line));
                }
            }
        }
    }

    Some(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_diff_returns_none() {
        assert!(unified_diff("hello", "hello", "test").is_none());
    }

    #[test]
    fn diff_shows_changes() {
        let result = unified_diff("hello\nworld", "hello\nearth", "stdout").unwrap();
        assert!(result.contains("- world"));
        assert!(result.contains("+ earth"));
    }
}
