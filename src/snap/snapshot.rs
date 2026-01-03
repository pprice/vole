// src/snap/snapshot.rs
//! Snapshot file format: [stdout] and [stderr] sections.

/// Parsed snapshot with stdout and stderr content
#[derive(Debug, Clone)]
pub struct Snapshot {
    pub stdout: String,
    pub stderr: String,
}

impl Snapshot {
    /// Parse a .snap file into stdout and stderr sections.
    pub fn parse(content: &str) -> Self {
        let mut stdout = String::new();
        let mut stderr = String::new();
        let mut current_section: Option<&str> = None;

        for line in content.lines() {
            if line == "[stdout]" {
                current_section = Some("stdout");
            } else if line == "[stderr]" {
                current_section = Some("stderr");
            } else if let Some(section) = current_section {
                let target = if section == "stdout" {
                    &mut stdout
                } else {
                    &mut stderr
                };
                if !target.is_empty() {
                    target.push('\n');
                }
                target.push_str(line);
            }
        }

        Self {
            stdout: trim_trailing(&stdout).to_string(),
            stderr: trim_trailing(&stderr).to_string(),
        }
    }

    /// Format stdout and stderr into .snap file content.
    pub fn format(stdout: &str, stderr: &str) -> String {
        let mut result = String::new();

        result.push_str("[stdout]\n");
        let trimmed_stdout = trim_trailing(stdout);
        if !trimmed_stdout.is_empty() {
            result.push_str(trimmed_stdout);
            result.push('\n');
        }
        result.push('\n');

        result.push_str("[stderr]\n");
        let trimmed_stderr = trim_trailing(stderr);
        if !trimmed_stderr.is_empty() {
            result.push_str(trimmed_stderr);
            result.push('\n');
        }

        result
    }
}

/// Trim trailing whitespace
fn trim_trailing(s: &str) -> &str {
    s.trim_end_matches([' ', '\n', '\r', '\t'])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_snapshot() {
        let content = "[stdout]\nhello\nworld\n\n[stderr]\nerror here";
        let snap = Snapshot::parse(content);
        assert_eq!(snap.stdout, "hello\nworld");
        assert_eq!(snap.stderr, "error here");
    }

    #[test]
    fn format_snapshot() {
        let result = Snapshot::format("hello\nworld", "");
        let expected = "[stdout]\nhello\nworld\n\n[stderr]\n";
        assert_eq!(result, expected);
    }

    #[test]
    fn roundtrip() {
        let original = "[stdout]\ntest output\n\n[stderr]\nsome error\n";
        let snap = Snapshot::parse(original);
        let formatted = Snapshot::format(&snap.stdout, &snap.stderr);
        let reparsed = Snapshot::parse(&formatted);
        assert_eq!(snap.stdout, reparsed.stdout);
        assert_eq!(snap.stderr, reparsed.stderr);
    }
}
