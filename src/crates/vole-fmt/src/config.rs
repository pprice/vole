// src/config.rs
//! Configuration for the Vole formatter.
//!
//! The canonical style is not user-configurable - there is only one true style.
//! This struct exists to keep formatting rules centralized and testable.

/// Formatting configuration. All values are fixed for canonical style.
#[derive(Debug, Clone, Copy)]
pub struct FormatConfig {
    /// Number of spaces per indentation level
    pub indent_width: u8,
    /// Maximum line width (soft limit for breaking decisions)
    pub max_line_width: u16,
}

impl Default for FormatConfig {
    fn default() -> Self {
        CANONICAL
    }
}

/// The canonical formatting style - the one true way.
pub const CANONICAL: FormatConfig = FormatConfig {
    indent_width: 4,
    max_line_width: 100,
};

impl FormatConfig {
    /// Get the indentation string for a given level.
    pub fn indent(&self, level: u32) -> String {
        " ".repeat(self.indent_width as usize * level as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_indent() {
        let config = CANONICAL;
        assert_eq!(config.indent(0), "");
        assert_eq!(config.indent(1), "    ");
        assert_eq!(config.indent(2), "        ");
    }
}
