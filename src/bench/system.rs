// src/bench/system.rs
//
// System information collection for benchmark context.

use serde::Serialize;
use sysinfo::System;

/// System information for benchmark context
#[derive(Debug, Clone, Serialize)]
pub struct SystemInfo {
    pub os: String,
    pub os_version: String,
    pub arch: String,
    pub cpu_model: String,
    pub cpu_cores: usize,
    pub memory_bytes: u64,
}

impl SystemInfo {
    /// Collect current system information
    pub fn collect() -> Self {
        let mut sys = System::new();
        sys.refresh_memory();
        sys.refresh_cpu_all();

        Self {
            os: System::name().unwrap_or_else(|| "Unknown".to_string()),
            os_version: System::os_version().unwrap_or_else(|| "Unknown".to_string()),
            arch: std::env::consts::ARCH.to_string(),
            cpu_model: sys
                .cpus()
                .first()
                .map(|cpu| cpu.brand().to_string())
                .unwrap_or_else(|| "Unknown".to_string()),
            cpu_cores: sys.cpus().len(),
            memory_bytes: sys.total_memory(),
        }
    }

    /// Format for display
    pub fn display(&self) -> String {
        use crate::util::format_bytes;

        let mut out = format!(
            "System: {} {} {}",
            self.os, self.os_version, self.arch
        );

        if self.cpu_cores > 0 {
            out.push_str(&format!(", {} cores", self.cpu_cores));
        }

        if self.memory_bytes > 0 {
            out.push_str(&format!(", {} RAM", format_bytes(self.memory_bytes)));
        }

        out.push('\n');

        if self.cpu_model != "Unknown" {
            out.push_str(&format!("CPU:    {}\n", self.cpu_model));
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_collect_returns_valid_info() {
        let info = SystemInfo::collect();

        // OS should be populated
        assert!(!info.os.is_empty());

        // Should have at least 1 core
        assert!(info.cpu_cores >= 1);

        // Arch should match current platform
        assert_eq!(info.arch, std::env::consts::ARCH);
    }

    #[test]
    fn test_display_format() {
        let info = SystemInfo::collect();
        let display = info.display();

        // Should contain "System:" prefix
        assert!(display.contains("System:"));

        // Should contain arch
        assert!(display.contains(&info.arch));
    }
}
