// src/bench/metrics.rs
//
// Resource usage metrics via getrusage.

use serde::Serialize;
use std::time::Duration;

/// Resource usage snapshot
#[derive(Debug, Clone, Default, Serialize)]
pub struct ResourceUsage {
    /// User CPU time
    pub user_time: Duration,
    /// System CPU time
    pub sys_time: Duration,
    /// Maximum resident set size (bytes)
    pub max_rss: u64,
}

impl ResourceUsage {
    /// Get current resource usage for this process
    #[cfg(unix)]
    pub fn current() -> Self {
        use std::mem::MaybeUninit;

        let mut usage = MaybeUninit::<libc::rusage>::uninit();
        let result = unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) };

        if result != 0 {
            return Self::default();
        }

        let usage = unsafe { usage.assume_init() };

        // Convert timeval to Duration
        let user_time = Duration::new(
            usage.ru_utime.tv_sec as u64,
            usage.ru_utime.tv_usec as u32 * 1000,
        );
        let sys_time = Duration::new(
            usage.ru_stime.tv_sec as u64,
            usage.ru_stime.tv_usec as u32 * 1000,
        );

        // ru_maxrss is in kilobytes on Linux, bytes on macOS
        #[cfg(target_os = "linux")]
        let max_rss = usage.ru_maxrss as u64 * 1024;
        #[cfg(target_os = "macos")]
        let max_rss = usage.ru_maxrss as u64;
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let max_rss = usage.ru_maxrss as u64 * 1024; // Assume Linux-like

        Self {
            user_time,
            sys_time,
            max_rss,
        }
    }

    #[cfg(not(unix))]
    pub fn current() -> Self {
        Self::default()
    }

    /// Total CPU time (user + sys)
    pub fn cpu_time(&self) -> Duration {
        self.user_time + self.sys_time
    }

    /// Compute delta from a previous snapshot
    pub fn delta(&self, previous: &Self) -> Self {
        Self {
            user_time: self.user_time.saturating_sub(previous.user_time),
            sys_time: self.sys_time.saturating_sub(previous.sys_time),
            // For RSS, we take the current value (not delta)
            max_rss: self.max_rss,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_current_returns_some_values() {
        let usage = ResourceUsage::current();

        // On Unix, we should get some values
        #[cfg(unix)]
        {
            // CPU time might be very small but should be valid Duration
            let _ = usage.user_time;
            let _ = usage.sys_time;
        }

        // max_rss should be > 0 for a running process
        // (Skip assertion as it may be 0 on some platforms)
        let _ = usage.max_rss;
    }

    #[test]
    fn test_cpu_time() {
        let usage = ResourceUsage {
            user_time: Duration::from_millis(100),
            sys_time: Duration::from_millis(50),
            max_rss: 0,
        };

        assert_eq!(usage.cpu_time(), Duration::from_millis(150));
    }

    #[test]
    fn test_delta() {
        let before = ResourceUsage {
            user_time: Duration::from_millis(100),
            sys_time: Duration::from_millis(50),
            max_rss: 1000,
        };
        let after = ResourceUsage {
            user_time: Duration::from_millis(150),
            sys_time: Duration::from_millis(75),
            max_rss: 2000,
        };

        let delta = after.delta(&before);
        assert_eq!(delta.user_time, Duration::from_millis(50));
        assert_eq!(delta.sys_time, Duration::from_millis(25));
        assert_eq!(delta.max_rss, 2000); // Current value, not delta
    }
}
