// src/runtime/stdlib/time.rs
//! Native time functions for std:time module.
//!
//! Provides:
//! - time_now() -> i64 - current time as nanoseconds since Unix epoch
//! - time_parse_iso(string) -> i64 - parse ISO 8601 string to nanos
//! - time_to_iso(nanos, offset_mins) -> string - format as ISO 8601
//! - time_add_months(nanos, months) -> i64 - calendar month addition
//! - time_add_years(nanos, years) -> i64 - calendar year addition
//! - time_get_date(nanos, offset_mins) -> i64 - packed date components
//! - time_get_time(nanos, offset_mins) -> i64 - packed time components

use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::string::RcString;
use chrono::{DateTime, Datelike, FixedOffset, NaiveDateTime, TimeZone, Timelike, Utc};

/// Create the std:time native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // time_now: () -> i64 - current time as nanoseconds since epoch
    m.register(
        "time_now",
        time_now as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::I64,
        },
    );

    // time_parse_iso: (string) -> i64 - parse ISO 8601, returns i64::MIN on error
    m.register(
        "time_parse_iso",
        time_parse_iso as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64,
        },
    );

    // time_to_iso: (i64, i64) -> string - format nanos as ISO 8601
    m.register(
        "time_to_iso",
        time_to_iso as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::String,
        },
    );

    // time_add_months: (i64, i64) -> i64 - add months to timestamp
    m.register(
        "time_add_months",
        time_add_months as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // time_add_years: (i64, i64) -> i64 - add years to timestamp
    m.register(
        "time_add_years",
        time_add_years as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // time_get_date: (i64, i64) -> i64 - get date components packed
    m.register(
        "time_get_date",
        time_get_date as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // time_get_time: (i64, i64) -> i64 - get time components packed
    m.register(
        "time_get_time",
        time_get_time as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    m
}

// =============================================================================
// Helper functions
// =============================================================================

/// Convert nanoseconds since epoch to DateTime<FixedOffset>
fn nanos_to_datetime(nanos: i64, offset_mins: i64) -> Option<DateTime<FixedOffset>> {
    let offset_secs = (offset_mins * 60) as i32;
    let offset = FixedOffset::east_opt(offset_secs)?;

    // Use DateTime::from_timestamp which handles negative timestamps correctly
    let secs = nanos.div_euclid(1_000_000_000);
    let nsecs = nanos.rem_euclid(1_000_000_000) as u32;

    let dt_utc = DateTime::from_timestamp(secs, nsecs)?;
    Some(dt_utc.with_timezone(&offset))
}

/// Convert DateTime to nanoseconds since epoch
fn datetime_to_nanos(dt: DateTime<FixedOffset>) -> i64 {
    let secs = dt.timestamp();
    let nsecs = dt.timestamp_subsec_nanos() as i64;
    secs * 1_000_000_000 + nsecs
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Get current time as nanoseconds since Unix epoch
#[unsafe(no_mangle)]
pub extern "C" fn time_now() -> i64 {
    let now = Utc::now();
    now.timestamp() * 1_000_000_000 + now.timestamp_subsec_nanos() as i64
}

/// Parse ISO 8601 string to nanoseconds since epoch
/// Returns i64::MIN on parse error
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn time_parse_iso(iso_ptr: *const RcString) -> i64 {
    if iso_ptr.is_null() {
        return i64::MIN;
    }

    let iso_str = unsafe { (*iso_ptr).as_str() };

    // Try parsing with timezone
    if let Ok(dt) = DateTime::parse_from_rfc3339(iso_str) {
        return datetime_to_nanos(dt);
    }

    // Try parsing as naive datetime and assume UTC
    if let Ok(naive) = NaiveDateTime::parse_from_str(iso_str, "%Y-%m-%dT%H:%M:%S") {
        let dt = Utc.from_utc_datetime(&naive);
        return dt.timestamp() * 1_000_000_000 + dt.timestamp_subsec_nanos() as i64;
    }

    // Try date only
    if let Ok(naive) = chrono::NaiveDate::parse_from_str(iso_str, "%Y-%m-%d")
        && let Some(dt) = naive.and_hms_opt(0, 0, 0)
    {
        let dt = Utc.from_utc_datetime(&dt);
        return dt.timestamp() * 1_000_000_000;
    }

    i64::MIN
}

/// Format nanoseconds as ISO 8601 string
#[unsafe(no_mangle)]
pub extern "C" fn time_to_iso(nanos: i64, offset_mins: i64) -> *const RcString {
    let Some(dt) = nanos_to_datetime(nanos, offset_mins) else {
        return RcString::new("");
    };

    let iso = dt.format("%Y-%m-%dT%H:%M:%S").to_string();

    // Add timezone suffix
    let result = if offset_mins == 0 {
        format!("{}Z", iso)
    } else {
        let offset_hours = offset_mins.abs() / 60;
        let offset_remaining_mins = offset_mins.abs() % 60;
        let sign = if offset_mins >= 0 { '+' } else { '-' };
        format!(
            "{}{}{:02}:{:02}",
            iso, sign, offset_hours, offset_remaining_mins
        )
    };

    RcString::new(&result)
}

/// Add months to a timestamp (calendar math)
#[unsafe(no_mangle)]
pub extern "C" fn time_add_months(nanos: i64, months: i64) -> i64 {
    let Some(dt) = nanos_to_datetime(nanos, 0) else {
        return nanos;
    };

    // Calculate new year and month
    let current_month = dt.month() as i64;
    let current_year = dt.year() as i64;

    let total_months = current_year * 12 + (current_month - 1) + months;
    let new_year = total_months / 12;
    let new_month = (total_months % 12 + 12) % 12 + 1; // Handle negative

    // Clamp day to valid range for new month
    let day = dt.day();
    let max_day = days_in_month(new_year as i32, new_month as u32);
    let clamped_day = day.min(max_day);

    // Reconstruct datetime
    let Some(new_date) =
        chrono::NaiveDate::from_ymd_opt(new_year as i32, new_month as u32, clamped_day)
    else {
        return nanos;
    };
    let new_dt = new_date.and_hms_nano_opt(dt.hour(), dt.minute(), dt.second(), dt.nanosecond());
    let Some(new_dt) = new_dt else {
        return nanos;
    };
    let new_dt = Utc.from_utc_datetime(&new_dt);

    new_dt.timestamp() * 1_000_000_000 + new_dt.timestamp_subsec_nanos() as i64
}

/// Add years to a timestamp (calendar math)
#[unsafe(no_mangle)]
pub extern "C" fn time_add_years(nanos: i64, years: i64) -> i64 {
    time_add_months(nanos, years * 12)
}

/// Get date components packed into i64
/// Format: year (signed, 32 bits) << 32 | month (16 bits) << 16 | day (16 bits)
#[unsafe(no_mangle)]
pub extern "C" fn time_get_date(nanos: i64, offset_mins: i64) -> i64 {
    let Some(dt) = nanos_to_datetime(nanos, offset_mins) else {
        return 0;
    };

    let year = dt.year() as i64;
    let month = dt.month() as i64;
    let day = dt.day() as i64;

    (year << 32) | (month << 16) | day
}

/// Get time components packed into i64
/// Format: hour (32 bits) << 32 | minute (16 bits) << 16 | second (16 bits)
#[unsafe(no_mangle)]
pub extern "C" fn time_get_time(nanos: i64, offset_mins: i64) -> i64 {
    let Some(dt) = nanos_to_datetime(nanos, offset_mins) else {
        return 0;
    };

    let hour = dt.hour() as i64;
    let minute = dt.minute() as i64;
    let second = dt.second() as i64;

    (hour << 32) | (minute << 16) | second
}

/// Helper: get number of days in a month
fn days_in_month(year: i32, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        _ => 30, // Fallback
    }
}

/// Helper: check if year is a leap year
fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to clean up a string
    unsafe fn cleanup_string(s: *const RcString) {
        if !s.is_null() {
            unsafe { RcString::dec_ref(s as *mut RcString) };
        }
    }

    // Helper to safely read a string
    unsafe fn read_string(s: *const RcString) -> String {
        if s.is_null() {
            String::new()
        } else {
            unsafe { (*s).as_str().to_string() }
        }
    }

    #[test]
    fn test_time_now_returns_positive() {
        let now = time_now();
        // Should be positive and reasonably recent (after 2020)
        assert!(now > 1577836800_000_000_000); // 2020-01-01
    }

    #[test]
    fn test_time_now_is_monotonic() {
        let t1 = time_now();
        let t2 = time_now();
        assert!(t2 >= t1);
    }

    #[test]
    fn test_time_parse_iso_rfc3339() {
        let iso = RcString::new("2024-01-15T12:30:45Z");
        let nanos = time_parse_iso(iso);
        assert_ne!(nanos, i64::MIN);

        // Verify it's in the right ballpark (2024)
        let secs = nanos / 1_000_000_000;
        assert!(secs > 1704067200); // 2024-01-01
        assert!(secs < 1735689600); // 2025-01-01

        unsafe {
            cleanup_string(iso);
        }
    }

    #[test]
    fn test_time_parse_iso_date_only() {
        let iso = RcString::new("2024-06-15");
        let nanos = time_parse_iso(iso);
        assert_ne!(nanos, i64::MIN);

        unsafe {
            cleanup_string(iso);
        }
    }

    #[test]
    fn test_time_parse_iso_invalid() {
        let iso = RcString::new("not a date");
        let nanos = time_parse_iso(iso);
        assert_eq!(nanos, i64::MIN);

        unsafe {
            cleanup_string(iso);
        }
    }

    #[test]
    fn test_time_parse_iso_null() {
        let nanos = time_parse_iso(std::ptr::null());
        assert_eq!(nanos, i64::MIN);
    }

    #[test]
    fn test_time_to_iso_utc() {
        // 2024-01-15T12:30:45Z = 1705321845 seconds since epoch
        let nanos = 1705321845_000_000_000i64;
        let result = time_to_iso(nanos, 0);

        unsafe {
            let iso = read_string(result);
            assert_eq!(iso, "2024-01-15T12:30:45Z");
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_to_iso_with_offset() {
        // Same instant but with +05:30 offset
        // 2024-01-15T12:30:45Z in UTC = 2024-01-15T18:00:45+05:30 in +05:30
        let nanos = 1705321845_000_000_000i64;
        let result = time_to_iso(nanos, 330); // 5 hours 30 minutes

        unsafe {
            let iso = read_string(result);
            assert_eq!(iso, "2024-01-15T18:00:45+05:30");
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_to_iso_negative_offset() {
        // 2024-01-15T12:30:45Z in UTC = 2024-01-15T07:30:45-05:00 in -05:00
        let nanos = 1705321845_000_000_000i64;
        let result = time_to_iso(nanos, -300); // -5 hours

        unsafe {
            let iso = read_string(result);
            assert_eq!(iso, "2024-01-15T07:30:45-05:00");
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_add_months_simple() {
        // 2024-01-15 + 1 month = 2024-02-15
        let jan = time_parse_iso(RcString::new("2024-01-15T12:00:00Z"));
        let feb = time_add_months(jan, 1);

        let result = time_to_iso(feb, 0);
        unsafe {
            let iso = read_string(result);
            assert!(iso.starts_with("2024-02-15"));
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_add_months_year_boundary() {
        // 2024-11-15 + 3 months = 2025-02-15
        let nov = time_parse_iso(RcString::new("2024-11-15T12:00:00Z"));
        let feb = time_add_months(nov, 3);

        let result = time_to_iso(feb, 0);
        unsafe {
            let iso = read_string(result);
            assert!(iso.starts_with("2025-02-15"));
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_add_months_day_clamping() {
        // 2024-01-31 + 1 month = 2024-02-29 (leap year, clamped from 31)
        let jan31 = time_parse_iso(RcString::new("2024-01-31T12:00:00Z"));
        let feb = time_add_months(jan31, 1);

        let result = time_to_iso(feb, 0);
        unsafe {
            let iso = read_string(result);
            assert!(iso.starts_with("2024-02-29"));
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_add_months_negative() {
        // 2024-03-15 - 1 month = 2024-02-15
        let mar = time_parse_iso(RcString::new("2024-03-15T12:00:00Z"));
        let feb = time_add_months(mar, -1);

        let result = time_to_iso(feb, 0);
        unsafe {
            let iso = read_string(result);
            assert!(iso.starts_with("2024-02-15"));
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_add_years_simple() {
        // 2024-06-15 + 2 years = 2026-06-15
        let y2024 = time_parse_iso(RcString::new("2024-06-15T12:00:00Z"));
        let y2026 = time_add_years(y2024, 2);

        let result = time_to_iso(y2026, 0);
        unsafe {
            let iso = read_string(result);
            assert!(iso.starts_with("2026-06-15"));
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_add_years_leap_day() {
        // 2024-02-29 + 1 year = 2025-02-28 (non-leap year)
        let leap = time_parse_iso(RcString::new("2024-02-29T12:00:00Z"));
        let next = time_add_years(leap, 1);

        let result = time_to_iso(next, 0);
        unsafe {
            let iso = read_string(result);
            assert!(iso.starts_with("2025-02-28"));
            cleanup_string(result);
        }
    }

    #[test]
    fn test_time_get_date() {
        // 2024-06-15
        let nanos = time_parse_iso(RcString::new("2024-06-15T12:30:45Z"));
        let packed = time_get_date(nanos, 0);

        let year = packed >> 32;
        let month = (packed >> 16) & 0xFFFF;
        let day = packed & 0xFFFF;

        assert_eq!(year, 2024);
        assert_eq!(month, 6);
        assert_eq!(day, 15);
    }

    #[test]
    fn test_time_get_date_with_offset() {
        // 2024-06-15T23:00:00Z with +02:00 offset = 2024-06-16T01:00:00+02:00
        let nanos = time_parse_iso(RcString::new("2024-06-15T23:00:00Z"));
        let packed = time_get_date(nanos, 120); // +2 hours

        let day = packed & 0xFFFF;
        assert_eq!(day, 16); // Should be next day in local time
    }

    #[test]
    fn test_time_get_time() {
        // 12:30:45
        let nanos = time_parse_iso(RcString::new("2024-06-15T12:30:45Z"));
        let packed = time_get_time(nanos, 0);

        let hour = packed >> 32;
        let minute = (packed >> 16) & 0xFFFF;
        let second = packed & 0xFFFF;

        assert_eq!(hour, 12);
        assert_eq!(minute, 30);
        assert_eq!(second, 45);
    }

    #[test]
    fn test_time_get_time_with_offset() {
        // 12:30:45 UTC with +03:00 offset = 15:30:45 local
        let nanos = time_parse_iso(RcString::new("2024-06-15T12:30:45Z"));
        let packed = time_get_time(nanos, 180); // +3 hours

        let hour = packed >> 32;
        assert_eq!(hour, 15);
    }

    #[test]
    fn test_roundtrip_parse_format() {
        let original = "2024-06-15T12:30:45Z";
        let iso = RcString::new(original);
        let nanos = time_parse_iso(iso);
        let result = time_to_iso(nanos, 0);

        unsafe {
            let formatted = read_string(result);
            assert_eq!(formatted, original);
            cleanup_string(result);
            cleanup_string(iso);
        }
    }

    #[test]
    fn test_days_in_month() {
        assert_eq!(days_in_month(2024, 1), 31);
        assert_eq!(days_in_month(2024, 2), 29); // Leap year
        assert_eq!(days_in_month(2023, 2), 28); // Non-leap year
        assert_eq!(days_in_month(2024, 4), 30);
        assert_eq!(days_in_month(2024, 12), 31);
    }

    #[test]
    fn test_is_leap_year() {
        assert!(is_leap_year(2024));
        assert!(!is_leap_year(2023));
        assert!(is_leap_year(2000)); // Divisible by 400
        assert!(!is_leap_year(1900)); // Divisible by 100 but not 400
    }

    #[test]
    fn test_module_registration() {
        let m = module();

        assert!(m.get("time_now").is_some());
        assert!(m.get("time_parse_iso").is_some());
        assert!(m.get("time_to_iso").is_some());
        assert!(m.get("time_add_months").is_some());
        assert!(m.get("time_add_years").is_some());
        assert!(m.get("time_get_date").is_some());
        assert!(m.get("time_get_time").is_some());

        // Check signatures
        let now_func = m.get("time_now").unwrap();
        assert!(now_func.signature.params.is_empty());
        assert_eq!(now_func.signature.return_type, NativeType::I64);

        let parse_func = m.get("time_parse_iso").unwrap();
        assert_eq!(parse_func.signature.params.len(), 1);
        assert_eq!(parse_func.signature.params[0], NativeType::String);
    }
}
