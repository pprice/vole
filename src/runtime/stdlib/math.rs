// src/runtime/stdlib/math.rs
//! Native math functions for std:math module.

use crate::runtime::native_registry::{NativeModule, NativeSignature, NativeType};

/// Create the std:math native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // Trigonometric functions: (f64) -> f64
    m.register(
        "sin",
        math_sin as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    m.register(
        "cos",
        math_cos as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    m.register(
        "tan",
        math_tan as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    // Roots and powers
    m.register(
        "sqrt",
        math_sqrt as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    m.register(
        "pow",
        math_pow as *const u8,
        NativeSignature {
            params: vec![NativeType::F64, NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    // Rounding functions: (f64) -> f64
    m.register(
        "floor",
        math_floor as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    m.register(
        "ceil",
        math_ceil as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    m.register(
        "round",
        math_round as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    // Absolute value: (f64) -> f64
    m.register(
        "abs",
        math_abs as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    // Min/max: (f64, f64) -> f64
    m.register(
        "min",
        math_min as *const u8,
        NativeSignature {
            params: vec![NativeType::F64, NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    m.register(
        "max",
        math_max as *const u8,
        NativeSignature {
            params: vec![NativeType::F64, NativeType::F64],
            return_type: NativeType::F64,
        },
    );

    m
}

// =============================================================================
// Trigonometric functions
// =============================================================================

/// Compute the sine of x (in radians)
#[unsafe(no_mangle)]
pub extern "C" fn math_sin(x: f64) -> f64 {
    x.sin()
}

/// Compute the cosine of x (in radians)
#[unsafe(no_mangle)]
pub extern "C" fn math_cos(x: f64) -> f64 {
    x.cos()
}

/// Compute the tangent of x (in radians)
#[unsafe(no_mangle)]
pub extern "C" fn math_tan(x: f64) -> f64 {
    x.tan()
}

// =============================================================================
// Roots and powers
// =============================================================================

/// Compute the square root of x
#[unsafe(no_mangle)]
pub extern "C" fn math_sqrt(x: f64) -> f64 {
    x.sqrt()
}

/// Compute x raised to the power y
#[unsafe(no_mangle)]
pub extern "C" fn math_pow(x: f64, y: f64) -> f64 {
    x.powf(y)
}

// =============================================================================
// Rounding functions
// =============================================================================

/// Round x down to the nearest integer
#[unsafe(no_mangle)]
pub extern "C" fn math_floor(x: f64) -> f64 {
    x.floor()
}

/// Round x up to the nearest integer
#[unsafe(no_mangle)]
pub extern "C" fn math_ceil(x: f64) -> f64 {
    x.ceil()
}

/// Round x to the nearest integer (half away from zero)
#[unsafe(no_mangle)]
pub extern "C" fn math_round(x: f64) -> f64 {
    x.round()
}

// =============================================================================
// Absolute value
// =============================================================================

/// Compute the absolute value of x
#[unsafe(no_mangle)]
pub extern "C" fn math_abs(x: f64) -> f64 {
    x.abs()
}

// =============================================================================
// Min/max functions
// =============================================================================

/// Return the minimum of x and y
#[unsafe(no_mangle)]
pub extern "C" fn math_min(x: f64, y: f64) -> f64 {
    x.min(y)
}

/// Return the maximum of x and y
#[unsafe(no_mangle)]
pub extern "C" fn math_max(x: f64, y: f64) -> f64 {
    x.max(y)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::f64::consts::PI;

    // ==========================================================================
    // Trigonometric function tests
    // ==========================================================================

    #[test]
    fn test_sin() {
        assert!((math_sin(0.0) - 0.0).abs() < 1e-10);
        assert!((math_sin(PI / 2.0) - 1.0).abs() < 1e-10);
        assert!((math_sin(PI) - 0.0).abs() < 1e-10);
        assert!((math_sin(-PI / 2.0) - (-1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_cos() {
        assert!((math_cos(0.0) - 1.0).abs() < 1e-10);
        assert!((math_cos(PI / 2.0) - 0.0).abs() < 1e-10);
        assert!((math_cos(PI) - (-1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_tan() {
        assert!((math_tan(0.0) - 0.0).abs() < 1e-10);
        assert!((math_tan(PI / 4.0) - 1.0).abs() < 1e-10);
        assert!((math_tan(-PI / 4.0) - (-1.0)).abs() < 1e-10);
    }

    // ==========================================================================
    // Roots and powers tests
    // ==========================================================================

    #[test]
    fn test_sqrt() {
        assert!((math_sqrt(4.0) - 2.0).abs() < 1e-10);
        assert!((math_sqrt(9.0) - 3.0).abs() < 1e-10);
        assert!((math_sqrt(2.0) - std::f64::consts::SQRT_2).abs() < 1e-10);
        assert!((math_sqrt(0.0) - 0.0).abs() < 1e-10);
    }

    #[test]
    fn test_sqrt_negative() {
        // sqrt of negative number returns NaN
        assert!(math_sqrt(-1.0).is_nan());
    }

    #[test]
    fn test_pow() {
        assert!((math_pow(2.0, 3.0) - 8.0).abs() < 1e-10);
        assert!((math_pow(3.0, 2.0) - 9.0).abs() < 1e-10);
        assert!((math_pow(4.0, 0.5) - 2.0).abs() < 1e-10);
        assert!((math_pow(2.0, -1.0) - 0.5).abs() < 1e-10);
        assert!((math_pow(5.0, 0.0) - 1.0).abs() < 1e-10);
    }

    // ==========================================================================
    // Rounding function tests
    // ==========================================================================

    #[test]
    fn test_floor() {
        assert_eq!(math_floor(3.7), 3.0);
        assert_eq!(math_floor(3.2), 3.0);
        assert_eq!(math_floor(-3.7), -4.0);
        assert_eq!(math_floor(-3.2), -4.0);
        assert_eq!(math_floor(5.0), 5.0);
    }

    #[test]
    fn test_ceil() {
        assert_eq!(math_ceil(3.7), 4.0);
        assert_eq!(math_ceil(3.2), 4.0);
        assert_eq!(math_ceil(-3.7), -3.0);
        assert_eq!(math_ceil(-3.2), -3.0);
        assert_eq!(math_ceil(5.0), 5.0);
    }

    #[test]
    fn test_round() {
        assert_eq!(math_round(3.7), 4.0);
        assert_eq!(math_round(3.2), 3.0);
        assert_eq!(math_round(3.5), 4.0); // half rounds away from zero
        assert_eq!(math_round(-3.7), -4.0);
        assert_eq!(math_round(-3.5), -4.0); // half rounds away from zero
        assert_eq!(math_round(5.0), 5.0);
    }

    // ==========================================================================
    // Absolute value tests
    // ==========================================================================

    #[test]
    fn test_abs() {
        assert_eq!(math_abs(5.0), 5.0);
        assert_eq!(math_abs(-5.0), 5.0);
        assert_eq!(math_abs(0.0), 0.0);
        assert_eq!(math_abs(-0.0), 0.0);
        assert!((math_abs(-3.25) - 3.25).abs() < 1e-10);
    }

    // ==========================================================================
    // Min/max tests
    // ==========================================================================

    #[test]
    fn test_min() {
        assert_eq!(math_min(3.0, 5.0), 3.0);
        assert_eq!(math_min(5.0, 3.0), 3.0);
        assert_eq!(math_min(-3.0, 5.0), -3.0);
        assert_eq!(math_min(3.0, 3.0), 3.0);
    }

    #[test]
    fn test_max() {
        assert_eq!(math_max(3.0, 5.0), 5.0);
        assert_eq!(math_max(5.0, 3.0), 5.0);
        assert_eq!(math_max(-3.0, 5.0), 5.0);
        assert_eq!(math_max(3.0, 3.0), 3.0);
    }

    // ==========================================================================
    // Module registration tests
    // ==========================================================================

    #[test]
    fn test_module_registration() {
        let m = module();

        // Verify all functions are registered
        assert!(m.get("sin").is_some());
        assert!(m.get("cos").is_some());
        assert!(m.get("tan").is_some());
        assert!(m.get("sqrt").is_some());
        assert!(m.get("pow").is_some());
        assert!(m.get("floor").is_some());
        assert!(m.get("ceil").is_some());
        assert!(m.get("round").is_some());
        assert!(m.get("abs").is_some());
        assert!(m.get("min").is_some());
        assert!(m.get("max").is_some());

        // Verify signatures
        let sin_func = m.get("sin").unwrap();
        assert_eq!(sin_func.signature.params.len(), 1);
        assert_eq!(sin_func.signature.params[0], NativeType::F64);
        assert_eq!(sin_func.signature.return_type, NativeType::F64);

        let pow_func = m.get("pow").unwrap();
        assert_eq!(pow_func.signature.params.len(), 2);
        assert_eq!(pow_func.signature.params[0], NativeType::F64);
        assert_eq!(pow_func.signature.params[1], NativeType::F64);
        assert_eq!(pow_func.signature.return_type, NativeType::F64);

        let min_func = m.get("min").unwrap();
        assert_eq!(min_func.signature.params.len(), 2);
        assert_eq!(min_func.signature.params[0], NativeType::F64);
        assert_eq!(min_func.signature.params[1], NativeType::F64);
        assert_eq!(min_func.signature.return_type, NativeType::F64);
    }
}
