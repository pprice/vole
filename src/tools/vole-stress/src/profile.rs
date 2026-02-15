//! Generation profiles for vole-stress.
//!
//! Profiles define presets for the planner configuration that produce
//! codebases of varying complexity and size. Each profile is defined as
//! a TOML file embedded in the binary at compile time. Fields omitted
//! from a TOML file inherit the "full" profile defaults (which are the
//! `Default` impls on each config struct).

use crate::emitter::EmitConfig;
use crate::planner::PlanConfig;

/// A generation profile combining plan and emit configurations.
///
/// The `Default` impl produces the "full" profile (all features enabled at
/// moderate probabilities). TOML profile files use `#[serde(default)]` so
/// they only need to specify fields that differ from the full profile.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
#[serde(default)]
pub struct Profile {
    /// Configuration for the planning phase.
    pub plan: PlanConfig,
    /// Configuration for the emit phase.
    pub emit: EmitConfig,
}

/// Error type for profile lookup failures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownProfileError(pub String);

impl std::fmt::Display for UnknownProfileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "unknown profile '{}', available profiles: {}",
            self.0,
            available_profiles().join(", ")
        )
    }
}

impl std::error::Error for UnknownProfileError {}

// Embedded profile TOML data (compiled into the binary).
static PROFILES: &[(&str, &str)] = &[
    ("minimal", include_str!("../profiles/minimal.toml")),
    ("full", include_str!("../profiles/full.toml")),
    (
        "deep-nesting",
        include_str!("../profiles/deep-nesting.toml"),
    ),
    ("wide-types", include_str!("../profiles/wide-types.toml")),
    (
        "many-modules",
        include_str!("../profiles/many-modules.toml"),
    ),
    (
        "generics-heavy",
        include_str!("../profiles/generics-heavy.toml"),
    ),
    (
        "stdlib-heavy",
        include_str!("../profiles/stdlib-heavy.toml"),
    ),
    (
        "closures-heavy",
        include_str!("../profiles/closures-heavy.toml"),
    ),
    (
        "fallible-heavy",
        include_str!("../profiles/fallible-heavy.toml"),
    ),
];

/// Returns a list of available profile names.
pub fn available_profiles() -> Vec<&'static str> {
    PROFILES.iter().map(|(name, _)| *name).collect()
}

/// Parse a TOML string into a `Profile`, using defaults for omitted fields.
fn parse_profile_toml(toml_str: &str) -> Result<Profile, String> {
    toml::from_str(toml_str).map_err(|e| format!("failed to parse profile TOML: {e}"))
}

/// Get a profile by name, or load from a file path.
///
/// If `name_or_path` contains `/` or ends with `.toml`, it is treated as
/// a file path and loaded from disk. Otherwise it is looked up among the
/// embedded profiles.
///
/// Returns `Err` if the profile name is not recognized or the file cannot
/// be read/parsed.
pub fn get_profile(name_or_path: &str) -> Result<Profile, UnknownProfileError> {
    // Check if this looks like a file path
    if name_or_path.contains('/') || name_or_path.ends_with(".toml") {
        let content = std::fs::read_to_string(name_or_path).map_err(|e| {
            UnknownProfileError(format!(
                "failed to read profile file '{}': {}",
                name_or_path, e
            ))
        })?;
        parse_profile_toml(&content).map_err(|e| {
            UnknownProfileError(format!(
                "failed to parse profile file '{}': {}",
                name_or_path, e
            ))
        })
    } else {
        // Look up by name in embedded profiles
        for (name, toml_str) in PROFILES {
            if *name == name_or_path {
                return parse_profile_toml(toml_str).map_err(|e| {
                    UnknownProfileError(format!(
                        "failed to parse embedded profile '{}': {}",
                        name, e
                    ))
                });
            }
        }
        Err(UnknownProfileError(name_or_path.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn minimal_profile_exists() {
        let profile = get_profile("minimal").expect("minimal profile should exist");
        // Verify minimal characteristics
        assert_eq!(profile.plan.layers, 1);
        assert_eq!(profile.plan.modules_per_layer, 1);
        assert_eq!(profile.plan.classes_per_module, (0, 0));
        assert_eq!(profile.plan.interfaces_per_module, (0, 0));
    }

    #[test]
    fn full_profile_exists() {
        let profile = get_profile("full").expect("full profile should exist");

        // Verify ticket requirements: 3 layers, 3-5 modules per layer
        assert_eq!(profile.plan.layers, 3, "full profile should have 3 layers");
        assert!(
            profile.plan.modules_per_layer >= 3 && profile.plan.modules_per_layer <= 5,
            "full profile should have 3-5 modules per layer"
        );

        // All declaration types should be enabled (non-zero ranges)
        assert!(
            profile.plan.classes_per_module.1 > 0,
            "full profile should generate classes"
        );
        assert!(
            profile.plan.interfaces_per_module.1 > 0,
            "full profile should generate interfaces"
        );
        assert!(
            profile.plan.errors_per_module.1 > 0,
            "full profile should generate errors"
        );
        assert!(
            profile.plan.functions_per_module.1 > 0,
            "full profile should generate functions"
        );
        assert!(
            profile.plan.implement_blocks_per_module.1 > 0,
            "full profile should generate implement blocks"
        );

        // Generics with constraints
        assert!(
            profile.plan.type_params_per_class.1 > 0,
            "full profile should support generic classes"
        );
        assert!(
            profile.plan.type_params_per_function.1 > 0,
            "full profile should support generic functions"
        );
        assert!(
            profile.plan.constraints_per_type_param.1 > 0,
            "full profile should support type param constraints"
        );

        // All expression types exercised (non-zero probabilities)
        let expr_cfg = &profile.emit.stmt_config.expr_config;
        assert!(
            expr_cfg.binary_probability > 0.0,
            "full profile should generate binary expressions"
        );
        assert!(
            expr_cfg.when_probability > 0.0,
            "full profile should generate when expressions"
        );
        assert!(
            expr_cfg.match_probability > 0.0,
            "full profile should generate match expressions"
        );
        assert!(
            expr_cfg.lambda_probability > 0.0,
            "full profile should generate lambda expressions"
        );

        // All statement types exercised
        let stmt_cfg = &profile.emit.stmt_config;
        assert!(
            stmt_cfg.if_probability > 0.0,
            "full profile should generate if statements"
        );
        assert!(
            stmt_cfg.while_probability > 0.0,
            "full profile should generate while statements"
        );
        assert!(
            stmt_cfg.for_probability > 0.0,
            "full profile should generate for statements"
        );
    }

    #[test]
    fn unknown_profile_returns_error() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("nonexistent"));
        assert!(err.to_string().contains("minimal"));
        assert!(err.to_string().contains("full"));
    }

    #[test]
    fn available_profiles_includes_minimal() {
        let profiles = available_profiles();
        assert!(profiles.contains(&"minimal"));
        assert!(profiles.contains(&"full"));
        assert!(profiles.contains(&"deep-nesting"));
    }

    #[test]
    fn deep_nesting_profile_exists() {
        let profile = get_profile("deep-nesting").expect("deep-nesting profile should exist");
        // Verify deep nesting characteristics
        assert_eq!(profile.plan.layers, 1);
        assert_eq!(profile.plan.modules_per_layer, 1);
        // Expression nesting depth (5+ for meaningful depth)
        assert!(
            profile.emit.stmt_config.expr_config.max_depth >= 5,
            "expression max_depth should be >= 5 for deep nesting"
        );
        // Statement nesting depth
        assert!(
            profile.emit.stmt_config.max_depth >= 4,
            "statement max_depth should be >= 4 for deep nesting"
        );
        // High binary probability for deep a + (b + (c + ...))
        assert!(
            profile.emit.stmt_config.expr_config.binary_probability >= 0.5,
            "binary_probability should be high for deep nesting"
        );
        // High if probability for deep if-else chains
        assert!(
            profile.emit.stmt_config.if_probability >= 0.4,
            "if_probability should be moderately high for deep nesting"
        );
    }

    #[test]
    fn unknown_profile_error_includes_deep_nesting() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("deep-nesting"),
            "error message should mention deep-nesting profile"
        );
    }

    #[test]
    fn wide_types_profile_exists() {
        let profile = get_profile("wide-types").expect("wide-types profile should exist");
        // Verify wide-types characteristics: focus on breadth, not depth

        // Wide parameter counts (20-50)
        assert!(
            profile.plan.params_per_function.0 >= 20,
            "params_per_function min should be >= 20 for wide types"
        );
        assert!(
            profile.plan.params_per_function.1 >= 50,
            "params_per_function max should be >= 50 for wide types"
        );

        // Many type parameters (5-10)
        assert!(
            profile.plan.type_params_per_class.0 >= 5,
            "type_params_per_class min should be >= 5 for wide types"
        );
        assert!(
            profile.plan.type_params_per_function.0 >= 5,
            "type_params_per_function min should be >= 5 for wide types"
        );

        // Wide field counts (20-50)
        assert!(
            profile.plan.fields_per_class.0 >= 20,
            "fields_per_class min should be >= 20 for wide types"
        );
        assert!(
            profile.plan.fields_per_class.1 >= 50,
            "fields_per_class max should be >= 50 for wide types"
        );

        // Many methods per interface (10-20)
        assert!(
            profile.plan.methods_per_interface.0 >= 10,
            "methods_per_interface min should be >= 10 for wide types"
        );

        // Moderate depth (not the focus)
        assert!(
            profile.emit.stmt_config.max_depth <= 5,
            "statement max_depth should be moderate for wide types"
        );
        assert!(
            profile.emit.stmt_config.expr_config.max_depth <= 5,
            "expression max_depth should be moderate for wide types"
        );
    }

    #[test]
    fn available_profiles_includes_wide_types() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"wide-types"),
            "available_profiles should include wide-types"
        );
    }

    #[test]
    fn unknown_profile_error_includes_wide_types() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("wide-types"),
            "error message should mention wide-types profile"
        );
    }

    #[test]
    fn many_modules_profile_exists() {
        let profile = get_profile("many-modules").expect("many-modules profile should exist");
        // Verify many-modules characteristics: focus on module graph breadth

        // 5+ layers
        assert!(
            profile.plan.layers >= 5,
            "layers should be >= 5 for many-modules"
        );

        // 10+ modules per layer
        assert!(
            profile.plan.modules_per_layer >= 10,
            "modules_per_layer should be >= 10 for many-modules"
        );

        // High cross-layer import probability for heavy import graph
        assert!(
            profile.plan.cross_layer_import_probability >= 0.5,
            "cross_layer_import_probability should be >= 0.5 for many-modules"
        );

        // Diamond dependencies enabled
        assert!(
            profile.plan.enable_diamond_dependencies,
            "enable_diamond_dependencies should be true for many-modules"
        );

        // Light declarations - focus on modules, not content complexity
        assert!(
            profile.plan.classes_per_module.1 <= 3,
            "classes_per_module max should be <= 3 for many-modules"
        );
        assert!(
            profile.plan.functions_per_module.1 <= 5,
            "functions_per_module max should be <= 5 for many-modules"
        );

        // Shallow nesting - focus on module graph, not code depth
        assert!(
            profile.emit.stmt_config.max_depth <= 2,
            "statement max_depth should be <= 2 for many-modules"
        );
        assert!(
            profile.emit.stmt_config.expr_config.max_depth <= 2,
            "expression max_depth should be <= 2 for many-modules"
        );
    }

    #[test]
    fn available_profiles_includes_many_modules() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"many-modules"),
            "available_profiles should include many-modules"
        );
    }

    #[test]
    fn unknown_profile_error_includes_many_modules() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("many-modules"),
            "error message should mention many-modules profile"
        );
    }

    #[test]
    fn generics_heavy_profile_exists() {
        let profile = get_profile("generics-heavy").expect("generics-heavy profile should exist");
        // Verify generics-heavy characteristics: focus on generic type parameters

        // Multiple type parameters per class (2-4)
        assert!(
            profile.plan.type_params_per_class.0 >= 2,
            "type_params_per_class min should be >= 2 for generics-heavy"
        );
        assert!(
            profile.plan.type_params_per_class.1 >= 4,
            "type_params_per_class max should be >= 4 for generics-heavy"
        );

        // Multiple type parameters per function (2-4)
        assert!(
            profile.plan.type_params_per_function.0 >= 2,
            "type_params_per_function min should be >= 2 for generics-heavy"
        );
        assert!(
            profile.plan.type_params_per_function.1 >= 4,
            "type_params_per_function max should be >= 4 for generics-heavy"
        );

        // Multiple constraints per type param (1-3)
        assert!(
            profile.plan.constraints_per_type_param.0 >= 1,
            "constraints_per_type_param min should be >= 1 for generics-heavy"
        );
        assert!(
            profile.plan.constraints_per_type_param.1 >= 3,
            "constraints_per_type_param max should be >= 3 for generics-heavy"
        );

        // Many interfaces for constraints
        assert!(
            profile.plan.interfaces_per_module.0 >= 3,
            "interfaces_per_module min should be >= 3 for generics-heavy"
        );

        // Many generic classes
        assert!(
            profile.plan.classes_per_module.0 >= 3,
            "classes_per_module min should be >= 3 for generics-heavy"
        );

        // Many methods for generic method testing
        assert!(
            profile.plan.methods_per_class.0 >= 3,
            "methods_per_class min should be >= 3 for generics-heavy"
        );

        // High interface extends probability for constraint hierarchies
        assert!(
            profile.plan.interface_extends_probability >= 0.5,
            "interface_extends_probability should be >= 0.5 for generics-heavy"
        );

        // Higher lambda probability for generic lambdas
        assert!(
            profile.emit.stmt_config.expr_config.lambda_probability >= 0.1,
            "lambda_probability should be >= 0.1 for generics-heavy"
        );
    }

    #[test]
    fn available_profiles_includes_generics_heavy() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"generics-heavy"),
            "available_profiles should include generics-heavy"
        );
    }

    #[test]
    fn unknown_profile_error_includes_generics_heavy() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("generics-heavy"),
            "error message should mention generics-heavy profile"
        );
    }

    #[test]
    fn fallible_heavy_profile_exists() {
        let profile = get_profile("fallible-heavy").expect("fallible-heavy profile should exist");

        // High fallible probability (>= 0.5)
        assert!(
            profile.plan.fallible_probability >= 0.5,
            "fallible_probability should be >= 0.5 for fallible-heavy"
        );

        // Many error types per module (min >= 2)
        assert!(
            profile.plan.errors_per_module.0 >= 2,
            "errors_per_module min should be >= 2 for fallible-heavy"
        );

        // High raise probability (>= 0.25)
        assert!(
            profile.emit.stmt_config.raise_probability >= 0.25,
            "raise_probability should be >= 0.25 for fallible-heavy"
        );

        // High try probability (>= 0.25)
        assert!(
            profile.emit.stmt_config.try_probability >= 0.25,
            "try_probability should be >= 0.25 for fallible-heavy"
        );

        // No generics (fallible functions require no type params)
        assert_eq!(
            profile.plan.type_params_per_class,
            (0, 0),
            "type_params_per_class should be (0,0) for fallible-heavy"
        );
        assert_eq!(
            profile.plan.type_params_per_function,
            (0, 0),
            "type_params_per_function should be (0,0) for fallible-heavy"
        );
    }

    #[test]
    fn available_profiles_includes_fallible_heavy() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"fallible-heavy"),
            "available_profiles should include fallible-heavy"
        );
    }

    #[test]
    fn unknown_profile_error_includes_fallible_heavy() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("fallible-heavy"),
            "error message should mention fallible-heavy profile"
        );
    }

    /// Verify all embedded profiles parse correctly.
    #[test]
    fn all_profiles_parse() {
        for name in available_profiles() {
            get_profile(name)
                .unwrap_or_else(|e| panic!("profile '{}' failed to parse: {}", name, e));
        }
    }

    /// Verify that a TOML round-trip preserves exact values for each profile.
    #[test]
    fn toml_round_trip_preserves_values() {
        for name in available_profiles() {
            let profile = get_profile(name).unwrap();
            let serialized = toml::to_string_pretty(&profile).unwrap();
            let deserialized: Profile = toml::from_str(&serialized).unwrap();
            let reserialized = toml::to_string_pretty(&deserialized).unwrap();
            assert_eq!(
                serialized, reserialized,
                "round-trip mismatch for profile '{}'",
                name
            );
        }
    }

    /// Verify custom file loading works with a temp file.
    #[test]
    fn custom_profile_from_file() {
        let dir = std::env::temp_dir().join("vole-stress-test-profiles");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("custom-test.toml");
        std::fs::write(&path, "[plan]\nlayers = 7\nmodules_per_layer = 2\n").unwrap();
        let profile = get_profile(path.to_str().unwrap()).unwrap();
        assert_eq!(profile.plan.layers, 7);
        assert_eq!(profile.plan.modules_per_layer, 2);
        // Other fields should be defaults (full profile values)
        assert_eq!(profile.plan.functions_per_module, (3, 6));
        let _ = std::fs::remove_file(&path);
    }
}
