//! Statement generation configuration.
//!
//! The old grammar-based `StmtGenerator` has been replaced by the rule-based
//! dispatch system in [`crate::emit`] + [`crate::rules::stmt`].  This module
//! retains only [`StmtConfig`] because it is embedded in
//! [`crate::emitter::EmitConfig`] and deserialized from profile TOML files.

use crate::expr::ExprConfig;

/// Configuration for statement generation.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(default)]
pub struct StmtConfig {
    /// Configuration for expression generation.
    pub expr_config: ExprConfig,
    /// Maximum nesting depth for statements.
    pub max_depth: usize,
    /// Number of statements per block (range).
    pub statements_per_block: (usize, usize),
    /// Probability of generating an if statement.
    pub if_probability: f64,
    /// Probability of generating a while loop.
    pub while_probability: f64,
    /// Probability of generating a for loop.
    pub for_probability: f64,
    /// Probability of generating break/continue inside loops.
    pub break_continue_probability: f64,
    /// Probability of generating a compound assignment (+=, -=, *=).
    pub compound_assign_probability: f64,
    /// Probability of generating a direct variable reassignment (x = new_value).
    pub reassign_probability: f64,
    /// Probability of generating a raise statement in fallible functions.
    pub raise_probability: f64,
    /// Probability of generating a try expression when calling fallible functions.
    pub try_probability: f64,
    /// Probability of generating a tuple let-binding with destructuring.
    pub tuple_probability: f64,
    /// Probability of generating a fixed-size array let-binding with destructuring.
    pub fixed_array_probability: f64,
    /// Probability of generating a struct let-binding with destructuring.
    pub struct_destructure_probability: f64,
    /// Probability of generating a class let-binding with destructuring.
    pub class_destructure_probability: f64,
    /// Probability of generating a discard expression (_ = expr) statement.
    pub discard_probability: f64,
    /// Probability of generating an early return statement in function bodies.
    pub early_return_probability: f64,
    /// Probability of generating else-if chains in if statements.
    pub else_if_probability: f64,
    /// Probability of using a static method call instead of direct construction.
    pub static_call_probability: f64,
    /// Probability of generating an array index assignment (`arr[i] = expr`).
    pub array_index_assign_probability: f64,
    /// Probability of generating an `arr.push(value)` statement.
    pub array_push_probability: f64,
    /// Probability of generating an array index compound assignment (`arr[i] += expr`).
    pub array_index_compound_assign_probability: f64,
    /// Probability that `generate_array_let` produces a `let mut` binding.
    pub mutable_array_probability: f64,
    /// Probability of generating an instance method call on a class-typed local.
    pub method_call_probability: f64,
    /// Probability of generating a method call on an interface-typed variable.
    pub interface_dispatch_probability: f64,
    /// Probability of generating a `let x = match var { ... }` statement.
    pub match_probability: f64,
    /// Probability of generating a `let x = match str_var { ... }` statement.
    pub string_match_probability: f64,
    /// Probability of generating a `let x = when { cond => val, ... }` statement.
    pub when_let_probability: f64,
    /// Probability of generating nested for-loops.
    pub nested_loop_probability: f64,
    /// Probability of generating a `let x = match union_var { ... }` statement.
    pub union_match_probability: f64,
    /// Probability of generating an iterator map/filter let-binding.
    pub iter_map_filter_probability: f64,
    /// Probability of generating a call to a free function with an interface param.
    pub iface_function_call_probability: f64,
    /// Probability of generating a generic-closure-interface iterator chain.
    pub generic_closure_interface_probability: f64,
    /// Probability of generating an empty-array-through-iterator-chain pattern.
    pub empty_array_iter_probability: f64,
    /// Probability of generating a match expression whose arms produce closures.
    pub match_closure_arm_probability: f64,
    /// Probability of generating a range-based iterator chain let-binding.
    pub range_iter_probability: f64,
    /// Probability of generating a closure that captures a field value.
    pub field_closure_let_probability: f64,
    /// Probability of generating a sentinel union let-binding.
    pub sentinel_union_probability: f64,
    /// Probability of generating an optional destructure match let-binding.
    pub optional_destructure_match_probability: f64,
    /// Probability of generating a closure that captures a sentinel union.
    pub sentinel_closure_capture_probability: f64,
    /// Probability of generating a closure that captures a struct.
    pub closure_struct_capture_probability: f64,
    /// Probability of generating a nested closure pattern.
    pub nested_closure_capture_probability: f64,
    /// Probability of generating a string interpolation let-binding.
    pub string_interpolation_probability: f64,
    /// Probability of generating a method call result used in match.
    pub match_on_method_result_probability: f64,
    /// Probability of generating an iterator-map that calls a class method.
    pub iter_method_map_probability: f64,
    /// Probability of generating a string split/collect let-binding.
    pub string_split_probability: f64,
    /// Probability of generating a string method call let-binding.
    pub string_method_probability: f64,
    /// Probability of generating an iterator predicate let-binding.
    pub iter_predicate_probability: f64,
    /// Probability of generating an iterator chunks/windows let-binding.
    pub iter_chunks_windows_probability: f64,
    /// Probability of generating a checked/wrapping/saturating arithmetic call.
    pub checked_arithmetic_probability: f64,
}

impl Default for StmtConfig {
    fn default() -> Self {
        // Default values match the "full" profile so TOML files only specify overrides.
        Self {
            expr_config: ExprConfig::default(),
            max_depth: 3,
            statements_per_block: (2, 4),
            if_probability: 0.3,
            while_probability: 0.15,
            for_probability: 0.2,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            reassign_probability: 0.15,
            raise_probability: 0.12,
            try_probability: 0.15,
            tuple_probability: 0.12,
            fixed_array_probability: 0.12,
            struct_destructure_probability: 0.15,
            class_destructure_probability: 0.12,
            discard_probability: 0.05,
            early_return_probability: 0.15,
            else_if_probability: 0.30,
            static_call_probability: 0.30,
            array_index_assign_probability: 0.10,
            array_push_probability: 0.08,
            array_index_compound_assign_probability: 0.10,
            mutable_array_probability: 0.4,
            method_call_probability: 0.12,
            interface_dispatch_probability: 0.10,
            match_probability: 0.08,
            string_match_probability: 0.06,
            when_let_probability: 0.08,
            nested_loop_probability: 0.06,
            union_match_probability: 0.10,
            iter_map_filter_probability: 0.10,
            iface_function_call_probability: 0.10,
            generic_closure_interface_probability: 0.15,
            empty_array_iter_probability: 0.06,
            match_closure_arm_probability: 0.10,
            range_iter_probability: 0.08,
            field_closure_let_probability: 0.08,
            sentinel_union_probability: 0.15,
            optional_destructure_match_probability: 0.12,
            sentinel_closure_capture_probability: 0.10,
            closure_struct_capture_probability: 0.12,
            nested_closure_capture_probability: 0.10,
            string_interpolation_probability: 0.12,
            match_on_method_result_probability: 0.10,
            iter_method_map_probability: 0.10,
            string_split_probability: 0.08,
            string_method_probability: 0.10,
            iter_predicate_probability: 0.08,
            iter_chunks_windows_probability: 0.06,
            checked_arithmetic_probability: 0.0,
        }
    }
}
