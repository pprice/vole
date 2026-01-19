// src/sema/types/special.rs
//
// Special types module - supporting types for Type enum's "special" variants.
//
// # Special Types Overview
//
// The Type enum contains several "special" variants that don't fit the categories
// of primitives, nominal types (class/record/interface), or compound types (array/union):
//
// ## Control Flow Types
// - `Void` - Return type for functions with no value (like `print`)
// - `Nil` - The "absence of value" for optionals (`T?` = `T | nil`)
// - `Done` - Sentinel for iterator termination (`next() -> T | Done`)
//
// ## Inference & Error Handling Types
// - `Placeholder(PlaceholderKind)` - Type waiting for inference or substitution
// - `Invalid(AnalysisError)` - Analysis failed, carries error chain
//
// ## Meta Types
// - `Type` - The metatype (type of types), for type aliases like `let MyInt = i32`
// - `TypeParam(NameId)` - A type parameter in generic context (`T` in `Box<T>`)
//
// ## Compound Special Types
// - `Module(ModuleType)` - Imported module with exports
// - `RuntimeIterator` - Builtin iterator (array.iter(), range.iter())
// - `Range` - Range literal type (0..10)
//
// This module defines the supporting structs for these variants. The variants
// themselves remain in the main Type enum for pattern matching convenience.

use crate::frontend::Span;
use crate::identity::{ModuleId, NameId};
use crate::sema::type_arena::TypeId;

/// Analysis error - represents a type that couldn't be determined.
///
/// Designed to be maximally useful for debugging:
/// - `kind` categorizes the error for filtering/grouping
/// - `message` provides full context with relevant details
/// - `source` chains to upstream errors for full traceability
///
/// # Examples
/// ```ignore
/// // Simple error
/// AnalysisError::new("unknown_field", "field 'foo' not found on Record 'Bar'")
///
/// // Error with location
/// AnalysisError::at("type_mismatch", "expected i32, got string", span)
///
/// // Propagated error
/// AnalysisError::propagate(&source_err, "while checking assignment", Some(span))
/// ```
#[derive(Debug, Clone)]
pub struct AnalysisError {
    /// Category for filtering/grouping (e.g., "unknown_field", "type_mismatch")
    pub kind: &'static str,
    /// Full human-readable description with all relevant context
    /// e.g., "field 'foo' not found on Record 'Bar' (has fields: x, y, z)"
    pub message: String,
    /// Where it happened in source
    pub span: Option<Span>,
    /// The upstream error we're propagating from (if any)
    pub source: Option<Box<AnalysisError>>,
}

impl AnalysisError {
    /// Create a fresh error with full context (preferred for new code)
    pub fn new(kind: &'static str, message: impl Into<String>) -> Self {
        let msg = message.into();
        tracing::trace!(kind, %msg, "AnalysisError::new");
        Self {
            kind,
            message: msg,
            span: None,
            source: None,
        }
    }

    /// Create a fresh error with location
    pub fn at(kind: &'static str, message: impl Into<String>, span: Span) -> Self {
        let msg = message.into();
        tracing::trace!(kind, %msg, ?span, "AnalysisError::at");
        Self {
            kind,
            message: msg,
            span: Some(span),
            source: None,
        }
    }

    /// Create a simple error (for migration from old API - prefer new() with message)
    pub fn simple(kind: &'static str) -> Self {
        Self {
            kind,
            message: kind.to_string(),
            span: None,
            source: None,
        }
    }

    /// Propagate from an existing error, adding context about what we were doing
    pub fn propagate(
        source: &AnalysisError,
        context: impl Into<String>,
        span: Option<Span>,
    ) -> Self {
        let ctx = context.into();
        let result = Self {
            kind: "propagate",
            message: ctx.clone(),
            span,
            source: Some(Box::new(source.clone())),
        };
        tracing::trace!(
            context = %ctx,
            root_cause = %source.root_cause().message,
            "AnalysisError::propagate"
        );
        result
    }

    /// Get the root cause of this error chain
    pub fn root_cause(&self) -> &AnalysisError {
        match &self.source {
            Some(src) => src.root_cause(),
            None => self,
        }
    }

    /// Format the full error chain for debugging (multi-line)
    pub fn full_chain(&self) -> String {
        let mut parts = vec![self.format_single()];
        let mut current = &self.source;
        while let Some(src) = current {
            parts.push(src.format_single());
            current = &src.source;
        }
        parts.join("\n  <- ")
    }

    fn format_single(&self) -> String {
        let mut s = format!("[{}] {}", self.kind, self.message);
        if let Some(span) = &self.span {
            s.push_str(&format!(" (line {}:{})", span.line, span.column));
        }
        s
    }
}

impl PartialEq for AnalysisError {
    fn eq(&self, _other: &Self) -> bool {
        // For type comparison, all Invalid types are equal
        // (we don't want type mismatches based on error details)
        true
    }
}

impl Eq for AnalysisError {}

// Custom Hash to match PartialEq semantics - all errors hash the same
impl std::hash::Hash for AnalysisError {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // All AnalysisErrors are equal, so they must have the same hash
        0u8.hash(state);
    }
}

impl std::fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.full_chain())
    }
}

/// What kind of type is being deferred as a placeholder.
///
/// Placeholders are used during type inference and generic instantiation:
///
/// - `Inference` - Type to be inferred (e.g., `let x = []` - element type unknown)
/// - `TypeParam(name)` - Generic type parameter (e.g., `T` in `Box<T>`)
/// - `SelfType` - `Self` in interface method signatures
///
/// Placeholders are resolved during type checking or monomorphization.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceholderKind {
    /// Generic type inference placeholder (e.g., empty array element type)
    Inference,
    /// Type parameter (e.g., T in Box<T>) - carries the parameter name for debugging
    TypeParam(String),
    /// Self type in interface signatures - resolved when interface is implemented
    SelfType,
}

impl std::fmt::Display for PlaceholderKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlaceholderKind::Inference => write!(f, "?"),
            PlaceholderKind::TypeParam(name) => write!(f, "{}", name),
            PlaceholderKind::SelfType => write!(f, "Self"),
        }
    }
}

/// A constant value that can be stored in a module.
///
/// Used by ModuleType to track compile-time constant exports:
/// ```ignore
/// // In math.vole:
/// let PI = 3.14159
/// let MAX_SIZE = 1024
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum ConstantValue {
    I64(i64),
    F64(f64),
    Bool(bool),
    String(String),
}

impl Eq for ConstantValue {}

// Manual Hash implementation because f64 doesn't implement Hash
impl std::hash::Hash for ConstantValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            ConstantValue::I64(v) => v.hash(state),
            ConstantValue::F64(v) => v.to_bits().hash(state),
            ConstantValue::Bool(v) => v.hash(state),
            ConstantValue::String(v) => v.hash(state),
        }
    }
}

/// Module type: represents an imported module with its exports.
///
/// Created when a module is imported:
/// ```ignore
/// let math = import("std/math")
/// math.sin(1.0)  // Access export via module type
/// ```
///
/// Tracks:
/// - All exported types and functions
/// - Constant values that can be inlined
/// - Which functions are external (FFI)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleType {
    /// Unique identifier for this module
    pub module_id: ModuleId,
    /// Exports keyed by fully-qualified name id (TypeId into the type arena)
    pub exports: std::collections::HashMap<NameId, TypeId>,
    /// Constant values from the module (let PI = 3.14...)
    pub constants: std::collections::HashMap<NameId, ConstantValue>,
    /// Names of functions that are external (FFI) - others are pure Vole
    pub external_funcs: std::collections::HashSet<NameId>,
}

// Manual Hash implementation because HashMap doesn't implement Hash.
// Two ModuleTypes with the same module_id refer to the same module.
impl std::hash::Hash for ModuleType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.module_id.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_analysis_error_chain() {
        let root = AnalysisError::new("root_cause", "original error");
        let propagated = AnalysisError::propagate(&root, "while doing X", None);

        assert_eq!(propagated.root_cause().kind, "root_cause");
        assert!(propagated.full_chain().contains("original error"));
        assert!(propagated.full_chain().contains("while doing X"));
    }

    #[test]
    fn test_analysis_error_equality() {
        // All AnalysisErrors are equal (for Type comparison)
        let err1 = AnalysisError::new("a", "message 1");
        let err2 = AnalysisError::new("b", "message 2");
        assert_eq!(err1, err2);
    }

    #[test]
    fn test_placeholder_display() {
        assert_eq!(format!("{}", PlaceholderKind::Inference), "?");
        assert_eq!(format!("{}", PlaceholderKind::TypeParam("T".into())), "T");
        assert_eq!(format!("{}", PlaceholderKind::SelfType), "Self");
    }
}
