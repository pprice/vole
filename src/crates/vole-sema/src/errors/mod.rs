// errors/mod.rs
//! Semantic analysis errors (E2xxx).

#![allow(unused_assignments)] // False positives from thiserror derive

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Error, Debug, Diagnostic, Clone)]
pub enum SemanticError {
    #[error("expected {expected}, found {found}")]
    #[diagnostic(code(E2001))]
    TypeMismatch {
        expected: String,
        found: String,
        #[label("type mismatch")]
        span: SourceSpan,
    },

    #[error("undefined variable '{name}'")]
    #[diagnostic(code(E2002))]
    UndefinedVariable {
        name: String,
        #[label("not found in scope")]
        span: SourceSpan,
    },

    #[error("undefined variable in field shorthand")]
    #[diagnostic(code(E2003))]
    UndefinedShorthandVariable {
        name: String,
        #[label("shorthand `{name}` expands to `{name}: {name}`, but `{name}` is not defined")]
        span: SourceSpan,
    },

    #[error("cannot assign to immutable variable '{name}'")]
    #[diagnostic(code(E2006), help("consider declaring with 'var' to make it mutable"))]
    ImmutableAssignment {
        name: String,
        #[label("cannot assign")]
        span: SourceSpan,
        #[label("declared as immutable here")]
        declaration: SourceSpan,
    },

    #[error("break outside of loop")]
    #[diagnostic(code(E2008))]
    InvalidBreak {
        #[label("not inside a loop")]
        span: SourceSpan,
    },

    #[error("expected {expected} arguments, found {found}")]
    #[diagnostic(code(E2012))]
    WrongArgumentCount {
        expected: usize,
        found: usize,
        #[label("wrong number of arguments")]
        span: SourceSpan,
    },

    #[error("expected {min} to {max} arguments, found {found}")]
    #[diagnostic(code(E2088))]
    WrongArgumentCountRange {
        min: usize,
        max: usize,
        found: usize,
        #[label("wrong number of arguments")]
        span: SourceSpan,
    },

    #[error("expected {expected} type arguments, found {found}")]
    #[diagnostic(code(E2013))]
    WrongTypeArgCount {
        expected: usize,
        found: usize,
        #[label("wrong number of type arguments")]
        span: SourceSpan,
    },

    #[error("condition must be boolean, found {found}")]
    #[diagnostic(code(E2027))]
    ConditionNotBool {
        found: String,
        #[label("expected bool")]
        span: SourceSpan,
    },

    #[error("non-exhaustive match")]
    #[diagnostic(
        code(E2030),
        help("add a wildcard pattern '_' or identifier to catch remaining cases")
    )]
    NonExhaustiveMatch {
        #[label("match may not cover all cases")]
        span: SourceSpan,
    },

    #[error("match arms have incompatible types: expected {expected}, found {found}")]
    #[diagnostic(code(E2031))]
    MatchArmTypeMismatch {
        expected: String,
        found: String,
        #[label("first arm has type {expected}")]
        first_arm: SourceSpan,
        #[label("this arm has type {found}")]
        span: SourceSpan,
    },

    #[error("match guard must be boolean, found {found}")]
    #[diagnostic(code(E2032))]
    MatchGuardNotBool {
        found: String,
        #[label("expected bool")]
        span: SourceSpan,
    },

    #[error("pattern type mismatch: expected {expected}, found {found}")]
    #[diagnostic(code(E2033))]
    PatternTypeMismatch {
        expected: String,
        found: String,
        #[label("pattern doesn't match scrutinee type")]
        span: SourceSpan,
    },

    #[error("cannot use return value of void function")]
    #[diagnostic(code(E2040), help("void functions don't return a usable value"))]
    VoidReturnUsed {
        #[label("void function called here")]
        span: SourceSpan,
    },

    #[error("null coalescing requires optional type, found {found}")]
    #[diagnostic(code(E2041))]
    NullCoalesceNotOptional {
        found: String,
        #[label("expected optional type")]
        span: SourceSpan,
    },

    #[error("type '{tested}' is not a variant of '{union_type}'")]
    #[diagnostic(code(E2042))]
    IsNotVariant {
        tested: String,
        union_type: String,
        #[label("not a variant of the union")]
        span: SourceSpan,
    },

    #[error("cannot infer type of lambda parameter '{name}'")]
    #[diagnostic(code(E2043), help("add a type annotation: ({name}: Type) => ..."))]
    CannotInferLambdaParam {
        name: String,
        #[label("type cannot be inferred")]
        span: SourceSpan,
    },

    #[error("cannot call non-function type '{ty}'")]
    #[diagnostic(code(E2044))]
    NotCallable {
        ty: String,
        #[label("not a function")]
        span: SourceSpan,
    },

    #[error("unknown type '{name}'")]
    #[diagnostic(code(E2020), help("{hint}"))]
    UnknownType {
        name: String,
        hint: String,
        #[label("not a known type")]
        span: SourceSpan,
    },

    #[error("missing field '{field}' in struct literal for '{ty}'")]
    #[diagnostic(code(E2021))]
    MissingField {
        ty: String,
        field: String,
        #[label("this field is required")]
        span: SourceSpan,
    },

    #[error("unknown field '{field}' in type '{ty}'")]
    #[diagnostic(code(E2022))]
    UnknownField {
        ty: String,
        field: String,
        #[label("no such field")]
        span: SourceSpan,
    },

    #[error("unknown method '{method}' on type '{ty}'")]
    #[diagnostic(code(E2023))]
    UnknownMethod {
        ty: String,
        method: String,
        #[label("no such method")]
        span: SourceSpan,
    },

    #[error("unknown interface '{name}'")]
    #[diagnostic(code(E2050))]
    UnknownInterface {
        name: String,
        #[label("not a known interface")]
        span: SourceSpan,
    },

    #[error("cannot implement interface for unknown type '{name}'")]
    #[diagnostic(code(E2051))]
    UnknownImplementType {
        name: String,
        #[label("not a known type")]
        span: SourceSpan,
    },

    #[error(
        "type '{type_name}' does not satisfy interface '{interface_name}': missing method '{method}'"
    )]
    #[diagnostic(code(E2052))]
    InterfaceNotSatisfied {
        type_name: String,
        interface_name: String,
        method: String,
        #[label("declared to implement {interface_name}")]
        span: SourceSpan,
    },

    #[error("method '{method}' has wrong signature for interface '{interface_name}'")]
    #[diagnostic(code(E2053), help("{details}\ninterface requires: {expected}"))]
    InterfaceSignatureMismatch {
        interface_name: String,
        method: String,
        expected: String,
        /// The actual signature found. Not currently displayed but stored for
        /// potential future use in enhanced error messages.
        found: String,
        details: String,
        #[label("signature mismatch")]
        span: SourceSpan,
    },

    #[error("raise statement outside fallible function")]
    #[diagnostic(code(E2054))]
    RaiseOutsideFallible {
        #[label("raise must be in a function with fallible return type")]
        span: SourceSpan,
    },

    #[error("undefined error type '{name}'")]
    #[diagnostic(code(E2055))]
    UndefinedError {
        name: String,
        #[label("not defined")]
        span: SourceSpan,
    },

    #[error("error type '{raised}' is not in function's error set")]
    #[diagnostic(
        code(E2056),
        help("add {raised} to error set, or use valid error types for this function: {declared}")
    )]
    IncompatibleRaiseError {
        raised: String,
        declared: String,
        #[label("cannot raise this error type")]
        span: SourceSpan,
    },

    #[error("try expression requires fallible type, found {found}")]
    #[diagnostic(
        code(E2057),
        help("try can only propagate errors from fallible function calls")
    )]
    TryOnNonFallible {
        found: String,
        #[label("not a fallible type")]
        span: SourceSpan,
    },

    #[error("success pattern used on non-fallible type '{found}'")]
    #[diagnostic(code(E2061))]
    SuccessPatternOnNonFallible {
        found: String,
        #[label("expected fallible type")]
        span: SourceSpan,
    },

    #[error("error pattern used on non-fallible type '{found}'")]
    #[diagnostic(code(E2062))]
    ErrorPatternOnNonFallible {
        found: String,
        #[label("expected fallible type")]
        span: SourceSpan,
    },

    #[error("match on fallible type requires at least one error arm")]
    #[diagnostic(code(E2063))]
    MissingErrorArm {
        #[label("fallible type matched here")]
        span: SourceSpan,
    },

    #[error("try expression outside fallible function")]
    #[diagnostic(code(E2064))]
    TryOutsideFallible {
        #[label("try must be in a function with fallible return type")]
        span: SourceSpan,
    },

    #[error("try propagates '{try_error}' but function error type is '{func_error}'")]
    #[diagnostic(code(E2065))]
    IncompatibleTryError {
        try_error: String,
        func_error: String,
        #[label("incompatible error type")]
        span: SourceSpan,
    },

    #[error("module not found: {path}")]
    #[diagnostic(code(E2066), help("{message}"))]
    ModuleNotFound {
        path: String,
        message: String,
        #[label("import here")]
        span: SourceSpan,
    },

    #[error("module '{module}' has no export '{name}'")]
    #[diagnostic(code(E2067))]
    ModuleNoExport {
        module: String,
        name: String,
        #[label("unknown export")]
        span: SourceSpan,
    },

    #[error("failed to parse module: {path}")]
    #[diagnostic(code(E2068), help("{message}"))]
    ModuleParseError {
        path: String,
        message: String,
        #[label("import here")]
        span: SourceSpan,
    },

    #[error("yield expression outside of generator function")]
    #[diagnostic(code(E2069), help("yield can only be used inside generator functions"))]
    YieldOutsideGenerator {
        #[label("yield used here")]
        span: SourceSpan,
    },

    #[error("yield in function without Iterator return type")]
    #[diagnostic(
        code(E2070),
        help("functions that use yield must have return type Iterator<T>")
    )]
    YieldInNonGenerator {
        found: String,
        #[label("function returns {found}, not Iterator<T>")]
        span: SourceSpan,
    },

    #[error("yield expression type '{found}' doesn't match Iterator element type '{expected}'")]
    #[diagnostic(code(E2071))]
    YieldTypeMismatch {
        expected: String,
        found: String,
        #[label("expected {expected}")]
        span: SourceSpan,
    },

    #[error("cannot call method '{method}' on optional type '{ty}'")]
    #[diagnostic(
        code(E2072),
        help("unwrap the value or narrow the type before calling the method")
    )]
    MethodOnOptional {
        ty: String,
        method: String,
        #[label("method call on optional type")]
        span: SourceSpan,
    },

    #[error("cannot call method '{method}' on union type '{ty}'")]
    #[diagnostic(code(E2073), help("narrow the type before calling the method"))]
    MethodOnUnion {
        ty: String,
        method: String,
        #[label("method call on union type")]
        span: SourceSpan,
    },

    #[error("type argument for '{type_param}' does not satisfy constraint '{expected}'")]
    #[diagnostic(code(E2074))]
    TypeParamConstraintMismatch {
        type_param: String,
        expected: String,
        found: String,
        #[label("found '{found}'")]
        span: SourceSpan,
    },

    #[error("interface method '{method}' has a body but is not marked 'default'")]
    #[diagnostic(code(E2075), help("add 'default' keyword: default func {method}(...)"))]
    InterfaceMethodBodyWithoutDefault {
        method: String,
        #[label("missing 'default' keyword")]
        span: SourceSpan,
    },

    #[error("index {index} out of bounds for tuple of length {len}")]
    #[diagnostic(code(E2076))]
    IndexOutOfBounds {
        index: usize,
        len: usize,
        #[label("index out of bounds")]
        span: SourceSpan,
    },

    #[error("'self' cannot be used in static method '{method}'")]
    #[diagnostic(
        code(E2077),
        help("static methods are called on the type, not on an instance")
    )]
    SelfInStaticMethod {
        method: String,
        #[label("'self' is not available in static context")]
        span: SourceSpan,
    },

    #[error("type '{type_name}' missing required static method '{method}'")]
    #[diagnostic(code(E2078))]
    MissingStaticMethod {
        type_name: String,
        method: String,
        interface: String,
        #[label("interface requires static method")]
        span: SourceSpan,
    },

    #[error("if expression requires an else branch")]
    #[diagnostic(
        code(E2079),
        help("add an else branch: if cond {{ ... }} else {{ ... }}")
    )]
    IfExprMissingElse {
        #[label("if expression used as value needs both branches")]
        span: SourceSpan,
    },

    #[error("ambiguous type alias: '{name}' could be a type or a value")]
    #[diagnostic(
        code(E2080),
        help("add explicit ': type' annotation: let {name}: type = {type_name}")
    )]
    AmbiguousTypeAlias {
        name: String,
        type_name: String,
        #[label("'{type_name}' is a type, but syntax is ambiguous")]
        span: SourceSpan,
    },

    #[error("type '{found}' does not satisfy structural constraint '{constraint}'")]
    #[diagnostic(code(E2081), help("{mismatch}"))]
    StructuralConstraintMismatch {
        constraint: String,
        found: String,
        mismatch: String,
        #[label("structural constraint not satisfied")]
        span: SourceSpan,
    },

    #[error("cannot infer return type for function '{name}'")]
    #[diagnostic(
        code(E2082),
        help("add explicit return type: func {name}(...) -> Type")
    )]
    CannotInferReturnType {
        name: String,
        #[label("return type cannot be inferred")]
        span: SourceSpan,
    },

    #[error("missing return statement in function '{name}'")]
    #[diagnostic(code(E2083), help("{hint}"))]
    MissingReturn {
        name: String,
        expected: String,
        hint: String,
        #[label("function expects to return {expected}")]
        span: SourceSpan,
    },

    #[error("parameter with default value must come after parameters without defaults")]
    #[diagnostic(
        code(E2084),
        help("move parameter '{name}' after all non-default parameters")
    )]
    DefaultParamNotLast {
        name: String,
        #[label("non-default parameter after default parameter")]
        span: SourceSpan,
    },

    #[error("default value type mismatch: expected {expected}, found {found}")]
    #[diagnostic(code(E2085))]
    DefaultExprTypeMismatch {
        expected: String,
        found: String,
        #[label("default value has wrong type")]
        span: SourceSpan,
    },

    #[error("required field '{field}' cannot follow field with default value")]
    #[diagnostic(
        code(E2086),
        help("move all fields with default values to the end of the field list")
    )]
    RequiredFieldAfterDefaulted {
        field: String,
        #[label("required field after defaulted field")]
        span: SourceSpan,
    },

    #[error("field default type mismatch: expected {expected}, found {found}")]
    #[diagnostic(code(E2087))]
    FieldDefaultTypeMismatch {
        expected: String,
        found: String,
        field: String,
        #[label("default value has wrong type")]
        span: SourceSpan,
    },

    #[error("default value for '{name}' must be a constant expression")]
    #[diagnostic(
        code(E2089),
        help(
            "use literals, operators on constants, or array/tuple literals with constant elements"
        )
    )]
    DefaultMustBeConstant {
        name: String,
        #[label("non-constant expression")]
        span: SourceSpan,
    },

    #[error("when expression must have at least one arm")]
    #[diagnostic(code(E2090))]
    WhenExprEmpty {
        #[label("empty when expression")]
        span: SourceSpan,
    },

    #[error("when expression is not exhaustive")]
    #[diagnostic(
        code(E2091),
        help("add a wildcard arm '_ => ...' to handle all remaining cases")
    )]
    WhenExprNotExhaustive {
        #[label("when expression may not cover all cases")]
        span: SourceSpan,
    },

    #[error("when condition must be boolean, found {found}")]
    #[diagnostic(code(E2092))]
    WhenConditionNotBool {
        found: String,
        #[label("expected bool")]
        span: SourceSpan,
    },

    #[error("when arms have incompatible types: expected {expected}, found {found}")]
    #[diagnostic(code(E2093))]
    WhenArmTypeMismatch {
        expected: String,
        found: String,
        #[label("type mismatch")]
        span: SourceSpan,
    },

    #[error("invalid literal suffix")]
    #[diagnostic(code(E2094), help("{hint}"))]
    InvalidLiteralSuffix {
        suffix: String,
        suffix_kind: String,
        literal_kind: String,
        hint: String,
        #[label("cannot apply {suffix_kind} suffix `_{suffix}` to {literal_kind} literal")]
        span: SourceSpan,
    },

    #[error("literal out of range for `{suffix}`")]
    #[diagnostic(code(E2095), help("use a larger type suffix"))]
    LiteralOutOfRange {
        suffix: String,
        value: String,
        range: String,
        #[label("value {value} does not fit in `{suffix}` ({range})")]
        span: SourceSpan,
    },

    #[error("return type mismatch in function expecting {expected}")]
    #[diagnostic(code(E2096), help("function expects {expected}"))]
    ReturnTypeMismatch {
        expected: String,
        found: String,
        #[label("this returns {found}")]
        span: SourceSpan,
    },

    #[error("expected module, found {found}")]
    #[diagnostic(
        code(E2097),
        help("'{name}' must be a module for qualified interface access")
    )]
    ExpectedModule {
        name: String,
        found: String,
        #[label("'{name}' is {found}, not a module")]
        span: SourceSpan,
    },

    #[error("the `never` type can only be used as a return type")]
    #[diagnostic(
        code(E2098),
        help(
            "`never` indicates a function that never returns; it cannot be used for variables, parameters, or fields"
        )
    )]
    NeverNotAllowed {
        #[label("cannot use `never` here")]
        span: SourceSpan,
    },

    #[error("`if` expressions cannot be used as values")]
    #[diagnostic(
        code(E2099),
        help("use `when` for conditional expressions: when {{ cond => value, _ => other }}")
    )]
    IfExpressionUsedAsValue {
        #[label("`if` is a statement, not an expression")]
        span: SourceSpan,
    },

    #[error("block expressions cannot have trailing expressions")]
    #[diagnostic(
        code(E2100),
        help("use explicit `return` in functions, or use `when`/`match` for conditional values")
    )]
    BlockTrailingExpression {
        #[label("trailing expression not allowed in block")]
        span: SourceSpan,
    },

    #[error("struct type '{name}' cannot be used as a union variant")]
    #[diagnostic(
        code(E2101),
        help("structs are value types and cannot participate in unions; use a class instead")
    )]
    StructInUnion {
        name: String,
        #[label("struct type not allowed in union")]
        span: SourceSpan,
    },

    #[error("intersection types (`A + B`) are not supported in type positions")]
    #[diagnostic(code(E2103), help("use type constraints instead: `<T: A + B>`"))]
    CombinationTypeNotAllowed {
        #[label("intersection type not allowed here")]
        span: SourceSpan,
    },

    #[error("duplicate implementation of '{interface}' for '{target}'")]
    #[diagnostic(code(E2104))]
    DuplicateImplementation {
        interface: String,
        target: String,
        #[label("duplicate implementation here")]
        span: SourceSpan,
        #[label("'{interface}' already implemented here")]
        first_impl: SourceSpan,
    },

    #[error("cannot compare non-optional type '{ty}' to nil")]
    #[diagnostic(
        code(E2105),
        help(
            "only optional types (T?) can be compared to nil; this comparison is always {result}"
        )
    )]
    NonOptionalNilComparison {
        ty: String,
        result: String,
        #[label("'{ty}' is not optional")]
        span: SourceSpan,
    },

    #[error("circular import detected: {path}")]
    #[diagnostic(
        code(E2106),
        help("modules cannot import themselves or form import cycles")
    )]
    CircularImport {
        path: String,
        #[label("import creates a cycle")]
        span: SourceSpan,
    },

    #[error("duplicate concrete type mapping for generic external '{ty}'")]
    #[diagnostic(
        code(E2107),
        help("each concrete type can appear at most once in a where mapping block")
    )]
    DuplicateGenericExternalTypeMapping {
        ty: String,
        #[label("duplicate mapping for '{ty}'")]
        span: SourceSpan,
        #[label("first mapping for '{ty}' is here")]
        first: SourceSpan,
    },

    #[error("duplicate default mapping for generic external")]
    #[diagnostic(code(E2108), help("use a single `default => \"...\"` fallback arm"))]
    DuplicateGenericExternalDefaultMapping {
        #[label("duplicate default mapping")]
        span: SourceSpan,
        #[label("first default mapping is here")]
        first: SourceSpan,
    },

    #[error("match expression must have at least one arm")]
    #[diagnostic(code(E2109))]
    MatchExprEmpty {
        #[label("empty match expression")]
        span: SourceSpan,
    },

    #[error("could not locate standard library at '{path}': {message}")]
    #[diagnostic(
        code(E2110),
        help("check that the standard library is installed correctly")
    )]
    PreludeNotFound { path: String, message: String },

    #[error("failed to parse standard library file '{path}': {message}")]
    #[diagnostic(
        code(E2111),
        help("the standard library file may be corrupted or from an incompatible version")
    )]
    PreludeParseError { path: String, message: String },

    #[error("method '{method}' on type '{ty}' is only visible within its defining module")]
    #[diagnostic(
        code(E2112),
        help("extension methods defined with `extend Type {{ }}` are file-scoped")
    )]
    ExtensionMethodNotVisible {
        ty: String,
        method: String,
        #[label("this method is not visible here")]
        span: SourceSpan,
    },

    #[error("named arguments are not supported for external functions")]
    #[diagnostic(
        code(E2113),
        help("external functions use C calling conventions; call positionally instead")
    )]
    ExternalFunctionNamedArg {
        #[label("named argument used here")]
        span: SourceSpan,
    },

    #[error("positional argument after named argument")]
    #[diagnostic(
        code(E2114),
        help("all positional arguments must come before named arguments")
    )]
    PositionalArgAfterNamed {
        #[label("positional argument not allowed here")]
        span: SourceSpan,
        #[label("named argument appeared here")]
        named_span: SourceSpan,
    },

    #[error("unknown parameter name '{name}'")]
    #[diagnostic(code(E2115))]
    UnknownParamName {
        name: String,
        #[label("no parameter named '{name}'")]
        span: SourceSpan,
    },

    #[error("argument '{name}' provided both positionally and by name")]
    #[diagnostic(code(E2116))]
    DuplicateArg {
        name: String,
        #[label("named argument here")]
        span: SourceSpan,
    },

    #[error("missing required argument '{name}'")]
    #[diagnostic(code(E2117))]
    MissingRequiredArg {
        name: String,
        #[label("call is missing argument '{name}'")]
        span: SourceSpan,
    },

    #[error("'it' cannot be used inside a nested implicit lambda")]
    #[diagnostic(
        code(E2118),
        help("use an explicit parameter name instead, e.g.: x => x > 0")
    )]
    ItInNestedLambda {
        #[label("'it' used here inside nested lambda context")]
        span: SourceSpan,
    },

    #[error("'{name}' is not an annotation type")]
    #[diagnostic(code(E2119), help("add @annotation to the declaration of '{name}'"))]
    NotAnAnnotationType {
        name: String,
        #[label("not an annotation type")]
        span: SourceSpan,
    },

    #[error("unknown annotation type '@{name}'")]
    #[diagnostic(code(E2120))]
    UnknownAnnotation {
        name: String,
        #[label("annotation type not found")]
        span: SourceSpan,
    },

    #[error("annotation type '{name}' cannot be generic")]
    #[diagnostic(
        code(E2121),
        help(
            "remove the type parameters from '{name}'; annotations are simple metadata, not generic abstractions"
        )
    )]
    GenericAnnotationType {
        name: String,
        #[label("generic type cannot be used as an annotation type")]
        span: SourceSpan,
    },

    #[error("annotation '@{name}' expects {expected} arguments, found {found}")]
    #[diagnostic(code(E2122))]
    AnnotationWrongArgCount {
        name: String,
        expected: usize,
        found: usize,
        #[label("wrong number of annotation arguments")]
        span: SourceSpan,
    },

    #[error("annotation '@{annotation}' has no field named '{arg_name}'")]
    #[diagnostic(code(E2123))]
    AnnotationUnknownArg {
        annotation: String,
        arg_name: String,
        #[label("unknown annotation field")]
        span: SourceSpan,
    },

    #[error("annotation '@{annotation}' field '{field}' specified more than once")]
    #[diagnostic(code(E2124))]
    AnnotationDuplicateArg {
        annotation: String,
        field: String,
        #[label("duplicate annotation argument")]
        span: SourceSpan,
    },
}

/// Semantic warnings (W3xxx) - these don't prevent compilation but indicate potential issues
/// Note: W3xxx to avoid overlap with E2xxx error codes
#[derive(Error, Debug, Diagnostic, Clone)]
pub enum SemanticWarning {
    #[error("structural type alias '{name}' is unusual")]
    #[diagnostic(
        code(W3001),
        help(
            "structural types are typically used inline as constraints: func foo<T: {{ {fields} }}>(x: T)"
        )
    )]
    StructuralTypeAlias {
        name: String,
        fields: String,
        #[label("consider using an interface instead")]
        span: SourceSpan,
    },

    #[error("unused expression result of type '{ty}'")]
    #[diagnostic(code(W3002), help("use `_ = expr` to discard explicitly"))]
    UnusedExpressionResult {
        ty: String,
        #[label("expression result is not used")]
        span: SourceSpan,
    },

    #[error("mutable binding on module import has no effect")]
    #[diagnostic(code(W3003), help("module bindings are always immutable"))]
    MutableModuleBinding {
        #[label("'mut' has no effect here")]
        span: SourceSpan,
    },

    #[error("union with `{ty}` will be simplified")]
    #[diagnostic(code(W3004), help("{simplification_hint}"))]
    UnionSimplification {
        ty: String,
        simplification_hint: String,
        #[label("{label}")]
        span: SourceSpan,
        label: String,
    },

    #[error("prelude module '{module}' had partial semantic analysis ({error_count} errors)")]
    #[diagnostic(
        code(W3005),
        help(
            "prelude loading continued with partial results; review logs for underlying semantic errors"
        )
    )]
    PreludePartialAnalysis { module: String, error_count: usize },
}

/// Returns a "did you mean" suggestion for common type typos.
///
/// Maps common mistakes to the correct Vole type names:
/// - `int`, `Int`, `INT` -> `i64`
/// - `str`, `Str` -> `string`
/// - `String` -> `string`
/// - `boolean`, `Boolean` -> `bool`
/// - `float`, `Float`, `double`, `Double` -> `f64`
/// - `char`, `Char` -> note about no char type
/// - `void`, `Void` -> note about using () or no return type
/// - `array`, `Array` -> `[T]`
pub(crate) fn unknown_type_hint(name: &str) -> String {
    match name {
        "int" | "Int" | "INT" | "integer" | "Integer" => "did you mean 'i64'?".to_string(),
        "str" | "Str" => "did you mean 'string'?".to_string(),
        "String" => "did you mean 'string'? (lowercase in Vole)".to_string(),
        "boolean" | "Boolean" | "Bool" => "did you mean 'bool'?".to_string(),
        "float" | "Float" => "did you mean 'f64'?".to_string(),
        "double" | "Double" => {
            "did you mean 'f64'? (Vole uses f64 for double-precision floats)".to_string()
        }
        "char" | "Char" | "Character" => {
            "Vole has no char type; use 'string' for single characters".to_string()
        }
        "void" | "Void" => {
            "Vole has no void type; omit return type for functions that return nothing".to_string()
        }
        "array" | "Array" => {
            "did you mean '[T]'? (e.g., [i64] for an array of integers)".to_string()
        }
        _ => "type not found".to_string(),
    }
}
