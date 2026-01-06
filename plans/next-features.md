# Vole: Next Features

**Status after PR #7:** 77/116 tests passing

## Quick Wins (simpler to add)

### 1. `else if` chains
Currently `} else if x > 0 {` fails. Need to parse `else if` as chained conditionals.
- Modify parser to handle `else` followed by `if`
- No AST changes needed (can desugar to nested if)

### 2. Compound assignment (`+=`, `-=`, etc.)
- Add tokens: `PlusEq`, `MinusEq`, `StarEq`, `SlashEq`, `PercentEq`
- Parse as sugar for `x = x + expr`
- Affects: `compound_assignment.vole` (once classes removed from test)

### 3. Property access (`.`)
Need for `.length` on arrays/strings. Options:
- **Minimal:** Hardcode `.length` for arrays/strings as special case
- **Better:** Add property access parsing, implement via trait intrinsics (see void stdlib/traits)

## Medium Complexity

### 4. Lambdas/Closures
Syntax: `(x) => x * 2` or `() => { ... }`
- Parse `=>` arrow functions
- Capture environment (closure conversion)
- Affects: `lambdas.vole`, `functional_interfaces.vole`

### 5. Type inference for function parameters
Currently requires `func add(a: i32, b: i32)`. Void allows `func add(a, b)`.
- Infer param types from usage
- Affects: `functions.vole`

### 6. Match expressions
```
match x {
    1 => "one",
    2 => "two",
    _ => "other"
}
```
- Affects: `match.vole`, `pattern_matching.vole`

## Larger Features

### 7. Records (value types)
```
record Point {
    x: i32,
    y: i32,
}
```
- Simpler than classes (no methods initially)
- Affects: `destructuring.vole`, `generics_records.vole`

### 8. Classes
```
class Point {
    x: i32,
    y: i32,

    func distance(self) -> f64 { ... }
}
```
- Heap allocated, reference counted
- Methods with `self`
- Affects: many tests

### 9. Error types / Fallible
```
error DivByZero {}

func divide(a: i32, b: i32) -> fallible(i32, DivByZero) {
    if b == 0 { return DivByZero{} }
    return a / b
}
```
- See void's `fallible(T, E)` pattern
- Uses TaggedValue for runtime representation
- Affects: `errors.vole`, `fallible_match.vole`, `catch_destructuring.vole`

### 10. Generics
```
func identity<T>(x: T) -> T { return x }
class Box<T> { value: T }
```
- Type parameters
- Monomorphization or type erasure
- Affects: `generics_*.vole` tests

### 11. Interfaces/Traits
```
interface Printable {
    func print(self)
}
```
- Trait intrinsics for `.length`, iterators, etc.
- See void stdlib/traits

## Not Started (lower priority)

- `import` statements
- Coroutines/generators (`yield`)
- Unicode identifiers
- String interpolation improvements
- Union types (`i32 | string`)

## Architecture Notes

### TaggedValue Foundation
PR #7 added `TaggedValue` (16-byte: tag + value) which is the foundation for:
- Heterogeneous arrays `[i32 | string]`
- Union-typed variables
- Fallible returns
- Any future dynamic typing

### Trait Intrinsics
Void implements `.length`, iterators, etc. via trait intrinsics in `stdlib/traits.zig`.
This is the proper way to add property access rather than hardcoding.

### Reference Counting
All heap objects (strings, arrays) use `RcHeader` for reference counting.
Classes/records will follow the same pattern.
