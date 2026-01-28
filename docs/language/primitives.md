# Primitive Types

This document covers Vole's primitive types: their behavior, operations, and available methods.

## Overview

Vole has the following primitive types:

| Category | Types |
|----------|-------|
| Signed integers | `i8`, `i16`, `i32`, `i64`, `i128` |
| Unsigned integers | `u8`, `u16`, `u32`, `u64` |
| Floating point | `f32`, `f64` |
| Boolean | `bool` |
| String | `string` |
| Nil | `nil` |

---

## Numeric Types

### Integer Types

| Type | Size | Min | Max |
|------|------|-----|-----|
| `i8` | 8-bit | -128 | 127 |
| `i16` | 16-bit | -32,768 | 32,767 |
| `i32` | 32-bit | -2,147,483,648 | 2,147,483,647 |
| `i64` | 64-bit | -9,223,372,036,854,775,808 | 9,223,372,036,854,775,807 |
| `i128` | 128-bit | -(2^127) | 2^127 - 1 |
| `u8` | 8-bit | 0 | 255 |
| `u16` | 16-bit | 0 | 65,535 |
| `u32` | 32-bit | 0 | 4,294,967,295 |
| `u64` | 64-bit | 0 | 18,446,744,073,709,551,615 |

### Floating Point Types

| Type | Size | Description |
|------|------|-------------|
| `f32` | 32-bit | IEEE 754 single precision |
| `f64` | 64-bit | IEEE 754 double precision |

### Default Literal Types

- Integer literals default to `i64`
- Float literals default to `f64`

```vole
let x = 42        // i64
let y = 3.14      // f64
let z: i32 = 42   // i32 (explicit annotation)
```

### Numeric Operations

**Arithmetic:**
- `+` addition
- `-` subtraction
- `*` multiplication
- `/` division
- `%` modulo

**Comparison:**
- `==`, `!=` equality
- `<`, `>`, `<=`, `>=` ordering

**Bitwise (integers only):**
- `&` AND
- `|` OR
- `^` XOR
- `<<` left shift
- `>>` right shift
- `~` NOT (unary)

**Unary:**
- `-` negation

### Type Promotion

When a smaller integer type is combined with a literal, the result promotes to `i64`:

```vole
let x: i32 = 2147483647       // i32 max value
let y = x + 1                 // y is i64, value is 2147483648 (no overflow!)

let a: u8 = 255
let b = a + 1                 // b is i64, value is 256 (no overflow!)
```

### Same-Type Operations Wrap

When both operands have the same explicit type, arithmetic stays in that type and wraps on overflow:

```vole
let x: i32 = 2147483647
let y: i32 = x + 1            // y is i32, value is -2147483648 (wrapped!)

let a: u8 = 255
let b: u8 = a + 1             // b is u8, value is 0 (wrapped!)
```

### Division Behavior

Integer division by zero panics:

```vole
let x = 10
let y = 0
let z = x / y  // panic: division by zero at file.vole:3
```

Float division by zero returns infinity (IEEE 754):

```vole
let x = 10.0
let y = 0.0
let z = x / y  // z is inf
```

Signed division overflow (MIN / -1) panics:

```vole
let x: i32 = -2147483648      // i32 min value
let y: i32 = -1
let z = x / y  // panic: integer overflow in division at file.vole:3
```

### Explicit Arithmetic Methods

#### Wrapping Methods

Wrap on overflow (two's complement behavior):

```vole
let x: i32 = 2147483647
let y = wrapping_add(x, 1)    // -2147483648

let a: u8 = 0
let b = wrapping_sub(a, 1)    // 255
```

Available: `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_neg`

#### Saturating Methods

Clamp to min/max on overflow:

```vole
let x: i32 = 2147483647
let y = saturating_add(x, 1)  // 2147483647 (clamped to max)

let a: u8 = 0
let b = saturating_sub(a, 1)  // 0 (clamped to min)
```

Available: `saturating_add`, `saturating_sub`, `saturating_mul`

#### Checked Methods

Return `nil` on overflow:

```vole
let x: i32 = 2147483647
let y: i32? = checked_add(x, 1)  // nil

let a: i32 = 100
let b: i32? = checked_add(a, 1)  // 101

// Handle the result
let result = checked_add(x, 1) ?? 0  // use 0 as fallback
```

Available: `checked_add`, `checked_sub`, `checked_mul`, `checked_div`

### Numeric Traits

All numeric types implement:
- **Equatable**: `equals(other) -> bool`
- **Comparable**: `compare(other) -> i32`
- **Hashable**: `hash() -> i64`
- **Stringable**: `to_string() -> string`
- **Default**: `default_value()` returns 0
- **Bounded** (integers): `min_value()`, `max_value()`

Floats also implement **FloatConstants**: `nan()`, `infinity()`, `neg_infinity()`, `epsilon()`

---

## Bool

The `bool` type has two values: `true` and `false`.

### Logical Operations

```vole
// AND - both must be true
assert(true && true)
assert(!(true && false))

// OR - at least one must be true
assert(true || false)
assert(!(false || false))

// NOT - inverts the value
assert(!false)
assert(!!true)
```

### Short-Circuit Evaluation

- `false && X` returns `false` without evaluating X
- `true || X` returns `true` without evaluating X

```vole
func expensive() -> bool {
    println("called!")
    return true
}

let x = false && expensive()  // "called!" is NOT printed
let y = true || expensive()   // "called!" is NOT printed
```

### Bool Traits

- **Equatable**: `equals(other) -> bool`
- **Stringable**: `to_string() -> string` (returns "true" or "false")
- **Default**: `default_value()` returns `false`

Note: Booleans support equality but not ordering comparisons.

---

## String

Strings are reference-counted, UTF-8 encoded, immutable sequences of characters.

### String Literals

```vole
let greeting = "Hello, world!"
let empty = ""
let multiline = "line one\nline two"
```

### String Concatenation

Strings can be concatenated with `+`. The right operand can be any type that implements `Stringable`:

```vole
let msg = "value: " + 42         // "value: 42"
let msg = "result: " + true      // "result: true"
let msg = "pi: " + 3.14          // "pi: 3.14"
let msg = "hello" + " world"     // "hello world"
```

### String Methods

| Method | Signature | Description |
|--------|-----------|-------------|
| `length()` | `() -> i64` | Character count (UTF-8 aware) |
| `byte_length()` | `() -> i64` | Byte count |
| `contains()` | `(needle: string) -> bool` | Substring search |
| `starts_with()` | `(prefix: string) -> bool` | Prefix check |
| `ends_with()` | `(suffix: string) -> bool` | Suffix check |
| `to_lower()` | `() -> string` | Lowercase conversion |
| `to_upper()` | `() -> string` | Uppercase conversion |
| `trim()` | `() -> string` | Trim whitespace both sides |
| `trim_start()` | `() -> string` | Trim leading whitespace |
| `trim_end()` | `() -> string` | Trim trailing whitespace |
| `index_of()` | `(needle: string) -> i32` | Find index (-1 if not found) |
| `substring()` | `(start: i32, end: i32) -> string` | Extract substring |
| `replace()` | `(old: string, new: string) -> string` | Replace first occurrence |
| `replace_all()` | `(old: string, new: string) -> string` | Replace all occurrences |
| `split()` | `(delimiter: string) -> Iterator<string>` | Split into iterator |
| `lines()` | `() -> Iterator<string>` | Split by newlines |
| `chars()` | `() -> Iterator<i32>` | Iterate codepoints |

### String Examples

```vole
let s = "  Hello, World!  "

assert(s.trim() == "Hello, World!")
assert(s.length() == 17)
assert(s.contains("World"))
assert(s.starts_with("  H"))
assert(s.to_lower().trim() == "hello, world!")

let parts = "a,b,c".split(",").collect()
assert(parts.length() == 3)
```

### String Traits

- **Equatable**: `equals(other) -> bool`
- **Comparable**: `compare(other) -> i32` (lexicographic)
- **Hashable**: `hash() -> i64`
- **Stringable**: `to_string() -> string` (returns self)
- **Default**: `default_value()` returns `""`

---

## Nil and Optional Types

`nil` represents the absence of a value. It's used with optional types.

### Optional Type Syntax

`T?` is syntactic sugar for `T | nil`:

```vole
let x: i32? = 42        // contains i32
let y: i32? = nil       // contains nil
let z: string? = nil    // contains nil
```

### Null Coalescing (`??`)

Provides a default value when optional is nil:

```vole
let x: i32? = nil
let result = x ?? 99           // result = 99

let y: i32? = 42
let result = y ?? 99           // result = 42

// Chaining
let a: i32? = nil
let b: i32? = nil
let c: i32? = 42
let result = a ?? b ?? c ?? 0  // result = 42
```

### Optional Chaining (`?.`)

Safely accesses fields on optional values:

```vole
record Person {
    name: string,
    age: i32,
}

let p: Person? = Person { name: "Alice", age: 30 }
let name = p?.name              // name is string?, value "Alice"

let q: Person? = nil
let age = q?.age                // age is i32?, value nil
```

### Type Narrowing (`is`)

Tests if an optional contains a value:

```vole
let x: i32? = 42
assert(x is i32)    // true - contains i32, not nil

let y: i32? = nil
assert(y is nil)    // true - contains nil
```

---

## Special Types

### Void

Return type for functions with no return value:

```vole
func greet(name: string) -> void {
    println("Hello, " + name)
}
```

### Done

Iterator termination sentinel. Iterators return `T | Done`:

```vole
let iter = [1, 2, 3].iter()
// iter.next() returns i32 | Done
```

### Range

Created with range literals:

```vole
for i in 0..10 {
    println(i)
}
```

---

## See Also

- [Types](types.md) - Full type system documentation
- [Operators](operators.md) - All operators
- [Traits](traits.md) - Trait system
