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

### Typed Literal Suffixes

You can use type suffixes on numeric literals to specify their type directly:

```vole
tests {
    test "literal suffixes" {
        let a = 42_u8
        let b = 1000_i16
        let c = 100_u32
        let d = 42_i64
        let e = 3.14_f32
        let f = 1.5e3_f64
        assert(a == 42)
        assert(b == 1000)
        assert(c == 100000 / 1000)
        assert(d == 42)
        assert(e > 3.0)
        assert(f > 1499.0)
    }
}
```

### Numeric Literal Formats

Vole supports several numeric literal formats:

```vole
tests {
    test "numeric literal formats" {
        // Hex literals
        assert(0xFF == 255)
        assert(0xDEAD == 57005)

        // Binary literals
        assert(0b1010 == 10)
        assert(0b11111111 == 255)

        // Underscore separators for readability
        assert(1_000_000 == 1000000)
        assert(0xFF_FF == 65535)
        assert(0b1111_0000 == 240)

        // Scientific notation (produces f64)
        assert(1e2 == 100.0)
        assert(1.5e2 == 150.0)
        assert(1e-1 == 0.1)
    }
}
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

**Compound assignment:**
- `+=`, `-=`, `*=`, `/=`

```vole
tests {
    test "compound assignment" {
        let mut a: i32 = 10
        a += 5
        assert(a == 15)
        a *= 2
        assert(a == 30)
        a /= 3
        assert(a == 10)
    }
}
```

### Type Promotion

When a smaller integer type is combined with a literal, the result promotes to `i64`:

```vole
let x: i32 = 2147483647       // i32 max value
let y = x + 1                 // y is i64, value is 2147483648 (no overflow!)

let a: u8 = 255
let b = a + 1                 // b is i64, value is 256 (no overflow!)
```

Small integer types (`i8`, `i16`, `u8`, `u16`) promote to `i32` when used in arithmetic with each other:

```vole
tests {
    test "small integer promotion" {
        let a: i8 = 10
        let b: i8 = 20
        let c = a + b  // c is i32
        assert(c == 30)

        let x: u16 = 30000
        let y: u16 = 30000
        let z = x + y  // z is i32
        assert(z == 60000)
    }
}
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

```vole,ignore
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

```vole,ignore
let x: i32 = -2147483648      // i32 min value
let y: i32 = -1
let z = x / y  // panic: integer overflow in division at file.vole:3
```

### Explicit Arithmetic Methods

These functions are available from `"std:lowlevel"` and provide explicit overflow control.

#### Wrapping Methods

Wrap on overflow (two's complement behavior):

```vole
let { wrapping_add, wrapping_sub } = import "std:lowlevel"

tests {
    test "wrapping arithmetic" {
        let x: i32 = 2147483647
        let one: i32 = 1
        assert(wrapping_add(x, one) == -2147483648)

        let a: u8 = 0
        let b: u8 = 1
        assert(wrapping_sub(a, b) == 255)
    }
}
```

Available: `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_neg`

#### Saturating Methods

Clamp to min/max on overflow:

```vole
let { saturating_add, saturating_sub } = import "std:lowlevel"

tests {
    test "saturating arithmetic" {
        let x: i32 = 2147483647
        let one: i32 = 1
        assert(saturating_add(x, one) == 2147483647)

        let a: u8 = 0
        let b: u8 = 1
        assert(saturating_sub(a, b) == 0)
    }
}
```

Available: `saturating_add`, `saturating_sub`, `saturating_mul`

#### Checked Methods

Return `nil` on overflow:

```vole
let { checked_add, checked_div } = import "std:lowlevel"

tests {
    test "checked arithmetic" {
        let x: i32 = 2147483647
        let one: i32 = 1
        let result = checked_add(x, one)
        assert(result is nil)

        let a: i32 = 100
        let b = checked_add(a, one)
        assert(b is i32)
        assert((b ?? 0) == 101)

        // Handle the result with null coalescing
        let safe = checked_add(x, one) ?? 0
        assert(safe == 0)
    }
}
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

```vole
tests {
    test "numeric trait methods" {
        let a: i64 = 42
        let b: i64 = 42
        assert(a.equals(b))

        let x: i64 = 5
        let y: i64 = 10
        assert(x.compare(y) < 0)

        let h1 = 42.hash()
        let h2 = 42.hash()
        assert(h1 == h2)
    }
}
```

### Float Constants

Floats implement **FloatConstants**: `nan()`, `infinity()`, `neg_infinity()`, `epsilon()`

```vole
tests {
    test "float constants" {
        let inf = f64.infinity()
        assert(inf > 1000000000000.0)
        assert(inf + 1.0 == inf)

        let neg_inf = f64.neg_infinity()
        assert(neg_inf < -1000000000000.0)

        let eps = f64.epsilon()
        assert(eps > 0.0)
        assert(1.0 + eps != 1.0)

        // NaN is the only value not equal to itself
        let n = f64.nan()
        assert(n != n)
    }
}
```

`f32` has the same constants available via `f32.nan()`, `f32.infinity()`, etc.

---

## Bool

The `bool` type has two values: `true` and `false`.

### Logical Operations

```vole
tests {
    test "logical operations" {
        // AND - both must be true
        assert(true && true)
        assert(!(true && false))

        // OR - at least one must be true
        assert(true || false)
        assert(!(false || false))

        // NOT - inverts the value
        assert(!false)
        assert(!!true)
    }
}
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

### String Interpolation

Strings support inline interpolation with `{expression}` syntax:

```vole
tests {
    test "string interpolation" {
        let name = "world"
        let s = "hello, {name}"
        assert(s == "hello, world")

        let a = 2
        let b = 3
        assert("sum is {a + b}" == "sum is 5")

        let arr = [1, 2, 3]
        assert("first: {arr[0]}, length: {arr.length()}" == "first: 1, length: 3")
    }
}
```

Raw strings (prefixed with `@`) disable interpolation and escape sequences:

```vole
tests {
    test "raw strings" {
        let s = @"{not interpolated}"
        assert(s.length() == 18)

        let path = @"path\to\file"
        assert(path.length() == 12)
    }
}
```

### Escape Sequences

Regular strings support the following escape sequences:

| Escape | Character |
|--------|-----------|
| `\n` | Newline |
| `\t` | Tab |
| `\r` | Carriage return |
| `\\` | Backslash |
| `\"` | Double quote |
| `\{` | Literal `{` |
| `\}` | Literal `}` |
| `{{` | Literal `{` (brace escape) |
| `}}` | Literal `}` (brace escape) |

```vole
tests {
    test "escape sequences" {
        let s = "line1\nline2"
        assert(s.length() == 11)

        let tab = "a\tb"
        assert(tab.length() == 3)

        let quoted = "she said \"hi\""
        assert(quoted.contains("hi"))
    }
}
```

### String Concatenation

Strings can be concatenated with `+`. The right operand can be any type that implements `Stringable`:

```vole
tests {
    test "string concatenation" {
        assert("value: " + 42 == "value: 42")
        assert("result: " + true == "result: true")
        assert("pi: " + 3.14 == "pi: 3.14")
        assert("hello" + " world" == "hello world")
    }
}
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
| `index_of_raw()` | `(needle: string) -> i32` | Find byte index (-1 if not found) |
| `substring()` | `(start: i32, end: i32) -> string` | Extract substring (-1 for end of string) |
| `replace()` | `(old: string, new: string) -> string` | Replace first occurrence |
| `replace_all()` | `(old: string, new: string) -> string` | Replace all occurrences |
| `split()` | `(delimiter: string) -> Iterator<string>` | Split into iterator |
| `lines()` | `() -> Iterator<string>` | Split by newlines |
| `chars()` | `() -> Iterator<i32>` | Iterate codepoints |
| `char_at_raw()` | `(index: i32) -> i32` | Get codepoint at byte index (-1 if out of bounds) |

### String Examples

```vole
tests {
    test "string methods" {
        let s = "  Hello, World!  "
        assert(s.trim() == "Hello, World!")
        assert(s.length() == 17)
        assert(s.contains("World"))
        assert(s.starts_with("  H"))

        let result = "hello".to_upper()
        assert(result == "HELLO")

        assert("WORLD".to_lower() == "world")

        let parts = "a,b,c".split(",").collect()
        assert(parts.length() == 3)
        assert(parts[0] == "a")
    }

    test "string replace" {
        assert("hello hello".replace("hello", "hi") == "hi hello")
        assert("hello hello hello".replace_all("hello", "hi") == "hi hi hi")
    }

    test "string substring" {
        let s = "hello world"
        assert(s.substring(0, 5) == "hello")
        assert(s.substring(6, -1) == "world")
    }
}
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
tests {
    test "null coalescing" {
        let x: i32? = nil
        assert((x ?? 99) == 99)

        let y: i32? = 42
        assert((y ?? 99) == 42)

        // Chaining
        let a: i32? = nil
        let b: i32? = nil
        let c: i32? = 42
        let result = a ?? b ?? c ?? 0
        assert(result == 42)
    }
}
```

### Optional Chaining (`?.`)

Safely accesses fields on optional values:

```vole
class Person {
    name: string,
    age: i32,
}

tests {
    test "optional chaining" {
        let p: Person? = Person { name: "Alice", age: 30 }
        let name = p?.name  // name is string?, value "Alice"
        assert((name ?? "") == "Alice")

        let q: Person? = nil
        let age = q?.age  // age is i32?, value nil
        assert(age is nil)
    }

    test "optional chaining with null coalescing" {
        let p: Person? = nil
        let name = p?.name ?? "Unknown"
        assert(name == "Unknown")
    }
}
```

### Type Narrowing (`is`)

Tests if an optional contains a value:

```vole
tests {
    test "type narrowing with is" {
        let x: i32? = 42
        assert(x is i32)

        let y: i32? = nil
        assert(y is nil)
    }

    test "narrowing in if" {
        let x: i64 | string = 5
        if x is i64 {
            let y = x + 1
            assert(y == 6)
        } else {
            assert(false)
        }
    }
}
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
tests {
    test "done type" {
        let result: i32 | Done = Done {}
        assert(result is Done)
    }
}
```

### Range

Created with range literals:

```vole
tests {
    test "range" {
        let mut sum = 0
        for i in 0..5 {
            sum += i
        }
        assert(sum == 10)
    }
}
```

---

## See Also

- [Types](types.md) - Full type system documentation
- [Operators](operators.md) - All operators
- [Interfaces](interfaces.md) - Interface system
