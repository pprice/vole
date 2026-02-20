# Types

Vole is statically typed with type inference. Types are checked at compile time.

## Quick Reference

| Type | Description | Example |
|------|-------------|---------|
| `i8`, `i16`, `i32`, `i64`, `i128` | Signed integers | `let x: i32 = 42` |
| `u8`, `u16`, `u32`, `u64` | Unsigned integers | `let b: u8 = 255` |
| `f32`, `f64` | Floating point | `let pi: f64 = 3.14` |
| `bool` | Boolean | `true`, `false` |
| `string` | Text | `"hello"` |
| `nil` | Absence of value | `nil` |
| `[T]` | Array of T | `[1, 2, 3]` |
| `[T; N]` | Fixed-size array | `[0; 5]` |
| `T?` | Optional T (T or nil) | `string?` |
| `A \| B` | Union of A or B | `i32 \| string` |
| `(T) -> U` | Function type | `(i64) -> i64` |
| `unknown` | Top type (any value) | `let x: unknown = 42` |
| `never` | Bottom type (no value) | `func f() -> never` |
| `handle` | Opaque native pointer | `let h: handle? = nil` |

**Default inference:** Integer literals are `i64`, float literals are `f64`.

## Numeric Literals

Vole supports several numeric literal formats:

| Format | Example | Notes |
|--------|---------|-------|
| Decimal | `42`, `1_000_000` | Default integer format |
| Hex | `0xFF`, `0x1A2B` | Prefix `0x` or `0X` |
| Binary | `0b1010`, `0b1111_0000` | Prefix `0b` or `0B` |
| Float | `3.14`, `0.5` | Decimal point makes it float |
| Scientific | `1e10`, `1.5e-3`, `2E+6` | Always produces a float |
| Underscore separators | `1_000_000`, `0xFF_FF` | Ignored during parsing, purely for readability |

### Typed Literal Suffixes

Append a type suffix to control the exact type of a numeric literal:

```vole
// Integer suffixes
let a = 42_u8       // u8
let b = 1000_i32    // i32
let c = 0xFF_u16    // u16, hex with suffix
let d = 0b1010_u8   // u8, binary with suffix

// Float suffixes
let e = 3.14_f32    // f32
let f = 1.5e3_f64   // f64, scientific with suffix
let g = 100_f32     // f32 (decimal integer with float suffix)
```

Without a suffix, integer literals default to `i64` and float literals default to `f64`.

Suffix type must match the literal kind: integer suffixes (`_u8`, `_i32`, etc.) cannot be applied to float literals, and float suffixes (`_f32`, `_f64`) cannot be applied to hex or binary literals.

## In Depth

### Integer Types

Vole has signed (`i8`, `i16`, `i32`, `i64`, `i128`) and unsigned (`u8`, `u16`, `u32`, `u64`) integers. Integer literals default to `i64`. See [Primitives](primitives.md) for ranges, overflow behavior, and arithmetic methods.

### Floating Point Types

`f32` (32-bit) and `f64` (64-bit) follow IEEE 754. Float literals default to `f64`. See [Primitives](primitives.md) for constants, NaN semantics, and division behavior.

### Booleans

```vole
let yes = true
let no = false
```

Used in conditionals and logical expressions. See [Operators](operators.md) for logical operators and [Primitives](primitives.md) for bool traits.

### Strings

Strings are UTF-8 encoded, reference-counted, and immutable. They support `{expression}` interpolation and `@"..."` raw string syntax:

```vole
let greeting = "Hello, World!"
let name = "Alice"
let msg = "Hello, {name}!"
let path = @"C:\Users\Alice"
```

See [Primitives](primitives.md) for string methods, escape sequences, and concatenation rules.

### Nil

Represents the absence of a value:

```vole
let nothing = nil
```

`nil` is primarily used with optional types. A bare `nil` has type `nil`.

### Arrays

Arrays hold ordered collections of a single type:

```vole
let numbers = [1, 2, 3, 4, 5]
let names: [string] = ["Alice", "Bob"]
let empty: [i64] = []
```

Array access and methods:

```vole
tests {
    test "array access" {
        let arr = [10, 20, 30]
        assert(arr[0] == 10)
        assert(arr.length() == 3)
    }
}
```

Array type syntax is `[T]` where T is the element type:

```vole
let matrix: [[i64]] = [[1, 2], [3, 4]]
```

### Fixed-Size Arrays

Fixed-size arrays have a compile-time known size. Created with repeat syntax `[value; count]`:

```vole
tests {
    test "fixed arrays" {
        let arr: [i64; 3] = [42; 3]
        assert(arr[0] == 42)
        assert(arr[1] == 42)
        assert(arr[2] == 42)

        var buf: [i64; 3] = [0; 3]
        buf[0] = 1
        buf[1] = 2
        buf[2] = 3
        assert(buf[0] == 1)
    }
}
```

### Tuples

Tuples are heterogeneous fixed-size collections. In Vole, tuples use array literal syntax but with mixed types:

```vole
tests {
    test "tuples" {
        let t = [42, "world"]
        assert(t[0] == 42)
        assert(t[1] == "world")

        let triple = [1, "two", 3.14]
        assert(triple[0] == 1)
        assert(triple[1] == "two")
        assert(triple[2] == 3.14)

        // Tuple destructuring
        let [a, b] = [10, "twenty"]
        assert(a == 10)
        assert(b == "twenty")
    }
}
```

### Optional Types

Optional types represent values that may or may not exist. Written as `T?`, which is sugar for `T | nil`:

```vole
let maybe_name: string? = "Alice"
let no_name: string? = nil
```

Handle optionals with the null coalescing operator `??`:

```vole
tests {
    test "null coalescing" {
        let name: string? = nil
        let display = name ?? "Unknown"
        assert(display == "Unknown")
    }
}
```

Use optional chaining `?.` for safe field access on optional class instances:

```vole
class User {
    name: string,
    age: i32,
}

tests {
    test "optional chaining" {
        let user: User? = User { name: "Alice", age: 30 }
        let name = user?.name
        assert((name ?? "") == "Alice")

        let nobody: User? = nil
        let age = nobody?.age
        assert(age is nil)
    }
}
```

### Union Types

Union types allow a value to be one of several types:

```vole
let value: i64 | string = 42
let other: i64 | string = "hello"
```

Check the actual type with `is`:

```vole
tests {
    test "is operator" {
        let x: i64 | string = 42
        if x is i64 {
            // x is narrowed to i64 here
            assert(x + 10 == 52)
        } else {
            assert(false)
        }
    }
}
```

Use `match` for exhaustive handling:

```vole
tests {
    test "match on union" {
        let result: i64 | string | nil = nil
        let message = match result {
            i64 => "got a number"
            string => "got a string"
            nil => "got nothing"
        }
        assert(message == "got nothing")
    }
}
```

Union types are more flexible than optionals -- they can combine any types:

```vole
let value: i64 | string | bool = true
```

### Type Aliases

Types can be assigned to `let` bindings and used as type annotations:

```vole
let Numeric = i32 | i64 | f64
let OptionalInt = i32?
let IntOrString = i32 | string

tests {
    test "type aliases" {
        let x: Numeric = 42
        assert(x is i32)

        let y: OptionalInt = nil
        assert(y is nil)

        let z: IntOrString = "hello"
        assert(z is string)
    }
}
```

### Function Types

Function types describe callable values. The syntax is `(ParamTypes) -> ReturnType`:

```vole
func apply(f: (i64) -> i64, x: i64) -> i64 {
    return f(x)
}

func make_adder(n: i64) -> (i64) -> i64 {
    return (x: i64) => x + n
}

tests {
    test "function types" {
        let double = (x: i64) => x * 2
        assert(apply(double, 5) == 10)

        let add5 = make_adder(5)
        assert(add5(10) == 15)
    }
}
```

See [Functions](functions.md) for more on lambdas and closures.

### Unknown Type

`unknown` is the top type -- any value can be assigned to it. Use `is` to narrow back to a concrete type:

```vole
tests {
    test "unknown type" {
        let x: unknown = 42
        assert(x is i64)
        assert(!(x is string))

        let y: unknown = "hello"
        assert(y is string)

        // Narrow with is-check
        if x is i64 {
            assert(x == 42)
        } else {
            assert(false)
        }
    }
}
```

### Never Type

`never` is the bottom type -- it represents computations that never produce a value. The `unreachable` expression has type `never` and traps at runtime if reached:

```vole
tests {
    test "never in when branch" {
        let x = when {
            true => 42,
            _ => unreachable
        }
        assert(x == 42)
    }

    test "never in match default" {
        let x: i64 = 5
        let result = match x {
            5 => "five",
            10 => "ten",
            _ => unreachable
        }
        assert(result == "five")
    }
}
```

Functions that never return can be annotated with `-> never`:

```vole,ignore
func always_panics() -> never {
    _ = unreachable
}
```

### Handle Type

`handle` is an opaque native pointer type used for interacting with external resources. Handles cannot be created directly in Vole code -- they are returned by native functions. Use `handle?` for optional handles:

```vole
let random = import "std:random"

class Resource {
    ptr: handle?
}

tests {
    test "handle type" {
        let r = Resource { ptr: nil }
        let p = r.ptr
        assert(p == nil)

        // Handles from native functions
        let rng = random.seeded(42)
        assert(rng.to_string() == "handle")
    }
}
```

---

## See Also

- [Primitives](primitives.md) - Detailed primitive type reference
- [Operators](operators.md) - All operators
- [Variables](variables.md) - Variable declarations and mutability
