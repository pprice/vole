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
| `T?` | Optional T (T or nil) | `string?` |
| `A \| B` | Union of A or B | `i32 \| string` |
| `type` | Type as value | `let t: type = i32` |

**Default inference:** Integer literals are `i32`, float literals are `f64`.

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

Without a suffix, integer literals default to `i32` and float literals default to `f64`.

Suffix type must match the literal kind: integer suffixes (`_u8`, `_i32`, etc.) cannot be applied to float literals, and float suffixes (`_f32`, `_f64`) cannot be applied to hex or binary literals.

## In Depth

### Integer Types

Signed integers store positive and negative values:

| Type | Range |
|------|-------|
| `i8` | -128 to 127 |
| `i16` | -32,768 to 32,767 |
| `i32` | -2,147,483,648 to 2,147,483,647 |
| `i64` | -9,223,372,036,854,775,808 to 9,223,372,036,854,775,807 |
| `i128` | -170,141,183,460,469,231,731,687,303,715,884,105,728 to 170,141,183,460,469,231,731,687,303,715,884,105,727 |

Unsigned integers store only non-negative values:

| Type | Range |
|------|-------|
| `u8` | 0 to 255 |
| `u16` | 0 to 65,535 |
| `u32` | 0 to 4,294,967,295 |
| `u64` | 0 to 18,446,744,073,709,551,615 |

```vole
let small: i8 = 127
let byte: u8 = 255
let count: i32 = 1_000_000
let big: i64 = 9_223_372_036_854_775_807
let mask: u8 = 0xFF
let bits: u8 = 0b1010_0101
```

Integer literals default to `i32`:

```vole
let x = 42          // x is i32
let y: i64 = 42     // explicit i64
let z = 42_u8       // u8 via suffix
```

### Floating Point Types

| Type | Precision |
|------|-----------|
| `f32` | Single precision (32-bit) |
| `f64` | Double precision (64-bit) |

```vole
let pi: f64 = 3.14159265358979
let approx: f32 = 3.14
let sci = 1.5e-3   // 0.0015, scientific notation
```

Float literals default to `f64`:

```vole
let x = 3.14        // x is f64
let y: f32 = 3.14   // explicit f32
let z = 3.14_f32    // f32 via suffix
let w = 2.5e6_f64   // f64, scientific with suffix
```

### Booleans

```vole
let yes = true
let no = false
```

Used in conditionals and logical expressions. See [Operators](operators.md) for logical operators.

### Strings

Strings are sequences of characters:

```vole
let greeting = "Hello, World!"
let empty = ""
```

String properties and operations:

```vole
let s = "hello"
println(s.length)      // 5

let combined = "Hello" + " " + "World"
```

String interpolation embeds expressions in strings:

```vole
let name = "Alice"
let age = 30
println("Name: {name}, Age: {age}")  // "Name: Alice, Age: 30"
```

Raw strings preserve backslashes:

```vole
let path = @"C:\Users\Alice"  // backslash is literal
```

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
let empty: [i32] = []
```

Array access and properties:

```vole
let arr = [10, 20, 30]
let first = arr[0]     // 10
let len = arr.length   // 3
```

Array type syntax is `[T]` where T is the element type:

```vole
let matrix: [[i32]] = [[1, 2], [3, 4]]  // Array of arrays
```

### Optional Types

Optional types represent values that may or may not exist. Written as `T?`:

```vole
let maybe_name: string? = "Alice"
let no_name: string? = nil
```

Handle optionals with the null coalescing operator `??`:

```vole
let name: string? = nil
let display = name ?? "Unknown"  // "Unknown"
```

Use optional chaining `?.` for safe access:

```vole
let user: User? = get_user()
let len = user?.name?.length  // nil if user or name is nil
```

### Union Types

Union types allow a value to be one of several types:

```vole
let value: i32 | string = 42
let other: i32 | string = "hello"
```

Check the actual type with `is`:

```vole
let x: i32 | string = get_value()

if x is i32 {
    // x is narrowed to i32 here
    println(x + 10)
}
```

Use `match` for exhaustive handling:

```vole
let result: i32 | string | nil = compute()

let message = match result {
    i32 => "got a number"
    string => "got a string"
    nil => "got nothing"
}
```

Union types are more flexible than optionals - they can combine any types:

```vole
let value: i32 | string | bool = true
```

### Type Values

Types themselves are first-class values with type `type`:

```vole
let t: type = i32
let types: [type] = [i32, string, f64]
```

Get the type of an expression with `type_of()`:

```vole
let x = 42
let t = type_of(x)  // i32
```

Compare types:

```vole
assert(type_of(42) == i32)
assert(i32 != string)
```

### Function Types

Function types describe callable values:

```vole
let add: (i32, i32) -> i32 = (a: i32, b: i32) => a + b
let print_num: (i32) -> nil = (n: i32) => println(n)
let get_value: () -> i32 = () => 42
```

See [Functions](functions.md) for more on lambdas and closures.
