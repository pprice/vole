# Operators

Vole provides arithmetic, comparison, logical, bitwise, and type operators.

## Quick Reference

### Arithmetic

| Operator | Description | Example |
|----------|-------------|---------|
| `+` | Addition | `5 + 3` -> `8` |
| `-` | Subtraction | `5 - 3` -> `2` |
| `*` | Multiplication | `5 * 3` -> `15` |
| `/` | Division | `7 / 2` -> `3` (integer) |
| `%` | Modulo | `7 % 3` -> `1` |
| `-` | Negation (unary) | `-5` |

### Comparison

| Operator | Description | Example |
|----------|-------------|---------|
| `==` | Equal | `5 == 5` -> `true` |
| `!=` | Not equal | `5 != 3` -> `true` |
| `<` | Less than | `3 < 5` -> `true` |
| `>` | Greater than | `5 > 3` -> `true` |
| `<=` | Less or equal | `3 <= 3` -> `true` |
| `>=` | Greater or equal | `5 >= 5` -> `true` |

### Logical

| Operator | Description | Example |
|----------|-------------|---------|
| `&&` | Logical AND | `true && false` -> `false` |
| `\|\|` | Logical OR | `true \|\| false` -> `true` |
| `!` | Logical NOT | `!true` -> `false` |

### Bitwise

| Operator | Description | Example |
|----------|-------------|---------|
| `&` | Bitwise AND | `5 & 3` -> `1` |
| `\|` | Bitwise OR | `5 \| 3` -> `7` |
| `^` | Bitwise XOR | `5 ^ 3` -> `6` |
| `~` | Bitwise NOT | `~5` -> `-6` |
| `<<` | Left shift | `1 << 3` -> `8` |
| `>>` | Right shift | `8 >> 2` -> `2` |

### Type Operators

| Operator | Description | Example |
|----------|-------------|---------|
| `is` | Type check | `x is i32` |
| `==` | Type equality | `i32 == i32` -> `true` |

### Optional Operators

| Operator | Description | Example |
|----------|-------------|---------|
| `??` | Null coalescing | `x ?? default` |
| `?.` | Optional chaining | `obj?.field` |

## In Depth

### Arithmetic Operators

Basic math operations:

```vole
let a = 10
let b = 3

println(a + b)   // 13
println(a - b)   // 7
println(a * b)   // 30
println(a / b)   // 3 (integer division)
println(a % b)   // 1 (remainder)
```

Unary negation:

```vole
let x = 5
let neg = -x     // -5
```

### Integer vs Float Division

Integer division truncates:

```vole
let result = 7 / 2  // 3, not 3.5
```

For decimal results, use floats:

```vole
let result = 7.0 / 2.0  // 3.5
```

### Comparison Operators

Compare values of the same type:

```vole
let x = 5
let y = 10

println(x == y)  // false
println(x != y)  // true
println(x < y)   // true
println(x > y)   // false
println(x <= y)  // true
println(x >= y)  // false
```

String comparison:

```vole
let a = "apple"
let b = "banana"

println(a == "apple")  // true
println(a < b)         // true (lexicographic)
```

### Logical Operators

Boolean logic:

```vole
let a = true
let b = false

println(a && b)  // false (AND)
println(a || b)  // true (OR)
println(!a)      // false (NOT)
```

Short-circuit evaluation:

```vole
// b() is not called if a() returns false
if a() && b() { }

// b() is not called if a() returns true
if a() || b() { }
```

Common patterns:

```vole
// Guard clause
if x != nil && x.valid {
    process(x)
}

// Default condition
if debug || verbose {
    log(message)
}
```

### Bitwise Operators

Operate on individual bits:

```vole
let a = 10  // binary: 1010
let b = 12  // binary: 1100

println(a & b)   // 8 (binary: 1000) - AND
println(a | b)   // 14 (binary: 1110) - OR
println(a ^ b)   // 6 (binary: 0110) - XOR
println(~a)      // inverts all bits
```

Shift operators:

```vole
let x = 1
println(x << 3)  // 8 (multiply by 2^3)
println(8 >> 2)  // 2 (divide by 2^2)
```

Common uses:

```vole
// Check if bit is set
let flags = 10  // binary: 1010
let has_flag = (flags & 2) != 0  // true (bit 1 is set)

// Set a bit
let new_flags = flags | 1  // 11 (binary: 1011)

// Clear a bit
let cleared = flags & ~2  // 8 (binary: 1000)

// Toggle a bit
let toggled = flags ^ 2  // 8 (binary: 1000)
```

### Type Operators

Check type at runtime with `is`:

```vole
let x: i32 | string = get_value()

if x is i32 {
    println("it's an integer")
    println(x + 10)  // x narrowed to i32
}
```

Compare types:

```vole
let t = type_of(42)
println(t == i32)     // true
println(t == string)  // false
```

Use in conditions:

```vole
func process(value: i32 | string | bool) {
    if value is i32 {
        println("number")
    } else if value is string {
        println("string")
    } else {
        println("boolean")
    }
}
```

### Null Coalescing Operator

Provide a default for optional values with `??`:

```vole
let name: string? = nil
let display = name ?? "Anonymous"  // "Anonymous"

let other: string? = "Alice"
let show = other ?? "Anonymous"    // "Alice"
```

Chain multiple fallbacks:

```vole
let primary: string? = nil
let secondary: string? = nil
let fallback = "default"

let result = primary ?? secondary ?? fallback
```

### Optional Chaining

Safely access fields on optional values with `?.`:

```vole
let user: User? = get_user()

// Returns nil if user is nil
let name = user?.name

// Chain multiple accesses
let city = user?.address?.city
```

Without optional chaining, you'd need:

```vole
let city = if user != nil {
    if user.address != nil {
        user.address.city
    } else {
        nil
    }
} else {
    nil
}
```

Combine with null coalescing:

```vole
let city = user?.address?.city ?? "Unknown"
```

### Operator Precedence

From highest to lowest:

1. Unary: `-`, `!`, `~`
2. Multiplicative: `*`, `/`, `%`
3. Additive: `+`, `-`
4. Shift: `<<`, `>>`
5. Comparison: `<`, `>`, `<=`, `>=`
6. Equality: `==`, `!=`
7. Bitwise AND: `&`
8. Bitwise XOR: `^`
9. Bitwise OR: `|`
10. Logical AND: `&&`
11. Logical OR: `||`
12. Null coalescing: `??`

Use parentheses for clarity:

```vole
let result = (a + b) * c
let check = (x > 0) && (y < 10)
```

### String Concatenation

The `+` operator concatenates strings:

```vole
let greeting = "Hello, " + "World!"
let message = "Count: " + count
```
