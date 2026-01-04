# Variables

Variables in Vole are immutable by default. Use `let` for bindings and `let mut` for mutable variables.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `let x = 42` | Immutable binding, type inferred |
| `let x: i64 = 42` | Immutable with explicit type |
| `let mut x = 0` | Mutable binding |
| `x = 10` | Reassign mutable variable |
| `let { x, y } = point` | Destructuring |

**Rules:**
- Immutable by default - prefer `let` over `let mut`
- No shadowing in the same scope
- Must be initialized at declaration
- Type can be inferred or explicit

## In Depth

### Immutable Bindings

Use `let` to create bindings that cannot be reassigned:

```vole
let name = "Alice"
let age = 30
let pi = 3.14159
```

Once bound, the value cannot change:

```vole
let x = 10
x = 20  // Error: cannot assign to immutable variable
```

Immutability is the default because it:
- Prevents accidental modification
- Makes code easier to reason about
- Enables compiler optimizations

### Mutable Bindings

When you need to change a value, use `let mut`:

```vole
let mut counter = 0
counter = counter + 1
counter = counter + 1
println(counter)  // 2
```

Common use cases for mutable variables:
- Loop counters
- Accumulators
- State that changes over time

```vole
let mut sum = 0
for i in 1..=10 {
    sum = sum + i
}
println(sum)  // 55
```

### Type Inference

Vole infers types from the assigned value:

```vole
let x = 42          // i32 (integer default)
let y = 3.14        // f64 (float default)
let name = "Alice"  // string
let flag = true     // bool
let items = [1, 2]  // [i32]
```

### Explicit Type Annotations

Specify types when you need a non-default type or want clarity:

```vole
let x: i64 = 42           // i64 instead of i32
let y: f32 = 3.14         // f32 instead of f64
let empty: [string] = []  // Required for empty arrays
```

Type annotations go after the variable name, before the `=`:

```vole
let name: string = get_name()
let mut count: i32 = 0
```

### Destructuring

Extract fields from records and classes:

```vole
record Point { x: i32, y: i32 }

let point = Point { x: 10, y: 20 }
let { x, y } = point
println(x)  // 10
println(y)  // 20
```

Rename while destructuring:

```vole
let { x: a, y: b } = point
println(a)  // 10
```

Partial destructuring (only some fields):

```vole
let { x } = point
println(x)  // 10
```

### Scoping

Variables are scoped to the block they're declared in:

```vole
let x = 1
{
    let y = 2
    println(x)  // 1 - x is accessible
    println(y)  // 2
}
println(x)  // 1
println(y)  // Error: y is not defined
```

### No Same-Scope Shadowing

Unlike some languages, Vole does not allow redeclaring a variable in the same scope:

```vole
let x = 1
let x = 2  // Error: 'x' is already defined in this scope
```

Use a nested scope if you need a new variable with the same name:

```vole
let x = 1
{
    let x = 2      // OK - different scope
    println(x)     // 2
}
println(x)         // 1
```

Or use mutation if the value needs to change:

```vole
let mut x = 1
x = 2              // OK - same variable, new value
println(x)         // 2
```

### Module-Level Variables

Variables can be declared at the top level:

```vole
let VERSION = "1.0.0"
let mut request_count = 0

func handle_request() {
    request_count = request_count + 1
}

func main() {
    println(VERSION)
    handle_request()
    println(request_count)  // 1
}
```

### Common Errors

**Reassigning immutable variable:**

```vole
let x = 1
x = 2  // Error: cannot assign to immutable variable
```

Fix: Use `let mut` if you need mutation.

**Redeclaring in same scope:**

```vole
let x = 1
let x = 2  // Error: 'x' is already defined
```

Fix: Use a different name, nested scope, or mutation.

**Using before declaration:**

```vole
println(x)  // Error: 'x' is not defined
let x = 1
```

Fix: Declare variables before use.

**Missing initialization:**

```vole
let x: i32  // Error: variable must be initialized
```

Fix: All variables must have an initial value.
