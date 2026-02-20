# Variables

Variables in Vole are immutable by default. Use `let` for bindings and `var` for mutable variables.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `let x = 42` | Immutable binding, type inferred |
| `let x: i64 = 42` | Immutable with explicit type |
| `var x = 0` | Mutable binding |
| `x = 10` | Reassign mutable variable |
| `let { x, y } = point` | Destructuring |

**Rules:**
- Immutable by default -- prefer `let` over `var`
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

```vole,ignore
let x = 10
x = 20  // Error: cannot assign to immutable variable
```

Immutability is the default because it:
- Prevents accidental modification
- Makes code easier to reason about
- Enables compiler optimizations

### Mutable Bindings

When you need to change a value, use `var`:

```vole
tests {
    test "mutable bindings" {
        var counter = 0
        counter = counter + 1
        counter = counter + 1
        assert(counter == 2)
    }
}
```

Common use cases for mutable variables:
- Loop counters
- Accumulators
- State that changes over time

```vole
tests {
    test "accumulator" {
        var sum = 0
        for i in 1..=10 {
            sum = sum + i
        }
        assert(sum == 55)
    }
}
```

### Compound Assignment

Mutable variables support compound assignment operators:

```vole
tests {
    test "compound assignment" {
        var x = 10
        x += 5
        assert(x == 15)
        x -= 3
        assert(x == 12)
        x *= 2
        assert(x == 24)
        x /= 4
        assert(x == 6)
    }
}
```

### Type Inference

Vole infers types from the assigned value:

```vole
let x = 42          // i64 (integer default)
let y = 3.14        // f64 (float default)
let name = "Alice"  // string
let flag = true     // bool
let items = [1, 2]  // [i64]
```

### Explicit Type Annotations

Specify types when you need a non-default type or want clarity:

```vole
let x: i32 = 42           // i32 instead of i64
let y: f32 = 3.14         // f32 instead of f64
let empty: [string] = []  // Required for empty arrays
```

Type annotations go after the variable name, before the `=`:

```vole
let name: string = "hello"
var count: i32 = 0
```

### Destructuring

Extract fields from classes and structs:

```vole
class Point {
    x: i32,
    y: i32,
}

tests {
    test "basic destructuring" {
        let point = Point { x: 10, y: 20 }
        let { x, y } = point
        assert(x == 10)
        assert(y == 20)
    }

    test "destructuring with rename" {
        let point = Point { x: 10, y: 20 }
        let { x: a, y: b } = point
        assert(a == 10)
        assert(b == 20)
    }

    test "partial destructuring" {
        let point = Point { x: 10, y: 20 }
        let { x } = point
        assert(x == 10)
    }

    test "mutable destructuring" {
        let point = Point { x: 1, y: 2 }
        var { x, y } = point
        x = 99
        assert(x == 99)
        assert(y == 2)
    }
}
```

Array/tuple destructuring:

```vole
tests {
    test "array destructuring" {
        let [a, b] = [10, "twenty"]
        assert(a == 10)
        assert(b == "twenty")

        // With wildcard
        let [x, _, z] = [42, "ignored", 99]
        assert(x == 42)
        assert(z == 99)
    }
}
```

Destructuring imports:

```vole
let { sqrt, PI } = import "std:math"

tests {
    test "destructured import" {
        assert(PI > 3.14)
        assert(sqrt(4.0) == 2.0)
    }
}
```

### Scoping

Variables are scoped to the block they're declared in. Blocks are created by control flow constructs like `if`, `for`, and function bodies:

```vole
func compute() -> i64 {
    let inner = 42
    return inner
}

tests {
    test "scoping" {
        let x = 1
        var y = 0
        if true {
            let inner = 2
            y = x + inner
        }
        assert(x == 1)
        assert(y == 3)
        // inner is not accessible here
    }
}
```

### No Same-Scope Shadowing

Unlike some languages, Vole does not allow redeclaring a variable in the same scope:

```vole,ignore
let x = 1
let x = 2  // Error: 'x' is already defined in this scope
```

Use a different block (such as an `if` or function) if you need a new variable with the same name:

```vole
tests {
    test "nested scope shadowing" {
        let x = 1
        var result = 0
        if true {
            let x = 2      // OK - different scope
            result = x
        }
        assert(result == 2)
        assert(x == 1)
    }
}
```

Or use mutation if the value needs to change:

```vole
tests {
    test "mutation instead of shadowing" {
        var x = 1
        x = 2
        assert(x == 2)
    }
}
```

### Module-Level Variables

Variables can be declared at the top level of a file. Top-level `let` and `var` are module-scoped:

```vole
let VERSION = "1.0.0"
var request_count = 0

func handle_request() {
    request_count = request_count + 1
}

tests {
    test "module-level variables" {
        handle_request()
        handle_request()
        assert(request_count == 2)
        assert(VERSION == "1.0.0")
    }
}
```

### Common Errors

**Reassigning immutable variable:**

```vole,ignore
let x = 1
x = 2  // Error: cannot assign to immutable variable
```

Fix: Use `var` if you need mutation.

**Redeclaring in same scope:**

```vole,ignore
let x = 1
let x = 2  // Error: 'x' is already defined
```

Fix: Use a different name, nested scope, or mutation.

**Using before declaration:**

```vole,ignore
println(x)  // Error: 'x' is not defined
let x = 1
```

Fix: Declare variables before use.

**Missing initialization:**

```vole,ignore
let x: i32  // Error: variable must be initialized
```

Fix: All variables must have an initial value.
