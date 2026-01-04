# Functions

Functions are first-class values in Vole. They can be passed as arguments, returned from other functions, and stored in variables.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `func name(a: T) -> R { }` | Named function with return type |
| `func name(a: T) { }` | No return value (implicit nil) |
| `return value` | Return a value |
| `return` | Return from nil function |
| `(x: T) => x * 2` | Lambda, single expression |
| `(x: T) => { ... }` | Lambda with block body |
| `(T, T) -> R` | Function type signature |

## In Depth

### Function Declaration

Declare functions with `func`, parameter types, and optional return type:

```vole
func add(a: i32, b: i32) -> i32 {
    return a + b
}

func greet(name: string) {
    println("Hello, " + name)
}
```

If no return type is specified, the function returns nil:

```vole
func log(message: string) {
    println(message)
    // implicit nil return
}
```

### Parameters

Parameters require explicit type annotations:

```vole
func process(text: string, count: i32, flag: bool) {
    // ...
}
```

Functions can take no parameters:

```vole
func get_value() -> i32 {
    return 42
}
```

### Return Values

Use `return` to return a value:

```vole
func square(x: i32) -> i32 {
    return x * x
}
```

The last expression in a function body is NOT automatically returned - you must use `return`:

```vole
func double(x: i32) -> i32 {
    x * 2  // This does nothing!
}

func double(x: i32) -> i32 {
    return x * 2  // Correct
}
```

Early return is allowed:

```vole
func abs(x: i32) -> i32 {
    if x < 0 {
        return -x
    }
    return x
}
```

### Lambda Expressions

Lambdas are anonymous functions. Single expression form:

```vole
let double = (x: i64) => x * 2
let add = (a: i64, b: i64) => a + b
let always_true = () => true
```

Block body form for multiple statements:

```vole
let process = (x: i64) => {
    let y = x * 2
    let z = y + 1
    return z
}
```

In block form, use `return` to return a value.

### Lambda Type Inference

Lambda parameter types are inferred from context:

```vole
let nums = [1, 2, 3, 4, 5]
let doubled = nums.map((x) => x * 2)  // x inferred as i32
```

When context isn't available, annotate the parameters or variable:

```vole
let fn: (i32, i32) -> i32 = (a, b) => a + b
// or
let fn = (a: i32, b: i32) => a + b
```

### Function Types

Function types describe the signature of callable values:

```vole
// Function that takes two i32 and returns i32
let add: (i32, i32) -> i32 = (a: i32, b: i32) => a + b

// Function that takes string and returns nothing
let log: (string) -> nil = (msg: string) => println(msg)

// Function that takes nothing and returns i32
let random: () -> i32 = () => 42
```

### Higher-Order Functions

Functions can take functions as parameters:

```vole
func apply(f: (i32) -> i32, x: i32) -> i32 {
    return f(x)
}

let result = apply((x: i32) => x * 2, 5)  // 10
```

### Closures

Lambdas capture variables from their enclosing scope:

```vole
let multiplier = 3
let triple = (x: i64) => x * multiplier
println(triple(4))  // 12
```

Closures can capture mutable variables:

```vole
let mut total = 0
let add_to_total = (x: i64) => {
    total = total + x
}

add_to_total(5)
add_to_total(3)
println(total)  // 8
```

> **Note:** Returning lambdas from functions (currying) is currently a work in progress and may not work correctly.

### Calling Functions

Call functions with parentheses:

```vole
let result = add(1, 2)
greet("Alice")
let now = get_value()
```

Functions stored in variables are called the same way:

```vole
let fn = (x: i64) => x * 2
let result = fn(5)  // 10
```

### Recursion

Functions can call themselves:

```vole
func factorial(n: i32) -> i32 {
    if n <= 1 {
        return 1
    }
    return n * factorial(n - 1)
}

println(factorial(5))  // 120
```

```vole
func fibonacci(n: i32) -> i32 {
    if n <= 1 {
        return n
    }
    return fibonacci(n - 1) + fibonacci(n - 2)
}
```

Tail-recursive functions are optimized by the compiler.

### Common Patterns

**Transform elements:**

```vole
let nums = [1, 2, 3, 4, 5]
let squared = nums.map((x) => x * x)
```

**Filter elements:**

```vole
let nums = [1, 2, 3, 4, 5]
let evens = nums.filter((x) => x % 2 == 0)
```

**Reduce to single value:**

```vole
let nums = [1, 2, 3, 4, 5]
let sum = nums.reduce(0, (acc, x) => acc + x)
```
