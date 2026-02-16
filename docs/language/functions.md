# Functions

Functions are first-class values in Vole. They can be passed as arguments, returned from other functions, and stored in variables.

## Quick Reference

```vole,ignore
func name(a: T) -> R { }      // Named function with return type
func name(a: T) { }           // No return value (void)
func name(a: T) -> R => expr  // Expression-bodied function
return value                   // Return a value
(x: T) -> R => x * 2          // Lambda, single expression
(x: T) -> R => { ... }        // Lambda with block body
(T, T) -> R                   // Function type signature
```

## In Depth

### Function Declaration

Declare functions with `func`, parameter types, and optional return type:

```vole
func add(a: i64, b: i64) -> i64 {
    return a + b
}

func greet(name: string) {
    print("Hello, " + name)
}

tests {
    test "basic functions" {
        assert(add(20, 22) == 42)
    }
}
```

If no return type is specified and the function has no return statement, the function is void:

```vole
func log(message: string) {
    let x = message
}

tests {
    test "void function" {
        log("hello")
        assert(true)
    }
}
```

### Return Values

Use `return` to return a value:

```vole
func square(x: i64) -> i64 {
    return x * x
}

tests {
    test "return value" {
        assert(square(5) == 25)
    }
}
```

The last expression in a function body is NOT automatically returned -- you must use `return`:

```vole
tests {
    test "explicit return required" {
        func double(x: i64) -> i64 {
            return x * 2
        }
        assert(double(21) == 42)
    }
}
```

Early return is allowed:

```vole
func abs(x: i64) -> i64 {
    if x < 0 {
        return -x
    }
    return x
}

tests {
    test "early return" {
        assert(abs(-5) == 5)
        assert(abs(5) == 5)
    }
}
```

### Expression-bodied Functions

Use `=>` for concise single-expression function bodies:

```vole
func double(x: i64) -> i64 => x * 2
func exprAdd(a: i64, b: i64) -> i64 => a + b
func always_true() => true
func greeting() => "hello"

tests {
    test "expression-bodied functions" {
        assert(double(5) == 10)
        assert(exprAdd(3, 4) == 7)
        assert(always_true() == true)
        assert(greeting() == "hello")
    }
}
```

The return type can be inferred for expression-bodied functions:

```vole
func triple(x: i64) => x * 3
func isPositive(x: i64) => x > 0

tests {
    test "inferred return type" {
        assert(triple(7) == 21)
        assert(isPositive(5) == true)
        assert(isPositive(-3) == false)
    }
}
```

### Default Parameter Values

Parameters can have default values:

```vole
func greet(name: string, greeting: string = "Hello") -> string => "{greeting}, {name}!"

func add(a: i64, b: i64 = 10, c: i64 = 100) -> i64 => a + b + c

tests {
    test "default parameters" {
        assert(greet("World", "Hi") == "Hi, World!")
        assert(greet("World") == "Hello, World!")

        assert(add(1) == 111)
        assert(add(1, 2) == 103)
        assert(add(1, 2, 3) == 6)
    }
}
```

### Optional Return Types

Functions can return optional types (`T?`):

```vole
func maybeDouble(x: i64) -> i64? {
    if x < 0 {
        return nil
    }
    return x * 2
}

func safeDouble(x: i64) -> i64 {
    return maybeDouble(x) ?? 0
}

tests {
    test "optional returns" {
        assert(maybeDouble(5) == 10)
        assert(maybeDouble(-1) == nil)
        assert(safeDouble(5) == 10)
        assert(safeDouble(-1) == 0)
    }
}
```

### Lambda Expressions

Lambdas are anonymous functions. Single expression form:

```vole
let simpleLambda = (x: i64) => x * 2
let noParams = () => 5
let multiParams = (a: i64, b: i64) => a + b

tests {
    test "simple lambdas" {
        assert(simpleLambda(5) == 10)
        assert(noParams() == 5)
        assert(multiParams(2, 3) == 5)
    }
}
```

Block body form for multiple statements (use `return` to return a value):

```vole
tests {
    test "block body lambda" {
        let complex = (x: i64) -> i64 => {
            let y = x * 2
            return y + 1
        }
        assert(complex(5) == 11)
    }
}
```

Lambdas with explicit return type annotation:

```vole
tests {
    test "typed lambda" {
        let typed = (x: i32, y: i32) -> i32 => x + y
        let a: i32 = 5
        let b: i32 = 3
        assert(typed(a, b) == 8)
    }
}
```

### Lambda Type Inference

Lambda parameter types can be inferred from context when passed to higher-order functions:

```vole
func applyFn(fn: (i32) -> i32, x: i32) -> i32 {
    return fn(x)
}

tests {
    test "lambda type inference" {
        let result = applyFn((x) => x + x, 5)
        assert(result == 10)
    }
}
```

### Function Types

Function types describe the signature of callable values:

```vole
tests {
    test "function types" {
        let add: (i64, i64) -> i64 = (a: i64, b: i64) => a + b
        assert(add(10, 20) == 30)

        let random: () -> i64 = () => 42
        assert(random() == 42)
    }
}
```

### Higher-Order Functions

Functions can take functions as parameters:

```vole
func apply(f: (i64) -> i64, x: i64) -> i64 {
    return f(x)
}

func double(x: i64) -> i64 {
    return x * 2
}

func triple(x: i64) -> i64 {
    return x * 3
}

tests {
    test "higher-order functions" {
        assert(apply(double, 5) == 10)
        assert(apply(triple, 5) == 15)
        assert(apply((x: i64) => x + 1, 5) == 6)
    }
}
```

### Functions as Values

Named functions can be stored in variables and passed around:

```vole
func double(x: i64) -> i64 {
    return x * 2
}

tests {
    test "function stored in variable" {
        let f = double
        assert(f(10) == 20)
    }
}
```

Functions can also be passed to iterator methods:

```vole
func double(x: i64) -> i64 {
    return x * 2
}

func is_even(x: i64) -> bool {
    return x % 2 == 0
}

tests {
    test "function passed to map" {
        let arr = [1, 2, 3]
        let result = arr.iter().map(double).collect()
        assert(result[0] == 2)
        assert(result[1] == 4)
        assert(result[2] == 6)
    }

    test "function passed to filter" {
        let arr = [1, 2, 3, 4, 5, 6]
        let evens = arr.iter().filter(is_even).collect()
        assert(evens[0] == 2)
        assert(evens[1] == 4)
        assert(evens[2] == 6)
    }
}
```

### Closures

Lambdas capture variables from their enclosing scope:

```vole
tests {
    test "closure capture" {
        let multiplier = 3
        let triple = (x: i64) => x * multiplier
        assert(triple(4) == 12)
    }
}
```

Closures can capture mutable variables:

```vole
tests {
    test "mutable closure" {
        let mut count = 0
        let inc = () -> i64 => {
            count = count + 1
            return count
        }
        assert(inc() == 1)
        assert(inc() == 2)
        assert(inc() == 3)
    }
}
```

### Returning Lambdas (Currying)

Functions can return lambdas:

```vole
tests {
    test "returned lambda" {
        let makeAdder = (n: i64) -> (i64) -> i64 => (x: i64) => x + n
        let add5 = makeAdder(5)
        assert(add5(10) == 15)
    }
}
```

### Recursion

Functions can call themselves:

```vole
func factorial(n: i64) -> i64 {
    if n <= 1 { return 1 }
    return n * factorial(n - 1)
}

func fibonacci(n: i64) -> i64 {
    if n <= 1 {
        return n
    }
    return fibonacci(n - 1) + fibonacci(n - 2)
}

tests {
    test "recursion" {
        assert(factorial(5) == 120)
        assert(fibonacci(10) == 55)
    }
}
```

Recursive lambdas also work:

```vole
tests {
    test "recursive lambda" {
        let factorial = (n: i64) -> i64 => {
            if n <= 1 { return 1 }
            return n * factorial(n - 1)
        }
        assert(factorial(5) == 120)
    }
}
```

Tail-recursive functions are optimized by the compiler, allowing deep recursion without stack overflow:

```vole
func countdown(n: i32) -> i32 {
    if n <= 0 {
        return 0_i32
    }
    return countdown(n - 1)
}

func factorial_tail(n: i32, acc: i32) -> i32 {
    if n <= 1 {
        return acc
    }
    return factorial_tail(n - 1, n * acc)
}

func factorial(n: i32) -> i32 {
    return factorial_tail(n, 1_i32)
}

tests {
    test "tail call optimization" {
        assert(countdown(10000) == 0)
        assert(factorial(5) == 120)
        assert(factorial(10) == 3628800)
    }
}
```

### Nested Functions

Functions can be declared inside other functions and test blocks:

```vole
tests {
    test "nested functions" {
        func localAdd(a: i64, b: i64) -> i64 {
            return a + b
        }
        assert(localAdd(10, 20) == 30)
    }

    test "nested function with closure" {
        let x = 10
        func addX(y: i64) -> i64 {
            return x + y
        }
        assert(addX(5) == 15)
    }

    test "nested expression-bodied function" {
        func double(x: i64) -> i64 => x * 2
        assert(double(21) == 42)
    }
}
```

### Trailing Commas

Trailing commas are allowed in parameter lists and call arguments:

```vole
func add(a: i32, b: i32,) -> i32 {
    return a + b
}

tests {
    test "trailing commas" {
        assert(add(1, 2) == 3)
        assert(add(1, 2,) == 3)

        let arr = [1, 2, 3,]
        assert(arr[0] == 1)
    }
}
```

### Union Return Type Inference

When a function has no declared return type but returns different types from different branches, the return type is inferred as a union:

```vole
func returnIntOrString(x: bool) {
    if x {
        return 42
    }
    return "hello"
}

tests {
    test "union return type inference" {
        let a = returnIntOrString(true)
        let b = returnIntOrString(false)
        assert(a is i64)
        assert(b is string)
    }
}
```
