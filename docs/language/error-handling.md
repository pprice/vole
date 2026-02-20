# Error Handling

Vole uses typed errors with `fallible` functions and pattern matching for explicit error handling.

## Quick Reference

```vole,ignore
error Name { }                                // Define error type
error Name { field: Type }                    // Error with data
fallible(T, E)                                // Return type that may fail
raise Error {}                                // Raise an error
match expr { success x => ..., error E => ... }  // Handle errors
try expr                                      // Propagate errors (prefix operator)
E1 | E2                                       // Union of error types
```

## In Depth

### Defining Errors

Define custom error types with `error`:

```vole
error NotFound {}
error InvalidInput {}
error Timeout { ms: i64 }
```

Errors can carry data:

```vole
error DivByZero {}

error Overflow {
    value: i64,
    max: i64,
}

error ParseError {
    message: string,
}
```

### Fallible Functions

Functions that can fail declare their return type with `fallible(T, E)`:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "basic success" {
        let result = match divide(10, 2) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 5)
    }
}
```

The `fallible(T, E)` type means:
- Success: returns a value of type `T`
- Failure: raises an error of type `E`

### Raising Errors

Use `raise` to signal failure:

```vole
error Overflow { value: i64, max: i64 }

func checkOverflow(value: i64, max: i64) -> fallible(i64, Overflow) {
    if value > max {
        raise Overflow { value: value, max: max }
    }
    return value
}

tests {
    test "raise on overflow" {
        let result = match checkOverflow(150, 100) {
            success x => x
            Overflow => -1
            error => -999
            _ => -888
        }
        assert(result == -1)
    }

    test "success when in range" {
        let result = match checkOverflow(50, 100) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 50)
    }
}
```

### Handling Errors with Match

Use `match` with `success` and `error` patterns to handle fallible results:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "success with binding" {
        let result = match divide(10, 2) {
            success x => x + 100
            error => 0
            _ => -888
        }
        assert(result == 105)
    }

    test "success without binding" {
        let result = match divide(10, 2) {
            success => 42
            error => 0
            _ => -888
        }
        assert(result == 42)
    }

    test "error match" {
        let result = match divide(10, 0) {
            success x => x
            error => -1
            _ => -888
        }
        assert(result == -1)
    }

    test "specific error type pattern" {
        let result = match divide(10, 0) {
            success x => x
            error DivByZero => -1
            error => -999
            _ => -888
        }
        assert(result == -1)
    }
}
```

The `error` keyword is required for error patterns. The `success` keyword is optional for success patterns but recommended for clarity.

### Error Pattern Variations

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "bare error catchall" {
        let result = match divide(10, 0) {
            success x => x
            error => -1
            _ => -888
        }
        assert(result == -1)
    }

    test "error with identifier binding" {
        let result = match divide(10, 0) {
            success x => x
            error e => -1
            _ => -888
        }
        assert(result == -1)
    }

    test "specific error type" {
        let result = match divide(10, 0) {
            success x => x
            error DivByZero => -1
            error => -999
            _ => -888
        }
        assert(result == -1)
    }
}
```

### Match Arm Ordering

Success and error patterns can appear in any order:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "success before error" {
        let result = match divide(10, 2) {
            success x => x
            error => -1
            _ => -888
        }
        assert(result == 5)
    }

    test "error before success" {
        let result = match divide(10, 2) {
            error => -1
            success x => x
            _ => -888
        }
        assert(result == 5)
    }

    test "specific error before catchall" {
        let result = match divide(10, 0) {
            success x => x
            error DivByZero => -1
            error => -999
            _ => -888
        }
        assert(result == -1)
    }
}
```

### Multiple Error Types

Functions can raise multiple error types using union:

```vole
error NotFound { key: string }
error Timeout { ms: i64 }

func complexOp(x: i64) -> fallible(i64, NotFound | Timeout) {
    if x < 0 {
        raise NotFound { key: "negative" }
    }
    if x > 100 {
        raise Timeout { ms: x }
    }
    return x * 2
}

tests {
    test "specific error types in union" {
        let r1 = match complexOp(-5) {
            success x => x
            error NotFound => -1
            error Timeout => -2
            error => -999
            _ => -888
        }
        assert(r1 == -1)

        let r2 = match complexOp(150) {
            success x => x
            error NotFound => -1
            error Timeout => -2
            error => -999
            _ => -888
        }
        assert(r2 == -2)
    }

    test "error catchall with union type" {
        let r1 = match complexOp(-5) {
            success x => x
            error => -1
            _ => -888
        }
        assert(r1 == -1)

        let r3 = match complexOp(25) {
            success x => x
            error => -999
            _ => -888
        }
        assert(r3 == 50)
    }
}
```

### Error Propagation with try

The `try` prefix operator unwraps successful results or propagates errors. It can only be used inside fallible functions:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

func processDivide(a: i64, b: i64, c: i64) -> fallible(i64, DivByZero) {
    let x = try divide(a, b)
    let y = try divide(x, c)
    return y
}

tests {
    test "try propagates success" {
        let result = match processDivide(100, 2, 5) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 10)
    }

    test "try propagates first error" {
        let result = match processDivide(100, 0, 5) {
            success x => x
            error DivByZero => -1
            error => -999
            _ => -888
        }
        assert(result == -1)
    }

    test "try propagates second error" {
        let result = match processDivide(100, 2, 0) {
            success x => x
            error DivByZero => -1
            error => -999
            _ => -888
        }
        assert(result == -1)
    }
}
```

### Chaining try with Normal Expressions

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

func mixedOps(a: i64, b: i64) -> fallible(i64, DivByZero) {
    let x = try divide(a, b)
    let y = x + 10
    let z = try divide(y, 2)
    return z * 3
}

tests {
    test "mixed operations with try" {
        let result = match mixedOps(20, 2) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 30)
    }
}
```

### try in Control Flow

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

func sumDivisions(n: i64) -> fallible(i64, DivByZero) {
    var sum = 0
    var i = 1
    while i <= n {
        let result = try divide(100, i)
        sum = sum + result
        i = i + 1
    }
    return sum
}

tests {
    test "try in loop" {
        let result = match sumDivisions(4) {
            success x => x
            error => -1
            _ => -888
        }
        assert(result == 208)
    }
}
```

### Guards on Fallible Match Patterns

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "guard on success pattern" {
        let result = match divide(100, 2) {
            success x if x > 100 => 1
            success x if x > 10 => 2
            success x => 3
            error => -1
            _ => -888
        }
        assert(result == 2)
    }
}
```

### Expression-bodied Fallible Functions

Fallible functions can use expression body syntax:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

func exprDivide(a: i64, b: i64) -> fallible(i64, DivByZero) => divide(a, b)
func exprDouble(x: i64) -> fallible(i64, DivByZero) => divide(x * 2, 1)

tests {
    test "expr-bodied success" {
        let result = match exprDivide(10, 2) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 5)
    }

    test "expr-bodied with arithmetic" {
        let result = match exprDouble(21) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 42)
    }
}
```

### Fallible Lambdas

Lambdas can also be fallible:

```vole
error DivByZero {}

let fallibleLambda = (a: i64, b: i64) -> fallible(i64, DivByZero) => {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "lambda block body success" {
        let result = match fallibleLambda(10, 2) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 5)
    }

    test "lambda block body error" {
        let result = match fallibleLambda(10, 0) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == -999)
    }
}
```

### Error Handling and Recovery

Handle an error, get a default value, then continue:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "handle error then continue" {
        let first = match divide(10, 0) {
            success x => x
            error => 100
            _ => -888
        }
        let second = match divide(first, 2) {
            success x => x
            error => -999
            _ => -888
        }
        assert(second == 50)
    }
}
```

### Early Return with raise

Functions with multiple raise paths work with early returns:

```vole
error ParseError { message: string }

func parsePositive(s: string) -> fallible(i64, ParseError) {
    if s == "one" {
        return 1
    }
    if s == "two" {
        return 2
    }
    raise ParseError { message: "unknown: " + s }
}

tests {
    test "early return paths" {
        let r1 = match parsePositive("one") {
            success x => x
            error => -999
            _ => -888
        }
        assert(r1 == 1)

        let r2 = match parsePositive("two") {
            success x => x
            error => -999
            _ => -888
        }
        assert(r2 == 2)

        let r3 = match parsePositive("three") {
            success x => x
            error ParseError => -999
            _ => -888
        }
        assert(r3 == -999)
    }
}
```

### Error vs Optional

Use errors when the failure reason matters; use optionals for simple presence/absence:

```vole
// Optional: finding an element
func find(arr: [i64], target: i64) -> i64? {
    for x in arr {
        if x == target {
            return x
        }
    }
    return nil
}

tests {
    test "optional find" {
        let result = find([1, 2, 3], 2)
        assert(result is i64)

        let missing = find([1, 2, 3], 99)
        assert(missing is nil)
    }
}
```

### Best Practices

1. **Use specific error types** -- Define errors that describe what went wrong
2. **Include relevant data** -- Add fields that help diagnose the issue
3. **Handle errors at the right level** -- Don't handle too early or too late
4. **Don't ignore errors** -- Always handle or propagate explicitly
5. **Use union types sparingly** -- Too many error types can be unwieldy
6. **Use `try` for propagation** -- Cleaner than manual re-raising in fallible functions
