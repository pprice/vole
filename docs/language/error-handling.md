# Error Handling

Vole uses typed errors with `fallible` functions and pattern matching for explicit error handling.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `error Name { }` | Define error type |
| `error Name { field: Type }` | Error with data |
| `fallible(T, E)` | Return type that may fail |
| `raise Error {}` | Raise an error |
| `match expr { success x => ..., error E => ... }` | Handle errors with pattern matching |
| `try expr` | Propagate errors (prefix operator) |
| `E1 \| E2` | Union of error types |

## In Depth

### Defining Errors

Define custom error types with `error`:

```vole
error NotFound {}
error InvalidInput {}
error Timeout {}
```

Errors can carry data:

```vole
error DivisionByZero {}

error OutOfRange {
    value: i32
    min: i32
    max: i32
}

error ParseError {
    message: string
    position: i32
}
```

### Fallible Functions

Functions that can fail declare their return type with `fallible(T, E)`:

```vole
func divide(a: i32, b: i32) -> fallible(i32, DivisionByZero) {
    if b == 0 {
        raise DivisionByZero {}
    }
    return a / b
}
```

The `fallible(T, E)` type means:
- Success: returns a value of type `T`
- Failure: raises an error of type `E`

### Raising Errors

Use `raise` to signal failure:

```vole
error NegativeValue {}

func safe_sqrt(x: f64) -> fallible(f64, NegativeValue) {
    if x < 0.0 {
        raise NegativeValue {}
    }
    // compute square root...
    return x  // placeholder
}
```

With error data:

```vole
error ValidationError {
    field: string
    message: string
}

func validate_age(age: i32) -> fallible(i32, ValidationError) {
    if age < 0 {
        raise ValidationError {
            field: "age",
            message: "must be non-negative"
        }
    }
    if age > 150 {
        raise ValidationError {
            field: "age",
            message: "unrealistic value"
        }
    }
    return age
}
```

### Handling Errors with Match

Use `match` with `success`/`error` patterns to handle fallible results:

```vole
let result = match divide(10, 0) {
    x => x * 2,                    // implicit success pattern
    error DivisionByZero => -1     // error pattern
}
println(result)  // -1
```

The `success` keyword is optional for success patterns, but the `error` keyword is required for error patterns:

```vole
// Explicit success keyword (optional)
let value = match risky_operation() {
    success x => x + 1,            // explicit success
    error NotFound => default_value,
    error Timeout => cached_value
}

// Implicit success (more concise)
let value = match risky_operation() {
    x => x + 1,                    // implicit success
    error NotFound => default_value,
    error Timeout => cached_value
}
```

### Destructuring Error Data

Extract fields from errors in match patterns:

```vole
error OutOfRange {
    value: i32
    max: i32
}

func clamp(x: i32, max: i32) -> fallible(i32, OutOfRange) {
    if x > max {
        raise OutOfRange { value: x, max: max }
    }
    return x
}

let result = match clamp(100, 50) {
    x => x,
    error OutOfRange { value, max } => {
        println("Value {value} exceeded max {max}")
        max
    }
}
```

### Multiple Error Types

Functions can raise multiple error types using union:

```vole
error NetworkError {}
error ParseError { message: string }

func fetch_data(url: string) -> fallible(string, NetworkError | ParseError) {
    if !is_valid_url(url) {
        raise ParseError { message: "Invalid URL format" }
    }
    if !network_available() {
        raise NetworkError {}
    }
    return do_fetch(url)
}
```

Handle each error type:

```vole
let data = match fetch_data("http://example.com") {
    result => result,
    error NetworkError => "offline",
    error ParseError { message } => {
        println("Parse failed: {message}")
        ""
    }
}
```

### Error Propagation with Try

The `try` prefix operator unwraps successful results or propagates errors. It can only be used inside fallible functions:

```vole
func process_user(id: i32) -> fallible(string, NotFound | DatabaseError) {
    let user = try find_user(id)   // unwraps on success, propagates on error
    return user.name
}
```

`try` has tight binding, so `try foo().bar()` means `(try foo()).bar()`:

```vole
func process() -> fallible(i64, DivByZero) {
    let x = try divide(10, 2)      // unwraps result
    let y = try divide(x, 3).abs() // (try divide(x, 3)).abs()
    return y
}
```

Using `try` for multiple fallible calls:

```vole
func process() -> fallible(Result, ProcessError) {
    let a = try step_one()
    let b = try step_two(a)
    return finalize(b)
}
```

### Exhaustive Error Handling

Match expressions on fallible types must have at least one error pattern:

```vole
// Must handle errors
let x = match operation() {
    result => result,
    error ErrorA => 1,
    error ErrorB => 2
}
```

Use a wildcard for catch-all error handling:

```vole
let x = match operation() {
    result => result,
    error _ => 0  // Catches all errors
}
```

### Converting Between Error Types

Map errors to different types:

```vole
error AppError {
    message: string
}

func app_operation() -> fallible(i32, AppError) {
    let result = match low_level_operation() {
        x => x,
        error LowLevelError { code } => {
            raise AppError {
                message: "Operation failed with code {code}"
            }
        }
    }
    return result
}
```

### Error Handling Patterns

**Default value on error:**

```vole
let config = match load_config() {
    c => c,
    error _ => default_config()
}
```

**Log and recover:**

```vole
let result = match risky_operation() {
    x => x,
    error err => {
        log_error(err)
        fallback_value
    }
}
```

**Propagate with try in fallible functions:**

```vole
func process() -> fallible(Result, ProcessError) {
    let a = try step_one()
    let b = try step_two(a)
    return finalize(b)
}
```

### Best Practices

1. **Use specific error types** - Define errors that describe what went wrong
2. **Include relevant data** - Add fields that help diagnose the issue
3. **Handle errors at the right level** - Don't handle too early or too late
4. **Don't ignore errors** - Always handle or propagate explicitly
5. **Use union types sparingly** - Too many error types can be unwieldy
6. **Use `try` for propagation** - Cleaner than manual re-raising in fallible functions

### Error vs Optional

Use errors when:
- The failure reason matters
- Caller needs to take different actions
- Failure is exceptional

Use optionals when:
- "Not found" is a normal case
- No additional context needed
- Simple presence/absence check

```vole
// Optional: finding an element
func find(arr: [i32], target: i32) -> i32? {
    for x in arr {
        if x == target {
            return x
        }
    }
    return nil
}

// Error: operation that should succeed
func read_file(path: string) -> fallible(string, FileError) {
    if !file_exists(path) {
        raise FileError { message: "File not found" }
    }
    return do_read(path)
}
```
