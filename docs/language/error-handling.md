# Error Handling

Vole uses typed errors with `fallible` functions and `try`/`catch` for explicit error handling.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `error Name { }` | Define error type |
| `error Name { field: Type }` | Error with data |
| `fallible(T, E)` | Return type that may fail |
| `raise Error {}` | Raise an error |
| `try expr catch { }` | Handle errors |
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

### Handling Errors with try/catch

Use `try`/`catch` to handle fallible results:

```vole
let result = try divide(10, 0) catch {
    DivisionByZero {} => -1
}
println(result)  // -1
```

The catch block pattern-matches on error types:

```vole
let value = try risky_operation() catch {
    NotFound {} => default_value
    Timeout {} => cached_value
    InvalidInput {} => fallback_value
}
```

### Destructuring Error Data

Extract fields from errors in catch:

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

let result = try clamp(100, 50) catch {
    OutOfRange { value, max } => {
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
let data = try fetch_data("http://example.com") catch {
    NetworkError {} => "offline"
    ParseError { message } => {
        println("Parse failed: {message}")
        ""
    }
}
```

### Error Propagation

Call fallible functions from other fallible functions:

```vole
func process_user(id: i32) -> fallible(string, NotFound | DatabaseError) {
    let user = try find_user(id) catch {
        NotFound {} => raise NotFound {}
        DatabaseError {} => raise DatabaseError {}
    }
    return user.name
}
```

### Exhaustive Error Handling

The catch block must handle all possible error types:

```vole
// Error: non-exhaustive catch
let x = try operation() catch {
    ErrorA {} => 1
    // Missing ErrorB handler!
}
```

Use a wildcard for catch-all:

```vole
let x = try operation() catch {
    ErrorA {} => 1
    _ => 0  // Catches all other errors
}
```

### Converting Between Error Types

Map errors to different types:

```vole
error AppError {
    message: string
}

func app_operation() -> fallible(i32, AppError) {
    let result = try low_level_operation() catch {
        LowLevelError { code } => {
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
let config = try load_config() catch {
    _ => default_config()
}
```

**Log and recover:**

```vole
let result = try risky_operation() catch {
    err => {
        log_error(err)
        fallback_value
    }
}
```

**Early return on error:**

```vole
func process() -> fallible(Result, ProcessError) {
    let a = try step_one() catch {
        StepOneError {} => raise ProcessError {}
    }

    let b = try step_two(a) catch {
        StepTwoError {} => raise ProcessError {}
    }

    return finalize(b)
}
```

### Best Practices

1. **Use specific error types** - Define errors that describe what went wrong
2. **Include relevant data** - Add fields that help diagnose the issue
3. **Handle errors at the right level** - Don't catch too early or too late
4. **Don't ignore errors** - Always handle or propagate explicitly
5. **Use union types sparingly** - Too many error types can be unwieldy

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
