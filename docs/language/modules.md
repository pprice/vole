# Modules and Imports

Vole organizes code into modules. Use `import` to bring in functionality from the standard library.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `let m = import "std:name"` | Import standard library module |
| `m.function()` | Call imported function |
| `m.CONSTANT` | Access module constant |

## Importing Modules

Import returns a module value:

```vole
let math = import "std:math"

let result = math.sqrt(16.0)
println("{result}")  // 4.0
```

## Standard Library

### std:math

Mathematical functions and constants:

| Export | Type | Description |
|--------|------|-------------|
| `sin(x)` | `(f64) -> f64` | Sine |
| `cos(x)` | `(f64) -> f64` | Cosine |
| `tan(x)` | `(f64) -> f64` | Tangent |
| `sqrt(x)` | `(f64) -> f64` | Square root |
| `pow(base, exp)` | `(f64, f64) -> f64` | Exponentiation |
| `floor(x)` | `(f64) -> f64` | Round down |
| `ceil(x)` | `(f64) -> f64` | Round up |
| `round(x)` | `(f64) -> f64` | Round to nearest |
| `abs(x)` | `(f64) -> f64` | Absolute value |
| `min(a, b)` | `(f64, f64) -> f64` | Minimum |
| `max(a, b)` | `(f64, f64) -> f64` | Maximum |
| `PI` | `f64` | Pi constant (3.14159...) |
