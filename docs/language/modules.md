# Modules and Imports

Vole organizes code into modules. Every `.vole` file is a module. All top-level declarations (functions, classes, interfaces, constants) are automatically exported.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `let m = import "std:name"` | Import standard library module |
| `let m = import "./path"` | Import relative module |
| `let { a, b } = import "std:name"` | Destructured import |
| `let { a as x } = import "std:name"` | Destructured import with rename |
| `m.function()` | Call imported function |
| `m.Type { ... }` | Construct imported type |
| `m.Type.static_method()` | Call imported static method |
| `m.CONSTANT` | Access module constant |

## Module Imports

Import returns a module value. Access exports with dot notation:

```vole
let math = import "std:math"

tests {
    test "module import" {
        assert(math.sqrt(16.0) == 4.0)
        assert(math.PI > 3.14)
        assert(math.PI < 3.15)
    }
}
```

## Destructured Imports

Extract specific exports directly into scope:

```vole
tests {
    test "destructured import" {
        let { sqrt, PI } = import "std:math"
        assert(sqrt(16.0) == 4.0)
        assert(PI > 3.14)
    }
}
```

Rename imports with `as`:

```vole
tests {
    test "destructured with rename" {
        let { sqrt as squareRoot, PI as pi } = import "std:math"
        assert(squareRoot(4.0) == 2.0)
        assert(pi > 3.14)
    }
}
```

Mix renamed and non-renamed imports:

```vole
tests {
    test "mixed destructured import" {
        let { sqrt, pow as power } = import "std:math"
        assert(sqrt(16.0) == 4.0)
        assert(power(2.0, 3.0) == 8.0)
    }
}
```

## Destructured Type Imports

Destructured imports can bring in types (classes, interfaces) for use as type names:

```vole
tests {
    test "destructured type import" {
        let { Duration } = import "std:time"
        let d = Duration { nanos: 1000 }
        assert(d.as_nanos() == 1000)
    }

    test "destructured type in annotation" {
        let { Duration } = import "std:time"
        func get_nanos(d: Duration) -> i64 {
            return d.as_nanos()
        }
        let d = Duration { nanos: 2000 }
        assert(get_nanos(d) == 2000)
    }

    test "renamed type import" {
        let { Duration as Dur } = import "std:time"
        let d = Dur { nanos: 5000 }
        assert(d.as_nanos() == 5000)
    }

    test "multiple type imports" {
        let { Duration, Timestamp } = import "std:time"
        let d = Duration { nanos: 1000 }
        let ts = Timestamp { nanos: 1000000000, offset_mins: 0 }
        assert(d.nanos == 1000)
        assert(ts.nanos == 1000000000)
    }
}
```

## Relative Imports

Import sibling or nested modules using relative paths:

```vole,ignore
// Import a sibling file (same directory)
let utils = import "./utils"

// Import from a subdirectory
let nested = import "./sub/nested"

// Import from a parent directory
let shared = import "../shared"

tests {
    test "use imported functions" {
        assert(utils.add(2, 3) == 5)
        assert(nested.square(7) == 49)
    }
}
```

Relative paths are resolved from the importing file's directory. The `.vole` extension is optional.

## Qualified Type Access

When you import a module, you can access its types with qualified names:

```vole,ignore
let lib = import "./my_lib"

// Use qualified type for interface dispatch
let g: lib.IGreeter = lib.SimpleGreeter { name: "hello" }

// Call methods on the qualified type
assert(g.greet() == "hello")
```

## Module-Qualified Static Methods

Call static methods on types from imported modules:

```vole,ignore
let types = import "./types_lib"

// Call a static method on an imported type
let d = types.Duration.seconds(5)
let p = types.Point.origin()
```

For standard library types with static methods:

```vole
tests {
    test "stdlib static methods" {
        let time = import "std:time"
        let d = time.Duration.nanos(4000)
        assert(d.as_nanos() == 4000)
    }
}
```

## Implementing Imported Interfaces

You can implement interfaces from imported modules using qualified syntax:

```vole,ignore
let traits = import "std:prelude/traits"

class Point {
    x: i64,
    y: i64,
}

implement traits.Hashable for Point {
    func hash() -> i64 {
        return self.x + self.y
    }
}
```

## Writing Modules

Every `.vole` file is a module. All top-level declarations are automatically exported:

```vole,ignore
// my_utils.vole

let VERSION = 42

func add(a: i64, b: i64) -> i64 {
    return a + b
}

func multiply(a: i64, b: i64) -> i64 {
    return a * b
}

class Point {
    x: i64,
    y: i64,
}
```

Other files can then import this module:

```vole,ignore
let utils = import "./my_utils"

tests {
    test "use module" {
        assert(utils.VERSION == 42)
        assert(utils.add(2, 3) == 5)
        let p = utils.Point { x: 1, y: 2 }
    }
}
```

## Imports Inside Tests Blocks

Imports can be placed inside `tests` blocks, scoped to that block:

```vole
tests "scoped import" {
    let math = import "std:math"

    test "import works inside tests block" {
        assert(math.sqrt(16.0) == 4.0)
    }
}

tests "destructured import in tests" {
    let { sqrt, min, max } = import "std:math"

    test "destructured functions work" {
        assert(sqrt(25.0) == 5.0)
        assert(min(1.0, 2.0) == 1.0)
        assert(max(1.0, 2.0) == 2.0)
    }
}
```

Imports in one `tests` block do not leak into other blocks.

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
| `lerp(a, b, t)` | `(f64, f64, f64) -> f64` | Linear interpolation |
| `clamp(x, lo, hi)` | `(f64, f64, f64) -> f64` | Clamp to range |
| `deg_to_rad(x)` | `(f64) -> f64` | Degrees to radians |
| `rad_to_deg(x)` | `(f64) -> f64` | Radians to degrees |
| `PI` | `f64` | Pi constant (3.14159...) |

```vole
let math = import "std:math"

tests {
    test "math functions" {
        assert(math.sqrt(16.0) == 4.0)
        assert(math.pow(2.0, 3.0) == 8.0)
        assert(math.abs(-5.0) == 5.0)
        assert(math.min(3.0, 5.0) == 3.0)
        assert(math.max(3.0, 5.0) == 5.0)
        assert(math.floor(3.7) == 3.0)
        assert(math.ceil(3.2) == 4.0)
        assert(math.round(3.5) == 4.0)
    }

    test "math trig" {
        assert(math.sin(0.0) == 0.0)
        assert(math.cos(0.0) == 1.0)
        assert(math.tan(0.0) == 0.0)
    }

    test "math pure vole functions" {
        assert(math.lerp(0.0, 10.0, 0.5) == 5.0)
        assert(math.clamp(5.0, 0.0, 10.0) == 5.0)
        assert(math.clamp(-5.0, 0.0, 10.0) == 0.0)
        assert(math.clamp(15.0, 0.0, 10.0) == 10.0)
    }

    test "math constants" {
        assert(math.PI > 3.14)
        assert(math.PI < 3.15)
    }
}
```

### std:time

Time-related types and functions:

```vole
let time = import "std:time"

tests {
    test "duration" {
        let d = time.Duration.nanos(4000)
        assert(d.as_nanos() == 4000)
    }

    test "duration from struct literal" {
        let { Duration } = import "std:time"
        let d = Duration { nanos: 1000 }
        assert(d.nanos == 1000)
    }
}
```

### std:collections/map and std:collections/set

Collection types:

```vole,ignore
let { Map } = import "std:collections/map"
let { Set } = import "std:collections/set"

let m = Map.new()
m.set("key", "value")
let v = m.get("key")

let s = Set.new()
s.add(42)
assert(s.contains(42))
```

### std:task

Async task execution and channels:

```vole,ignore
let { Task, Channel } = import "std:task"

let ch = Channel.new()
Task.spawn(() => {
    ch.send(42)
})
let result = ch.recv()
```

### std:prelude/traits

Standard interfaces available for implementation:

```vole,ignore
let traits = import "std:prelude/traits"

class MyType {
    value: i64,
}

implement traits.Hashable for MyType {
    func hash() -> i64 {
        return self.value
    }
}
```
