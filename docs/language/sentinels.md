# Sentinel Types

Sentinels are zero-field types that act as lightweight singleton markers. They are commonly used in union types to represent states like "not found", "timed out", or "done".

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `sentinel Name` | Declare a sentinel type |
| `Name` | Construct a sentinel (bare) |
| `Name {}` | Construct a sentinel (braced, equivalent) |
| `x is Name` | Check if a value is a particular sentinel |

## Declaring Sentinels

Use the `sentinel` keyword to declare a new sentinel type:

```vole
sentinel Empty

sentinel Ready

sentinel Waiting

tests {
    test "sentinel construction" {
        let e = Empty
        let r = Ready {}
        assert(true)
    }
}
```

Both bare (`Empty`) and braced (`Empty {}`) construction are equivalent:

```vole
sentinel Marker

tests {
    test "bare and braced are equal" {
        let a = Marker
        let b = Marker {}
        assert(a == b)
    }
}
```

## Built-in Sentinels

Vole provides two built-in sentinels in the prelude:

| Sentinel | Purpose |
|----------|---------|
| `Done` | Signals iterator exhaustion |
| `nil` | Represents the absence of a value |

```vole
tests {
    test "built-in sentinels" {
        let d = Done
        let d2 = Done {}
        assert(d == d2)

        let n = nil
        let n2 = nil
        assert(n == n2)
    }
}
```

## Using Sentinels in Unions

Sentinels are most useful as members of union types, where they represent distinct states alongside data-carrying types:

```vole
sentinel NotFound
sentinel Timeout

func lookup(key: string) -> i64 | NotFound {
    if key == "x" {
        return 42
    }
    return NotFound
}

tests {
    test "sentinel in union return" {
        let result = lookup("x")
        assert(result is i64)

        let missing = lookup("y")
        assert(missing is NotFound)
    }
}
```

Multiple sentinels can appear in the same union:

```vole
sentinel NotFound
sentinel Timeout

func classify(x: i64 | Timeout | NotFound) -> string {
    return match x {
        i64 => "value"
        Timeout => "timeout"
        NotFound => "not_found"
    }
}

tests {
    test "multiple sentinels in union" {
        assert(classify(42) == "value")
        assert(classify(Timeout) == "timeout")
        assert(classify(NotFound) == "not_found")
    }
}
```

## Pattern Matching

### Match Expressions

Sentinels work naturally in `match` expressions for exhaustive handling:

```vole
sentinel Ready
sentinel Waiting
sentinel Closed

tests {
    test "match on sentinel union" {
        let state: Ready | Waiting | Closed = Waiting
        let result = match state {
            Ready => "ready"
            Waiting => "waiting"
            Closed => "closed"
        }
        assert(result == "waiting")
    }
}
```

### The `is` Operator

Use `is` to check whether a union value holds a specific sentinel:

```vole
sentinel Timeout

tests {
    test "is check with sentinel" {
        let x: i64 | Timeout = Timeout
        assert(x is Timeout)
        assert(!(x is i64))

        let y: i64 | Timeout = 42
        assert(y is i64)
        assert(!(y is Timeout))
    }
}
```

### Type Narrowing in `if`

After an `is` check, the variable is narrowed in the branch body:

```vole
sentinel Timeout

tests {
    test "narrowing after is check" {
        let x: i64 | Timeout = 42
        if x is Timeout {
            assert(false)
        } else {
            let n = x + 1
            assert(n == 43)
        }
    }
}
```

### When Expressions

Sentinels work with `when` expressions using `is` checks:

```vole
sentinel Timeout
sentinel NotFound

tests {
    test "when with sentinel is checks" {
        let x: i64 | Timeout | NotFound = NotFound
        let result = when {
            x is i64 => "number"
            x is Timeout => "timeout"
            x is NotFound => "not_found"
            _ => "unknown"
        }
        assert(result == "not_found")
    }
}
```

## Common Patterns

### Result-like Return Types

Use sentinels to create lightweight result types without defining full error classes:

```vole
sentinel NotFound
sentinel Timeout

func fetch(key: string) -> string | NotFound | Timeout {
    if key == "" {
        return Timeout
    }
    if key == "missing" {
        return NotFound
    }
    return "value_for_" + key
}

tests {
    test "result-like pattern" {
        let result = fetch("hello")
        let msg = match result {
            string => "ok"
            NotFound => "missing"
            Timeout => "timed out"
        }
        assert(msg == "ok")

        assert(fetch("missing") is NotFound)
        assert(fetch("") is Timeout)
    }
}
```

### State Machines

Model state transitions with sentinel-only unions:

```vole
sentinel Ready
sentinel Waiting
sentinel Closed

tests {
    test "state machine" {
        let s: Ready | Waiting | Closed = Waiting
        let next = match s {
            Waiting => Ready
            Ready => Closed
            Closed => Closed
        }
        assert(next is Ready)
    }
}
```

### Iterator Protocol

The built-in `Done` sentinel is used by the iterator protocol. Iterators return `T | Done` from their `next()` method:

```vole
tests {
    test "Done in iterator context" {
        let x: i64 | Done = Done
        let result = match x {
            i64 => "has value"
            Done => "exhausted"
        }
        assert(result == "exhausted")
    }
}
```

---

## See Also

- [Types](types.md) - Full type system documentation
- [Control Flow](control-flow.md) - Match expressions and when
- [Iterators](iterators.md) - Iterator protocol using Done
