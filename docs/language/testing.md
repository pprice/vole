# Testing

Vole has built-in testing support with `test` blocks and assertions.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `test "name" { }` | Define a test with block body |
| `test "name" => expr` | Define a test with expression body |
| `tests { }` | Group multiple tests |
| `tests "name" { }` | Named test group |
| `func name() => ...` | Scoped helper function (inside tests block) |
| `let name = ...` | Scoped constant (inside tests block) |
| `assert(condition)` | Assert condition is true |

**Running tests:**
```bash
vole test path/to/tests
```

## In Depth

### Test Blocks

Define tests with the `test` keyword:

```vole
tests {
    test "addition works" {
        assert(1 + 1 == 2)
    }

    test "string concatenation" {
        let result = "Hello" + " " + "World"
        assert(result == "Hello World")
    }
}
```

Tests are collected and run by the test runner.

### Expression Tests

For simple single-assertion tests, use expression syntax:

```vole
tests {
    test "addition works" => assert(1 + 1 == 2)
    test "comparison" => assert(10 > 5)
    test "string length" => assert("hello".length() == 5)
}
```

Use block syntax when you need multiple statements or local variables:

```vole
tests {
    test "complex setup" {
        let a = 10
        let b = 20
        assert(a + b == 30)
    }
}
```

### Assertions

Use `assert()` to verify conditions:

```vole
tests {
    test "assertions" {
        assert(true)
        assert(1 < 2)
        assert("hello".length() == 5)

        let x = 42
        assert(x == 42)
    }
}
```

When an assertion fails, the test fails with an error message.

### Test Groups

Group related tests with `tests`:

```vole
tests {
    test "first" {
        assert(true)
    }

    test "second" {
        assert(1 + 1 == 2)
    }
}
```

Named groups for organization:

```vole
tests "Math operations" {
    test "addition" => assert(2 + 2 == 4)
    test "subtraction" => assert(5 - 3 == 2)
    test "multiplication" => assert(3 * 4 == 12)
}

tests "String operations" {
    test "length" => assert("hello".length() == 5)
    test "concatenation" => assert("a" + "b" == "ab")
}
```

### Scoped Declarations

Define helper functions and constants scoped to a tests block:

```vole
tests "Math helpers" {
    func double(x: i64) -> i64 => x * 2

    let FACTOR = 10

    test "double works" => assert(double(21) == 42)
    test "use constant" => assert(double(FACTOR) == 20)
}
```

Declarations must appear before test cases. Scoped declarations are only visible within their tests block.

For helpers shared across multiple tests blocks, keep them at module level:

```vole
func shared_helper(x: i64) -> i64 => x + 1

tests "first group" {
    test "uses shared" => assert(shared_helper(1) == 2)
}

tests "second group" {
    test "also uses shared" => assert(shared_helper(10) == 11)
}
```

### Imports in Tests Blocks

You can import modules inside tests blocks:

```vole
tests "using math" {
    let math = import "std:math"

    test "sqrt works" {
        assert(math.sqrt(16.0) == 4.0)
    }
}

tests "destructured import" {
    let { sqrt, min, max } = import "std:math"

    test "imported functions work" {
        assert(sqrt(25.0) == 5.0)
        assert(min(1.0, 2.0) == 1.0)
    }
}
```

### Running Unit Tests

Run tests with the `test` command:

```bash
# Run all tests in a directory
vole test path/to/tests/

# Run tests in a specific file
vole test path/to/tests/math.vole

# Run tests matching a pattern
vole test path/to/tests/*.vole
```

### Test File Structure

A typical test file with scoped helpers:

```vole
tests "Calculator" {
    func add(a: i64, b: i64) -> i64 => a + b

    test "add positive numbers" => assert(add(2, 3) == 5)
    test "add negative numbers" => assert(add(-1, -1) == -2)
    test "add mixed" => assert(add(-5, 10) == 5)
}
```

Or with module-level functions when testing imported code:

```vole
let math = import "std:math"

tests "math module" {
    test "sqrt" => assert(math.sqrt(4.0) == 2.0)
    test "abs" => assert(math.abs(-5.0) == 5.0)
}
```

### Testing Patterns

**Test one thing per test:**

```vole
tests {
    test "array length" {
        assert([1, 2, 3].length() == 3)
    }

    test "empty array length" {
        let empty: [i64] = []
        assert(empty.length() == 0)
    }
}
```

**Arrange-Act-Assert pattern:**

```vole
class User {
    name: string,
    age: i64,
}

tests {
    test "user can be created with valid data" {
        let name = "Alice"
        let age = 30

        let user = User { name: name, age: age }

        assert(user.name == "Alice")
        assert(user.age == 30)
    }
}
```

### Testing Edge Cases

```vole
tests "Division" {
    test "positive numbers" => assert(10 / 2 == 5)
    test "result truncates" => assert(7 / 2 == 3)
    test "negative dividend" => assert(-10 / 2 == -5)
    test "negative divisor" => assert(10 / -2 == -5)
    test "both negative" => assert(-10 / -2 == 5)
}
```

### Testing Error Handling

Test that errors are raised correctly:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests "divide function" {
    test "divides correctly" {
        let result = match divide(10, 2) {
            x => x
            error DivByZero => -1
        }
        assert(result == 5)
    }

    test "raises on zero divisor" {
        let result = match divide(10, 0) {
            x => x
            error DivByZero => -999
        }
        assert(result == -999)
    }
}
```

### Testing with Setup

Share setup across tests using scoped helpers:

```vole
class User {
    name: string,
    age: i64,
    active: bool,
}

tests "User operations" {
    func make_test_user() -> User {
        return User {
            name: "Test User",
            age: 25,
            active: true,
        }
    }

    test "can get name" {
        let user = make_test_user()
        assert(user.name == "Test User")
    }

    test "can check active status" {
        let user = make_test_user()
        assert(user.active)
    }
}
```

### Testing Iterators

```vole
tests "Iterator operations" {
    test "map transforms elements" {
        let nums = [1, 2, 3]
        let doubled = nums.map(x => x * 2).collect()
        assert(doubled[0] == 2)
        assert(doubled[1] == 4)
        assert(doubled[2] == 6)
    }

    test "filter selects matching" {
        let nums = [1, 2, 3, 4, 5]
        let evens = nums.filter(x => x % 2 == 0).collect()
        assert(evens.length() == 2)
        assert(evens[0] == 2)
        assert(evens[1] == 4)
    }

    test "reduce accumulates" {
        let nums = [1, 2, 3, 4, 5]
        let sum = nums.reduce(0, (acc, x) => acc + x)
        assert(sum == 15)
    }
}
```

### Best Practices

1. **Keep tests fast** -- avoid slow operations in tests
2. **Test behavior, not implementation** -- focus on what, not how
3. **One assertion focus per test** -- even if multiple asserts
4. **Use descriptive names** -- test name should explain the scenario
5. **Test edge cases** -- empty, zero, negative, boundary values
6. **Use expression syntax for simple tests** -- `test "name" => assert(...)`
7. **Scope helpers to tests blocks** -- keep helpers close to where they're used
