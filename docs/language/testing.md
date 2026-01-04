# Testing

Vole has built-in testing support with `test` blocks and assertions.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `test "name" { }` | Define a test |
| `tests { }` | Group multiple tests |
| `tests "name" { }` | Named test group |
| `assert(condition)` | Assert condition is true |

**Running tests:**
```bash
vole test test/unit
```

## In Depth

### Test Blocks

Define tests with the `test` keyword:

```vole
test "addition works" {
    assert(1 + 1 == 2)
}

test "string concatenation" {
    let result = "Hello" + " " + "World"
    assert(result == "Hello World")
}
```

Tests are collected and run by the test runner.

### Assertions

Use `assert()` to verify conditions:

```vole
test "assertions" {
    assert(true)
    assert(1 < 2)
    assert("hello".length == 5)

    let x = 42
    assert(x == 42)
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
    test "addition" {
        assert(2 + 2 == 4)
    }

    test "subtraction" {
        assert(5 - 3 == 2)
    }

    test "multiplication" {
        assert(3 * 4 == 12)
    }
}

tests "String operations" {
    test "length" {
        assert("hello".length == 5)
    }

    test "concatenation" {
        assert("a" + "b" == "ab")
    }
}
```

### Running Unit Tests

Run tests with the `test` command:

```bash
# Run all tests in a directory
vole test test/unit

# Run tests in a specific file
vole test test/unit/math.vole

# Run tests matching a pattern
vole test test/unit/*.vole
```

### Test File Structure

A typical test file:

```vole
// test/unit/calculator.vole

// Define or use the functions being tested
func add(a: i32, b: i32) -> i32 {
    return a + b
}

tests "Calculator" {
    test "add positive numbers" {
        assert(add(2, 3) == 5)
    }

    test "add negative numbers" {
        assert(add(-1, -1) == -2)
    }

    test "add mixed" {
        assert(add(-5, 10) == 5)
    }
}
```

### Testing Patterns

**Test one thing per test:**

```vole
// Good
test "array length" {
    assert([1, 2, 3].length == 3)
}

test "empty array length" {
    let empty: [i32] = []
    assert(empty.length == 0)
}

// Avoid
test "array stuff" {
    assert([1, 2, 3].length == 3)
    assert([].length == 0)  // Multiple concerns
    assert([1] + [2] == [1, 2])
}
```

**Descriptive test names:**

```vole
// Good
test "filter removes non-matching elements" { }
test "map preserves array length" { }
test "reduce with empty array returns initial value" { }

// Avoid
test "filter test" { }
test "test1" { }
test "it works" { }
```

**Arrange-Act-Assert pattern:**

```vole
test "user can be created with valid data" {
    // Arrange
    let name = "Alice"
    let age = 30

    // Act
    let user = User { name: name, age: age }

    // Assert
    assert(user.name == "Alice")
    assert(user.age == 30)
}
```

### Testing Edge Cases

```vole
tests "Division" {
    test "positive numbers" {
        assert(10 / 2 == 5)
    }

    test "result truncates" {
        assert(7 / 2 == 3)
    }

    test "negative dividend" {
        assert(-10 / 2 == -5)
    }

    test "negative divisor" {
        assert(10 / -2 == -5)
    }

    test "both negative" {
        assert(-10 / -2 == 5)
    }
}
```

### Testing Error Handling

Test that errors are raised correctly:

```vole
error DivByZero {}

func divide(a: i32, b: i32) -> fallible(i32, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests "divide function" {
    test "divides correctly" {
        let result = try divide(10, 2) catch {
            DivByZero {} => -1
        }
        assert(result == 5)
    }

    test "raises on zero divisor" {
        let result = try divide(10, 0) catch {
            DivByZero {} => -999
        }
        assert(result == -999)
    }
}
```

### Testing with Setup

Share setup across tests:

```vole
record User {
    name: string
    age: i32
    active: bool
}

func make_test_user() -> User {
    return User {
        name: "Test User",
        age: 25,
        active: true
    }
}

tests "User operations" {
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
        let doubled = nums.map((x) => x * 2).collect()
        assert(doubled[0] == 2)
        assert(doubled[1] == 4)
        assert(doubled[2] == 6)
    }

    test "filter selects matching" {
        let nums = [1, 2, 3, 4, 5]
        let evens = nums.filter((x) => x % 2 == 0).collect()
        assert(evens.length == 2)
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

### Test Organization

Recommended directory structure:

```
test/
└── unit/           # Unit tests using assert()
    ├── language/   # Language feature tests
    ├── types/      # Type system tests
    └── ...
```

### Best Practices

1. **Keep tests fast** - Avoid slow operations in tests
2. **Test behavior, not implementation** - Focus on what, not how
3. **One assertion focus per test** - Even if multiple asserts
4. **Use descriptive names** - Test name should explain the scenario
5. **Test edge cases** - Empty, zero, negative, boundary values
6. **Don't test the language** - Test your code, not Vole itself
