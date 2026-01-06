---
name: adding-tests
description: Use when adding unit tests or snapshot tests for Vole features
---

# Adding Tests

## Overview

Vole has two test systems: unit tests (preferred) and snapshot tests.

## Useful Tools

```bash
just dev-test-for <feature>  # Find existing tests for a feature
just unit                    # Run all unit tests
just snap                    # Run all snapshot tests
```

## Test Types

| Type | Location | Use For |
|------|----------|---------|
| Unit tests | `test/unit/` | Features that compile and run correctly |
| Snapshot (check) | `test/snapshot/check/` | Error messages (parse/type errors) |
| Snapshot (run) | `test/snapshot/run/` | Simple smoke tests |

**Prefer unit tests** when code compiles successfully.

## Unit Tests

### Structure

```vole
// test/unit/language/your_feature.vole

// Helper functions if needed
func helper(x: i64) -> i64 {
    return x * 2
}

tests {
    test "descriptive name" {
        assert(helper(2) == 4)
    }

    test "another case" {
        let result = some_operation()
        assert(result == expected)
    }
}
```

### Organization

| Directory | Purpose |
|-----------|---------|
| `test/unit/language/` | Language features (lambdas, control flow, etc.) |
| `test/unit/types/` | Type system tests |
| `test/unit/modules/` | Module system tests |

### Running

```bash
# Run all unit tests
cargo run --bin vole -- test test/unit/

# Run specific file
cargo run --bin vole -- test test/unit/language/lambdas.vole

# Run specific directory
cargo run --bin vole -- test test/unit/types/
```

## Snapshot Tests (Error Messages)

### Structure

Create a `.vole` file that triggers the error:

```vole
// test/snapshot/check/your_error.vole
func bad() {
    let x: i64 = "oops"  // type error
}
```

Create matching `.snap` file:

```
[stdout]

[stderr]
error[E2001]: type mismatch
  --> test/snapshot/check/your_error.vole:3:18
   |
 3 |     let x: i64 = "oops"
   |                  ^^^^^^ expected `i64`, found `string`
```

### Blessing Snapshots

```bash
# Bless a single snapshot
cargo run --bin vole-snap -- bless test/snapshot/check/your_error.vole

# Bless all snapshots in directory
cargo run --bin vole-snap -- bless test/snapshot/check/
```

### Skipping Tests

Prefix filename with `_` to skip: `_work_in_progress.vole`

## Checklist

1. **Decide test type**: Unit (compiles) or snapshot (errors)?

2. **Find related tests**:
   ```bash
   just dev-test-for <feature>
   ```

3. **Create test file** in appropriate directory

4. **Run the test**:
   ```bash
   # Unit test
   cargo run --bin vole -- test test/unit/your_test.vole

   # Snapshot test
   just snap
   ```

5. **Bless snapshot** (if snapshot test):
   ```bash
   cargo run --bin vole-snap -- bless test/snapshot/check/your_test.vole
   ```

6. **Verify all tests pass**:
   ```bash
   just ci
   ```

## Assertions

Available in unit tests:

```vole
assert(condition)           // Basic assertion
assert(a == b)              // Equality
assert(a != b)              // Inequality
assert(a < b)               // Comparison
assert(some_func())         // Function result
```

## Tips

- Keep tests focused - one concept per test
- Use descriptive test names
- Add edge cases (zero, negative, empty, etc.)
- Check Void's tests for reference: `~/code/personal/void/test/`
