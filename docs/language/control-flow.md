# Control Flow

Vole provides conditionals, loops, and pattern matching for controlling program execution.

## Quick Reference

```vole,ignore
if cond { }                          // Conditional
if cond { } else { }                 // Conditional with else
while cond { }                       // While loop
for x in collection { }              // For-in loop over iterable
for i in 0..10 { }                   // Range loop (exclusive end)
for i in 0..=10 { }                 // Range loop (inclusive end)
match expr { pat => val }            // Pattern matching
when { cond => val, _ => default }   // Conditional expression
break                                // Exit loop
continue                             // Skip to next iteration
```

## In Depth

### if/else

`if` is a **statement** in Vole -- it cannot be used as an expression. To get conditional values, use `when` or `match`.

Basic conditional:

```vole
tests {
    test "basic if" {
        var x = 0
        if true { x = 1 }
        assert(x == 1)
    }
}
```

With else:

```vole
tests {
    test "if else" {
        var x = 0
        if false { x = 1 } else { x = 2 }
        assert(x == 2)
    }
}
```

Else-if chains:

```vole
tests {
    test "else-if chain" {
        let score = 85
        var grade = ""
        if score >= 90 {
            grade = "A"
        } else if score >= 80 {
            grade = "B"
        } else if score >= 70 {
            grade = "C"
        } else {
            grade = "F"
        }
        assert(grade == "B")
    }
}
```

### Conditional Expressions with `when`

Since `if` is statement-only, use `when` for conditional values:

```vole
tests {
    test "when instead of if expression" {
        let x = 10
        let sign = when { x > 0 => "positive", _ => "non-positive" }
        assert(sign == "positive")
    }
}
```

See the [when Expressions](#when-expressions) section below for full details.

### while Loops

Execute while a condition is true:

```vole
tests {
    test "simple while" {
        var i = 0
        var sum = 0
        while i < 5 {
            sum = sum + i
            i = i + 1
        }
        assert(sum == 10)
    }
}
```

Infinite loop (break to exit):

```vole
tests {
    test "while true with break" {
        var count = 0
        while true {
            count = count + 1
            if count >= 10 {
                break
            }
        }
        assert(count == 10)
    }
}
```

### for-in Loops

Iterate over arrays:

```vole
tests {
    test "for over array" {
        let arr = [10, 20, 30]
        var sum = 0
        for x in arr {
            sum = sum + x
        }
        assert(sum == 60)
    }
}
```

### Range Expressions

Exclusive range with `..` (end not included):

```vole
tests {
    test "exclusive range" {
        var sum = 0
        for i in 0..5 {
            sum = sum + i
        }
        assert(sum == 10)
    }
}
```

Inclusive range with `..=` (end included):

```vole
tests {
    test "inclusive range" {
        var total = 0
        for i in 1..=10 {
            total = total + i
        }
        assert(total == 55)
    }
}
```

Ranges can start at any value:

```vole
tests {
    test "range with offset" {
        var sum = 0
        for i in 5..8 {
            sum = sum + i
        }
        assert(sum == 18)
    }
}
```

### break

Exit a loop early:

```vole
tests {
    test "break in for loop" {
        var sum = 0
        for i in 0..100 {
            if i >= 5 {
                break
            }
            sum = sum + i
        }
        assert(sum == 10)
    }
}
```

With while:

```vole
tests {
    test "break in while loop" {
        var i = 0
        while true {
            if i >= 5 {
                break
            }
            i = i + 1
        }
        assert(i == 5)
    }
}
```

### continue

Skip to the next iteration:

```vole
tests {
    test "continue skips even numbers" {
        var sum = 0
        for i in 0..10 {
            if i % 2 == 0 {
                continue
            }
            sum = sum + i
        }
        assert(sum == 25)
    }
}
```

### break and continue Together

```vole
tests {
    test "break and continue in same loop" {
        var sum = 0
        var i = 0
        while i < 20 {
            i = i + 1
            if i % 2 == 0 {
                continue
            }
            if i > 10 {
                break
            }
            sum = sum + i
        }
        assert(sum == 25)
    }
}
```

### Nested Loops

`break` and `continue` apply to the innermost loop:

```vole
tests {
    test "break in nested loops - inner only" {
        var count = 0
        for i in 0..3 {
            for j in 0..10 {
                if j >= 2 {
                    break
                }
                count = count + 1
            }
        }
        assert(count == 6)
    }
}
```

### match Expressions

`match` compares a value against patterns and returns a result.

#### Literal Patterns

```vole
tests {
    test "match integer literals" {
        let x = 2
        let result = match x {
            1 => 100
            2 => 200
            3 => 300
            _ => 0
        }
        assert(result == 200)
    }
}
```

The `_` pattern matches anything (wildcard).

#### Negative Literals

```vole
tests {
    test "match negative integers" {
        let x = -5
        let result = match x {
            -10 => 1
            -5 => 2
            0 => 3
            _ => 4
        }
        assert(result == 2)
    }
}
```

#### Matching on Expressions

```vole
tests {
    test "match on expression" {
        let a = 2
        let b = 3
        let result = match a + b {
            5 => 100
            _ => 0
        }
        assert(result == 100)
    }
}
```

#### Identifier Binding Patterns

An identifier pattern binds the matched value to a new variable:

```vole
tests {
    test "identifier binding pattern" {
        let x = 7
        let result = match x {
            0 => 0
            n => n + n
        }
        assert(result == 14)
    }
}
```

#### String Literal Patterns

```vole
tests {
    test "match string literals" {
        let check = (s: string) -> string => match s {
            "hello" => "greeting"
            other => "got: {other}"
        }
        assert(check("hello") == "greeting")
        assert(check("world") == "got: world")
    }
}
```

#### val Patterns (Value Comparison)

By default, an identifier in a match arm creates a new binding. Use `val` to compare against an existing variable instead:

```vole
tests {
    test "val pattern compares against variable" {
        let MAGIC = 42
        let x = 42
        let result = match x {
            val MAGIC => "magic"
            _ => "other"
        }
        assert(result == "magic")
    }

    test "identifier binds, val compares" {
        let target = 999
        let x = 5

        // val pattern compares - doesn't match since 5 != 999
        let result = match x {
            val target => "matched target"
            other => "got {other}"
        }
        assert(result == "got 5")
    }
}
```

#### Match with Guards

Use `if` guards for conditional matching:

```vole
tests {
    test "match with guards" {
        let score = 85
        let grade = match score {
            _ if score >= 90 => 1
            _ if score >= 80 => 2
            _ if score >= 70 => 3
            _ => 4
        }
        assert(grade == 2)
    }

    test "identifier guard with binding" {
        let x = 15
        let result = match x {
            n if n > 10 => n * 2
            n => n
        }
        assert(result == 30)
    }
}
```

#### Matching Union Types

Match is useful with union types and classes:

```vole
class Cat { name: string }
class Dog { name: string }

tests {
    test "match on class union type" {
        let animal: Cat | Dog = Cat { name: "Whiskers" }
        let result = match animal {
            Cat { name } => name
            Dog { name } => name
        }
        assert(result == "Whiskers")
    }

    test "match class without destructuring" {
        let animal: Cat | Dog = Dog { name: "Rex" }
        let step = match animal {
            Cat => 1
            Dog => 2
        }
        assert(step == 2)
    }
}
```

#### Nested Match

```vole
tests {
    test "nested match" {
        let x = 1
        let y = 2
        let result = match x {
            1 => match y {
                2 => 12
                _ => 10
            }
            _ => 0
        }
        assert(result == 12)
    }
}
```

#### Matching Fallible Results

Match is used to handle results from fallible functions:

```vole
error DivByZero {}

func divide(a: i64, b: i64) -> fallible(i64, DivByZero) {
    if b == 0 {
        raise DivByZero {}
    }
    return a / b
}

tests {
    test "match success and error" {
        let result = match divide(10, 2) {
            success x => x
            error => -999
            _ => -888
        }
        assert(result == 5)
    }

    test "match catches error" {
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

### when Expressions

`when` is a subject-less conditional expression for evaluating a chain of conditions. Unlike `match` which compares a value against patterns, `when` evaluates boolean conditions in order.

**Terse single-line form** (arms separated by commas):

```vole
func abs(x: i64) -> i64 => when { x < 0 => -x, _ => x }
func sign(x: i64) -> i64 => when { x > 0 => 1, x < 0 => -1, _ => 0 }

tests {
    test "terse when" {
        assert(abs(-5) == 5)
        assert(abs(5) == 5)
        assert(sign(10) == 1)
        assert(sign(-10) == -1)
        assert(sign(0) == 0)
    }
}
```

**Multi-line form** (arms separated by newlines):

```vole
func classify_age(age: i64) -> string {
    return when {
        age < 0 => "invalid"
        age < 13 => "child"
        age < 20 => "teenager"
        age < 65 => "adult"
        _ => "senior"
    }
}

tests {
    test "multiline when" {
        assert(classify_age(-1) == "invalid")
        assert(classify_age(5) == "child")
        assert(classify_age(15) == "teenager")
        assert(classify_age(30) == "adult")
        assert(classify_age(70) == "senior")
    }
}
```

**Mixed form** (commas and newlines, trailing comma allowed):

```vole
func clamp(x: i64, lo: i64, hi: i64) -> i64 => when {
    x < lo => lo,
    x > hi => hi,
    _ => x,
}

tests {
    test "trailing comma when" {
        assert(clamp(5, 0, 10) == 5)
        assert(clamp(-5, 0, 10) == 0)
        assert(clamp(15, 0, 10) == 10)
    }
}
```

The `_` arm is required and must be last (exhaustiveness).

**Nested when expressions:**

```vole
func day_type(day: i64) -> string {
    return when {
        day == 0 || day == 6 => "weekend"
        _ => when {
            day == 5 => "TGIF"
            _ => "weekday"
        }
    }
}

tests {
    test "nested when" {
        assert(day_type(0) == "weekend")
        assert(day_type(5) == "TGIF")
        assert(day_type(3) == "weekday")
    }
}
```

### when vs match

| Feature | `when` | `match` |
|---------|--------|---------|
| Has subject | No | Yes |
| Conditions | Boolean expressions | Patterns |
| Use case | Condition chains | Value matching |

```vole
tests {
    test "when vs match" {
        let score = 95
        let value = 1

        // when: evaluate conditions
        let grade = when { score >= 90 => "A", _ => "other" }

        // match: match a value against patterns
        let name = match value { 1 => "one", _ => "other" }

        assert(grade == "A")
        assert(name == "one")
    }
}
```

### Nested Control Flow

Control structures can be nested:

```vole
tests {
    test "nested control flow" {
        var count = 0
        for i in 0..4 {
            if i % 2 == 0 {
                for j in 0..i {
                    count = count + 1
                }
            }
        }
        assert(count == 2)
    }
}
```

### Common Patterns

**Find first match:**

```vole
tests {
    test "find first match" {
        let nums = [1, 2, 3, 4, 5]
        var found = -1
        for n in nums {
            if n > 3 {
                found = n
                break
            }
        }
        assert(found == 4)
    }
}
```

**Count occurrences:**

```vole
tests {
    test "count occurrences" {
        let nums = [1, 2, 1, 3, 1]
        var count = 0
        for n in nums {
            if n == 1 {
                count = count + 1
            }
        }
        assert(count == 3)
    }
}
```

**Accumulate values:**

```vole
tests {
    test "accumulate" {
        let nums = [1, 2, 3, 4, 5]
        var sum = 0
        for n in nums {
            sum = sum + n
        }
        assert(sum == 15)
    }
}
```

**Exhaustive returns in functions:**

```vole
func sign(x: i64) -> i64 {
    if x > 0 {
        return 1
    } else if x < 0 {
        return -1
    } else {
        return 0
    }
}

tests {
    test "exhaustive returns" {
        assert(sign(5) == 1)
        assert(sign(-5) == -1)
        assert(sign(0) == 0)
    }
}
```

Functions with exhaustive if/else returning in all branches do not need a trailing return statement.

**Logical operators in conditions:**

```vole
tests {
    test "logical operators in conditions" {
        let x = 5
        let y = 10
        var result = false
        if x > 0 && y > 0 {
            result = true
        }
        assert(result == true)

        var either = false
        if x > 100 || y > 0 {
            either = true
        }
        assert(either == true)
    }
}
```
