# Control Flow

Vole provides conditionals, loops, and pattern matching for controlling program execution.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `if cond { }` | Conditional |
| `if cond { } else { }` | Conditional with else |
| `while cond { }` | While loop |
| `for x in collection { }` | For-in loop over iterable |
| `for i in 0..10 { }` | Range loop (exclusive end) |
| `for i in 0..=10 { }` | Range loop (inclusive end) |
| `match expr { pat => val }` | Pattern matching |
| `when { cond => val, _ => default }` | Conditional expression |
| `break` | Exit loop |
| `continue` | Skip to next iteration |

## In Depth

### if/else

Basic conditional:

```vole
if x > 0 {
    println("positive")
}
```

With else:

```vole
if x > 0 {
    println("positive")
} else {
    println("not positive")
}
```

Else-if chains:

```vole
if x > 0 {
    println("positive")
} else if x < 0 {
    println("negative")
} else {
    println("zero")
}
```

### if as Expression

`if` can be used as an expression that returns a value:

```vole
let sign = if x > 0 {
    "positive"
} else if x < 0 {
    "negative"
} else {
    "zero"
}
```

Both branches must return the same type:

```vole
let abs = if x < 0 { -x } else { x }
```

### while Loops

Execute while a condition is true:

```vole
let mut i = 0
while i < 5 {
    println(i)
    i = i + 1
}
```

Infinite loop (break to exit):

```vole
let mut count = 0
while true {
    count = count + 1
    if count >= 10 {
        break
    }
}
```

### for-in Loops

Iterate over arrays:

```vole
let names = ["Alice", "Bob", "Charlie"]
for name in names {
    println(name)
}
```

### Range Expressions

Exclusive range with `..` (end not included):

```vole
for i in 0..5 {
    println(i)  // 0, 1, 2, 3, 4
}
```

Inclusive range with `..=` (end included):

```vole
for i in 0..=5 {
    println(i)  // 0, 1, 2, 3, 4, 5
}
```

Ranges can start at any value:

```vole
for i in 5..10 {
    println(i)  // 5, 6, 7, 8, 9
}
```

### break

Exit a loop early:

```vole
for i in 0..100 {
    if i == 5 {
        break
    }
    println(i)  // 0, 1, 2, 3, 4
}
```

With while:

```vole
let mut i = 0
while true {
    if i >= 5 {
        break
    }
    println(i)
    i = i + 1
}
```

### continue

Skip to the next iteration:

```vole
for i in 0..10 {
    if i % 2 == 0 {
        continue
    }
    println(i)  // 1, 3, 5, 7, 9
}
```

### match Expressions

Match against patterns:

```vole
let x = 2
let name = match x {
    1 => "one"
    2 => "two"
    3 => "three"
    _ => "other"
}
```

The `_` pattern matches anything (wildcard).

### Matching Types

Match is especially useful with union types:

```vole
let value: i32 | string = get_value()

let result = match value {
    i32 => "got a number"
    string => "got a string"
}
```

Type narrowing in match arms:

```vole
let value: i32 | string | nil = get_value()

match value {
    i32 => println(value + 10)      // value is i32 here
    string => println(value.length) // value is string here
    nil => println("nothing")
}
```

### Destructuring in Match

Match can destructure records and classes:

```vole
record Point { x: i32, y: i32 }

let p = Point { x: 10, y: 20 }
match p {
    Point { x, y } => println("x={x}, y={y}")
}
```

### Exhaustive Matching

Match must cover all possibilities:

```vole
let x: i32 | string = get_value()

// Error: non-exhaustive match
let result = match x {
    i32 => "number"
    // missing string case!
}
```

Use `_` to catch remaining cases:

```vole
let result = match x {
    i32 => "number"
    _ => "something else"  // covers string
}
```

### Match with Guards

Use `if` guards for conditional matching:

```vole
let score = 85
let grade = match score {
    _ if score >= 90 => "A"
    _ if score >= 80 => "B"
    _ if score >= 70 => "C"
    _ => "F"
}
```

### when Expressions

`when` is a subject-less conditional expression for evaluating a chain of conditions:

```vole
let grade = when {
    score >= 90 => "A"
    score >= 80 => "B"
    score >= 70 => "C"
    _ => "F"
}
```

Unlike `match` which compares a value against patterns, `when` evaluates boolean conditions in order.

**Terse single-line form** (arms separated by commas):

```vole
let abs = when { x < 0 => -x, _ => x }
let sign = when { x > 0 => 1, x < 0 => -1, _ => 0 }
```

**Multi-line form** (arms separated by newlines):

```vole
let category = when {
    age < 13 => "child"
    age < 20 => "teenager"
    age < 65 => "adult"
    _ => "senior"
}
```

**Mixed form** (commas and newlines, trailing comma allowed):

```vole
let result = when {
    x < 0 => "negative",
    x == 0 => "zero",
    _ => "positive",
}
```

The `_` arm is required and must be last (exhaustiveness).

### when vs match

| Feature | `when` | `match` |
|---------|--------|---------|
| Has subject | No | Yes |
| Conditions | Boolean expressions | Patterns |
| Use case | Condition chains | Value matching |

```vole
// when: evaluate conditions
let grade = when { score >= 90 => "A", _ => "other" }

// match: match a value against patterns
let name = match value { 1 => "one", _ => "other" }
```

### Nested Control Flow

Control structures can be nested:

```vole
for i in 0..10 {
    if i % 2 == 0 {
        for j in 0..i {
            println(j)
        }
    }
}
```

### Common Patterns

**Find first match:**

```vole
let nums = [1, 2, 3, 4, 5]
let mut found = -1
for n in nums {
    if n > 3 {
        found = n
        break
    }
}
```

**Count occurrences:**

```vole
let nums = [1, 2, 1, 3, 1]
let mut count = 0
for n in nums {
    if n == 1 {
        count = count + 1
    }
}
```

**Accumulate values:**

```vole
let nums = [1, 2, 3, 4, 5]
let mut sum = 0
for n in nums {
    sum = sum + n
}
```

**Transform with condition:**

```vole
let nums = [1, 2, 3, 4, 5]
let evens = nums.filter((x) => x % 2 == 0).collect()
```
