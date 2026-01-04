# Iterators

Iterators provide lazy, composable operations over sequences. Most iterator operations are lazy - they don't execute until consumed.

## Quick Reference

| Method | Description |
|--------|-------------|
| `.map(fn)` | Transform each element |
| `.filter(fn)` | Keep elements matching predicate |
| `.take(n)` | Take first n elements |
| `.skip(n)` | Skip first n elements |
| `.reduce(init, fn)` | Fold to single value |
| `.sum()` | Sum numeric elements |
| `.count()` | Count elements |
| `.collect()` | Materialize to array |

## In Depth

### Creating Iterators

Arrays support iterator methods directly:

```vole
let nums = [1, 2, 3, 4, 5]
let doubled = nums.map((x) => x * 2).collect()
```

For-in loops work directly on arrays:

```vole
for x in [1, 2, 3] {
    println(x)
}
```

### map

Transform each element:

```vole
let nums = [1, 2, 3, 4, 5]
let doubled = nums.map((x) => x * 2).collect()
// [2, 4, 6, 8, 10]
```

Change types:

```vole
let nums = [1, 2, 3]
let strings = nums.map((x) => "Number: {x}").collect()
// ["Number: 1", "Number: 2", "Number: 3"]
```

### filter

Keep elements matching a predicate:

```vole
let nums = [1, 2, 3, 4, 5, 6]
let evens = nums.filter((x) => x % 2 == 0).collect()
// [2, 4, 6]
```

```vole
let words = ["apple", "pie", "application"]
let long_words = words.filter((w) => w.length > 3).collect()
// ["apple", "application"]
```

### Chaining Operations

Iterator methods return iterators, enabling chains:

```vole
let nums = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

let result = nums
    .filter((x) => x % 2 == 0)  // [2, 4, 6, 8, 10]
    .map((x) => x * x)          // [4, 16, 36, 64, 100]
    .take(3)                    // [4, 16, 36]
    .collect()

println(result)  // [4, 16, 36]
```

### Lazy Evaluation

Iterator operations are lazy - nothing happens until consumption:

```vole
let nums = [1, 2, 3, 4, 5]

// This doesn't execute the map yet
let doubled = nums.map((x) => {
    println("Processing {x}")
    return x * 2
})

// Now it executes
let result = doubled.collect()
```

Benefits:
- Memory efficient for large datasets
- Only compute what's needed

### take and skip

Take first n elements:

```vole
let nums = [1, 2, 3, 4, 5]
let first_three = nums.take(3).collect()  // [1, 2, 3]
```

Skip first n elements:

```vole
let nums = [1, 2, 3, 4, 5]
let rest = nums.skip(2).collect()  // [3, 4, 5]
```

Pagination pattern:

```vole
let page_size = 10
let page = 2
let items = all_items.skip(page * page_size).take(page_size).collect()
```

### reduce

Fold elements into a single value:

```vole
let nums = [1, 2, 3, 4, 5]
let sum = nums.reduce(0, (acc, x) => acc + x)
// 15
```

The first argument is the initial accumulator value:

```vole
let nums = [1, 2, 3, 4]
let product = nums.reduce(1, (acc, x) => acc * x)
// 24
```

Build a string:

```vole
let words = ["Hello", "World"]
let sentence = words.reduce("", (acc, w) => {
    if acc == "" {
        return w
    } else {
        return acc + " " + w
    }
})
// "Hello World"
```

### sum

Sum numeric elements:

```vole
let nums = [1, 2, 3, 4, 5]
let total = nums.sum()  // 15
```

With transformation:

```vole
record Item { price: i32 }

let items = [Item { price: 10 }, Item { price: 20 }]
let total = items.map((i) => i.price).sum()  // 30
```

### count

Count elements:

```vole
let nums = [1, 2, 3, 4, 5]
let n = nums.count()  // 5
```

Count matching elements:

```vole
let nums = [1, 2, 3, 4, 5, 6]
let even_count = nums.filter((x) => x % 2 == 0).count()  // 3
```

### collect

Materialize a lazy iterator into an array:

```vole
let nums = [1, 2, 3, 4, 5]
let doubled = nums.map((x) => x * 2).collect()
// doubled is [2, 4, 6, 8, 10]
```

Always call `.collect()` when you need the actual array.

### Common Patterns

**Find first match:**

```vole
let nums = [1, 2, 3, 4, 5]
let first_even = nums.filter((x) => x % 2 == 0).take(1).collect()
// [2]
```

**Check if any match:**

```vole
let nums = [1, 3, 5, 7, 8]
let has_even = nums.filter((x) => x % 2 == 0).count() > 0
// true
```

**Check if all match:**

```vole
let nums = [2, 4, 6, 8]
let all_even = nums.filter((x) => x % 2 != 0).count() == 0
// true
```

**Transform and filter:**

```vole
record User { active: bool, email: string }

let users = get_users()
let active_emails = users
    .filter((u) => u.active)
    .map((u) => u.email)
    .collect()
```

**Flatten nested structure:**

```vole
let groups = [[1, 2], [3, 4], [5, 6]]
let flat = groups.reduce([], (acc, g) => acc + g)
// [1, 2, 3, 4, 5, 6]
```

### Performance Considerations

- Chained operations don't create intermediate arrays
- `.collect()` allocates a new array
- Use `.count()` instead of `.collect().length`
