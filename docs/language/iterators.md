# Iterators

Iterators provide lazy, composable operations over sequences. Most iterator operations are lazy -- they don't execute until consumed by a terminal operation like `collect()`, `sum()`, or `count()`.

## Quick Reference

| Method | Description |
|--------|-------------|
| `.iter()` | Create an iterator from an array, string, or range |
| `.map(fn)` | Transform each element |
| `.filter(fn)` | Keep elements matching predicate |
| `.flat_map(fn)` | Map then flatten results |
| `.flatten()` | Flatten nested iterators |
| `.take(n)` | Take first n elements |
| `.skip(n)` | Skip first n elements |
| `.chain(iter)` | Concatenate two iterators |
| `.enumerate()` | Yield (index, value) pairs |
| `.zip(iter)` | Combine two iterators into pairs |
| `.chunks(n)` | Group into non-overlapping chunks |
| `.windows(n)` | Sliding windows of size n |
| `.reverse()` | Reverse element order |
| `.sorted()` | Sort elements |
| `.unique()` | Remove consecutive duplicates |
| `.reduce(init, fn)` | Fold to single value |
| `.sum()` | Sum numeric elements |
| `.count()` | Count elements |
| `.collect()` | Materialize to array |
| `.for_each(fn)` | Run function on each element |
| `.find(fn)` | First element matching predicate (or nil) |
| `.first()` | First element (or nil) |
| `.last()` | Last element (or nil) |
| `.nth(n)` | Element at index n (or nil) |
| `.any(fn)` | True if any element matches |
| `.all(fn)` | True if all elements match |

## Factory Functions

| Function | Description |
|----------|-------------|
| `repeat(val)` | Infinite iterator yielding the same value |
| `once(val)` | Iterator that yields a single value |
| `empty()` | Iterator that yields nothing |

## Creating Iterators

Arrays, strings, and ranges all support `.iter()`:

```vole
tests {
    test "array iterator" {
        let arr = [1, 2, 3]
        let iter = arr.iter()
        let collected = iter.collect()
        assert(collected.length() == 3)
    }
}
```

Strings iterate over unicode characters:

```vole
tests {
    test "string iterator" {
        let s = "hello"
        let chars = s.iter().collect()
        assert(chars.length() == 5)
        assert(chars[0] == "h")
        assert(chars[4] == "o")
    }
}
```

Ranges produce integer sequences:

```vole
tests {
    test "range iterator" {
        let result = (0..5).iter().collect()
        assert(result.length() == 5)
        assert(result[0] == 0)
        assert(result[4] == 4)
    }
}
```

Inclusive ranges use `..=`:

```vole
tests {
    test "inclusive range" {
        let result = (0..=4).iter().collect()
        assert(result.length() == 5)
        assert(result[4] == 4)
    }
}
```

For-in loops work directly on arrays, strings, and generators:

```vole
tests {
    test "for in loop" {
        var sum = 0
        for x in [1, 2, 3] {
            sum = sum + x
        }
        assert(sum == 6)
    }
}
```

## Transforming: map

Transform each element:

```vole
tests {
    test "map doubles" {
        let nums = [1, 2, 3, 4, 5]
        let doubled = nums.iter().map((x) => x * 2).collect()
        assert(doubled[0] == 2)
        assert(doubled[4] == 10)
    }
}
```

Closures can capture variables from the enclosing scope:

```vole
tests {
    test "map with capture" {
        let arr = [1, 2, 3]
        let multiplier = 10
        let result = arr.iter().map((x) => x * multiplier).collect()
        assert(result[0] == 10)
        assert(result[1] == 20)
        assert(result[2] == 30)
    }
}
```

## Filtering: filter

Keep elements matching a predicate:

```vole
tests {
    test "filter evens" {
        let nums = [1, 2, 3, 4, 5, 6]
        let evens = nums.iter().filter((x) => x % 2 == 0).collect()
        assert(evens.length() == 3)
        assert(evens[0] == 2)
        assert(evens[1] == 4)
        assert(evens[2] == 6)
    }
}
```

## Chaining Operations

Iterator methods return iterators, enabling chains:

```vole
tests {
    test "filter then map" {
        let nums = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        let result = nums.iter()
            .filter((x) => x % 2 == 0)
            .map((x) => x * x)
            .take(3)
            .collect()
        assert(result[0] == 4)
        assert(result[1] == 16)
        assert(result[2] == 36)
    }
}
```

## take and skip

Take the first n elements:

```vole
tests {
    test "take" {
        let nums = [1, 2, 3, 4, 5]
        let first3 = nums.iter().take(3).collect()
        assert(first3.length() == 3)
        assert(first3[0] == 1)
        assert(first3[2] == 3)
    }
}
```

Skip the first n elements:

```vole
tests {
    test "skip" {
        let nums = [1, 2, 3, 4, 5]
        let rest = nums.iter().skip(2).collect()
        assert(rest.length() == 3)
        assert(rest[0] == 3)
        assert(rest[2] == 5)
    }
}
```

Combine skip and take for pagination:

```vole
tests {
    test "skip then take" {
        let arr = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        let page = arr.iter().skip(3).take(4).collect()
        assert(page.length() == 4)
        assert(page[0] == 4)
        assert(page[3] == 7)
    }
}
```

## reduce

Fold elements into a single value. The first argument is the initial accumulator:

```vole
tests {
    test "reduce sum" {
        let nums = [1, 2, 3, 4, 5]
        let total = nums.iter().reduce(0, (acc, x) => acc + x)
        assert(total == 15)
    }

    test "reduce product" {
        let nums = [1, 2, 3, 4]
        let product = nums.iter().reduce(1, (acc, x) => acc * x)
        assert(product == 24)
    }
}
```

## sum and count

```vole
tests {
    test "sum" {
        let nums = [1, 2, 3, 4, 5]
        assert(nums.iter().sum() == 15)
    }

    test "count" {
        let nums = [1, 2, 3, 4, 5]
        assert(nums.iter().count() == 5)
    }

    test "count with filter" {
        let nums = [1, 2, 3, 4, 5, 6]
        let even_count = nums.iter().filter((x) => x % 2 == 0).count()
        assert(even_count == 3)
    }
}
```

## collect

Materialize a lazy iterator into an array:

```vole
tests {
    test "collect" {
        let nums = [1, 2, 3, 4, 5]
        let doubled = nums.iter().map((x) => x * 2).collect()
        assert(doubled.length() == 5)
        assert(doubled[0] == 2)
        assert(doubled[4] == 10)
    }
}
```

Always call `.collect()` when you need the actual array.

## Search Methods: find, any, all

`find` returns the first matching element (or nil):

```vole
tests {
    test "find" {
        let arr = [1, 2, 3, 4, 5]
        let result = arr.iter().find((x) => x > 3)
        assert(result is i64)
        assert((result ?? 0) == 4)
    }

    test "find returns nil" {
        let arr = [1, 2, 3]
        let result = arr.iter().find((x) => x > 10)
        assert(result is nil)
    }
}
```

`any` checks if at least one element matches:

```vole
tests {
    test "any" {
        let arr = [1, 2, 3, 4, 5]
        assert(arr.iter().any((x) => x > 3))
        assert(!arr.iter().any((x) => x > 10))
    }
}
```

`all` checks if every element matches:

```vole
tests {
    test "all" {
        let arr = [2, 4, 6, 8]
        assert(arr.iter().all((x) => x % 2 == 0))
        assert(!arr.iter().all((x) => x > 5))
    }
}
```

## first, last, nth

```vole
tests {
    test "first and last" {
        let arr = [10, 20, 30]
        let first = arr.iter().first()
        let last = arr.iter().last()
        assert((first ?? 0) == 10)
        assert((last ?? 0) == 30)
    }

    test "nth" {
        let s = "hello"
        let ch = s.iter().nth(2)
        assert(ch is string)
        assert((ch ?? "") == "l")
    }
}
```

## chain

Concatenate two iterators:

```vole
tests {
    test "chain" {
        let a = [1, 2, 3]
        let b = [4, 5, 6]
        let result = a.iter().chain(b.iter()).collect()
        assert(result.length() == 6)
        assert(result[0] == 1)
        assert(result[5] == 6)
    }
}
```

## enumerate

Yield (index, value) pairs as arrays:

```vole
tests {
    test "enumerate" {
        let arr = [10, 20, 30]
        var sum = 0
        for pair in arr.iter().enumerate() {
            sum = sum + pair[0] + pair[1]
        }
        assert(sum == 63)
    }

    test "enumerate with map" {
        let arr = [1, 2, 3]
        let result = arr.iter().enumerate().map((pair) => pair[0] * pair[1]).collect()
        assert(result[0] == 0)
        assert(result[1] == 2)
        assert(result[2] == 6)
    }
}
```

## zip

Combine two iterators into pairs. Stops at the shorter iterator:

```vole
tests {
    test "zip" {
        let a = [1, 2, 3]
        let b = [10, 20, 30]
        var sum = 0
        for pair in a.iter().zip(b.iter()) {
            sum = sum + pair[0] + pair[1]
        }
        assert(sum == 66)
    }

    test "zip with map" {
        let a = [1, 2, 3]
        let b = [10, 20, 30]
        let result = a.iter().zip(b.iter()).map((pair) => pair[0] + pair[1]).collect()
        assert(result[0] == 11)
        assert(result[1] == 22)
        assert(result[2] == 33)
    }

    test "zip stops at shorter" {
        let a = [1, 2, 3, 4, 5]
        let b = [10, 20]
        let zipped = a.iter().zip(b.iter()).collect()
        assert(zipped.length() == 2)
    }
}
```

## flatten and flat_map

Flatten nested arrays:

```vole
tests {
    test "flatten" {
        let nested = [[1, 2], [3, 4]]
        let flat = nested.iter().flatten().collect()
        assert(flat.length() == 4)
        assert(flat[0] == 1)
        assert(flat[3] == 4)
    }
}
```

`flat_map` maps then flattens in one step:

```vole
tests {
    test "flat_map" {
        let arr = [1, 2, 3]
        let result = arr.iter().flat_map((x) => [x, x * 10]).collect()
        assert(result.length() == 6)
        assert(result[0] == 1)
        assert(result[1] == 10)
        assert(result[2] == 2)
        assert(result[3] == 20)
    }
}
```

## chunks and windows

`chunks` groups elements into non-overlapping chunks:

```vole
tests {
    test "chunks" {
        let arr = [1, 2, 3, 4, 5]
        let c = arr.iter().chunks(2).collect()
        assert(c.length() == 3)
        assert(c[0].length() == 2)
        assert(c[0][0] == 1)
        assert(c[0][1] == 2)
        assert(c[2].length() == 1)
        assert(c[2][0] == 5)
    }
}
```

`windows` produces overlapping sliding windows:

```vole
tests {
    test "windows" {
        let arr = [1, 2, 3, 4, 5]
        let w = arr.iter().windows(3).collect()
        assert(w.length() == 3)
        assert(w[0][0] == 1)
        assert(w[0][2] == 3)
        assert(w[1][0] == 2)
        assert(w[2][0] == 3)
        assert(w[2][2] == 5)
    }
}
```

## reverse, sorted, unique

```vole
tests {
    test "reverse" {
        let arr = [1, 2, 3]
        let rev = arr.iter().reverse().collect()
        assert(rev[0] == 3)
        assert(rev[1] == 2)
        assert(rev[2] == 1)
    }

    test "sorted" {
        let arr = [3, 1, 4, 1, 5, 9, 2, 6]
        let s = arr.iter().sorted().collect()
        assert(s[0] == 1)
        assert(s[1] == 1)
        assert(s[2] == 2)
        assert(s[7] == 9)
    }

    test "unique removes consecutive duplicates" {
        let arr = [1, 1, 2, 2, 2, 3, 1]
        let u = arr.iter().unique().collect()
        assert(u.length() == 4)
        assert(u[0] == 1)
        assert(u[1] == 2)
        assert(u[2] == 3)
        assert(u[3] == 1)
    }

    test "sorted then unique for true dedup" {
        let arr = [3, 1, 2, 1, 3, 2]
        let result = arr.iter().sorted().unique().collect()
        assert(result.length() == 3)
        assert(result[0] == 1)
        assert(result[1] == 2)
        assert(result[2] == 3)
    }
}
```

## for_each

Run a function on each element (for side effects):

```vole
tests {
    test "for_each" {
        let arr = [1, 2, 3]
        arr.iter().for_each((x) => { let y = x * 2 })
        assert(true)
    }
}
```

## Factory Functions

`repeat` creates an infinite iterator that yields the same value. Always use with `take`:

```vole
tests {
    test "repeat" {
        let result = repeat(42).take(3).collect()
        assert(result.length() == 3)
        assert(result[0] == 42)
        assert(result[1] == 42)
        assert(result[2] == 42)
    }
}
```

`once` yields a single value:

```vole
tests {
    test "once" {
        let result = once(42).collect()
        assert(result.length() == 1)
        assert(result[0] == 42)
    }
}
```

`empty` yields nothing:

```vole
tests {
    test "empty" {
        let result = empty().collect()
        assert(result.length() == 0)
    }
}
```

These compose well together:

```vole
tests {
    test "chain factory iterators" {
        let result = repeat(1).take(2).chain(once(99)).collect()
        assert(result.length() == 3)
        assert(result[0] == 1)
        assert(result[1] == 1)
        assert(result[2] == 99)
    }
}
```

## Generators

Generator functions use `yield` to produce iterator values lazily:

```vole
func fibonacci() -> Iterator<i64> {
    var a = 0
    var b = 1
    while true {
        yield a
        let next = a + b
        a = b
        b = next
    }
}

tests {
    test "fibonacci generator" {
        let result = fibonacci().take(8).collect()
        assert(result[0] == 0)
        assert(result[1] == 1)
        assert(result[2] == 1)
        assert(result[3] == 2)
        assert(result[4] == 3)
        assert(result[5] == 5)
        assert(result[6] == 8)
        assert(result[7] == 13)
    }
}
```

Generators support `yield` inside loops and conditionals:

```vole
func count_up(n: i64) -> Iterator<i64> {
    var i = 0
    while i < n {
        yield i
        i = i + 1
    }
}

func evens_up_to(n: i64) -> Iterator<i64> {
    var i = 0
    while i < n {
        if i % 2 == 0 {
            yield i
        }
        i = i + 1
    }
}

tests {
    test "yield in while loop" {
        let result = count_up(5).collect()
        assert(result.length() == 5)
        assert(result[0] == 0)
        assert(result[4] == 4)
    }

    test "conditional yield" {
        let result = evens_up_to(10).collect()
        assert(result.length() == 5)
        assert(result[0] == 0)
        assert(result[1] == 2)
        assert(result[4] == 8)
    }
}
```

All iterator methods work with generators:

```vole
func simple_gen() -> Iterator<i64> {
    yield 1
    yield 2
    yield 3
}

tests {
    test "generator with collect" {
        let result = simple_gen().collect()
        assert(result.length() == 3)
        assert(result[0] == 1)
        assert(result[1] == 2)
        assert(result[2] == 3)
    }

    test "generator with map and filter" {
        let result = simple_gen().map((x) => x * 2).filter((x) => x > 2).collect()
        assert(result.length() == 2)
        assert(result[0] == 4)
        assert(result[1] == 6)
    }

    test "generator sum" {
        assert(simple_gen().sum() == 6)
    }
}
```

Generators can also be consumed by for loops:

```vole
func count_to(n: i64) -> Iterator<i64> {
    var i = 0
    while i < n {
        yield i
        i = i + 1
    }
}

tests {
    test "generator in for loop" {
        var sum = 0
        for x in count_to(5) {
            sum = sum + x
        }
        assert(sum == 10)
    }
}
```

## Range Iterators

Ranges work as iterators for computing sequences:

```vole
tests {
    test "range sum" {
        let sum = (1..101).iter().sum()
        assert(sum == 5050)
    }

    test "range with pipeline" {
        let sum_of_squares = (1..11).iter()
            .map((x) => x * x)
            .sum()
        assert(sum_of_squares == 385)
    }

    test "range with variables" {
        let start = 5
        let end = 10
        let result = (start..end).iter().collect()
        assert(result.length() == 5)
        assert(result[0] == 5)
        assert(result[4] == 9)
    }
}
```

## String Iterators

Strings iterate over unicode characters:

```vole
tests {
    test "string characters" {
        let chars = "hello".iter().collect()
        assert(chars.length() == 5)
        assert(chars[0] == "h")
        assert(chars[4] == "o")
    }

    test "unicode string" {
        let chars = "abc".iter().collect()
        assert(chars.length() == 3)
        assert(chars[0] == "a")
    }

    test "string iter with pipeline" {
        let chars = "abcdefgh".iter().skip(2).take(4).collect()
        assert(chars.length() == 4)
        assert(chars[0] == "c")
        assert(chars[3] == "f")
    }

    test "for loop over string" {
        let s = "abc"
        var count = 0
        for ch in s {
            count = count + 1
        }
        assert(count == 3)
    }
}
```

## Lazy Evaluation

Iterator operations are lazy -- nothing happens until a terminal operation consumes the iterator:

```vole
tests {
    test "lazy evaluation" {
        let nums = [1, 2, 3, 4, 5]
        let doubled = nums.iter().map((x) => x * 2)
        let result = doubled.collect()
        assert(result.length() == 5)
    }
}
```

Benefits:
- Memory efficient for large datasets
- Only compute what's needed (e.g., `take(3)` on an infinite generator)
- Chained operations don't create intermediate arrays

## Performance Tips

- Use `.count()` instead of `.collect().length()`
- Use `.sum()` instead of `.reduce(0, (acc, x) => acc + x)` for readability
- Use `.take(n)` with infinite iterators (generators, `repeat`)
- Use `.sorted().unique()` for true deduplication (`unique` only removes consecutive duplicates)
