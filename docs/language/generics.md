# Generics

Generics allow writing code that works with multiple types while maintaining type safety. Vole uses structural generics with type inference.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `func name<T>()` | Generic function |
| `class Name<T> { }` | Generic class |
| `record Name<T> { }` | Generic record |
| `<T: A \| B>` | Union constraint |

> **Note:** Structural constraints (`<T: { field: Type }>`) are not yet implemented.

## In Depth

### Generic Functions

Define type parameters in angle brackets:

```vole
func identity<T>(x: T) -> T {
    return x
}

let n = identity(42)        // T inferred as i32
let s = identity("hello")   // T inferred as string
```

Multiple type parameters:

```vole
func pair<A, B>(first: A, second: B) -> Pair<A, B> {
    return Pair { first: first, second: second }
}
```

### Type Inference

Vole infers type parameters from arguments:

```vole
func first<T>(arr: [T]) -> T? {
    if arr.length > 0 {
        return arr[0]
    }
    return nil
}

let nums = [1, 2, 3]
let x = first(nums)  // T inferred as i32, returns i32?
```

### Generic Records

Records can have type parameters:

```vole
record Box<T> {
    value: T

    func unwrap() -> T {
        return self.value
    }
}

let int_box = Box { value: 42 }
let str_box = Box { value: "hello" }

println(int_box.unwrap())  // 42
println(str_box.unwrap())  // "hello"
```

### Generic Classes

Classes work the same way:

```vole
class Container<T> {
    item: T

    func get() -> T {
        return self.item
    }

    func set(new_item: T) {
        self.item = new_item
    }
}

let c = Container { item: 100 }
c.set(200)
println(c.get())  // 200
```

### Multiple Type Parameters

```vole
record Pair<A, B> {
    first: A
    second: B
}

let entry = Pair { first: "name", second: 42 }
println(entry.first)   // "name"
println(entry.second)  // 42
```

### Union Constraints

Constrain to a set of specific types:

```vole
func double<T: i32 | i64 | f64>(x: T) -> T {
    return x + x
}

println(double(21))     // 42 (i32)
println(double(3.14))   // 6.28 (f64)
```

This is useful for numeric operations that should work across number types.

### Generic Interfaces

Interfaces can have type parameters:

```vole
interface Container<T> {
    func get() -> T
    func set(value: T)
}

interface Iterator<T> {
    func next() -> T?
}
```

### Implementing Generic Interfaces

```vole
interface Mapper<A, B> {
    func map(value: A) -> B
}

record StringToInt implements Mapper<string, i32> {
    func map(value: string) -> i32 {
        return value.length
    }
}
```

### Generic Methods

Methods can have their own type parameters:

```vole
record Transformer {
    func transform<T, U>(value: T, f: (T) -> U) -> U {
        return f(value)
    }
}

let t = Transformer {}
let result = t.transform(5, (x: i32) => x * 2)  // 10
```

### Where Type Parameters Are Inferred

Type parameters are inferred at call sites:

```vole
func wrap<T>(value: T) -> Box<T> {
    return Box { value: value }
}

let box = wrap(42)  // Returns Box<i32>
```

When the return type is generic and can't be inferred from arguments, you may need to annotate the variable:

```vole
func empty<T>() -> [T] {
    return []
}

let nums: [i32] = empty()  // Need annotation
```

### Common Generic Patterns

**Optional wrapper:**

```vole
record Option<T> {
    value: T?

    func is_some() -> bool {
        return self.value != nil
    }

    func unwrap_or(default: T) -> T {
        return self.value ?? default
    }
}
```

**Result type:**

```vole
record Result<T, E> {
    value: T?
    error: E?

    func is_ok() -> bool {
        return self.value != nil
    }

    func is_err() -> bool {
        return self.error != nil
    }
}
```

**Generic collection operations:**

```vole
func map_array<T, U>(arr: [T], f: (T) -> U) -> [U] {
    let mut result: [U] = []
    for item in arr {
        result = result + [f(item)]
    }
    return result
}

func filter_array<T>(arr: [T], predicate: (T) -> bool) -> [T] {
    let mut result: [T] = []
    for item in arr {
        if predicate(item) {
            result = result + [item]
        }
    }
    return result
}
```

### Type Parameter Naming Conventions

| Name | Common Use |
|------|------------|
| `T` | Single generic type ("Type") |
| `U`, `V` | Additional types |
| `K` | Key type (maps) |
| `V` | Value type (maps) |
| `E` | Error type |
| `A`, `B` | When relationship matters |
