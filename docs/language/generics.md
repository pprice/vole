# Generics

Generics allow writing code that works with multiple types while maintaining type safety. Vole supports type inference, interface constraints, structural constraints, and multiple constraint syntax.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `func name<T>()` | Generic function |
| `class Name<T> { }` | Generic class |
| `<T: Interface>` | Interface constraint |
| `<T: A + B>` | Multiple interface constraints |
| `<T: { field: Type }>` | Structural field constraint |
| `<T: { func m() -> T }>` | Structural method constraint |
| `let Alias: type = ...` | Type alias for constraints |

## Generic Functions

Define type parameters in angle brackets. Vole infers types from arguments:

```vole
func identity<T>(x: T) -> T {
    return x
}

tests { test "generic function" {
    let n = identity(42)
    assert(n == 42)

    let s = identity("hello")
    assert(s == "hello")

    let b = identity(true)
    assert(b == true)
} }
```

### Multiple Type Parameters

```vole
func swap<A, B>(a: A, b: B) -> B {
    return b
}

tests { test "multiple type params" {
    let result = swap(123, "world")
    assert(result == "world")
} }
```

### Generic Functions with Arrays

```vole
func first<T>(arr: [T]) -> T {
    return arr[0]
}

tests { test "generic array function" {
    let arr = [1, 2, 3]
    assert(first(arr) == 1)

    let strs = ["a", "b", "c"]
    assert(first(strs) == "a")
} }
```

### Higher-Order Generic Functions

Generic functions can accept function parameters:

```vole
func apply_twice<T>(x: T, f: (T) -> T) -> T {
    return f(f(x))
}

tests { test "higher-order generic" {
    let double = (x: i64) => x * 2
    let result = apply_twice(5, double)
    assert(result == 20)

    let negate = (b: bool) => !b
    assert(apply_twice(true, negate) == true)
} }
```

## Generic Classes

Classes can have type parameters:

```vole
class Wrapper<T> {
    data: T,

    func unwrap() -> T {
        return self.data
    }
}

tests { test "generic class" {
    let w = Wrapper { data: 100 }
    assert(w.data == 100)
    assert(w.unwrap() == 100)

    let ws = Wrapper { data: "wrapped" }
    assert(ws.unwrap() == "wrapped")
} }
```

### Generic Class Methods

Methods on generic classes can read and write the type parameter:

```vole
class Box<T> {
    value: T,

    func get() -> T {
        return self.value
    }

    func set(v: T) {
        self.value = v
    }
}

tests { test "generic class methods" {
    let box = Box { value: 42 }
    assert(box.get() == 42)
    box.set(100)
    assert(box.get() == 100)
} }
```

### Multiple Type Parameters

```vole
class Pair<A, B> {
    first: A,
    second: B,

    func getFirst() -> A {
        return self.first
    }

    func getSecond() -> B {
        return self.second
    }
}

tests { test "generic pair" {
    let p = Pair { first: "name", second: 42 }
    assert(p.getFirst() == "name")
    assert(p.getSecond() == 42)
} }
```

### Nested Generics

Generic types can be nested:

```vole
class Wrapper<T> {
    data: T,
}

tests { test "nested generics" {
    let inner = Wrapper { data: 5 }
    let outer = Wrapper { data: inner }
    assert(outer.data.data == 5)
} }
```

### Generic Static Methods

Static methods on generic classes can use the class's type parameters:

```vole
class Box<T> {
    value: T,

    statics {
        func create(v: T) -> Box<T> {
            return Box { value: v }
        }
    }

    func get() -> T {
        return self.value
    }
}

tests { test "generic static methods" {
    let b = Box.create(42)
    assert(b.get() == 42)

    let bs = Box.create("hello")
    assert(bs.get() == "hello")
} }
```

You can also provide explicit type arguments:

```vole
class Box<T> {
    value: T,

    statics {
        func create(v: T) -> Box<T> {
            return Box { value: v }
        }
    }

    func get() -> T {
        return self.value
    }
}

tests { test "explicit type args" {
    let b = Box.create<string>("world")
    assert(b.get() == "world")
} }
```

## Generic Structs

Structs also support type parameters:

```vole
struct Point<T> {
    x: T,
    y: T,

    statics {
        func origin(zero: T) -> Point<T> {
            return Point { x: zero, y: zero }
        }

        func create(x: T, y: T) -> Point<T> {
            return Point { x: x, y: y }
        }
    }
}

tests { test "generic struct" {
    let p = Point.create(3, 4)
    assert(p.x == 3)
    assert(p.y == 4)

    let pf = Point.create(1.5, 2.5)
    assert(pf.x == 1.5)
    assert(pf.y == 2.5)
} }
```

## Interface Constraints

Constrain type parameters to types that implement an interface:

```vole
interface Hashable {
    func hash() -> i64
}

class HashBox<T: Hashable> {
    value: T,

    func hash_value() -> i64 {
        return self.value.hash()
    }
}

tests { test "interface constraint" {
    let b = HashBox { value: 42 }
    assert(b.hash_value() == 42.hash())
} }
```

### Multiple Interface Constraints

Use `+` to require multiple interfaces:

```vole
interface Hashable {
    func hash() -> i64
}

interface Eq {
    func equals(other: Self) -> bool
}

interface Stringable {
    func to_string() -> string
}

func needs_hash_and_eq<T: Hashable + Eq>(x: T) -> i64 {
    return x.hash()
}

func needs_all<T: Hashable + Eq + Stringable>(x: T) -> string {
    return x.to_string()
}

class Point {
    x: i64
    y: i64
}

implement Hashable for Point {
    func hash() -> i64 {
        return self.x * 31 + self.y
    }
}

implement Eq for Point {
    func equals(other: Point) -> bool {
        return self.x == other.x && self.y == other.y
    }
}

implement Stringable for Point {
    func to_string() -> string {
        return "Point"
    }
}

tests { test "multiple constraints" {
    let p = Point { x: 10, y: 20 }
    assert(needs_hash_and_eq(p) == 330)
    assert(needs_all(p) == "Point")
} }
```

### Constrained Generic Classes

Classes can have constrained type parameters that work in both instance and static methods:

```vole
interface Hashable { func hash() -> i64 }
interface Eq { func eq(other: Self) -> bool }

class Container<T: Hashable + Eq> {
    item: T,

    func getHash() -> i64 {
        return self.item.hash()
    }

    func matches(other: T) -> bool {
        return self.item.eq(other)
    }
}

class Id implements Hashable, Eq {
    n: i64,
}

implement Hashable for Id {
    func hash() -> i64 { return self.n * 17 }
}

implement Eq for Id {
    func eq(other: Id) -> bool { return self.n == other.n }
}

tests { test "constrained generic class" {
    let c = Container { item: Id { n: 5 } }
    assert(c.getHash() == 85)
    assert(c.matches(Id { n: 5 }) == true)
    assert(c.matches(Id { n: 10 }) == false)
} }
```

### Different Constraints on Different Type Parameters

```vole
interface Hashable { func hash() -> i64 }
interface Stringable { func str() -> string }

class KeyValue<K: Hashable, V: Stringable> {
    key: K,
    value: V,

    func keyHash() -> i64 {
        return self.key.hash()
    }

    func valueStr() -> string {
        return self.value.str()
    }
}

class Id implements Hashable {
    n: i64,
}

implement Hashable for Id {
    func hash() -> i64 { return self.n * 17 }
}

class Label implements Stringable {
    text: string,
}

implement Stringable for Label {
    func str() -> string { return self.text }
}

tests { test "different constraints per param" {
    let kv = KeyValue { key: Id { n: 4 }, value: Label { text: "four" } }
    assert(kv.keyHash() == 68)
    assert(kv.valueStr() == "four")
} }
```

## Structural Constraints

Constrain type parameters by requiring specific fields or methods, without needing a named interface:

### Field Constraints

```vole
class Person {
    name: string,
    age: i64,
}

class Animal {
    name: string,
    species: string,
}

func getName<T: { name: string }>(x: T) -> string {
    return x.name
}

tests { test "structural field constraint" {
    let p = Person { name: "Alice", age: 30 }
    assert(getName(p) == "Alice")

    let a = Animal { name: "Fluffy", species: "Cat" }
    assert(getName(a) == "Fluffy")
} }
```

### Method Constraints

```vole
class CounterWithGet {
    value: i64,
    func get() -> i64 { return self.value }
}

func call_get<T: { func get() -> i64 }>(x: T) -> i64 {
    return x.get()
}

tests { test "structural method constraint" {
    let c = CounterWithGet { value: 42 }
    assert(call_get(c) == 42)
} }
```

### Method Constraints with Parameters

```vole
class Accumulator {
    value: i64,
    func add(n: i64) -> i64 { return self.value + n }
}

func call_add<T: { func add(n: i64) -> i64 }>(x: T) -> i64 {
    return x.add(5)
}

tests { test "method constraint with params" {
    let a = Accumulator { value: 10 }
    assert(call_add(a) == 15)
} }
```

### Mixed Field and Method Constraints

```vole
class ValidUser {
    name: string,
    func validate() -> bool { return true }
}

class InvalidUser {
    name: string,
    func validate() -> bool { return false }
}

func process<T: { name: string, func validate() -> bool }>(x: T) -> string {
    if x.validate() {
        return x.name
    } else {
        return "invalid"
    }
}

tests { test "mixed constraints" {
    assert(process(ValidUser { name: "Alice" }) == "Alice")
    assert(process(InvalidUser { name: "Bob" }) == "invalid")
} }
```

### Structural Constraints with Arrays

```vole
class Item { value: i64 }

func sum_values<T: { value: i64 }>(items: [T]) -> i64 {
    let mut total = 0
    for item in items {
        total = total + item.value
    }
    return total
}

tests { test "structural constraint on array" {
    let items = [Item { value: 10 }, Item { value: 20 }, Item { value: 30 }]
    assert(sum_values(items) == 60)
} }
```

## Type Aliases as Constraints

Type aliases (`let Name: type = ...`) can be used as constraints for reusable duck typing:

```vole
let HasName: type = { name: string }
let HasValue: type = { value: i64 }

class Person { name: string, age: i64 }
class Pet { name: string, species: string }
class Counter { value: i64 }
class Score { value: i64, player: string }

func greet<T: HasName>(x: T) -> string {
    return "Hello, " + x.name
}

func double_value<T: HasValue>(x: T) -> i64 {
    return x.value * 2
}

tests { test "type alias constraints" {
    assert(greet(Person { name: "Alice", age: 30 }) == "Hello, Alice")
    assert(greet(Pet { name: "Fluffy", species: "cat" }) == "Hello, Fluffy")

    assert(double_value(Counter { value: 21 }) == 42)
    assert(double_value(Score { value: 50, player: "X" }) == 100)
} }
```

### Interface Combination Aliases

Type aliases can combine multiple interfaces using `+`:

```vole
interface Hashable {
    func hash() -> i64
}

interface Eq {
    func equals(other: Self) -> bool
}

interface Stringable {
    func to_string() -> string
}

let HashEq: type = Hashable + Eq
let HashEqStr: type = Hashable + Eq + Stringable

func process<T: HashEq>(x: T) -> i64 {
    return x.hash()
}

func describe<T: HashEqStr>(x: T) -> string {
    return x.to_string()
}

class Point {
    x: i64
    y: i64
}

implement Hashable for Point {
    func hash() -> i64 {
        return self.x * 31 + self.y
    }
}

implement Eq for Point {
    func equals(other: Point) -> bool {
        return self.x == other.x && self.y == other.y
    }
}

implement Stringable for Point {
    func to_string() -> string {
        return "Point"
    }
}

tests { test "interface combination alias" {
    let p = Point { x: 10, y: 20 }
    assert(process(p) == 330)
    assert(describe(p) == "Point")
} }
```

## Generic Interfaces

Interfaces can have type parameters:

```vole
interface Producer<T> {
    func produce() -> T
}

class IntProducer {
    value: i64,
    func produce() -> i64 { return self.value }
}

func get_value<T, P: Producer<T>>(producer: P) -> T {
    return producer.produce()
}

tests { test "generic interface" {
    let p = IntProducer { value: 42 }
    let v = get_value(p)
    assert(v == 42)
} }
```

## Generic Implement Blocks

Implement blocks can work with generic classes:

```vole
interface Describable {
    func describe() -> string
}

class Wrapper<T> {
    value: T,
}

implement Describable for Wrapper<T> {
    func describe() -> string {
        return "wrapper"
    }
}

tests { test "generic implement block" {
    let w = Wrapper { value: 42 }
    assert(w.describe() == "wrapper")

    let ws = Wrapper { value: "hello" }
    assert(ws.describe() == "wrapper")
} }
```

Parameterized interfaces on generic classes:

```vole
interface Producer<T> {
    func produce() -> T
}

class Box<T> {
    item: T,
}

implement Producer<T> for Box<T> {
    func produce() -> T {
        return self.item
    }
}

tests { test "parameterized interface implement" {
    let b = Box { item: 99 }
    assert(b.produce() == 99)

    let bs = Box { item: "test" }
    assert(bs.produce() == "test")
} }
```

## Type Parameter Naming Conventions

| Name | Common Use |
|------|------------|
| `T` | Single generic type ("Type") |
| `U`, `V` | Additional types |
| `K` | Key type |
| `V` | Value type |
| `A`, `B` | When relationship matters |
