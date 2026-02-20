# Classes and Structs

Vole provides two ways to define structured data types: **classes** (reference types, mutable) and **structs** (value types, copy semantics).

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `class Name { fields }` | Mutable reference type |
| `struct Name { fields }` | Immutable value type (copy semantics) |
| `Name { field: value }` | Instantiation |
| `Name { field }` | Shorthand when variable matches field name |
| `self` | Reference to current instance in methods |
| `instance.field` | Field access |
| `instance.method()` | Method call |
| `field: Type = default` | Field with default value |
| `statics { }` | Block for static methods |

## Classes

Classes define mutable reference types with fields and methods:

```vole
class Point {
    x: i64,
    y: i64,
}
```

Create instances with struct literal syntax:

```vole
class Point {
    x: i64,
    y: i64,
}

tests { test "create point" {
    let p = Point { x: 10, y: 20 }
    assert(p.x == 10)
    assert(p.y == 20)
} }
```

### Mutable Fields

Class fields can be modified directly:

```vole
class Counter {
    value: i64,
}

tests { test "mutate field" {
    let c = Counter { value: 0 }
    c.value = c.value + 1
    assert(c.value == 1)
} }
```

### Reference Semantics

Classes use reference semantics. Assigning a class instance to another variable creates an alias, not a copy:

```vole
class Point {
    x: i64,
    y: i64,
}

tests { test "reference semantics" {
    let p1 = Point { x: 10, y: 20 }
    let p2 = p1
    p1.x = 99
    assert(p2.x == 99)
} }
```

### Methods

Define methods inside the class body using `self` to reference the current instance:

```vole
class Point {
    x: i64,
    y: i64,

    func sum() -> i64 {
        return self.x + self.y
    }

    func product() -> i64 => self.x * self.y
}

tests { test "methods" {
    let p = Point { x: 3, y: 4 }
    assert(p.sum() == 7)
    assert(p.product() == 12)
} }
```

### Expression-Bodied Methods

Methods can use the `=>` syntax for concise single-expression bodies:

```vole
class Point {
    x: i64,
    y: i64,

    func sum() -> i64 => self.x + self.y

    func doubled() => Point { x: self.x * 2, y: self.y * 2 }
}

tests { test "expression-bodied" {
    let p = Point { x: 5, y: 7 }
    assert(p.sum() == 12)
    let d = p.doubled()
    assert(d.x == 10)
    assert(d.y == 14)
} }
```

### Mutating Methods

Methods can mutate the instance through `self`:

```vole
class Counter {
    value: i64,

    func get() -> i64 {
        return self.value
    }

    func increment() -> i64 {
        self.value = self.value + 1
        return self.value
    }
}

tests { test "mutating methods" {
    let c = Counter { value: 0 }
    assert(c.increment() == 1)
    assert(c.increment() == 2)
    assert(c.get() == 2)
} }
```

### Static Methods

Static methods are defined inside a `statics { }` block and called on the type itself:

```vole
class Point {
    x: i64,
    y: i64,

    statics {
        func origin() -> Point {
            return Point { x: 0, y: 0 }
        }

        func create(x: i64, y: i64) -> Point {
            return Point { x: x, y: y }
        }
    }
}

tests { test "static methods" {
    let p = Point.origin()
    assert(p.x == 0)
    assert(p.y == 0)

    let p2 = Point.create(10, 20)
    assert(p2.x == 10)
    assert(p2.y == 20)
} }
```

Static methods can call other static methods:

```vole
class Rectangle {
    x: i64,
    y: i64,
    width: i64,
    height: i64,

    statics {
        func at_origin(width: i64, height: i64) -> Rectangle {
            return Rectangle { x: 0, y: 0, width: width, height: height }
        }

        func square(size: i64) -> Rectangle {
            return Rectangle.at_origin(size, size)
        }
    }
}

tests { test "static calling static" {
    let r = Rectangle.square(10)
    assert(r.width == 10)
    assert(r.height == 10)
} }
```

### Extend Blocks

Methods can be added to a class (or struct) outside its body using `extend T { }`. This is useful for splitting a type's helpers across a file without making them part of the type's public interface:

```vole
class Counter {
    value: i64
}

extend Counter {
    func get() -> i64 => self.value
    func increment(amount: i64) -> i64 => self.value + amount
}

tests { test "extend block" {
    let c = Counter { value: 42 }
    assert(c.get() == 42)
    assert(c.increment(8) == 50)
} }
```

Methods added via `extend T { }` are visible only within the current file.

To retroactively add an interface to a type, use `extend T with I { }` (see [Interfaces](interfaces.md)).

### Implementing Interfaces

When defining your own type, list interfaces directly in the class declaration. This is the preferred form when the type and its interface implementations live together:

| Syntax | When to use |
|--------|-------------|
| `class T implements I { }` | Defining your own type — bind interface at the declaration site |
| `extend T with I { }` | Adding an interface to a type defined elsewhere (retroactive / external) |

Classes can implement interfaces directly in their declaration:

```vole
interface Clonable {
    func clone() -> Self
}

class Position implements Clonable {
    x: i32,
    y: i32,

    func clone() -> Self {
        return Position { x: self.x, y: self.y }
    }
}

tests { test "implements interface" {
    let p = Position { x: 10, y: 20 }
    let p2 = p.clone()
    assert(p2.x == 10)
    assert(p2.y == 20)
} }
```

Multiple interfaces can be implemented:

```vole
interface Addable {
    func add(other: Self) -> Self
}

interface Subtractable {
    func sub(other: Self) -> Self
}

class Number implements Addable, Subtractable {
    value: i32,

    func add(other: Self) -> Self {
        return Number { value: self.value + other.value }
    }

    func sub(other: Self) -> Self {
        return Number { value: self.value - other.value }
    }
}

tests { test "multiple interfaces" {
    let a = Number { value: 10 }
    let b = Number { value: 3 }
    assert(a.add(b).value == 13)
    assert(a.sub(b).value == 7)
} }
```

## Structs

Structs define value types with copy semantics. They are immutable by default.

```vole
struct Point {
    x: i64,
    y: i64,
}

tests { test "struct basics" {
    let p = Point { x: 10, y: 20 }
    assert(p.x == 10)
    assert(p.y == 20)
} }
```

### Copy Semantics

Unlike classes, structs are copied on assignment:

```vole
struct Point {
    x: i64,
    y: i64,
}

tests { test "copy semantics" {
    let a = Point { x: 1, y: 2 }
    let b = a
    assert(b.x == 1)
    assert(b.y == 2)
    assert(a.x == 1)
} }
```

### Struct Methods

Structs can have methods just like classes:

```vole
struct Point {
    x: i64,
    y: i64,

    func sum() -> i64 {
        return self.x + self.y
    }

    func product() -> i64 => self.x * self.y

    func doubled() -> Point {
        return Point { x: self.x * 2, y: self.y * 2 }
    }

    func add(other: Point) -> Point {
        return Point { x: self.x + other.x, y: self.y + other.y }
    }
}

tests { test "struct methods" {
    let p = Point { x: 3, y: 7 }
    assert(p.sum() == 10)
    assert(p.product() == 21)

    let d = p.doubled()
    assert(d.x == 6)
    assert(d.y == 14)

    let p2 = Point { x: 10, y: 20 }
    let p3 = p.add(p2)
    assert(p3.x == 13)
    assert(p3.y == 27)
} }
```

### Struct Static Methods

Structs can also have static methods:

```vole
struct Duration {
    nanos: i64,

    statics {
        func seconds(n: i64) -> Duration {
            return Duration { nanos: n * 1000000000 }
        }

        func zero() -> Duration {
            return Duration { nanos: 0 }
        }
    }

    func as_ms() -> i64 {
        return self.nanos / 1000000
    }
}

tests { test "struct statics" {
    let d = Duration.seconds(5)
    assert(d.as_ms() == 5000)
    assert(Duration.zero().nanos == 0)
} }
```

### Struct Equality

Structs support equality comparison with `==` and `!=`:

```vole
struct Point { x: i64, y: i64 }

tests { test "struct equality" {
    let p1 = Point { x: 10, y: 20 }
    let p2 = Point { x: 10, y: 20 }
    let p3 = Point { x: 10, y: 30 }
    assert(p1 == p2)
    assert(p1 != p3)
} }
```

## Classes vs Structs

| Feature | Class | Struct |
|---------|-------|--------|
| Semantics | Reference (alias on assignment) | Value (copy on assignment) |
| Field mutation | Yes | No |
| Methods | Yes | Yes |
| Static methods | Yes | Yes |
| Equality (`==`) | By reference | By value |
| Use case | Mutable state, shared objects | Data containers, value objects |

Choose structs for:
- Data that should not change
- Value objects (points, colors, dimensions)
- Configuration data
- Function return types that carry multiple values

Choose classes for:
- Objects with changing state (counters, accumulators)
- Shared mutable objects (bank accounts, game entities)
- Builder patterns

## Common Features

The following features work with both classes and structs.

### Field Default Values

Fields can have default values, making them optional at instantiation:

```vole
class Config {
    debug: bool = false,
    timeout: i64 = 30,
    name: string = "default",
}

tests { test "field defaults" {
    let cfg = Config {}
    assert(cfg.debug == false)
    assert(cfg.timeout == 30)
    assert(cfg.name == "default")

    let custom = Config { debug: true, timeout: 60 }
    assert(custom.debug == true)
    assert(custom.timeout == 60)
    assert(custom.name == "default")
} }
```

You can mix required and default fields:

```vole
class Point {
    x: i64,
    y: i64,
    z: i64 = 0,
}

tests { test "mixed required and default" {
    let p = Point { x: 1, y: 2 }
    assert(p.z == 0)

    let p2 = Point { x: 1, y: 2, z: 3 }
    assert(p2.z == 3)
} }
```

### Field Init Shorthand

When a variable has the same name as a field, you can use the shorthand syntax:

```vole
class Point {
    x: i32,
    y: i32,

    func sum() -> i32 {
        return self.x + self.y
    }
}

tests { test "init shorthand" {
    let x: i32 = 10
    let y: i32 = 20
    let p = Point { x, y }
    assert(p.x == 10)
    assert(p.y == 20)
    assert(p.sum() == 30)
} }
```

You can mix shorthand and explicit forms:

```vole
class Point {
    x: i32,
    y: i32,
}

tests { test "mixed shorthand" {
    let x: i32 = 10
    let p = Point { x, y: 30 }
    assert(p.x == 10)
    assert(p.y == 30)
} }
```

### Nested Types

Types can contain fields of other struct or class types:

```vole
struct Point { x: i64, y: i64 }
struct Rectangle { top_left: Point, bottom_right: Point }

tests { test "nested types" {
    let rect = Rectangle {
        top_left: Point { x: 0, y: 0 },
        bottom_right: Point { x: 10, y: 5 },
    }
    assert(rect.top_left.x == 0)
    assert(rect.bottom_right.x == 10)

    let width = rect.bottom_right.x - rect.top_left.x
    assert(width == 10)
} }
```

### Destructuring

Struct instances can be destructured to extract fields:

```vole
struct Point { x: i64, y: i64 }

tests { test "destructuring" {
    let p = Point { x: 10, y: 20 }

    let { x, y } = p
    assert(x == 10)
    assert(y == 20)
} }
```

You can rename fields during destructuring:

```vole
struct Point { x: i64, y: i64 }

tests { test "destructuring with rename" {
    let p = Point { x: 10, y: 20 }
    let { x: a, y: b } = p
    assert(a == 10)
    assert(b == 20)
} }
```

Partial destructuring extracts only some fields:

```vole
struct Color { r: i64, g: i64, b: i64 }

tests { test "partial destructuring" {
    let c = Color { r: 255, g: 128, b: 0 }
    let { r } = c
    assert(r == 255)
} }
```

### Diverse Field Types

Structs and classes support fields of any type including strings, booleans, floats, and arrays:

```vole
struct Config {
    name: string,
    count: i64,
    enabled: bool,
    rate: f64,
}

tests { test "diverse field types" {
    let c = Config { name: "app", count: 5, enabled: true, rate: 0.75 }
    assert(c.name == "app")
    assert(c.count == 5)
    assert(c.enabled == true)
    assert(c.rate == 0.75)
} }
```

### Forward References

Types can reference other types that are defined later in the file:

```vole
class Parent {
    child: Child,

    func getChildValue() -> i32 {
        return self.child.value
    }
}

class Child {
    value: i32
}

tests { test "forward references" {
    let child = Child { value: 42 }
    let parent = Parent { child: child }
    assert(parent.getChildValue() == 42)
} }
```

### Optional Fields

Fields can be nullable using the `?` suffix on the type:

```vole
class NodeA {
    next: NodeB?,
    data: i32
}

class NodeB {
    prev: NodeA?,
    data: string
}

tests { test "nullable fields" {
    let a = NodeA { next: nil, data: 100 }
    let b = NodeB { prev: a, data: "hello" }
    assert(b.prev?.data == 100)
} }
```

### Method Chaining

Methods that return instances of the same type support chaining:

```vole
interface Chainable {
    func chain() -> Self
}

class Builder implements Chainable {
    count: i32,

    func chain() -> Self {
        return Builder { count: self.count + 1 }
    }
}

tests { test "method chaining" {
    let b = Builder { count: 0 }
    let b2 = b.chain().chain().chain()
    assert(b2.count == 3)
} }
```

### Common Patterns

**Factory function:**

```vole
struct Point {
    x: i64,
    y: i64,
}

func origin() -> Point {
    return Point { x: 0, y: 0 }
}

tests { test "factory" {
    let p = origin()
    assert(p.x == 0)
    assert(p.y == 0)
} }
```

**Builder pattern:**

```vole
class BankAccount {
    balance: i64,
    transaction_count: i64,

    statics {
        func empty() -> BankAccount {
            return BankAccount { balance: 0, transaction_count: 0 }
        }

        func with_initial_deposit(amount: i64) -> BankAccount {
            return BankAccount { balance: amount, transaction_count: 1 }
        }
    }

    func deposit(amount: i64) {
        self.balance = self.balance + amount
        self.transaction_count = self.transaction_count + 1
    }

    func get_balance() -> i64 {
        return self.balance
    }
}

tests { test "builder pattern" {
    let acc = BankAccount.with_initial_deposit(100)
    acc.deposit(50)
    assert(acc.get_balance() == 150)
} }
```
