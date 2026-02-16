# Interfaces

Interfaces define contracts that types can implement. Vole supports explicit implementation, structural implementation, and standalone `implement` blocks.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `interface Name { }` | Define interface |
| `func method() -> T` | Required method |
| `default func method() -> T { }` | Default method |
| `class C implements I { }` | Explicit implementation |
| `Self` | The implementing type |
| `interface Child extends Parent { }` | Interface inheritance |
| `implement I for T { }` | Standalone implementation block |
| `static interface Name { }` | Interface with only static methods |

## Defining Interfaces

Interfaces declare method signatures that types must implement:

```vole
interface Hashable {
    func hash() -> i64
}
```

Interfaces can require fields:

```vole
interface Named {
    name: string
}
```

## Implementing Interfaces

Use `implements` in the class declaration to explicitly implement an interface:

```vole
interface Hashable {
    func hash() -> i64
}

class User implements Hashable {
    id: i64,

    func hash() -> i64 {
        return self.id
    }
}

tests { test "explicit implements" {
    let u = User { id: 42 }
    assert(u.hash() == 42)
} }
```

## The Self Type

`Self` refers to the implementing type, enabling type-safe method signatures:

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

tests { test "Self type" {
    let p = Position { x: 10, y: 20 }
    let p2 = p.clone()
    assert(p2.x == 10)
    assert(p2.y == 20)
} }
```

`Self` can be used as both parameter and return types:

```vole
interface BinaryOp {
    func combine(other: Self) -> Self
}

class Vector implements BinaryOp {
    x: i32,
    y: i32,

    func combine(other: Self) -> Self {
        return Vector { x: self.x + other.x, y: self.y + other.y }
    }
}

tests { test "Self in params and return" {
    let v1 = Vector { x: 1, y: 2 }
    let v2 = Vector { x: 3, y: 4 }
    let v3 = v1.combine(v2)
    assert(v3.x == 4)
    assert(v3.y == 6)
} }
```

## Interface Values

A variable typed as an interface can hold any implementing class, and method calls dispatch dynamically:

```vole
interface Hashable {
    func hash() -> i64
}

class User implements Hashable {
    id: i64,

    func hash() -> i64 {
        return self.id
    }
}

tests { test "interface-typed variable" {
    let h: Hashable = User { id: 7 }
    assert(h.hash() == 7)
} }
```

## Multiple Interfaces

A type can implement multiple interfaces:

```vole
interface Hashable {
    func hash() -> i64
}

interface Serializable {
    func toJson() -> string
}

class Entity implements Hashable, Serializable {
    id: i64,
    name: string,

    func hash() -> i64 {
        return self.id
    }

    func toJson() -> string {
        return self.name
    }
}

tests { test "multiple interfaces" {
    let e = Entity { id: 123, name: "entity123" }
    assert(e.hash() == 123)
    assert(e.toJson() == "entity123")
} }
```

## Default Methods

Interfaces can provide default implementations using the `default` keyword. Implementors only need to provide the abstract methods:

```vole
interface Comparable {
    func compare(other: i64) -> i64

    default func lessThan(other: i64) -> bool {
        return self.compare(other) < 0
    }

    default func greaterThan(other: i64) -> bool {
        return self.compare(other) > 0
    }
}

class Score implements Comparable {
    value: i64,

    func compare(other: i64) -> i64 {
        return self.value - other
    }
}

tests { test "default methods" {
    let s = Score { value: 10 }
    assert(s.compare(20) == -10)
    assert(s.lessThan(20) == true)
    assert(s.greaterThan(5) == true)
} }
```

Default methods can be overridden:

```vole
interface Comparable {
    func compare(other: i64) -> i64

    default func lessThan(other: i64) -> bool {
        return self.compare(other) < 0
    }
}

class Rating implements Comparable {
    stars: i64,

    func compare(other: i64) -> i64 {
        return self.stars - other
    }

    func lessThan(other: i64) -> bool {
        if self.stars == 5 {
            return false
        }
        return self.compare(other) < 0
    }
}

tests { test "override default method" {
    let r = Rating { stars: 5 }
    assert(r.lessThan(10) == false)

    let r2 = Rating { stars: 3 }
    assert(r2.lessThan(5) == true)
} }
```

Default methods also work through interface-typed variables (vtable dispatch):

```vole
interface Counter {
    func value() -> i64

    default func increment() -> i64 {
        return self.value() + 1
    }

    default func decrement() -> i64 {
        return self.value() - 1
    }

    func reset() -> i64
}

class SimpleCounter implements Counter {
    current: i64,

    func value() -> i64 {
        return self.current
    }

    func reset() -> i64 {
        return 0
    }
}

tests { test "default method via interface type" {
    let c: Counter = SimpleCounter { current: 5 }
    assert(c.value() == 5)
    assert(c.increment() == 6)
    assert(c.decrement() == 4)
} }
```

## Interface Inheritance

Interfaces can extend other interfaces:

```vole
interface Base {
    func base_method() -> i64
}

interface Extended extends Base {
    func extended_method() -> i64
}

class ExtendedImpl implements Extended {
    value: i64,

    func base_method() -> i64 {
        return self.value
    }

    func extended_method() -> i64 {
        return self.value * 2
    }
}

tests { test "interface inheritance" {
    let e = ExtendedImpl { value: 10 }
    assert(e.base_method() == 10)
    assert(e.extended_method() == 20)

    let b: Base = ExtendedImpl { value: 11 }
    assert(b.base_method() == 11)
} }
```

## Standalone Implement Blocks

Add interface implementations to existing types using `implement ... for ...` blocks:

```vole
interface Describable {
    func describe() -> string
}

class Person {
    name: string,
    age: i64,
}

implement Describable for Person {
    func describe() -> string {
        return self.name
    }
}

tests { test "implement block for interface" {
    let p = Person { name: "Bob", age: 25 }
    assert(p.describe() == "Bob")

    let d: Describable = Person { name: "Dana", age: 22 }
    assert(d.describe() == "Dana")
} }
```

Implement blocks work for primitive types too:

```vole
interface Describable {
    func describe() -> string
}

implement Describable for i32 {
    func describe() -> string {
        return "an integer"
    }
}

implement Describable for string {
    func describe() -> string {
        return "a string"
    }
}

tests { test "implement block for primitives" {
    let x: i32 = 42
    assert(x.describe() == "an integer")

    let s: string = "hello"
    assert(s.describe() == "a string")
} }
```

You can also declare `implements` on a class and satisfy it via a separate implement block:

```vole
interface Incrementable {
    func increment() -> i64
}

class Score implements Incrementable {
    value: i64
}

implement Incrementable for Score {
    func increment() -> i64 {
        return self.value + 1
    }
}

tests { test "implements satisfied by external block" {
    let s = Score { value: 10 }
    assert(s.increment() == 11)
} }
```

Expression-bodied methods work in implement blocks:

```vole
interface Tripler {
    func triple() -> i64
}

class Quantity {
    n: i64
}

implement Tripler for Quantity {
    func triple() -> i64 => self.n * 3
}

tests { test "expression-bodied in implement block" {
    let q = Quantity { n: 14 }
    assert(q.triple() == 42)
} }
```

## Functional Interfaces

A functional interface is an interface with exactly one abstract method and no fields. Lambdas matching the method signature can be assigned to variables of that interface type:

```vole
interface Predicate {
    func check(value: i64) -> bool
}

interface Transform {
    func apply(value: i64) -> i64
}

let isPositive: Predicate = (x: i64) => x > 0
let double: Transform = (x: i64) => x * 2

tests { test "functional interfaces" {
    assert(isPositive(5) == true)
    assert(isPositive(-3) == false)
    assert(isPositive.check(10) == true)

    assert(double(21) == 42)
    assert(double.apply(21) == 42)
} }
```

Functional interfaces can be called directly (like a function) or through the interface method. They also work with local variables inside test blocks:

```vole
interface Transform {
    func apply(value: i64) -> i64
}

tests { test "local functional interface" {
    let triple: Transform = (x: i64) => x * 3
    assert(triple(7) == 21)
    assert(triple.apply(10) == 30)
} }
```

Multi-parameter functional interfaces work too:

```vole
interface BiTransform {
    func apply(a: i64, b: i64) -> i64
}

let add: BiTransform = (a: i64, b: i64) => a + b

tests { test "multi-param functional interface" {
    assert(add(20, 22) == 42)
    assert(add.apply(20, 22) == 42)
} }
```

## Static Interfaces

Static interfaces define type-level methods (called on the type, not an instance). The `static interface` syntax is shorthand for an interface with only a `statics` block:

```vole
static interface DefaultValue {
    func default_value() -> Self
}

static interface Bounded {
    func min_bound() -> Self
    func max_bound() -> Self
}

class MyNumber {
    value: i64,
}

implement DefaultValue for MyNumber {
    statics {
        func default_value() -> MyNumber {
            return MyNumber { value: 0 }
        }
    }
}

implement Bounded for MyNumber {
    statics {
        func min_bound() -> MyNumber {
            return MyNumber { value: -1000 }
        }

        func max_bound() -> MyNumber {
            return MyNumber { value: 1000 }
        }
    }
}

tests { test "static interfaces" {
    let n = MyNumber.default_value()
    assert(n.value == 0)

    let min = MyNumber.min_bound()
    let max = MyNumber.max_bound()
    assert(min.value == -1000)
    assert(max.value == 1000)
} }
```

Built-in types implement static interfaces like `Default` and `Bounded`:

```vole
tests { test "built-in static interfaces" {
    assert(i32.default_value() == 0)
    assert(i64.default_value() == 0)
    assert(bool.default_value() == false)
    assert(string.default_value() == "")

    assert(i32.min_value() == -2147483648)
    assert(i32.max_value() == 2147483647)
} }
```

## Interface-Typed Fields

Classes can have fields typed as interfaces:

```vole
interface Animal {
    func speak() -> string
}

class Dog {
    name: string,
}

class Cat {
    name: string,
}

implement Animal for Dog {
    func speak() -> string {
        return "woof"
    }
}

implement Animal for Cat {
    func speak() -> string {
        return "meow"
    }
}

class AnimalHolder {
    pet: Animal,
}

tests { test "interface-typed field" {
    let dog: Animal = Dog { name: "rex" }
    let holder = AnimalHolder { pet: dog }
    assert(holder.pet.speak() == "woof")
} }
```

## Common Patterns

**Comparison interface:**

```vole
interface Comparable {
    func compare(other: Self) -> i32
}

class Point implements Comparable {
    x: i32,
    y: i32,

    func compare(other: Self) -> i32 {
        return self.x - other.x
    }
}

tests { test "comparable pattern" {
    let a = Point { x: 10, y: 5 }
    let b = Point { x: 3, y: 8 }
    assert(a.compare(b) == 7)
} }
```

**Polymorphic dispatch:**

```vole
interface Greeter {
    func greet() -> string
}

class HelloGreeter implements Greeter {
    name: string,

    func greet() -> string {
        return "hello " + self.name
    }
}

class FormalGreeter implements Greeter {
    title: string,

    func greet() -> string {
        return "good day " + self.title
    }
}

tests { test "polymorphic dispatch" {
    let g1: Greeter = HelloGreeter { name: "world" }
    let g2: Greeter = FormalGreeter { title: "sir" }
    assert(g1.greet() == "hello world")
    assert(g2.greet() == "good day sir")
} }
```
