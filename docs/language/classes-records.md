# Classes and Records

Vole provides two ways to define structured data types: classes (mutable) and records (immutable by default).

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `class Name { fields }` | Mutable class |
| `record Name { fields }` | Immutable record |
| `Name { field: value }` | Instantiation |
| `self` | Reference to current instance |
| `instance.field` | Field access |
| `instance.method()` | Method call |

## In Depth

### Classes

Classes define mutable data structures with fields and methods:

```vole
class Point {
    x: i32
    y: i32
}
```

Create instances with struct literal syntax:

```vole
let p = Point { x: 10, y: 20 }
println(p.x)  // 10
println(p.y)  // 20
```

### Mutable Fields

Class fields can be modified:

```vole
class Counter {
    value: i32
}

let c = Counter { value: 0 }
c.value = c.value + 1
println(c.value)  // 1
```

### Methods

Define methods inside the class body:

```vole
class Point {
    x: i32
    y: i32

    func move_by(dx: i32, dy: i32) {
        self.x = self.x + dx
        self.y = self.y + dy
    }

    func distance_squared() -> i32 {
        return self.x * self.x + self.y * self.y
    }
}

let p = Point { x: 3, y: 4 }
println(p.distance_squared())  // 25
p.move_by(1, 1)
println(p.x)  // 4
```

### The self Keyword

Inside methods, `self` refers to the current instance:

```vole
class Rectangle {
    width: i32
    height: i32

    func area() -> i32 {
        return self.width * self.height
    }

    func scale(factor: i32) {
        self.width = self.width * factor
        self.height = self.height * factor
    }
}
```

### Records

Records are similar to classes but emphasize immutability:

```vole
record Person {
    name: string
    age: i32
}

let alice = Person { name: "Alice", age: 30 }
println(alice.name)  // "Alice"
```

### Record Methods

Records can have methods:

```vole
record Rectangle {
    width: i32
    height: i32

    func area() -> i32 {
        return self.width * self.height
    }

    func perimeter() -> i32 {
        return 2 * (self.width + self.height)
    }
}

let r = Rectangle { width: 10, height: 5 }
println(r.area())       // 50
println(r.perimeter())  // 30
```

### Classes vs Records

| Feature | Class | Record |
|---------|-------|--------|
| Field mutation | Yes | No (by default) |
| Methods | Yes | Yes |
| Use case | Mutable state | Data containers |

Choose records for:
- Data that shouldn't change
- Value objects
- Configuration
- API responses

Choose classes for:
- Objects with changing state
- Stateful components
- Game entities

### Nested Types

Classes and records can be nested:

```vole
record Address {
    street: string
    city: string
}

record Person {
    name: string
    address: Address
}

let person = Person {
    name: "Alice",
    address: Address {
        street: "123 Main St",
        city: "Springfield"
    }
}

println(person.address.city)  // "Springfield"
```

### Field Initialization

All fields must be initialized when creating an instance:

```vole
class Point {
    x: i32
    y: i32
}

let p = Point { x: 10, y: 20 }  // OK
let q = Point { x: 10 }          // Error: missing field 'y'
```

### Methods Returning Self

Methods can return the instance for chaining:

```vole
class Builder {
    value: i32

    func add(n: i32) -> Builder {
        self.value = self.value + n
        return self
    }

    func multiply(n: i32) -> Builder {
        self.value = self.value * n
        return self
    }
}

let b = Builder { value: 0 }
b.add(5).multiply(2).add(3)
println(b.value)  // 13
```

### Common Patterns

**Factory function:**

```vole
record Point {
    x: i32
    y: i32
}

func origin() -> Point {
    return Point { x: 0, y: 0 }
}
```

**Builder pattern:**

```vole
class Config {
    debug: bool
    verbose: bool
    max_retries: i32
}

func default_config() -> Config {
    return Config {
        debug: false,
        verbose: false,
        max_retries: 3
    }
}
```

**Data container:**

```vole
record Response {
    status: i32
    body: string
}

func make_response(status: i32, body: string) -> Response {
    return Response {
        status: status,
        body: body
    }
}
```
