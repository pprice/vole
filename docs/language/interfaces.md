# Interfaces

Interfaces define contracts that types can implement. Vole supports both explicit and structural interface implementation.

## Quick Reference

| Syntax | Description |
|--------|-------------|
| `interface Name { }` | Define interface |
| `func method() -> T` | Required method |
| `func method() -> T { }` | Default method |
| `record R implements I { }` | Explicit implementation |
| `Self` | The implementing type |
| `interface Child extends Parent { }` | Interface inheritance |
| `implement I for T { }` | Standalone implementation block |

## In Depth

### Defining Interfaces

Interfaces declare method signatures that types must implement:

```vole
interface Printable {
    func print()
}

interface Comparable {
    func compare(other: Self) -> i32
}
```

Interfaces can also require fields:

```vole
interface Named {
    name: string
}
```

### Implementing Interfaces

Use `implements` to explicitly implement an interface:

```vole
interface Describable {
    func describe() -> string
}

record Person implements Describable {
    name: string
    age: i32

    func describe() -> string {
        return "{self.name} is {self.age} years old"
    }
}

let p = Person { name: "Alice", age: 30 }
println(p.describe())  // "Alice is 30 years old"
```

### The Self Type

`Self` refers to the implementing type, enabling type-safe method signatures:

```vole
interface Cloneable {
    func clone() -> Self
}

record Point implements Cloneable {
    x: i32
    y: i32

    func clone() -> Self {
        return Point { x: self.x, y: self.y }
    }
}

let p = Point { x: 10, y: 20 }
let copy = p.clone()  // Returns Point, not just Cloneable
```

### Comparison Interface

Common pattern for comparable types:

```vole
interface Comparable {
    func compare(other: Self) -> i32
}

record Score implements Comparable {
    value: i32

    func compare(other: Self) -> i32 {
        return self.value - other.value
    }
}

let a = Score { value: 100 }
let b = Score { value: 80 }
println(a.compare(b))  // 20 (a > b)
```

### Default Methods

Interfaces can provide default implementations:

```vole
interface Printable {
    func to_string() -> string

    func print() {
        println(self.to_string())
    }
}

record Item implements Printable {
    name: string

    func to_string() -> string {
        return self.name
    }
    // print() is inherited from the interface
}

let item = Item { name: "Widget" }
item.print()  // "Widget"
```

### Interface Inheritance

Interfaces can extend other interfaces:

```vole
interface Named {
    func name() -> string
}

interface Described extends Named {
    func description() -> string
}

record Product implements Described {
    title: string
    details: string

    func name() -> string {
        return self.title
    }

    func description() -> string {
        return self.details
    }
}
```

### Structural Implementation

Types can satisfy interfaces structurally without explicit `implements`:

```vole
interface HasLength {
    func length() -> i32
}

record Buffer {
    data: [u8]

    func length() -> i32 {
        return self.data.length
    }
}

// Buffer satisfies HasLength structurally
func print_length(x: HasLength) {
    println(x.length())
}

let buf = Buffer { data: [1, 2, 3] }
print_length(buf)  // Works!
```

### Standalone Implementation Blocks

Add methods to types using `implement` blocks:

```vole
record Point {
    x: i32
    y: i32
}

// Add methods without modifying the original definition
implement Point {
    func origin() -> Point {
        return Point { x: 0, y: 0 }
    }

    func add(other: Point) -> Point {
        return Point {
            x: self.x + other.x,
            y: self.y + other.y
        }
    }
}

let p = Point { x: 1, y: 2 }
let q = Point { x: 3, y: 4 }
let sum = p.add(q)
```

Implement an interface for an existing type:

```vole
interface Describable {
    func describe() -> string
}

implement Describable for Point {
    func describe() -> string {
        return "Point({self.x}, {self.y})"
    }
}
```

### Multiple Interfaces

A type can implement multiple interfaces:

```vole
interface Named {
    func name() -> string
}

interface Aged {
    func age() -> i32
}

record Person implements Named, Aged {
    full_name: string
    years: i32

    func name() -> string {
        return self.full_name
    }

    func age() -> i32 {
        return self.years
    }
}
```

### Common Patterns

**Polymorphic function:**

```vole
interface Shape {
    func area() -> f64
}

record Circle implements Shape {
    radius: f64

    func area() -> f64 {
        return 3.14159 * self.radius * self.radius
    }
}

record Square implements Shape {
    side: f64

    func area() -> f64 {
        return self.side * self.side
    }
}

func total_area(shapes: [Shape]) -> f64 {
    let mut sum = 0.0
    for shape in shapes {
        sum = sum + shape.area()
    }
    return sum
}
```

**Strategy pattern:**

```vole
interface Formatter {
    func format(value: i32) -> string
}

record DecimalFormatter implements Formatter {
    func format(value: i32) -> string {
        return "{value}"
    }
}

func display(value: i32, formatter: Formatter) {
    println(formatter.format(value))
}
```
