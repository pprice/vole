# Vole Cheatsheet

Single-page syntax reference.

## Variables

```vole
let x = 42              // Immutable, inferred type
let x: i64 = 42         // Immutable, explicit type
let mut x = 0           // Mutable
x = 10                  // Reassign mutable
let { a, b } = point    // Destructuring
```

## Types

```vole
// Primitives
i8  i16  i32  i64  i128 // Signed integers (i32 default)
u8  u16  u32  u64       // Unsigned integers
f32  f64                // Floats (f64 default)
bool                    // true, false
string                  // "hello"
nil                     // Absence of value

// Compound
[T]                     // Array: [1, 2, 3]
T?                      // Optional: string?
A | B                   // Union: i32 | string
(A, B) -> R             // Function: (i32) -> bool
type                    // Type as value: let t: type = i32
```

## Strings

```vole
// String interpolation
let name = "Alice"
let age = 30
let msg = "Hello, {name}! You are {age} years old."

// Any expression works
let sum = "2 + 2 = {2 + 2}"
let len = "Length: {items.length}"

// Raw strings (no interpolation, no escapes)
let path = @"C:\Users\name"      // Literal backslashes
```

## Functions

```vole
func add(a: i32, b: i32) -> i32 {
    return a + b
}

func greet(name: string) {      // Nil return
    println("Hi " + name)
}

// Lambdas
let f = (x: i64) => x * 2           // Expression
let g = (x: i64) => { return x * 2 }    // Block body
let h: (i32) -> i32 = (x) => x      // Typed, inferred params
```

## Control Flow

```vole
// Conditionals
if x > 0 { } else if x < 0 { } else { }
let y = if x > 0 { "pos" } else { "neg" }

// Loops
while condition { }
for item in array { }
for i in 0..10 { }              // 0-9 (exclusive)
for i in 0..=10 { }             // 0-10 (inclusive)
break                           // Exit loop
continue                        // Next iteration

// Match - literals, types, wildcards
match x {
    1 => "one"                      // Literal
    "hello" => "greeting"           // String
    true => "yes"                   // Boolean
    i32 => "number"                 // Type
    string => "text"                // Type
    Point { x, y } => x + y         // Destructure
    _ if x > 10 => "big"            // Guard
    _ => "default"                  // Wildcard (must be last)
}
```

## Operators

```vole
// Arithmetic
+  -  *  /  %

// Compound Assignment
+=  -=  *=  /=  %=

// Comparison
==  !=  <  >  <=  >=

// Logical
&&  ||  !

// Bitwise
&  |  ^  ~  <<  >>

// Type
x is T                  // Type check
type_of(x)              // Get type

// Optional
x ?? default            // Null coalescing
x?.field                // Optional chaining
```

## Classes & Records

```vole
class Point {                   // Mutable
    x: i32
    y: i32
    func move(dx: i32) { self.x = self.x + dx }
}

record Point {                  // Immutable
    x: i32
    y: i32
    func sum() -> i32 { return self.x + self.y }
}

let p = Point { x: 10, y: 20 }
p.x                             // Field access
p.move(5)                       // Method call
```

## Interfaces

```vole
interface Named {
    func name() -> string
}

interface Greeter extends Named {
    func greet() { println("Hi " + self.name()) }  // Default
}

record Person implements Named {
    n: string
    func name() -> string { return self.n }
}

// Standalone implementation
implement Named for Point {
    func name() -> string { return "Point" }
}
```

## Generics

```vole
func identity<T>(x: T) -> T { return x }

record Box<T> {
    value: T
    func unwrap() -> T { return self.value }
}

// Union constraints
func double<T: i32 | f64>(x: T) -> T { return x + x }
```

## Error Handling

```vole
error NotFound {}
error Invalid { message: string }

func find(id: i32) -> fallible(Item, NotFound) {
    if id < 0 { raise NotFound {} }
    return items[id]
}

// Match with success/error patterns
let item = match find(42) {
    x => x,                              // implicit success pattern
    error NotFound => default_item,      // error pattern (keyword required)
    error Invalid { message } => handle(message)
}

// Explicit success keyword (optional)
match fallible_expr {
    success x => x + 1,
    error e => handle(e)
}

// Try propagation (in fallible functions only)
func process() -> fallible(i64, NotFound) {
    let x = try find(42)    // unwraps on success, propagates on error
    return x * 2
}
```

## Iterators

```vole
array
    .map((x) => x * 2)          // Transform
    .filter((x) => x > 0)       // Filter
    .take(5)                    // First 5
    .skip(2)                    // Skip 2
    .reduce(0, (a, x) => a + x) // Fold
    .sum()                      // Sum numbers
    .count()                    // Count elements
    .collect()                  // To array
```

## Testing

```vole
test "name" {
    assert(condition)
}

tests "group" {
    test "a" { }
    test "b" { }
}
```

## External Blocks (Native FFI)

```vole
// Inside implement block - add native methods to types
implement string {
    external("std:string") {
        func "string_length" as length() -> i64
        func "string_contains" as contains(needle: string) -> bool
    }
}

// Usage
"hello".length()        // 5
"hello".contains("ell") // true
```

## Modules

```vole
let math = import "std:math"

math.sqrt(16.0)     // 4.0
math.sin(math.PI)   // ~0.0
math.pow(2.0, 10.0) // 1024.0
```

## Built-in Functions

```vole
print(x)        // Print without newline
println(x)      // Print with newline
assert(cond)    // Assert condition
type_of(x)      // Get type of value
```

## CLI

```bash
vole run file.vole          # Run program
vole check file.vole        # Type-check only
vole test dir/              # Run tests
vole fmt file.vole          # Format code (WIP)
```

## Program Structure

```vole
// Statements are separated by newlines (no semicolons)
let x = 1
let y = 2

// Top-level declarations
let VERSION = "1.0"
func helper() { }
class Foo { }
record Bar { }
interface Baz { }
error Qux { }
tests { }

// Entry point (optional)
func main() { }
```
