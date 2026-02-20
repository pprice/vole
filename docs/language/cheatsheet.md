# Vole Cheatsheet

Single-page syntax reference.

## Variables

```vole
tests {
    test "variables" {
        let x = 42              // Immutable, inferred type
        let y: i64 = 42         // Immutable, explicit type
        var z = 0           // Mutable
        z = 10                  // Reassign mutable
        assert(x == 42)
        assert(y == 42)
        assert(z == 10)
    }
}
```

## Types

```vole,ignore
// Primitives
i8  i16  i32  i64  i128 // Signed integers (i64 default)
u8  u16  u32  u64       // Unsigned integers
f32  f64                // Floats (f64 default)
bool                    // true, false
string                  // "hello"
nil                     // Absence of value
Done                    // Iterator termination sentinel

// Numeric literals
42                      // Decimal integer (i64)
0xFF                    // Hex integer
0b1010                  // Binary integer
3.14                    // Float (f64)
1.5e-3                  // Scientific notation (float)
1_000_000               // Underscore separators
42_u8                   // Typed suffix: u8
3.14_f32                // Typed suffix: f32

// Compound
[T]                     // Array: [1, 2, 3]
T?                      // Optional: string?
A | B                   // Union: i64 | string
(A, B) -> R             // Function: (i64) -> bool
Iterator<T>             // Iterator: produces values of type T
type                    // Type as value: let t: type = i64
```

## Strings

```vole
tests {
    test "strings" {
        let name = "Alice"
        let age = 30
        let msg = "Hello, {name}! You are {age} years old."
        assert(msg == "Hello, Alice! You are 30 years old.")

        let sum = "2 + 2 = {2 + 2}"
        assert(sum == "2 + 2 = 4")

        // Raw strings (no interpolation, no escapes)
        let path = @"C:\Users\name"
        assert(path.length() == 13)
    }
}
```

## Functions

```vole
func add(a: i64, b: i64) -> i64 {
    return a + b
}

func greet(name: string) {
    println("Hi " + name)
}

tests {
    test "functions" {
        assert(add(2, 3) == 5)

        // Lambdas
        let f = (x: i64) => x * 2
        let g = (x: i64) => { return x * 2 }
        assert(f(5) == 10)
        assert(g(5) == 10)
    }
}
```

## Control Flow

```vole
tests {
    test "if else" {
        let x = 5
        var result = ""
        if x > 0 {
            result = "pos"
        } else {
            result = "neg"
        }
        assert(result == "pos")
    }

    test "when expression" {
        let x = 5
        let label = when {
            x > 0 => "pos"
            _ => "neg"
        }
        assert(label == "pos")
    }

    test "loops" {
        var sum = 0
        for i in 0..5 {
            sum = sum + i
        }
        assert(sum == 10)
    }
}
```

Match supports literals, types, destructuring, and guards:

```vole,ignore
match x {
    1 => "one"                      // Literal
    "hello" => "greeting"           // String
    true => "yes"                   // Boolean
    i64 => "number"                 // Type
    string => "text"                // Type
    Point { x, y } => x + y        // Destructure
    _ if x > 10 => "big"           // Guard
    _ => "default"                  // Wildcard (must be last)
}
```

## Operators

```vole,ignore
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
x ?? default            // Null coalescing
x?.field                // Optional chaining
```

## Classes

```vole
class Point {
    x: i64,
    y: i64,

    func move_x(dx: i64) {
        self.x = self.x + dx
    }

    func sum() -> i64 {
        return self.x + self.y
    }
}

tests {
    test "class usage" {
        let p = Point { x: 10, y: 20 }
        assert(p.x == 10)
        assert(p.sum() == 30)
        p.move_x(5)
        assert(p.x == 15)
    }
}
```

## Interfaces

```vole
interface Named {
    func name() -> string
}

class Person implements Named {
    n: string,

    func name() -> string {
        return self.n
    }
}

tests {
    test "interface" {
        let p = Person { n: "Alice" }
        assert(p.name() == "Alice")
    }
}
```

## Generics

```vole
func identity<T>(x: T) -> T {
    return x
}

class Box<T> {
    value: T,

    func unwrap() -> T {
        return self.value
    }
}

tests {
    test "generics" {
        assert(identity(42) == 42)
        assert(identity("hello") == "hello")
        let b = Box { value: 99 }
        assert(b.unwrap() == 99)
    }
}
```

## Error Handling

```vole
error NotFound {}
error Invalid { message: string }

func find(id: i64) -> fallible(i64, NotFound) {
    if id < 0 {
        raise NotFound {}
    }
    return id * 10
}

tests {
    test "error handling" {
        let item = match find(42) {
            x => x
            error NotFound => -1
        }
        assert(item == 420)

        let missing = match find(-1) {
            x => x
            error NotFound => -1
        }
        assert(missing == -1)
    }
}
```

Try propagation (in fallible functions only):

```vole,ignore
func process() -> fallible(i64, NotFound) {
    let x = try find(42)    // unwraps on success, propagates on error
    return x * 2
}
```

## Iterators

Arrays provide `.iter()` to get an iterator. Iterators are lazy and support chaining.

**Transformers (lazy, return iterators):**
- `.map(fn)` -- transform each element
- `.filter(fn)` -- keep if predicate true
- `.take(n)` -- first n elements
- `.skip(n)` -- skip first n
- `.chain(iter)` -- concatenate two iterators
- `.enumerate()` -- yield (index, value) pairs
- `.zip(iter)` -- combine two iterators into pairs
- `.flatten()` -- flatten nested iterators
- `.flat_map(fn)` -- map then flatten
- `.chunks(n)` -- non-overlapping chunks
- `.windows(n)` -- sliding windows
- `.reverse()` -- reverse order
- `.sorted()` -- sort elements
- `.unique()` -- remove consecutive duplicates

**Consumers (eager, materialize results):**
- `.collect()` -- to array
- `.count()` -- count elements
- `.sum()` -- sum numeric elements
- `.reduce(init, fn)` -- fold to single value
- `.for_each(fn)` -- execute side effects
- `.find(fn)` -- first match (or nil)
- `.first()` -- first element (or nil)
- `.last()` -- last element (or nil)
- `.any(fn)` -- true if any matches
- `.all(fn)` -- true if all match

```vole
tests {
    test "iterator chaining" {
        let result = [1, 2, 3, 4, 5].iter()
            .filter((x) => x % 2 == 0)
            .map((x) => x * 10)
            .collect()
        assert(result.length() == 2)
        assert(result[0] == 20)
        assert(result[1] == 40)
    }
}
```

## Generators

Functions containing `yield` are generators. They return `Iterator<T>`.

```vole
func counter(max: i64) -> Iterator<i64> {
    var i = 0
    while i < max {
        yield i
        i = i + 1
    }
}

tests {
    test "generator" {
        let result = counter(3).collect()
        assert(result.length() == 3)
        assert(result[0] == 0)
        assert(result[1] == 1)
        assert(result[2] == 2)
    }
}
```

## Testing

```vole
tests "group name" {
    test "a" {
        assert(1 + 1 == 2)
    }

    test "b" => assert(true)
}
```

## Modules

```vole
let math = import "std:math"

tests {
    test "modules" {
        assert(math.sqrt(16.0) == 4.0)
        assert(math.PI > 3.14)
    }
}
```

Destructured imports:

```vole
tests {
    test "destructured" {
        let { sqrt, PI } = import "std:math"
        assert(sqrt(4.0) == 2.0)
        assert(PI > 3.14)
    }
}
```

## Built-in Functions

```vole,ignore
print(x)        // Print without newline
println(x)      // Print with newline
assert(cond)    // Assert condition
```

## CLI

```bash
vole run file.vole          # Run program
vole check file.vole        # Type-check only
vole test dir/              # Run tests
```

## Program Structure

```vole,ignore
// Statements are separated by newlines (no semicolons)
let x = 1
let y = 2

// Top-level declarations
let VERSION = "1.0"
func helper() { }
class Foo { }
struct Bar { x: i64 }
interface Baz { }
error Qux { }
tests { }

// Entry point (optional)
func main() { }
```
