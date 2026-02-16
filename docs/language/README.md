# Vole Language Documentation

Vole is a statically typed, compiled language with JIT compilation via Cranelift. It features structural typing, generics, first-class functions, and a robust error handling system.

## Quick Start

```vole
func main() {
    println("Hello, Vole!")
}
```

Run with:
```bash
vole run hello.vole
```

## Documentation

### Core Language

| Doc | Description |
|-----|-------------|
| [Cheatsheet](cheatsheet.md) | Single-page syntax reference |
| [Types](types.md) | Type system: primitives, arrays, optionals, unions |
| [Variables](variables.md) | let/let mut, scoping, destructuring |
| [Functions](functions.md) | Functions, lambdas, closures, higher-order |
| [Control Flow](control-flow.md) | if/else, while, for, match, when, break/continue |
| [Operators](operators.md) | Arithmetic, comparison, logical, bitwise, type ops |

### Data Structures

| Doc | Description |
|-----|-------------|
| [Classes & Records](classes-records.md) | Mutable classes, structs, methods, statics |
| [Interfaces](interfaces.md) | Contracts, structural typing, default methods |
| [Generics](generics.md) | Type parameters, constraints |

### Advanced Features

| Doc | Description |
|-----|-------------|
| [Error Handling](error-handling.md) | Typed errors, fallible functions, match patterns |
| [Iterators](iterators.md) | Lazy sequences: map, filter, reduce, generators |
| [Modules](modules.md) | Import system, standard library, destructured imports |
| [Testing](testing.md) | Test blocks, assertions, test organization |

## Example

```vole
class Person {
    name: string,
    age: i64,

    func greet() -> string {
        return "Hi, I'm {self.name}!"
    }
}

func main() {
    let people = [
        Person { name: "Alice", age: 30 },
        Person { name: "Bob", age: 25 },
    ]

    let greetings = people.iter()
        .filter((p) => p.age >= 18)
        .map((p) => p.greet())
        .collect()

    for greeting in greetings {
        println(greeting)
    }
}
```

## Feature Status

| Feature | Status |
|---------|--------|
| Core types (i8-i128, u8-u64, f32/f64, bool, string) | Implemented |
| Arrays, optionals, unions | Implemented |
| Functions, lambdas, closures | Implemented |
| Currying / returned lambdas | Implemented |
| Classes, structs, interfaces | Implemented |
| Generics (union constraints) | Implemented |
| Error handling (fallible, try, match patterns) | Implemented |
| External blocks (native FFI) | Implemented |
| Iterators (map, filter, reduce, etc.) | Implemented |
| Generators (yield, infinite sequences) | Implemented |
| Functional interface calls | Implemented |
| Raw strings (@"...") | Implemented |
| Testing (test blocks, assert) | Implemented |
| Modules / imports | Implemented |
| Destructured imports | Implemented |
| Standard library (std:math, std:time, etc.) | Implemented |
| Async tasks and channels (std:task) | Implemented |
| Type aliases | Not yet |
| Structural generic constraints | Not yet |
