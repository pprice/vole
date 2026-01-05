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
| [Control Flow](control-flow.md) | if/else, while, for, match, break/continue |
| [Operators](operators.md) | Arithmetic, comparison, logical, bitwise, type ops |

### Data Structures

| Doc | Description |
|-----|-------------|
| [Classes & Records](classes-records.md) | Mutable classes, immutable records, methods |
| [Interfaces](interfaces.md) | Contracts, structural typing, default methods |
| [Generics](generics.md) | Type parameters, constraints |

### Advanced Features

| Doc | Description |
|-----|-------------|
| [Error Handling](error-handling.md) | Typed errors, fallible functions, match patterns |
| [Iterators](iterators.md) | Lazy sequences: map, filter, reduce, collect |
| [Modules](modules.md) | Standard library imports (std:math) |
| [Testing](testing.md) | Test blocks, assertions, test organization |

## Example

```vole
record Person {
    name: string
    age: i32

    func greet() -> string {
        return "Hi, I'm {self.name}!"
    }
}

func main() {
    let people = [
        Person { name: "Alice", age: 30 },
        Person { name: "Bob", age: 25 }
    ]

    let greetings = people
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
| Classes, records, interfaces | Implemented |
| Generics (union constraints) | Implemented |
| Error handling (fallible, try, match patterns) | Implemented |
| External blocks (native FFI) | Implemented |
| Iterators (map, filter, reduce, etc.) | Implemented |
| Testing (test blocks, assert) | Implemented |
| Returned closures (currying) | WIP |
| Modules / imports | Implemented |
| Standard library (std:math) | Implemented |
| Coroutines / generators | Not yet |
| Type aliases | Not yet |
| Structural generic constraints | Not yet |
