# Vole

A fast little scripting language, with fancy types.

Vole is a statically typed, JIT-compiled language built on [Cranelift](https://cranelift.dev/). It has structural typing, generics, first-class functions, iterators, generators, async tasks, and a module system with a standard library.

⚠️⚠️⚠️ This is an experimental project exploring what it looks like to build a programming language primarily through collaboration with AI coding assistants (specifically [Claude Code](https://docs.anthropic.com/en/docs/claude-code) and [Codex](https://chatgpt.com/codex)). The vast majority of the code has been written by and reviewed by coding assistants, with human direction for features and guardrails.

## Quick look

```vole
interface Scorable {
    func score() -> i64
    func label() -> string
}

class Player {
    name: string,
    wins: i64,
    losses: i64,
}

extend Player with Scorable {
    func score() -> i64    { return self.wins * 3 - self.losses }
    func label() -> string { return "{self.name}: {self.score()} pts" }
}

// Works with any type that implements Scorable
func leaderboard<T: Scorable>(players: [T]) -> [string] {
    return players
        .filter(p => p.score() > 0)
        .map(p => p.label())
        .collect()
}

func main() {
    let squad = [
        Player { name: "Alice", wins: 10, losses: 2 },
        Player { name: "Bob",   wins: 4,  losses: 8 },
        Player { name: "Carol", wins: 7,  losses: 1 },
    ]

    for line in leaderboard(squad) {
        println(line)
    }
}
```

## Install

See [docs/install.md](docs/install.md) for download and build instructions.

## Documentation

The language documentation lives in [docs/language/](docs/language/):

- [Cheatsheet](docs/language/cheatsheet.md) -- single-page syntax reference
- [Types](docs/language/types.md) -- primitives, arrays, optionals, unions
- [Functions](docs/language/functions.md) -- lambdas, closures, higher-order
- [Classes & Records](docs/language/classes-records.md) -- methods, statics
- [Interfaces](docs/language/interfaces.md) -- structural typing, constraints
- [Generics](docs/language/generics.md) -- type parameters
- [Error Handling](docs/language/error-handling.md) -- typed errors, fallible functions
- [Iterators](docs/language/iterators.md) -- lazy sequences, generators
- [Modules](docs/language/modules.md) -- imports, standard library
- [Concurrency](docs/language/concurrency.md) -- async tasks, channels
- [Testing](docs/language/testing.md) -- test blocks, assertions

## Building from source

Requires [Rust](https://rustup.rs/) (stable) and [just](https://github.com/casey/just).

```bash
git clone https://github.com/pprice/vole.git
cd vole
cargo build --release
./target/release/vole run hello.vole
```

## License

[MIT](LICENSE)
