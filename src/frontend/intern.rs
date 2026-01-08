// src/frontend/intern.rs

use crate::frontend::ast::Symbol;
use std::collections::HashMap;

/// Interns strings to unique Symbol IDs
#[derive(Debug, Default, Clone)]
pub struct Interner {
    map: HashMap<String, Symbol>,
    strings: Vec<String>,
}

impl Interner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(&sym) = self.map.get(s) {
            return sym;
        }

        let sym = Symbol(self.strings.len() as u32);
        self.strings.push(s.to_string());
        self.map.insert(s.to_string(), sym);
        sym
    }

    pub fn resolve(&self, sym: Symbol) -> &str {
        &self.strings[sym.0 as usize]
    }

    /// Look up a string to get its symbol, if it has been interned.
    /// Returns None if the string hasn't been interned.
    pub fn lookup(&self, s: &str) -> Option<Symbol> {
        self.map.get(s).copied()
    }

    pub fn intern_with_prefix(&mut self, prefix: &str, base: Symbol) -> Symbol {
        let name = format!("{}{}", prefix, self.resolve(base));
        self.intern(&name)
    }

    pub fn seed_builtin_symbols(&mut self) {
        for name in [
            "i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "f32", "f64", "bool",
            "string", "Iterator", "Iterable",
        ] {
            let _ = self.intern(name);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_returns_same_symbol() {
        let mut interner = Interner::new();
        let s1 = interner.intern("hello");
        let s2 = interner.intern("hello");
        let s3 = interner.intern("world");

        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
    }

    #[test]
    fn resolve_returns_original_string() {
        let mut interner = Interner::new();
        let sym = interner.intern("test");
        assert_eq!(interner.resolve(sym), "test");
    }
}
