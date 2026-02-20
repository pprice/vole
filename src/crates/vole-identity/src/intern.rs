// intern.rs
//
// String interning for Symbol IDs.

use std::hash::BuildHasher;

use crate::Symbol;
use rustc_hash::FxBuildHasher;

/// Interns strings to unique Symbol IDs
#[derive(Debug, Clone)]
pub struct Interner {
    map: hashbrown::HashMap<String, Symbol, FxBuildHasher>,
    strings: Vec<String>,
}

impl Default for Interner {
    fn default() -> Self {
        Self {
            map: hashbrown::HashMap::with_hasher(FxBuildHasher),
            strings: Vec::new(),
        }
    }
}

impl Interner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, s: &str) -> Symbol {
        use hashbrown::hash_map::RawEntryMut;

        // Hash once, reuse for both lookup and insert.
        let hash = self.map.hasher().hash_one(s);

        let entry = self.map.raw_entry_mut().from_hash(hash, |k| k == s);

        match entry {
            RawEntryMut::Occupied(e) => *e.get(),
            RawEntryMut::Vacant(e) => {
                let sym = Symbol::new(self.strings.len() as u32);
                let owned = s.to_string();
                self.strings.push(owned.clone());
                e.insert_hashed_nocheck(hash, owned, sym);
                sym
            }
        }
    }

    pub fn resolve(&self, sym: Symbol) -> &str {
        &self.strings[sym.index() as usize]
    }

    /// Returns the number of interned strings.
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Returns true if no strings have been interned.
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
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
            "string", "range", "array", "Iterator", "Iterable",
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
