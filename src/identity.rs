// src/identity.rs
//
// Shared name interning for fully-qualified item identities.

use std::collections::HashMap;

use crate::frontend::{Interner, Symbol};

mod namer;
pub use namer::{Namer, NamerLookup};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u32);

impl ModuleId {
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NameId(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
enum NameSegment {
    Symbol(Symbol),
    Raw(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualifiedName {
    module: ModuleId,
    segments: Vec<NameSegment>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct NameKey {
    module: ModuleId,
    segments: Vec<NameKeySegment>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum NameKeySegment {
    Symbol(Symbol),
    Raw(String),
}

#[derive(Debug, Clone)]
pub struct NameTable {
    modules: Vec<String>,
    module_lookup: HashMap<String, ModuleId>,
    names: Vec<QualifiedName>,
    name_lookup: HashMap<NameKey, NameId>,
    main_module: ModuleId,
}

impl NameTable {
    pub fn new() -> Self {
        let mut table = Self {
            modules: Vec::new(),
            module_lookup: HashMap::new(),
            names: Vec::new(),
            name_lookup: HashMap::new(),
            main_module: ModuleId(0),
        };
        let main_module = table.module_id("main");
        table.main_module = main_module;
        let _ = table.module_id("");
        table
    }

    pub fn main_module(&self) -> ModuleId {
        self.main_module
    }

    pub fn module_id(&mut self, path: &str) -> ModuleId {
        if let Some(id) = self.module_lookup.get(path) {
            return *id;
        }
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(path.to_string());
        self.module_lookup.insert(path.to_string(), id);
        id
    }

    pub fn module_id_if_known(&self, path: &str) -> Option<ModuleId> {
        self.module_lookup.get(path).copied()
    }

    pub fn builtin_module(&mut self) -> ModuleId {
        self.module_id("")
    }

    pub fn builtin_module_id(&self) -> Option<ModuleId> {
        self.module_id_if_known("")
    }

    pub fn module_path(&self, module: ModuleId) -> &str {
        &self.modules[module.0 as usize]
    }

    pub fn intern(&mut self, module: ModuleId, segments: &[Symbol]) -> NameId {
        let key = NameKey {
            module,
            segments: segments
                .iter()
                .copied()
                .map(NameKeySegment::Symbol)
                .collect(),
        };
        if let Some(id) = self.name_lookup.get(&key) {
            return *id;
        }
        let id = NameId(self.names.len() as u32);
        self.names.push(QualifiedName {
            module,
            segments: segments.iter().copied().map(NameSegment::Symbol).collect(),
        });
        self.name_lookup.insert(key, id);
        id
    }

    pub fn intern_raw(&mut self, module: ModuleId, segments: &[&str]) -> NameId {
        let key = NameKey {
            module,
            segments: segments
                .iter()
                .map(|segment| NameKeySegment::Raw((*segment).to_string()))
                .collect(),
        };
        if let Some(id) = self.name_lookup.get(&key) {
            return *id;
        }
        let id = NameId(self.names.len() as u32);
        self.names.push(QualifiedName {
            module,
            segments: segments
                .iter()
                .map(|segment| NameSegment::Raw((*segment).to_string()))
                .collect(),
        });
        self.name_lookup.insert(key, id);
        id
    }

    pub fn intern_indexed_raw(&mut self, module: ModuleId, prefix: &str, index: usize) -> NameId {
        let name = format!("{}{}", prefix, index);
        self.intern_raw(module, &[name.as_str()])
    }

    pub fn name_id(&self, module: ModuleId, segments: &[Symbol]) -> Option<NameId> {
        let key = NameKey {
            module,
            segments: segments
                .iter()
                .copied()
                .map(NameKeySegment::Symbol)
                .collect(),
        };
        self.name_lookup.get(&key).copied()
    }

    pub fn name_id_raw(&self, module: ModuleId, segments: &[&str]) -> Option<NameId> {
        let key = NameKey {
            module,
            segments: segments
                .iter()
                .map(|segment| NameKeySegment::Raw((*segment).to_string()))
                .collect(),
        };
        self.name_lookup.get(&key).copied()
    }

    pub fn name(&self, id: NameId) -> &QualifiedName {
        &self.names[id.0 as usize]
    }

    pub fn module_of(&self, id: NameId) -> ModuleId {
        self.name(id).module
    }

    pub fn intern_with_symbol(&mut self, prefix: NameId, symbol: Symbol) -> NameId {
        let name = self.name(prefix);
        let mut segments = name.segments.clone();
        segments.push(NameSegment::Symbol(symbol));
        let key = NameKey {
            module: name.module,
            segments: segments
                .iter()
                .map(|segment| match segment {
                    NameSegment::Symbol(sym) => NameKeySegment::Symbol(*sym),
                    NameSegment::Raw(raw) => NameKeySegment::Raw(raw.clone()),
                })
                .collect(),
        };
        if let Some(id) = self.name_lookup.get(&key) {
            return *id;
        }
        let id = NameId(self.names.len() as u32);
        self.names.push(QualifiedName {
            module: name.module,
            segments,
        });
        self.name_lookup.insert(key, id);
        id
    }

    pub fn display(&self, id: NameId, interner: &Interner) -> String {
        let name = self.name(id);
        let module = self.module_path(name.module);
        let mut out = String::new();
        if !module.is_empty() {
            out.push_str(module);
        }
        for (idx, segment) in name.segments.iter().enumerate() {
            if !out.is_empty() || idx > 0 {
                out.push_str("::");
            }
            match segment {
                NameSegment::Symbol(sym) => out.push_str(interner.resolve(*sym)),
                NameSegment::Raw(segment) => out.push_str(segment),
            }
        }
        out
    }

    pub fn last_segment_str(&self, id: NameId, interner: &Interner) -> Option<String> {
        let name = self.name(id);
        name.segments.last().map(|segment| match segment {
            NameSegment::Symbol(sym) => interner.resolve(*sym).to_string(),
            NameSegment::Raw(raw) => raw.clone(),
        })
    }

    pub fn last_symbol(&self, id: NameId) -> Option<Symbol> {
        let name = self.name(id);
        name.segments
            .iter()
            .rev()
            .find_map(|segment| match segment {
                NameSegment::Symbol(sym) => Some(*sym),
                NameSegment::Raw(_) => None,
            })
    }
}

impl Default for NameTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Interner;

    #[test]
    fn name_table_displays_module_and_segments() {
        let mut interner = Interner::new();
        let foo = interner.intern("foo");
        let bar = interner.intern("bar");

        let mut names = NameTable::new();
        let module = names.module_id("std:math");
        let name_id = names.intern(module, &[foo, bar]);

        assert_eq!(names.display(name_id, &interner), "std:math::foo::bar");
    }
}
