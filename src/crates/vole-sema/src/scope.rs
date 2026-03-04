// src/sema/scope.rs

use crate::type_arena::TypeId;
use core::hash::BuildHasher;
use hashbrown::hash_map::RawEntryMut;
use rustc_hash::FxBuildHasher;
use vole_frontend::{Span, Symbol};

type VariableMap = hashbrown::HashMap<Symbol, Variable, FxBuildHasher>;

#[derive(Debug, Clone)]
pub struct Variable {
    pub ty: TypeId,
    pub mutable: bool,
    pub declaration_span: Span,
}

/// Undo entry for restoring state when a scope is popped.
///
/// Each entry stores a pre-computed hash so that the undo loop can skip
/// re-hashing the symbol (the hash computation was the dominant cost in
/// the previous implementation).
#[derive(Debug)]
enum UndoEntry {
    /// Variable was newly inserted; remove it on pop.
    Remove(Symbol, u64),
    /// Variable shadowed a previous value; restore it on pop.
    Restore(Symbol, u64, Variable),
}

/// Flat scope: a single hash map for O(1) lookups, with an undo stack
/// for scope push/pop. This avoids the linked-list parent chain walk
/// that shows up as a hotspot in the analyzer.
#[derive(Debug)]
pub struct Scope {
    /// All variables visible in the current scope (flattened).
    variables: VariableMap,
    /// Stack of undo entries per scope level. Each `push_scope` adds a new Vec.
    undo_stack: Vec<Vec<UndoEntry>>,
}

impl Default for Scope {
    fn default() -> Self {
        Self {
            variables: VariableMap::with_hasher(FxBuildHasher),
            undo_stack: Vec::new(),
        }
    }
}

/// Compute the FxHash for a symbol, matching what the hashmap would compute.
#[inline(always)]
fn hash_symbol(sym: &Symbol) -> u64 {
    FxBuildHasher.hash_one(sym)
}

impl Scope {
    pub fn with_parent(parent: Scope) -> Self {
        let mut s = parent;
        s.undo_stack.push(Vec::new());
        s
    }

    pub fn define(&mut self, name: Symbol, var: Variable) {
        let hash = hash_symbol(&name);
        let prev = match self
            .variables
            .raw_entry_mut()
            .from_key_hashed_nocheck(hash, &name)
        {
            RawEntryMut::Occupied(mut entry) => {
                let old = std::mem::replace(entry.get_mut(), var);
                Some(old)
            }
            RawEntryMut::Vacant(entry) => {
                entry.insert_hashed_nocheck(hash, name, var);
                None
            }
        };
        if let Some(undo_level) = self.undo_stack.last_mut() {
            match prev {
                Some(old) => undo_level.push(UndoEntry::Restore(name, hash, old)),
                None => undo_level.push(UndoEntry::Remove(name, hash)),
            }
        }
        // If undo_stack is empty, we're at the root scope — no undo needed.
    }

    pub fn get(&self, name: Symbol) -> Option<&Variable> {
        self.variables.get(&name)
    }

    pub fn into_parent(mut self) -> Option<Scope> {
        let undo_entries = self.undo_stack.pop()?;
        // Undo in reverse order to correctly handle multiple defines of the same
        // symbol within one scope level.
        for entry in undo_entries.into_iter().rev() {
            match entry {
                UndoEntry::Remove(sym, hash) => {
                    // Use pre-computed hash to skip re-hashing during remove.
                    if let RawEntryMut::Occupied(entry) = self
                        .variables
                        .raw_entry_mut()
                        .from_key_hashed_nocheck(hash, &sym)
                    {
                        entry.remove();
                    }
                }
                UndoEntry::Restore(sym, hash, old_var) => {
                    // Use pre-computed hash to skip re-hashing during restore.
                    match self
                        .variables
                        .raw_entry_mut()
                        .from_key_hashed_nocheck(hash, &sym)
                    {
                        RawEntryMut::Occupied(mut entry) => {
                            *entry.get_mut() = old_var;
                        }
                        RawEntryMut::Vacant(entry) => {
                            // Should not happen in correct usage, but handle gracefully.
                            entry.insert_hashed_nocheck(hash, sym, old_var);
                        }
                    }
                }
            }
        }
        Some(self)
    }
}
