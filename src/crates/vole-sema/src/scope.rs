// src/sema/scope.rs

use crate::type_arena::TypeId;
use rustc_hash::FxHashMap;
use vole_frontend::{Span, Symbol};

#[derive(Debug, Clone)]
pub struct Variable {
    pub ty: TypeId,
    pub mutable: bool,
    pub declaration_span: Span,
}

/// Undo entry for restoring state when a scope is popped.
#[derive(Debug)]
enum UndoEntry {
    /// Variable was newly inserted; remove it on pop.
    Remove(Symbol),
    /// Variable shadowed a previous value; restore it on pop.
    Restore(Symbol, Variable),
}

/// Flat scope: a single hash map for O(1) lookups, with an undo stack
/// for scope push/pop. This avoids the linked-list parent chain walk
/// that shows up as a hotspot in the analyzer.
#[derive(Debug, Default)]
pub struct Scope {
    /// All variables visible in the current scope (flattened).
    variables: FxHashMap<Symbol, Variable>,
    /// Stack of undo entries per scope level. Each `push_scope` adds a new Vec.
    undo_stack: Vec<Vec<UndoEntry>>,
}

impl Scope {
    pub fn with_parent(parent: Scope) -> Self {
        let mut s = parent;
        s.undo_stack.push(Vec::new());
        s
    }

    pub fn define(&mut self, name: Symbol, var: Variable) {
        let prev = self.variables.insert(name, var);
        if let Some(undo_level) = self.undo_stack.last_mut() {
            match prev {
                Some(old) => undo_level.push(UndoEntry::Restore(name, old)),
                None => undo_level.push(UndoEntry::Remove(name)),
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
                UndoEntry::Remove(sym) => {
                    self.variables.remove(&sym);
                }
                UndoEntry::Restore(sym, old_var) => {
                    self.variables.insert(sym, old_var);
                }
            }
        }
        Some(self)
    }
}
