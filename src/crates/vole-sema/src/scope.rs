// src/sema/scope.rs

use crate::type_arena::TypeId;
use rustc_hash::FxHashMap;
use vole_frontend::{Span, Symbol};

#[derive(Debug)]
pub struct Variable {
    pub ty: TypeId,
    pub mutable: bool,
    pub declaration_span: Span,
}

#[derive(Debug, Default)]
pub struct Scope {
    variables: FxHashMap<Symbol, Variable>,
    parent: Option<Box<Scope>>,
}

impl Scope {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_parent(parent: Scope) -> Self {
        Self {
            variables: FxHashMap::default(),
            parent: Some(Box::new(parent)),
        }
    }

    pub fn define(&mut self, name: Symbol, var: Variable) {
        self.variables.insert(name, var);
    }

    pub fn get(&self, name: Symbol) -> Option<&Variable> {
        self.variables
            .get(&name)
            .or_else(|| self.parent.as_ref().and_then(|p| p.get(name)))
    }

    pub fn into_parent(self) -> Option<Scope> {
        self.parent.map(|b| *b)
    }
}
