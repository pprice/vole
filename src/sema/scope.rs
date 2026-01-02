// src/sema/scope.rs

use crate::frontend::Symbol;
use crate::sema::Type;
use std::collections::HashMap;

#[derive(Debug)]
pub struct Variable {
    pub ty: Type,
    pub mutable: bool,
}

#[derive(Debug, Default)]
pub struct Scope {
    variables: HashMap<Symbol, Variable>,
    parent: Option<Box<Scope>>,
}

impl Scope {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_parent(parent: Scope) -> Self {
        Self {
            variables: HashMap::new(),
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
