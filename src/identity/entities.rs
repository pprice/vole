//! First-class identity types for language entities.
//!
//! These types provide type-safe identifiers for types, methods, fields, and functions,
//! eliminating string-based lookups and preventing mix-ups between different entity kinds.

/// Identity for a type definition (interface, class, record, error type, primitive)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeDefId(u32);

impl TypeDefId {
    pub(crate) fn new(index: u32) -> Self {
        Self(index)
    }

    pub fn index(self) -> u32 {
        self.0
    }
}

/// Identity for a method (always has a defining type)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MethodId(u32);

impl MethodId {
    pub(crate) fn new(index: u32) -> Self {
        Self(index)
    }

    pub fn index(self) -> u32 {
        self.0
    }
}

/// Identity for a field (always has a defining type)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FieldId(u32);

impl FieldId {
    pub(crate) fn new(index: u32) -> Self {
        Self(index)
    }

    pub fn index(self) -> u32 {
        self.0
    }
}

/// Identity for a free function (belongs to a module)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionId(u32);

impl FunctionId {
    pub(crate) fn new(index: u32) -> Self {
        Self(index)
    }

    pub fn index(self) -> u32 {
        self.0
    }
}
