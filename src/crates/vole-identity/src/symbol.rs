// symbol.rs
//
// Unique identifier for interned strings.

/// Unique identifier for symbols (interned strings)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// The unknown/fallback symbol (index 0).
    pub const UNKNOWN: Self = Self(0);

    /// Create a Symbol from a raw index. Only the interner should use this.
    pub(crate) fn new(index: u32) -> Self {
        Self(index)
    }

    /// Return the underlying index.
    pub fn index(self) -> u32 {
        self.0
    }

    /// Create a synthetic symbol with a high-bit index that won't collide
    /// with user symbols. Used for synthetic type parameters.
    pub fn synthetic(offset: u32) -> Self {
        Self(0x8000_0000 + offset)
    }

    /// Create a Symbol with an arbitrary index in test code.
    #[cfg(any(test, feature = "testing"))]
    pub fn new_for_test(index: u32) -> Self {
        Self(index)
    }
}
