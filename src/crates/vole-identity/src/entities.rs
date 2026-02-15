//! First-class identity types for language entities.
//!
//! These types provide type-safe identifiers for types, methods, fields, and functions,
//! eliminating string-based lookups and preventing mix-ups between different entity kinds.

macro_rules! define_entity_id {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        $vis struct $name(u32);

        impl $name {
            pub fn new(index: u32) -> Self {
                Self(index)
            }

            pub fn index(self) -> u32 {
                self.0
            }
        }
    };
}

define_entity_id! {
    /// Identity for a type definition (interface, class, struct, error type, primitive)
    pub struct TypeDefId;
}

define_entity_id! {
    /// Identity for a method (always has a defining type)
    pub struct MethodId;
}

define_entity_id! {
    /// Identity for a field (always has a defining type)
    pub struct FieldId;
}

define_entity_id! {
    /// Identity for a free function (belongs to a module)
    pub struct FunctionId;
}

define_entity_id! {
    /// Identity for a global variable (module-level let/var)
    pub struct GlobalId;
}

define_entity_id! {
    /// Identity for a type parameter (e.g., T in `func identity<T>(x: T) -> T`)
    /// Distinct from NameId to avoid confusion with inference variables.
    pub struct TypeParamId;
}
