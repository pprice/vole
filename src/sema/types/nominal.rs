// src/sema/types/nominal.rs
//
// Nominal type enum consolidating Class, Record, Interface, and Error types.
// These are types that have a type definition identity (TypeDefId) and optional
// type arguments for generic instantiation.

use std::sync::Arc;

use smallvec::SmallVec;

use crate::identity::{NameId, TypeDefId};
use crate::sema::type_arena::{TypeId, TypeIdVec};

use super::LegacyType;

/// SmallVec for interface extends list - most interfaces extend 0-2 parents
pub type ExtendsVec = SmallVec<[TypeDefId; 2]>;

/// Nominal types - types with a definition identity in the EntityRegistry.
/// All nominal types have a TypeDefId for looking up their definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NominalType {
    /// Class instance type
    Class(ClassType),
    /// Record instance type
    Record(RecordType),
    /// Interface type
    Interface(InterfaceType),
    /// Error type (e.g., DivByZero)
    Error(ErrorTypeInfo),
}

impl NominalType {
    /// Get the TypeDefId for this nominal type.
    pub fn type_def_id(&self) -> TypeDefId {
        match self {
            NominalType::Class(c) => c.type_def_id,
            NominalType::Record(r) => r.type_def_id,
            NominalType::Interface(i) => i.type_def_id,
            NominalType::Error(e) => e.type_def_id,
        }
    }

    /// Get type arguments as TypeIds for arena-based substitution.
    /// Returns empty slice for errors.
    pub fn type_args_id(&self) -> &[TypeId] {
        match self {
            NominalType::Class(c) => &c.type_args_id,
            NominalType::Record(r) => &r.type_args_id,
            NominalType::Interface(i) => &i.type_args_id,
            NominalType::Error(_) => &[],
        }
    }

    /// Check if this is a class type.
    pub fn is_class(&self) -> bool {
        matches!(self, NominalType::Class(_))
    }

    /// Check if this is a record type.
    pub fn is_record(&self) -> bool {
        matches!(self, NominalType::Record(_))
    }

    /// Check if this is an interface type.
    pub fn is_interface(&self) -> bool {
        matches!(self, NominalType::Interface(_))
    }

    /// Check if this is an error type.
    pub fn is_error(&self) -> bool {
        matches!(self, NominalType::Error(_))
    }

    /// Check if this is a struct-like type (class or record - things with fields).
    pub fn is_struct_like(&self) -> bool {
        matches!(self, NominalType::Class(_) | NominalType::Record(_))
    }

    /// Get the type name for error messages.
    pub fn name(&self) -> &'static str {
        match self {
            NominalType::Class(_) => "class",
            NominalType::Record(_) => "record",
            NominalType::Interface(_) => "interface",
            NominalType::Error(_) => "error",
        }
    }

    /// Get as ClassType if this is a class.
    pub fn as_class(&self) -> Option<&ClassType> {
        match self {
            NominalType::Class(c) => Some(c),
            _ => None,
        }
    }

    /// Get as RecordType if this is a record.
    pub fn as_record(&self) -> Option<&RecordType> {
        match self {
            NominalType::Record(r) => Some(r),
            _ => None,
        }
    }

    /// Get as InterfaceType if this is an interface.
    pub fn as_interface(&self) -> Option<&InterfaceType> {
        match self {
            NominalType::Interface(i) => Some(i),
            _ => None,
        }
    }

    /// Get as ErrorTypeInfo if this is an error type.
    pub fn as_error(&self) -> Option<&ErrorTypeInfo> {
        match self {
            NominalType::Error(e) => Some(e),
            _ => None,
        }
    }
}

/// Class type information
#[derive(Debug, Clone, Eq)]
pub struct ClassType {
    /// Reference to the type definition in EntityRegistry
    pub type_def_id: TypeDefId,
    /// Interned type arguments (empty for non-generic classes)
    pub type_args_id: TypeIdVec,
}

impl PartialEq for ClassType {
    fn eq(&self, other: &Self) -> bool {
        // Use type_args_id (TypeId) for equality - it's the canonical source
        self.type_def_id == other.type_def_id && self.type_args_id == other.type_args_id
    }
}

impl std::hash::Hash for ClassType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Use type_args_id (TypeId) for hashing - it's the canonical source
        self.type_def_id.hash(state);
        self.type_args_id.hash(state);
    }
}

impl ClassType {
    /// Get interned type argument IDs.
    pub fn type_args_id(&self) -> &TypeIdVec {
        &self.type_args_id
    }
}

/// Record type information
#[derive(Debug, Clone, Eq)]
pub struct RecordType {
    /// Reference to the type definition in EntityRegistry
    pub type_def_id: TypeDefId,
    /// Interned type arguments (empty for non-generic records)
    pub type_args_id: TypeIdVec,
}

impl PartialEq for RecordType {
    fn eq(&self, other: &Self) -> bool {
        // Use type_args_id (TypeId) for equality - it's the canonical source
        self.type_def_id == other.type_def_id && self.type_args_id == other.type_args_id
    }
}

impl std::hash::Hash for RecordType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Use type_args_id (TypeId) for hashing - it's the canonical source
        self.type_def_id.hash(state);
        self.type_args_id.hash(state);
    }
}

impl RecordType {
    /// Get interned type argument IDs.
    pub fn type_args_id(&self) -> &TypeIdVec {
        &self.type_args_id
    }
}

/// Interface type information
#[derive(Clone, Eq)]
pub struct InterfaceType {
    /// Reference to the type definition in EntityRegistry
    pub type_def_id: TypeDefId,
    /// Interned type arguments (empty for non-generic interfaces)
    pub type_args_id: TypeIdVec,
    pub methods: Arc<[InterfaceMethodType]>,
    pub extends: ExtendsVec, // Parent interface TypeDefIds (inline for 0-2)
}

// Custom Debug to avoid massive output when tracing - just show identity, not all methods
impl std::fmt::Debug for InterfaceType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InterfaceType")
            .field("type_def_id", &self.type_def_id)
            .field("type_args_id", &self.type_args_id)
            .field("methods", &format_args!("[{} methods]", self.methods.len()))
            .field("extends", &self.extends)
            .finish()
    }
}

// Custom PartialEq using type_args_id (TypeId) - the canonical source
impl PartialEq for InterfaceType {
    fn eq(&self, other: &Self) -> bool {
        self.type_def_id == other.type_def_id && self.type_args_id == other.type_args_id
    }
}

// Custom Hash using type_args_id (TypeId) - the canonical source
impl std::hash::Hash for InterfaceType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.type_def_id.hash(state);
        self.type_args_id.hash(state);
    }
}

impl InterfaceType {
    /// Get interned type argument IDs.
    pub fn type_args_id(&self) -> &TypeIdVec {
        &self.type_args_id
    }
}

/// Method signature in an interface
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InterfaceMethodType {
    pub name: NameId,
    pub params: Arc<[LegacyType]>,
    pub return_type: Box<LegacyType>,
    pub has_default: bool, // True if interface provides default implementation
    /// Interned parameter types (canonical - use for comparisons)
    pub params_id: TypeIdVec,
    /// Interned return type (canonical - use for comparisons)
    pub return_type_id: TypeId,
}

/// Error type definition (e.g., DivByZero, OutOfRange { value: i32 })
///
/// Fields are not stored here - they are looked up from EntityRegistry using
/// the type_def_id, just like class and record fields.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ErrorTypeInfo {
    pub type_def_id: TypeDefId,
}

impl std::fmt::Display for NominalType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_class(id: u32) -> NominalType {
        NominalType::Class(ClassType {
            type_def_id: TypeDefId::new(id),
            type_args_id: TypeIdVec::new(),
        })
    }

    fn make_record(id: u32) -> NominalType {
        NominalType::Record(RecordType {
            type_def_id: TypeDefId::new(id),
            type_args_id: TypeIdVec::new(),
        })
    }

    fn make_interface(id: u32) -> NominalType {
        NominalType::Interface(InterfaceType {
            type_def_id: TypeDefId::new(id),
            type_args_id: TypeIdVec::new(),
            methods: vec![].into(),
            extends: vec![].into(),
        })
    }

    fn make_error(id: u32) -> NominalType {
        NominalType::Error(ErrorTypeInfo {
            type_def_id: TypeDefId::new(id),
        })
    }

    #[test]
    fn test_type_def_id() {
        let class = make_class(1);
        let record = make_record(2);
        let interface = make_interface(3);
        let error = make_error(4);

        assert_eq!(class.type_def_id(), TypeDefId::new(1));
        assert_eq!(record.type_def_id(), TypeDefId::new(2));
        assert_eq!(interface.type_def_id(), TypeDefId::new(3));
        assert_eq!(error.type_def_id(), TypeDefId::new(4));
    }

    #[test]
    fn test_is_methods() {
        let class = make_class(1);
        let record = make_record(2);
        let interface = make_interface(3);
        let error = make_error(4);

        assert!(class.is_class());
        assert!(!class.is_record());
        assert!(class.is_struct_like());

        assert!(record.is_record());
        assert!(!record.is_class());
        assert!(record.is_struct_like());

        assert!(interface.is_interface());
        assert!(!interface.is_struct_like());

        assert!(error.is_error());
        assert!(!error.is_struct_like());
    }

    #[test]
    fn test_as_methods() {
        let class = make_class(1);
        let record = make_record(2);

        assert!(class.as_class().is_some());
        assert!(class.as_record().is_none());

        assert!(record.as_record().is_some());
        assert!(record.as_class().is_none());
    }

    #[test]
    fn test_name() {
        assert_eq!(make_class(1).name(), "class");
        assert_eq!(make_record(1).name(), "record");
        assert_eq!(make_interface(1).name(), "interface");
        assert_eq!(make_error(1).name(), "error");
    }
}
