// type_arena/sema_type.rs
//
// SemaType: the canonical interned type representation and associated data types.

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::types::{ConstantValue, PlaceholderKind, PrimitiveType};
use vole_identity::{ModuleId, NameId, TypeDefId, TypeParamId};

use super::type_id::{TypeId, TypeIdVec};

/// Interned representation of a structural method
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedStructuralMethod {
    pub name: NameId,
    pub params: TypeIdVec,
    pub return_type: TypeId,
}

/// Interned representation of a structural type (duck typing constraint)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedStructural {
    pub fields: SmallVec<[(NameId, TypeId); 4]>,
    pub methods: SmallVec<[InternedStructuralMethod; 2]>,
}

/// Interned representation of a module type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedModule {
    pub module_id: ModuleId,
    /// Exports as (name, type) pairs - part of the module's type signature
    pub exports: SmallVec<[(NameId, TypeId); 8]>,
}

impl InternedModule {
    /// Look up an export's type by name.
    pub fn export_type(&self, name_id: NameId) -> Option<TypeId> {
        self.exports
            .iter()
            .find(|(n, _)| *n == name_id)
            .map(|&(_, type_id)| type_id)
    }
}

/// Module metadata stored separately from the type.
///
/// This contains codegen-relevant data that isn't part of the module's type identity.
/// The type identity is just (module_id, exports) - this is the "extra" data.
///
/// FUTURE OPTIMIZATION:
/// - `constants`: Can be eliminated with constant folding during analysis.
///   Instead of storing constant values here, fold them directly into the AST.
/// - `external_funcs`: Can be eliminated by treating external funcs as regular funcs.
///   The "external" distinction is a codegen detail, not a type system concept.
#[derive(Debug, Clone, Default)]
pub struct ModuleMetadata {
    /// Compile-time constant values (e.g., math.PI = 3.14159...)
    pub constants: FxHashMap<NameId, ConstantValue>,
    /// Functions implemented via FFI rather than Vole code
    pub external_funcs: FxHashSet<NameId>,
}

/// The canonical type representation in Vole.
///
/// This is an interned type stored in the TypeArena. Use TypeId handles
/// for O(1) equality and pass-by-copy. Access the SemaType via arena.get(id).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SemaType {
    // Primitives
    Primitive(PrimitiveType),

    // Opaque handle type (native pointer, no arithmetic/comparison)
    Handle,

    // Special types
    Void,
    Range,
    MetaType, // metatype - the type of types

    // Top and bottom types
    Never, // Bottom type - the type of expressions that never return (e.g., unreachable, panic)
    Unknown, // Top type - the type that includes all values (used for inference/gradual typing)

    // Error/invalid type
    Invalid {
        kind: &'static str,
    },

    // Compound types with TypeId children
    Union(TypeIdVec),
    Tuple(TypeIdVec),
    Array(TypeId),
    FixedArray {
        element: TypeId,
        size: usize,
    },
    RuntimeIterator(TypeId),

    // Function type
    Function {
        params: TypeIdVec,
        ret: TypeId,
        is_closure: bool,
    },

    // Nominal types (class, struct, interface, error)
    Class {
        type_def_id: TypeDefId,
        type_args: TypeIdVec,
    },
    Struct {
        type_def_id: TypeDefId,
        type_args: TypeIdVec,
    },
    Interface {
        type_def_id: TypeDefId,
        type_args: TypeIdVec,
    },
    Error {
        type_def_id: TypeDefId,
    },

    // Type parameters
    TypeParam(NameId),
    TypeParamRef(TypeParamId),

    // Module type - exports are part of the type identity
    // Note: Boxed to keep SemaType size small
    Module(Box<InternedModule>),

    // Fallible type: fallible(T, E) - result-like type
    Fallible {
        success: TypeId,
        error: TypeId,
    },

    // Structural type: duck typing constraint
    // e.g., { name: string, func greet() -> string }
    // Note: Boxed to keep SemaType size small
    Structural(Box<InternedStructural>),

    // Placeholder for inference (if we decide to intern these)
    Placeholder(PlaceholderKind),
}
