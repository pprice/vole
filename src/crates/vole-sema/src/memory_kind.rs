// src/sema/memory_kind.rs
//
// MemoryKind classification for types: determines whether a type is a plain
// value (fits in a register, no cleanup) or reference-counted (heap-allocated,
// needs inc/dec).

use crate::type_arena::{SemaType, TypeArena, TypeId};
use crate::types::PrimitiveType;

/// Whether a type is a plain value or reference-counted.
///
/// This is the core classification codegen uses to decide whether a local
/// variable needs drop-flag tracking and RC cleanup on scope exit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryKind {
    /// No cleanup needed. Fits in one or more registers/stack slots.
    /// Examples: i64, f64, bool, unit/void, never, unions (tagged value),
    /// tuples (stack-allocated), fixed arrays (stack-allocated), enums (integer tag),
    /// structs (stack-allocated, per-field cleanup by codegen).
    Value,

    /// Reference-counted heap object. Needs rc_inc on copy and rc_dec on drop.
    /// Examples: string, Array<T>, Map<K,V>, Set<T>, class instances,
    /// closures, iterators, error types.
    Rc,
}

impl TypeArena {
    /// Classify a type as `Value` or `Rc` for codegen memory management.
    ///
    /// After monomorphization all generic type parameters should be resolved
    /// to concrete types, so `TypeParam` / `TypeParamRef` fall through to
    /// `Rc` (the safe default).
    pub fn memory_kind(&self, id: TypeId) -> MemoryKind {
        match self.get(id) {
            // Numeric primitives and bool are plain values.
            // String is the one primitive that is Rc (heap-allocated).
            SemaType::Primitive(p) => match p {
                PrimitiveType::String => MemoryKind::Rc,
                PrimitiveType::I8
                | PrimitiveType::I16
                | PrimitiveType::I32
                | PrimitiveType::I64
                | PrimitiveType::I128
                | PrimitiveType::U8
                | PrimitiveType::U16
                | PrimitiveType::U32
                | PrimitiveType::U64
                | PrimitiveType::F32
                | PrimitiveType::F64
                | PrimitiveType::Bool => MemoryKind::Value,
            },

            // Handle is an opaque native pointer. It's a plain value (i64-sized pointer)
            // with no RC header — cleanup is the responsibility of the native code.
            SemaType::Handle => MemoryKind::Value,

            // Special types — all plain values (zero-size or register-sized).
            SemaType::Void | SemaType::Range | SemaType::MetaType => MemoryKind::Value,

            // Bottom/top types — never values exist at runtime, but Value is
            // correct: never is uninhabited, unknown is erased before codegen.
            SemaType::Never | SemaType::Unknown => MemoryKind::Value,

            // Invalid / analysis error — should not reach codegen, but Value
            // is harmless (no cleanup emitted).
            SemaType::Invalid { .. } => MemoryKind::Value,

            // Unions are a tagged value on the stack. The *contained* value
            // gets its own MemoryKind when extracted, but the union container
            // itself is a stack slot.
            SemaType::Union(_) => MemoryKind::Value,

            // Tuples are stack-allocated. Individual elements may be Rc, but
            // codegen handles that by inspecting each element type.
            SemaType::Tuple(_) => MemoryKind::Value,

            // Fixed-size arrays are stack-allocated. Element cleanup is
            // codegen's responsibility per-element.
            SemaType::FixedArray { .. } => MemoryKind::Value,

            // Fallible(T, E) is like a union — tagged stack value.
            SemaType::Fallible { .. } => MemoryKind::Value,

            // Structs are value types — stack-allocated with per-field cleanup
            // handled by codegen. No RC header.
            SemaType::Struct { .. } => MemoryKind::Value,

            // Heap-allocated, reference-counted types.
            SemaType::Array(_) => MemoryKind::Rc,
            SemaType::RuntimeIterator(_) => MemoryKind::Rc,
            SemaType::Function { .. } => MemoryKind::Rc,
            SemaType::Class { .. } => MemoryKind::Rc,
            SemaType::Interface { .. } => MemoryKind::Rc,
            SemaType::Error { .. } => MemoryKind::Rc,
            SemaType::Module(_) => MemoryKind::Rc,
            SemaType::Structural(_) => MemoryKind::Rc,

            // Type parameters should be monomorphized before codegen.
            // Default to Rc (safe: unnecessary dec is a bug, but missing dec
            // is a leak — Rc is the conservative choice).
            SemaType::TypeParam(_) | SemaType::TypeParamRef(_) => MemoryKind::Rc,

            // Placeholders should never survive to codegen, but Rc is safe.
            SemaType::Placeholder(_) => MemoryKind::Rc,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;
    use vole_identity::TypeDefId;

    // ── helpers ──────────────────────────────────────────────────────────

    fn arena() -> TypeArena {
        TypeArena::new()
    }

    // ── primitive value types ────────────────────────────────────────────

    #[test]
    fn integer_types_are_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::I8), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::I16), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::I32), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::I64), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::I128), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::U8), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::U16), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::U32), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::U64), MemoryKind::Value);
    }

    #[test]
    fn float_types_are_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::F32), MemoryKind::Value);
        assert_eq!(a.memory_kind(TypeId::F64), MemoryKind::Value);
    }

    #[test]
    fn bool_is_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::BOOL), MemoryKind::Value);
    }

    // ── primitive Rc type ───────────────────────────────────────────────

    #[test]
    fn string_is_rc() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::STRING), MemoryKind::Rc);
    }

    // ── special types ───────────────────────────────────────────────────

    #[test]
    fn void_is_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::VOID), MemoryKind::Value);
    }

    #[test]
    fn never_is_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::NEVER), MemoryKind::Value);
    }

    #[test]
    fn unknown_is_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::UNKNOWN), MemoryKind::Value);
    }

    #[test]
    fn range_is_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::RANGE), MemoryKind::Value);
    }

    #[test]
    fn metatype_is_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::METATYPE), MemoryKind::Value);
    }

    #[test]
    fn invalid_is_value() {
        let a = arena();
        assert_eq!(a.memory_kind(TypeId::INVALID), MemoryKind::Value);
    }

    // ── compound value types ────────────────────────────────────────────

    #[test]
    fn union_is_value() {
        let mut a = arena();
        let u = a.union(smallvec![TypeId::I32, TypeId::STRING]);
        assert_eq!(a.memory_kind(u), MemoryKind::Value);
    }

    #[test]
    fn tuple_is_value() {
        let mut a = arena();
        let t = a.tuple(smallvec![TypeId::I32, TypeId::STRING]);
        assert_eq!(a.memory_kind(t), MemoryKind::Value);
    }

    #[test]
    fn fixed_array_is_value() {
        let mut a = arena();
        let fa = a.fixed_array(TypeId::I32, 4);
        assert_eq!(a.memory_kind(fa), MemoryKind::Value);
    }

    #[test]
    fn fallible_is_value() {
        let mut a = arena();
        let f = a.fallible(TypeId::I32, TypeId::STRING);
        assert_eq!(a.memory_kind(f), MemoryKind::Value);
    }

    #[test]
    fn struct_is_value() {
        let mut a = arena();
        let s = a.struct_type(TypeDefId::new(0), smallvec![]);
        assert_eq!(a.memory_kind(s), MemoryKind::Value);
    }

    // ── Rc types ────────────────────────────────────────────────────────

    #[test]
    fn array_is_rc() {
        let mut a = arena();
        let arr = a.array(TypeId::I32);
        assert_eq!(a.memory_kind(arr), MemoryKind::Rc);
    }

    #[test]
    fn runtime_iterator_is_rc() {
        let mut a = arena();
        let it = a.runtime_iterator(TypeId::I32);
        assert_eq!(a.memory_kind(it), MemoryKind::Rc);
    }

    #[test]
    fn function_is_rc() {
        let mut a = arena();
        let f = a.function(smallvec![TypeId::I32], TypeId::BOOL, false);
        assert_eq!(a.memory_kind(f), MemoryKind::Rc);
    }

    #[test]
    fn closure_is_rc() {
        let mut a = arena();
        let c = a.function(smallvec![TypeId::I32], TypeId::BOOL, true);
        assert_eq!(a.memory_kind(c), MemoryKind::Rc);
    }

    #[test]
    fn class_is_rc() {
        let mut a = arena();
        let cls = a.class(TypeDefId::new(0), smallvec![]);
        assert_eq!(a.memory_kind(cls), MemoryKind::Rc);
    }

    #[test]
    fn interface_is_rc() {
        let mut a = arena();
        let i = a.interface(TypeDefId::new(0), smallvec![]);
        assert_eq!(a.memory_kind(i), MemoryKind::Rc);
    }

    #[test]
    fn error_is_rc() {
        let mut a = arena();
        let e = a.error_type(TypeDefId::new(0));
        assert_eq!(a.memory_kind(e), MemoryKind::Rc);
    }
}
