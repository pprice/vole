// type_arena/query.rs
//
// TypeArena query methods: predicates, unwrap helpers, and display_basic.

use vole_identity::{NameId, TypeDefId, TypeParamId};

use super::arena::TypeArena;
use super::sema_type::*;
use super::type_id::{NominalKind, TypeId, TypeIdVec};

impl TypeArena {
    // ========================================================================
    // Query methods - predicates and unwrap helpers
    // ========================================================================

    /// Check if this is a numeric type (can do arithmetic)
    #[inline]
    pub fn is_numeric(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all primitive numerics
        id.is_numeric()
    }

    /// Check if this is an integer type
    #[inline]
    pub fn is_integer(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all primitive integers
        id.is_integer()
    }

    /// Check if this is a floating point type
    #[inline]
    pub fn is_float(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all primitive floats
        id.is_float()
    }

    /// Check if this is a signed integer type
    #[inline]
    pub fn is_signed(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all signed integers
        id.is_signed_int()
    }

    /// Check if this is an unsigned integer type
    #[inline]
    pub fn is_unsigned(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all unsigned integers
        id.is_unsigned_int()
    }

    /// Check if this is an optional type (union containing nil)
    pub fn is_optional(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::Union(variants) => variants.contains(&self.nil()),
            _ => false,
        }
    }

    /// Unwrap an array type, returning the element type
    pub fn unwrap_array(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            SemaType::Array(elem) => Some(*elem),
            _ => None,
        }
    }

    /// Unwrap an optional type, returning the non-nil type
    pub fn unwrap_optional(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            SemaType::Union(variants) => {
                let nil = self.nil();
                let non_nil: TypeIdVec = variants.iter().copied().filter(|&v| v != nil).collect();
                if non_nil.len() == 1 {
                    Some(non_nil[0])
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Unwrap an optional type (union containing nil), returning all non-nil variants.
    /// Returns `Some(variants)` for any union that contains nil (one or more non-nil variants).
    /// Returns `None` if the type is not a union or does not contain nil.
    pub fn unwrap_optional_non_nil_variants(&self, id: TypeId) -> Option<TypeIdVec> {
        match self.get(id) {
            SemaType::Union(variants) => {
                let nil = self.nil();
                if !variants.contains(&nil) {
                    return None;
                }
                let non_nil: TypeIdVec = variants.iter().copied().filter(|&v| v != nil).collect();
                Some(non_nil)
            }
            _ => None,
        }
    }

    /// Unwrap a function type, returning (params, return_type, is_closure)
    pub fn unwrap_function(&self, id: TypeId) -> Option<(&TypeIdVec, TypeId, bool)> {
        match self.get(id) {
            SemaType::Function {
                params,
                ret,
                is_closure,
            } => Some((params, *ret, *is_closure)),
            _ => None,
        }
    }

    /// Unwrap a tuple type, returning the element types
    pub fn unwrap_tuple(&self, id: TypeId) -> Option<&TypeIdVec> {
        match self.get(id) {
            SemaType::Tuple(elements) => Some(elements),
            _ => None,
        }
    }

    /// Unwrap a fixed array type, returning (element, size)
    pub fn unwrap_fixed_array(&self, id: TypeId) -> Option<(TypeId, usize)> {
        match self.get(id) {
            SemaType::FixedArray { element, size } => Some((*element, *size)),
            _ => None,
        }
    }

    /// Get TypeDefId for nominal types (class, struct, interface, error)
    pub fn type_def_id(&self, id: TypeId) -> Option<TypeDefId> {
        match self.get(id) {
            SemaType::Class { type_def_id, .. }
            | SemaType::Interface { type_def_id, .. }
            | SemaType::Error { type_def_id } => Some(*type_def_id),
            _ => None,
        }
    }

    /// Get type arguments for generic types
    pub fn type_args(&self, id: TypeId) -> &[TypeId] {
        match self.get(id) {
            SemaType::Class { type_args, .. } | SemaType::Interface { type_args, .. } => type_args,
            _ => &[],
        }
    }

    /// Assert this type is valid. Panics with context if invalid.
    /// Use in codegen where invalid types indicate a compiler bug.
    #[track_caller]
    pub fn expect_valid(&self, id: TypeId, context: &str) -> TypeId {
        if self.is_invalid(id) {
            panic!(
                "INTERNAL ERROR: Invalid type in codegen\n\
                 Context: {}\n\
                 Location: {}",
                context,
                std::panic::Location::caller()
            );
        }
        id
    }

    // =========================================================================
    // Type predicates for codegen pattern matching
    // =========================================================================

    /// Check if this is an array type
    pub fn is_array(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Array(_))
    }

    /// Check if this is a function type
    pub fn is_function(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Function { .. })
    }

    /// Check if this is a class type
    pub fn is_class(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Class { .. })
    }

    /// Mark a TypeId as a sentinel type.
    ///
    /// Called during sentinel signature collection to register both well-known
    /// (nil, Done) and user-defined sentinels. Sentinel types are zero-field struct
    /// types that should not be treated as regular structs for codegen purposes.
    pub fn mark_sentinel(&mut self, id: TypeId) {
        self.sentinel_ids.insert(id);
    }

    /// Check if this TypeId is a sentinel type (e.g., nil, Done, or user-defined sentinels).
    ///
    /// Sentinel types are zero-field struct types that get special treatment:
    /// they are not treated as regular structs for codegen (auto-boxing, field access, etc.),
    /// they are represented as i8 in Cranelift, and they have zero logical size.
    #[inline]
    pub fn is_sentinel(&self, id: TypeId) -> bool {
        self.sentinel_ids.contains(&id)
    }

    /// Check if this is a struct type (stack-allocated value type)
    pub fn is_struct(&self, id: TypeId) -> bool {
        // Sentinel types are not treated as structs for codegen purposes
        // (e.g., auto-boxing in unions), even though they are SemaType::Struct internally.
        if self.is_sentinel(id) {
            return false;
        }
        matches!(self.get(id), SemaType::Struct { .. })
    }

    /// Check if this is an interface type
    pub fn is_interface(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Interface { .. })
    }

    /// Check if this is an error type
    pub fn is_error(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Error { .. })
    }

    /// Check if this is a union type
    pub fn is_union(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Union(_))
    }

    /// Check if this is the string primitive
    #[inline]
    pub fn is_string(&self, id: TypeId) -> bool {
        id == TypeId::STRING
    }

    /// Check if this is a handle type
    #[inline]
    pub fn is_handle(&self, id: TypeId) -> bool {
        id == TypeId::HANDLE
    }

    /// Check if this is nil
    #[inline]
    pub fn is_nil(&self, id: TypeId) -> bool {
        id.is_nil()
    }

    /// Check if this is void
    #[inline]
    pub fn is_void(&self, id: TypeId) -> bool {
        id.is_void()
    }

    /// Check if this is the never type (bottom type)
    #[inline]
    pub fn is_never(&self, id: TypeId) -> bool {
        id.is_never()
    }

    /// Check if this is the unknown type (top type)
    #[inline]
    pub fn is_unknown(&self, id: TypeId) -> bool {
        id.is_unknown()
    }

    /// Check if this is a runtime iterator type
    pub fn is_runtime_iterator(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::RuntimeIterator(_))
    }

    /// Check if an integer literal value fits within a type (handles unions)
    pub fn literal_fits_id(&self, value: i64, id: TypeId) -> bool {
        // Unknown type accepts any value
        if id.is_unknown() {
            return true;
        }
        // Check primitive types directly
        if id.fits_literal(value) {
            return true;
        }
        // For unions, check if literal fits any numeric variant
        if let Some(variants) = self.unwrap_union(id) {
            return variants.iter().any(|&v| v.fits_literal(value));
        }
        false
    }

    // =========================================================================
    // Unwrap helpers for codegen
    // =========================================================================

    /// Unwrap a class type, returning (type_def_id, type_args)
    pub fn unwrap_class(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec)> {
        match self.get(id) {
            SemaType::Class {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args)),
            _ => None,
        }
    }

    /// Unwrap a struct type, returning (type_def_id, type_args).
    ///
    /// Returns `None` for sentinel types (e.g., nil, Done, user-defined sentinels) even
    /// after they've been rebound to `SemaType::Struct`, since they should not be treated
    /// as regular structs for codegen purposes (signatures, auto-boxing, field access, etc.).
    pub fn unwrap_struct(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec)> {
        if self.is_sentinel(id) {
            return None;
        }
        match self.get(id) {
            SemaType::Struct {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args)),
            _ => None,
        }
    }

    /// Unwrap an interface type, returning (type_def_id, type_args)
    pub fn unwrap_interface(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec)> {
        match self.get(id) {
            SemaType::Interface {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args)),
            _ => None,
        }
    }

    /// Unwrap any nominal type (class, struct, or interface), returning (type_def_id, type_args, kind).
    ///
    /// This is a convenience helper that combines unwrap_class, unwrap_struct, and unwrap_interface
    /// into a single call. Use this when you need to handle all nominal types uniformly.
    ///
    /// Returns `None` for sentinel types (e.g., nil, Done, user-defined sentinels) even after rebinding.
    pub fn unwrap_nominal(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec, NominalKind)> {
        if self.is_sentinel(id) {
            return None;
        }
        match self.get(id) {
            SemaType::Class {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args, NominalKind::Class)),
            SemaType::Struct {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args, NominalKind::Struct)),
            SemaType::Interface {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args, NominalKind::Interface)),
            _ => None,
        }
    }

    /// Unwrap a nominal type that is a class or struct (not interface).
    ///
    /// This is a convenience wrapper around `unwrap_nominal` that filters out
    /// interfaces, since many call sites only care about field-bearing types.
    pub fn unwrap_class_or_struct(
        &self,
        id: TypeId,
    ) -> Option<(TypeDefId, &TypeIdVec, NominalKind)> {
        self.unwrap_nominal(id)
            .filter(|(_, _, kind)| kind.is_class_or_struct())
    }

    /// Unwrap an error type, returning type_def_id
    pub fn unwrap_error(&self, id: TypeId) -> Option<TypeDefId> {
        match self.get(id) {
            SemaType::Error { type_def_id } => Some(*type_def_id),
            _ => None,
        }
    }

    /// Unwrap an error or struct type, returning just the TypeDefId.
    pub fn unwrap_error_or_struct_def(&self, id: TypeId) -> Option<TypeDefId> {
        self.unwrap_error(id)
            .or_else(|| self.unwrap_struct(id).map(|(def_id, _)| def_id))
    }

    /// Unwrap a union type, returning the variants
    pub fn unwrap_union(&self, id: TypeId) -> Option<&TypeIdVec> {
        match self.get(id) {
            SemaType::Union(variants) => Some(variants),
            _ => None,
        }
    }

    /// Unwrap a runtime iterator type, returning the element type
    pub fn unwrap_runtime_iterator(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            SemaType::RuntimeIterator(elem) => Some(*elem),
            _ => None,
        }
    }

    /// Look up an existing RuntimeIterator type by element type (read-only).
    /// Returns None if the type doesn't exist in the arena.
    pub fn lookup_runtime_iterator(&self, element: TypeId) -> Option<TypeId> {
        let ty = SemaType::RuntimeIterator(element);
        self.intern_map.get(&ty).copied()
    }

    /// Look up an existing Array type by element type (read-only).
    /// Returns None if the type doesn't exist in the arena.
    pub fn lookup_array(&self, element: TypeId) -> Option<TypeId> {
        let ty = SemaType::Array(element);
        self.intern_map.get(&ty).copied()
    }

    /// Look up an existing Interface type by type_def_id and type_args (read-only).
    /// Returns None if the type doesn't exist in the arena.
    pub fn lookup_interface(&self, type_def_id: TypeDefId, type_args: TypeIdVec) -> Option<TypeId> {
        let ty = SemaType::Interface {
            type_def_id,
            type_args,
        };
        self.intern_map.get(&ty).copied()
    }

    /// Return all concrete (non-TypeParam) element types for which a RuntimeIterator exists.
    ///
    /// Used by codegen to find the concrete array element types that need array Iterable
    /// default methods (count, map, filter, etc.) compiled for them.
    pub fn all_concrete_runtime_iterator_elem_types(&self) -> Vec<TypeId> {
        self.types
            .iter()
            .filter_map(|ty| {
                if let SemaType::RuntimeIterator(elem) = ty {
                    // Skip abstract TypeParam elements
                    if matches!(self.get(*elem), SemaType::TypeParam(_)) {
                        None
                    } else {
                        Some(*elem)
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    /// Look up any existing Array TypeId (read-only).
    ///
    /// Searches for the first array type available in the arena.
    /// Useful in codegen when the arena is immutable but we need a representative
    /// array TypeId (all array TypeIds map to pointer type in Cranelift).
    /// Returns None only if no array type has been interned yet.
    pub fn lookup_any_array(&self) -> Option<TypeId> {
        self.intern_map
            .iter()
            .find_map(|(ty, &id)| matches!(ty, SemaType::Array(_)).then_some(id))
    }

    /// Look up an existing optional (T?) type for a given value type (read-only).
    ///
    /// Returns the TypeId of `Union(value_type, nil)` — a union with EXACTLY two variants
    /// (the value type and nil) — if it exists in the arena, or None otherwise.
    ///
    /// This is intentionally strict: it only matches the exact 2-variant optional, not
    /// wider unions like `A | B | nil` that also happen to contain both nil and value_type.
    /// Using a wider union as a fallback return type (e.g. for `first()`) would cause
    /// codegen to try to store a scalar value into the wrong union shape.
    ///
    /// Useful as a fallback when deriving return types without expression data.
    pub fn lookup_optional(&self, value_type: TypeId) -> Option<TypeId> {
        let nil_type = self.nil();
        self.intern_map.iter().find_map(|(ty, &id)| {
            if let SemaType::Union(variants) = ty {
                // Must be exactly [value_type, nil] (in sorted order — Union stores variants
                // sorted, so we check length == 2 and both are present).
                if variants.len() == 2
                    && variants.contains(&nil_type)
                    && variants.contains(&value_type)
                {
                    Some(id)
                } else {
                    None
                }
            } else {
                None
            }
        })
    }

    /// Unwrap a fallible type, returning (success, error)
    pub fn unwrap_fallible(&self, id: TypeId) -> Option<(TypeId, TypeId)> {
        match self.get(id) {
            SemaType::Fallible { success, error } => Some((*success, *error)),
            _ => None,
        }
    }

    /// Unwrap a module type, returning the InternedModule
    pub fn unwrap_module(&self, id: TypeId) -> Option<&InternedModule> {
        match self.get(id) {
            SemaType::Module(m) => Some(m.as_ref()),
            _ => None,
        }
    }

    /// Unwrap a type parameter, returning its NameId
    pub fn unwrap_type_param(&self, id: TypeId) -> Option<NameId> {
        match self.get(id) {
            SemaType::TypeParam(name_id) => Some(*name_id),
            _ => None,
        }
    }

    /// Check if a type contains any TypeParam anywhere in its structure.
    /// Recursively walks through compound types (classes, arrays, unions, etc.).
    pub fn contains_type_param(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::TypeParam(_) => true,
            SemaType::TypeParamRef(_) => true,
            SemaType::Class { type_args, .. }
            | SemaType::Struct { type_args, .. }
            | SemaType::Interface { type_args, .. } => {
                type_args.iter().any(|&arg| self.contains_type_param(arg))
            }
            SemaType::Union(types) | SemaType::Tuple(types) => {
                types.iter().any(|&t| self.contains_type_param(t))
            }
            SemaType::Array(elem) | SemaType::RuntimeIterator(elem) => {
                self.contains_type_param(*elem)
            }
            SemaType::FixedArray { element, .. } => self.contains_type_param(*element),
            SemaType::Function { params, ret, .. } => {
                params.iter().any(|&p| self.contains_type_param(p))
                    || self.contains_type_param(*ret)
            }
            SemaType::Fallible { success, error } => {
                self.contains_type_param(*success) || self.contains_type_param(*error)
            }
            _ => false,
        }
    }

    /// Unwrap a type parameter reference, returning its TypeParamId
    pub fn unwrap_type_param_ref(&self, id: TypeId) -> Option<TypeParamId> {
        match self.get(id) {
            SemaType::TypeParamRef(id) => Some(*id),
            _ => None,
        }
    }

    /// Unwrap a structural type, returning its fields and methods
    pub fn unwrap_structural(&self, id: TypeId) -> Option<&InternedStructural> {
        match self.get(id) {
            SemaType::Structural(s) => Some(s),
            _ => None,
        }
    }

    /// Display a type for error messages (basic version without name resolution)
    pub fn display_basic(&self, id: TypeId) -> String {
        // Sentinel types display as "sentinel#N" using their TypeDefId index.
        // For full name display, use display_type() which has access to entity_registry.
        if self.is_sentinel(id)
            && let SemaType::Struct { type_def_id, .. } = self.get(id)
        {
            return format!("sentinel#{}", type_def_id.index());
        }
        match self.get(id) {
            SemaType::Primitive(p) => p.name().to_string(),
            SemaType::Handle => "handle".to_string(),
            SemaType::Void => "void".to_string(),
            SemaType::Range => "range".to_string(),
            SemaType::MetaType => "type".to_string(),
            SemaType::Never => "never".to_string(),
            SemaType::Unknown => "unknown".to_string(),
            SemaType::Invalid { kind } => format!("<invalid: {}>", kind),
            SemaType::Union(variants) => {
                let parts: Vec<String> = variants.iter().map(|&v| self.display_basic(v)).collect();
                parts.join(" | ")
            }
            SemaType::Tuple(elements) => {
                let parts: Vec<String> = elements.iter().map(|&e| self.display_basic(e)).collect();
                format!("[{}]", parts.join(", "))
            }
            SemaType::Array(elem) => format!("[{}]", self.display_basic(*elem)),
            SemaType::FixedArray { element, size } => {
                format!("[{}; {}]", self.display_basic(*element), size)
            }
            SemaType::RuntimeIterator(elem) => {
                format!("Iterator<{}>", self.display_basic(*elem))
            }
            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let param_str: Vec<String> =
                    params.iter().map(|&p| self.display_basic(p)).collect();
                let closure_marker = if *is_closure { "closure " } else { "" };
                format!(
                    "{}({}) -> {}",
                    closure_marker,
                    param_str.join(", "),
                    self.display_basic(*ret)
                )
            }
            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                if type_args.is_empty() {
                    format!("class#{}", type_def_id.index())
                } else {
                    let args: Vec<String> =
                        type_args.iter().map(|&a| self.display_basic(a)).collect();
                    format!("class#{}<{}>", type_def_id.index(), args.join(", "))
                }
            }
            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                if type_args.is_empty() {
                    format!("interface#{}", type_def_id.index())
                } else {
                    let args: Vec<String> =
                        type_args.iter().map(|&a| self.display_basic(a)).collect();
                    format!("interface#{}<{}>", type_def_id.index(), args.join(", "))
                }
            }
            SemaType::Struct {
                type_def_id,
                type_args,
            } => {
                if type_args.is_empty() {
                    format!("struct#{}", type_def_id.index())
                } else {
                    let args: Vec<String> =
                        type_args.iter().map(|&a| self.display_basic(a)).collect();
                    format!("struct#{}<{}>", type_def_id.index(), args.join(", "))
                }
            }
            SemaType::Error { type_def_id } => format!("error#{}", type_def_id.index()),
            SemaType::TypeParam(name_id) => format!("TypeParam({:?})", name_id),
            SemaType::TypeParamRef(id) => format!("TypeParamRef#{}", id.index()),
            SemaType::Module(m) => format!("module#{}", m.module_id.index()),
            SemaType::Fallible { success, error } => {
                format!(
                    "fallible({}, {})",
                    self.display_basic(*success),
                    self.display_basic(*error)
                )
            }
            SemaType::Structural(st) => {
                let field_strs: Vec<String> = st
                    .fields
                    .iter()
                    .map(|(name, ty)| format!("{:?}: {}", name, self.display_basic(*ty)))
                    .collect();
                let method_strs: Vec<String> = st
                    .methods
                    .iter()
                    .map(|m| {
                        let params: Vec<String> =
                            m.params.iter().map(|&p| self.display_basic(p)).collect();
                        format!(
                            "{:?}({}) -> {}",
                            m.name,
                            params.join(", "),
                            self.display_basic(m.return_type)
                        )
                    })
                    .collect();
                format!(
                    "{{ {} | {} }}",
                    field_strs.join(", "),
                    method_strs.join(", ")
                )
            }
            SemaType::Placeholder(kind) => format!("{}", kind),
        }
    }
}
