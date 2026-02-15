// type_arena/substitution.rs
//
// Type substitution methods for generic instantiation.

use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use crate::types::PlaceholderKind;
use vole_identity::NameId;

use super::arena::TypeArena;
use super::sema_type::*;
use super::type_id::{TypeId, TypeIdVec};

impl TypeArena {
    // ========================================================================
    // Type substitution
    // ========================================================================

    /// Substitute type parameters with concrete types.
    ///
    /// This is the core operation for generic type instantiation. Given a map
    /// from type parameter NameIds to concrete TypeIds, returns a new TypeId with
    /// all type parameters replaced.
    ///
    /// Automatically cached via interning: same input produces same TypeId.
    pub fn substitute(&mut self, ty: TypeId, subs: &FxHashMap<NameId, TypeId>) -> TypeId {
        // Early exit if no substitutions
        if subs.is_empty() {
            return ty;
        }

        // Clone the interned type to release the borrow
        match self.get(ty).clone() {
            // Direct substitution for type parameters
            SemaType::TypeParam(name_id) => subs.get(&name_id).copied().unwrap_or(ty),

            // TypeParamRef doesn't substitute based on NameId
            SemaType::TypeParamRef(_) => ty,

            // Recursive substitution for compound types
            SemaType::Array(elem) => {
                let new_elem = self.substitute(elem, subs);
                self.array(new_elem)
            }

            SemaType::Union(variants) => {
                let new_variants: TypeIdVec =
                    variants.iter().map(|&v| self.substitute(v, subs)).collect();
                self.union(new_variants)
            }

            SemaType::Tuple(elements) => {
                let new_elements: TypeIdVec =
                    elements.iter().map(|&e| self.substitute(e, subs)).collect();
                self.tuple(new_elements)
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: TypeIdVec =
                    params.iter().map(|&p| self.substitute(p, subs)).collect();
                let new_ret = self.substitute(ret, subs);
                self.function(new_params, new_ret, is_closure)
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.class(type_def_id, new_args)
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.interface(type_def_id, new_args)
            }

            SemaType::RuntimeIterator(elem) => {
                let new_elem = self.substitute(elem, subs);
                self.runtime_iterator(new_elem)
            }

            SemaType::FixedArray { element, size } => {
                let new_elem = self.substitute(element, subs);
                self.fixed_array(new_elem, size)
            }

            SemaType::Fallible { success, error } => {
                let new_success = self.substitute(success, subs);
                let new_error = self.substitute(error, subs);
                self.fallible(new_success, new_error)
            }

            SemaType::Structural(st) => {
                let new_fields: SmallVec<[(NameId, TypeId); 4]> = st
                    .fields
                    .iter()
                    .map(|(name, ty)| (*name, self.substitute(*ty, subs)))
                    .collect();
                let new_methods: SmallVec<[InternedStructuralMethod; 2]> = st
                    .methods
                    .iter()
                    .map(|m| InternedStructuralMethod {
                        name: m.name,
                        params: m.params.iter().map(|&p| self.substitute(p, subs)).collect(),
                        return_type: self.substitute(m.return_type, subs),
                    })
                    .collect();
                self.structural(new_fields, new_methods)
            }

            // Types without nested type parameters - return unchanged
            SemaType::Primitive(_)
            | SemaType::Handle
            | SemaType::Void
            | SemaType::Range
            | SemaType::MetaType
            | SemaType::Never
            | SemaType::Unknown
            | SemaType::Invalid { .. }
            | SemaType::Error { .. }
            | SemaType::Struct { .. }
            | SemaType::Module(_)
            | SemaType::Placeholder(_) => ty,
        }
    }

    /// Look up a substituted type without creating new types.
    ///
    /// This is the read-only version of `substitute`. Returns `Some(type_id)` if
    /// the substituted type already exists in the arena, `None` if any intermediate
    /// or final type would need to be created.
    ///
    /// Use this in codegen where all types should already be fully instantiated.
    pub fn lookup_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<TypeId> {
        // Early exit if no substitutions
        if subs.is_empty() {
            return Some(ty);
        }

        match self.get(ty) {
            // Direct substitution for type parameters
            SemaType::TypeParam(name_id) => subs.get(name_id).copied(),

            // TypeParamRef doesn't substitute based on NameId
            SemaType::TypeParamRef(_) => Some(ty),

            // Recursive lookup for compound types
            SemaType::Array(elem) => {
                let new_elem = self.lookup_substitute(*elem, subs)?;
                if new_elem == *elem {
                    return Some(ty);
                }
                let result_ty = SemaType::Array(new_elem);
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Union(variants) => {
                let new_variants: Option<TypeIdVec> = variants
                    .iter()
                    .map(|&v| self.lookup_substitute(v, subs))
                    .collect();
                let new_variants = new_variants?;
                if new_variants == *variants {
                    return Some(ty);
                }
                // Re-sort substituted variants to match the normalized union order
                // (mirrors what `union()` does when creating new union types).
                // Without this, substituting `T | Done` with T=i64 produces [Done, i64]
                // but the interned type is [i64, Done] due to sort-key ordering.
                let mut sorted: Vec<TypeId> = new_variants.to_vec();
                sorted.sort_by_cached_key(|&v| std::cmp::Reverse(self.union_sort_key(v)));
                sorted.dedup();
                let result_ty = SemaType::Union(sorted.into());
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Tuple(elements) => {
                let new_elements: Option<TypeIdVec> = elements
                    .iter()
                    .map(|&e| self.lookup_substitute(e, subs))
                    .collect();
                let new_elements = new_elements?;
                if new_elements == *elements {
                    return Some(ty);
                }
                let result_ty = SemaType::Tuple(new_elements);
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: Option<TypeIdVec> = params
                    .iter()
                    .map(|&p| self.lookup_substitute(p, subs))
                    .collect();
                let new_params = new_params?;
                let new_ret = self.lookup_substitute(*ret, subs)?;
                if new_params == *params && new_ret == *ret {
                    return Some(ty);
                }
                let result_ty = SemaType::Function {
                    params: new_params,
                    ret: new_ret,
                    is_closure: *is_closure,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: Option<TypeIdVec> = type_args
                    .iter()
                    .map(|&a| self.lookup_substitute(a, subs))
                    .collect();
                let new_args = new_args?;
                if new_args == *type_args {
                    return Some(ty);
                }
                let result_ty = SemaType::Class {
                    type_def_id: *type_def_id,
                    type_args: new_args,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: Option<TypeIdVec> = type_args
                    .iter()
                    .map(|&a| self.lookup_substitute(a, subs))
                    .collect();
                let new_args = new_args?;
                if new_args == *type_args {
                    return Some(ty);
                }
                let result_ty = SemaType::Interface {
                    type_def_id: *type_def_id,
                    type_args: new_args,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::RuntimeIterator(elem) => {
                let new_elem = self.lookup_substitute(*elem, subs)?;
                if new_elem == *elem {
                    return Some(ty);
                }
                let result_ty = SemaType::RuntimeIterator(new_elem);
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::FixedArray { element, size } => {
                let new_elem = self.lookup_substitute(*element, subs)?;
                if new_elem == *element {
                    return Some(ty);
                }
                let result_ty = SemaType::FixedArray {
                    element: new_elem,
                    size: *size,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Fallible { success, error } => {
                let new_success = self.lookup_substitute(*success, subs)?;
                let new_error = self.lookup_substitute(*error, subs)?;
                if new_success == *success && new_error == *error {
                    return Some(ty);
                }
                let result_ty = SemaType::Fallible {
                    success: new_success,
                    error: new_error,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Structural(st) => {
                let new_fields: Option<SmallVec<[(NameId, TypeId); 4]>> = st
                    .fields
                    .iter()
                    .map(|(name, ty)| Some((*name, self.lookup_substitute(*ty, subs)?)))
                    .collect();
                let new_fields = new_fields?;
                let new_methods: Option<SmallVec<[InternedStructuralMethod; 2]>> = st
                    .methods
                    .iter()
                    .map(|m| {
                        let new_params: Option<TypeIdVec> = m
                            .params
                            .iter()
                            .map(|&p| self.lookup_substitute(p, subs))
                            .collect();
                        Some(InternedStructuralMethod {
                            name: m.name,
                            params: new_params?,
                            return_type: self.lookup_substitute(m.return_type, subs)?,
                        })
                    })
                    .collect();
                let new_methods = new_methods?;
                if new_fields == st.fields && new_methods == st.methods {
                    return Some(ty);
                }
                let result_ty = SemaType::Structural(Box::new(InternedStructural {
                    fields: new_fields,
                    methods: new_methods,
                }));
                self.intern_map.get(&result_ty).copied()
            }

            // Types without nested type parameters - return unchanged
            SemaType::Primitive(_)
            | SemaType::Handle
            | SemaType::Void
            | SemaType::Range
            | SemaType::MetaType
            | SemaType::Never
            | SemaType::Unknown
            | SemaType::Invalid { .. }
            | SemaType::Error { .. }
            | SemaType::Struct { .. }
            | SemaType::Module(_)
            | SemaType::Placeholder(_) => Some(ty),
        }
    }

    /// Look up a substituted type, panicking if it doesn't exist.
    ///
    /// This is a helper for codegen where all types should be fully instantiated.
    /// Panics with a detailed error message if the lookup fails.
    #[track_caller]
    pub fn expect_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
        context: &str,
    ) -> TypeId {
        self.lookup_substitute(ty, subs).unwrap_or_else(|| {
            panic!(
                "INTERNAL ERROR: Type not found after substitution\n\
                 Context: {}\n\
                 Original type: {}\n\
                 Location: {}",
                context,
                self.display_basic(ty),
                std::panic::Location::caller()
            )
        })
    }

    /// Substitute SelfType placeholders with a concrete type.
    ///
    /// Used when resolving interface method signatures on type parameters:
    /// the interface's `Self` type should be replaced with the receiver type.
    pub fn substitute_self(&mut self, ty: TypeId, self_type: TypeId) -> TypeId {
        // Clone the interned type to release the borrow
        match self.get(ty).clone() {
            // Substitute SelfType placeholder
            SemaType::Placeholder(PlaceholderKind::SelfType) => self_type,

            // Recursive substitution for compound types
            SemaType::Array(elem) => {
                let new_elem = self.substitute_self(elem, self_type);
                self.array(new_elem)
            }

            SemaType::Union(variants) => {
                let new_variants: TypeIdVec = variants
                    .iter()
                    .map(|&v| self.substitute_self(v, self_type))
                    .collect();
                self.union(new_variants)
            }

            SemaType::Tuple(elements) => {
                let new_elements: TypeIdVec = elements
                    .iter()
                    .map(|&e| self.substitute_self(e, self_type))
                    .collect();
                self.tuple(new_elements)
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: TypeIdVec = params
                    .iter()
                    .map(|&p| self.substitute_self(p, self_type))
                    .collect();
                let new_ret = self.substitute_self(ret, self_type);
                self.function(new_params, new_ret, is_closure)
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute_self(a, self_type))
                    .collect();
                self.class(type_def_id, new_args)
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute_self(a, self_type))
                    .collect();
                self.interface(type_def_id, new_args)
            }

            SemaType::RuntimeIterator(elem) => {
                let new_elem = self.substitute_self(elem, self_type);
                self.runtime_iterator(new_elem)
            }

            SemaType::FixedArray { element, size } => {
                let new_elem = self.substitute_self(element, self_type);
                self.fixed_array(new_elem, size)
            }

            SemaType::Fallible { success, error } => {
                let new_success = self.substitute_self(success, self_type);
                let new_error = self.substitute_self(error, self_type);
                self.fallible(new_success, new_error)
            }

            // Types that don't contain SelfType placeholders
            SemaType::Primitive(_)
            | SemaType::Handle
            | SemaType::TypeParam(_)
            | SemaType::TypeParamRef(_)
            | SemaType::Void
            | SemaType::Range
            | SemaType::MetaType
            | SemaType::Never
            | SemaType::Unknown
            | SemaType::Invalid { .. }
            | SemaType::Error { .. }
            | SemaType::Struct { .. }
            | SemaType::Module(_)
            | SemaType::Placeholder(PlaceholderKind::Inference)
            | SemaType::Placeholder(PlaceholderKind::TypeParam(_))
            | SemaType::Structural(_) => ty,
        }
    }

    /// Substitute Inference placeholders with a concrete type.
    ///
    /// Used when resolving builtin methods on generic types like Array<T>:
    /// the registered method signature has Placeholder(Inference) for the
    /// element type, which must be replaced with the actual element type.
    pub fn substitute_inference(&mut self, ty: TypeId, concrete: TypeId) -> TypeId {
        match self.get(ty).clone() {
            SemaType::Placeholder(PlaceholderKind::Inference) => concrete,

            SemaType::Array(elem) => {
                let new_elem = self.substitute_inference(elem, concrete);
                self.array(new_elem)
            }

            SemaType::Union(variants) => {
                let new_variants: TypeIdVec = variants
                    .iter()
                    .map(|&v| self.substitute_inference(v, concrete))
                    .collect();
                self.union(new_variants)
            }

            SemaType::Tuple(elements) => {
                let new_elements: TypeIdVec = elements
                    .iter()
                    .map(|&e| self.substitute_inference(e, concrete))
                    .collect();
                self.tuple(new_elements)
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: TypeIdVec = params
                    .iter()
                    .map(|&p| self.substitute_inference(p, concrete))
                    .collect();
                let new_ret = self.substitute_inference(ret, concrete);
                self.function(new_params, new_ret, is_closure)
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute_inference(a, concrete))
                    .collect();
                self.class(type_def_id, new_args)
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute_inference(a, concrete))
                    .collect();
                self.interface(type_def_id, new_args)
            }

            SemaType::RuntimeIterator(elem) => {
                let new_elem = self.substitute_inference(elem, concrete);
                self.runtime_iterator(new_elem)
            }

            SemaType::FixedArray { element, size } => {
                let new_elem = self.substitute_inference(element, concrete);
                self.fixed_array(new_elem, size)
            }

            SemaType::Fallible { success, error } => {
                let new_success = self.substitute_inference(success, concrete);
                let new_error = self.substitute_inference(error, concrete);
                self.fallible(new_success, new_error)
            }

            _ => ty,
        }
    }
}
