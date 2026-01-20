// src/sema/infer.rs
//
// Type inference support: InferType and InferCtx for type unification.
//
// During type analysis, types may be either concrete (resolved) or
// inference variables (waiting to be unified). This module provides:
//
// - InferType: Either a resolved Type or an inference variable
// - InferVarId: Identifier for an inference variable
// - InferCtx: Context for managing variable bindings and unification

use crate::type_arena::{TypeArena, TypeId};

/// Identifier for an inference variable.
///
/// Inference variables are created during type checking when a type
/// is not yet known (e.g., `let x = [];` - element type unknown).
/// They are resolved through unification as more information is gathered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InferVarId(u32);

impl InferVarId {
    /// Create a new inference variable ID.
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value.
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }
}

/// Type during inference - either resolved or a variable.
///
/// This enum separates inference variables from concrete types,
/// allowing the type system to track what's known vs. unknown.
/// After inference completes, all InferTypes must resolve to Type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferType {
    /// A resolved concrete type (known).
    Resolved(TypeId),
    /// An inference variable (to be unified).
    Var(InferVarId),
}

impl InferType {
    /// Create a resolved type.
    #[inline]
    pub fn resolved(ty: TypeId) -> Self {
        InferType::Resolved(ty)
    }

    /// Create an inference variable.
    #[inline]
    pub fn var(id: InferVarId) -> Self {
        InferType::Var(id)
    }

    /// Check if this is a resolved type.
    #[inline]
    pub fn is_resolved(&self) -> bool {
        matches!(self, InferType::Resolved(_))
    }

    /// Check if this is an inference variable.
    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self, InferType::Var(_))
    }

    /// Get the resolved type, if any.
    #[inline]
    pub fn as_resolved(&self) -> Option<TypeId> {
        match self {
            InferType::Resolved(ty) => Some(*ty),
            InferType::Var(_) => None,
        }
    }

    /// Get the variable ID, if this is a variable.
    #[inline]
    pub fn as_var(&self) -> Option<InferVarId> {
        match self {
            InferType::Var(id) => Some(*id),
            InferType::Resolved(_) => None,
        }
    }
}

impl From<TypeId> for InferType {
    fn from(ty: TypeId) -> Self {
        InferType::Resolved(ty)
    }
}

/// Error during type unification.
#[derive(Debug, Clone)]
pub enum UnifyError {
    /// Types are incompatible and cannot be unified.
    Mismatch { expected: TypeId, found: TypeId },
    /// Occurs check failed - infinite type detected.
    OccursCheck { var: InferVarId, ty: TypeId },
}

/// Inference context for managing variable bindings.
///
/// Tracks inference variables and their resolved types during
/// type checking. Supports unification to find consistent types.
pub struct InferCtx {
    /// Bindings from inference variable to resolved type.
    /// None means the variable is still unbound.
    bindings: Vec<Option<TypeId>>,
}

impl InferCtx {
    /// Create a new inference context.
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    /// Create a fresh inference variable.
    pub fn fresh_var(&mut self) -> InferType {
        let id = InferVarId::new(self.bindings.len() as u32);
        self.bindings.push(None);
        InferType::Var(id)
    }

    /// Get the binding for an inference variable, if any.
    pub fn get(&self, var: InferVarId) -> Option<TypeId> {
        self.bindings.get(var.raw() as usize).copied().flatten()
    }

    /// Bind an inference variable to a type.
    ///
    /// Returns error if the variable is already bound to a different type.
    pub fn bind(&mut self, var: InferVarId, ty: TypeId) -> Result<(), UnifyError> {
        let idx = var.raw() as usize;
        if idx >= self.bindings.len() {
            // Extend bindings if needed
            self.bindings.resize(idx + 1, None);
        }

        match self.bindings[idx] {
            None => {
                self.bindings[idx] = Some(ty);
                Ok(())
            }
            Some(existing) if existing == ty => Ok(()),
            Some(existing) => Err(UnifyError::Mismatch {
                expected: existing,
                found: ty,
            }),
        }
    }

    /// Resolve an InferType to its concrete type, if fully resolved.
    ///
    /// Returns None if the type contains unbound inference variables.
    pub fn resolve(&self, t: InferType) -> Option<TypeId> {
        match t {
            InferType::Resolved(ty) => Some(ty),
            InferType::Var(var) => self.get(var),
        }
    }

    /// Unify two inference types.
    ///
    /// After successful unification, both types will resolve to the same
    /// concrete type. This may bind inference variables.
    pub fn unify(
        &mut self,
        a: InferType,
        b: InferType,
        _arena: &TypeArena,
    ) -> Result<(), UnifyError> {
        match (a, b) {
            // Both resolved - must be equal
            (InferType::Resolved(ta), InferType::Resolved(tb)) => {
                if ta == tb {
                    Ok(())
                } else {
                    Err(UnifyError::Mismatch {
                        expected: ta,
                        found: tb,
                    })
                }
            }

            // Variable unified with resolved type - bind variable
            (InferType::Var(var), InferType::Resolved(ty))
            | (InferType::Resolved(ty), InferType::Var(var)) => {
                // Check if already bound
                if let Some(existing) = self.get(var) {
                    if existing == ty {
                        Ok(())
                    } else {
                        Err(UnifyError::Mismatch {
                            expected: existing,
                            found: ty,
                        })
                    }
                } else {
                    self.bind(var, ty)
                }
            }

            // Two variables - bind one to the other's eventual type
            (InferType::Var(va), InferType::Var(vb)) => {
                if va == vb {
                    return Ok(());
                }

                // If one is bound, bind the other to same type
                match (self.get(va), self.get(vb)) {
                    (Some(ta), Some(tb)) => {
                        if ta == tb {
                            Ok(())
                        } else {
                            Err(UnifyError::Mismatch {
                                expected: ta,
                                found: tb,
                            })
                        }
                    }
                    (Some(ta), None) => self.bind(vb, ta),
                    (None, Some(tb)) => self.bind(va, tb),
                    (None, None) => {
                        // Both unbound - we'll link them later when one gets bound
                        // For now, just succeed (they're compatible until proven otherwise)
                        // TODO: implement union-find for proper variable linking
                        Ok(())
                    }
                }
            }
        }
    }

    /// Check if all variables are resolved.
    pub fn is_complete(&self) -> bool {
        self.bindings.iter().all(|b| b.is_some())
    }

    /// Get the number of inference variables.
    pub fn var_count(&self) -> usize {
        self.bindings.len()
    }

    /// Get the number of resolved variables.
    pub fn resolved_count(&self) -> usize {
        self.bindings.iter().filter(|b| b.is_some()).count()
    }
}

impl Default for InferCtx {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_arena::TypeArena;
    use crate::types::PrimitiveType;

    fn make_arena() -> TypeArena {
        TypeArena::new()
    }

    fn i32_type(arena: &TypeArena) -> TypeId {
        arena.primitive(PrimitiveType::I32)
    }

    fn i64_type(arena: &TypeArena) -> TypeId {
        arena.primitive(PrimitiveType::I64)
    }

    #[test]
    fn test_fresh_var() {
        let mut ctx = InferCtx::new();
        let v1 = ctx.fresh_var();
        let v2 = ctx.fresh_var();

        assert!(v1.is_var());
        assert!(v2.is_var());
        assert_ne!(v1.as_var(), v2.as_var());
        assert_eq!(ctx.var_count(), 2);
    }

    #[test]
    fn test_resolve_unbound() {
        let ctx = InferCtx::new();
        let arena = make_arena();
        let ty = i32_type(&arena);

        // Resolved type resolves to itself
        assert_eq!(ctx.resolve(InferType::Resolved(ty)), Some(ty));
    }

    #[test]
    fn test_bind_and_resolve() {
        let mut ctx = InferCtx::new();
        let arena = make_arena();
        let var = ctx.fresh_var();
        let ty = i32_type(&arena);

        // Initially unbound
        assert_eq!(ctx.resolve(var), None);

        // Bind variable
        ctx.bind(var.as_var().unwrap(), ty).unwrap();

        // Now resolves
        assert_eq!(ctx.resolve(var), Some(ty));
    }

    #[test]
    fn test_unify_same_type() {
        let mut ctx = InferCtx::new();
        let arena = make_arena();
        let ty = i32_type(&arena);

        let a = InferType::Resolved(ty);
        let b = InferType::Resolved(ty);

        assert!(ctx.unify(a, b, &arena).is_ok());
    }

    #[test]
    fn test_unify_different_types() {
        let mut ctx = InferCtx::new();
        let arena = make_arena();
        let ty1 = i32_type(&arena);
        let ty2 = i64_type(&arena);

        let a = InferType::Resolved(ty1);
        let b = InferType::Resolved(ty2);

        assert!(matches!(
            ctx.unify(a, b, &arena),
            Err(UnifyError::Mismatch { .. })
        ));
    }

    #[test]
    fn test_unify_var_with_type() {
        let mut ctx = InferCtx::new();
        let arena = make_arena();
        let var = ctx.fresh_var();
        let ty = i32_type(&arena);
        let resolved = InferType::Resolved(ty);

        // Unify variable with type
        assert!(ctx.unify(var, resolved, &arena).is_ok());

        // Variable now resolves to that type
        assert_eq!(ctx.resolve(var), Some(ty));
    }

    #[test]
    fn test_unify_two_vars() {
        let mut ctx = InferCtx::new();
        let arena = make_arena();
        let v1 = ctx.fresh_var();
        let v2 = ctx.fresh_var();

        // Unify two unbound variables
        assert!(ctx.unify(v1, v2, &arena).is_ok());

        // Both still unbound (until one gets a concrete type)
        assert_eq!(ctx.resolve(v1), None);
        assert_eq!(ctx.resolve(v2), None);
    }

    #[test]
    fn test_infer_type_from_type() {
        let arena = make_arena();
        let ty = i32_type(&arena);
        let infer: InferType = ty.into();

        assert!(infer.is_resolved());
        assert_eq!(infer.as_resolved(), Some(ty));
    }
}
