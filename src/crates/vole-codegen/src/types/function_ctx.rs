#![allow(dead_code)]
// types/function_ctx.rs
//
// Per-function compilation context.

use rustc_hash::FxHashMap;
use std::cell::RefCell;

use vole_identity::{ModuleId, NameId, TypeId, VirTypeId};
use vole_vir::type_table::VirTypeTable;

/// Per-function compilation context.
/// Contains state that varies for each function being compiled.
pub struct FunctionCtx<'a> {
    /// Return type of the current function (for raise statements)
    pub return_type: Option<TypeId>,
    /// Module being compiled (None for main program)
    pub current_module: Option<ModuleId>,
    /// Type parameter substitutions for monomorphized generics (VirTypeId-native)
    pub substitutions: Option<&'a FxHashMap<NameId, VirTypeId>>,
    /// Cache for substituted types (avoids repeated HashMap conversion and arena mutations)
    pub(crate) substitution_cache: RefCell<FxHashMap<TypeId, TypeId>>,
}

impl<'a> FunctionCtx<'a> {
    /// Create context for main program function (no module, no substitutions)
    pub fn main(return_type: Option<TypeId>) -> Self {
        Self {
            return_type,
            current_module: None,
            substitutions: None,
            substitution_cache: RefCell::new(FxHashMap::default()),
        }
    }

    /// Create context for module function
    pub fn module(return_type: Option<TypeId>, module_id: ModuleId) -> Self {
        Self {
            return_type,
            current_module: Some(module_id),
            substitutions: None,
            substitution_cache: RefCell::new(FxHashMap::default()),
        }
    }

    /// Create context for monomorphized generic function
    pub fn monomorphized(
        return_type: Option<TypeId>,
        substitutions: &'a FxHashMap<NameId, VirTypeId>,
    ) -> Self {
        Self {
            return_type,
            current_module: None,
            substitutions: Some(substitutions),
            substitution_cache: RefCell::new(FxHashMap::default()),
        }
    }

    /// Create context for test function (no return type)
    pub fn test() -> Self {
        Self {
            return_type: None,
            current_module: None,
            substitutions: None,
            substitution_cache: RefCell::new(FxHashMap::default()),
        }
    }

    /// Substitute type parameters with concrete types using TypeId directly.
    ///
    /// Uses VirTypeTable for structural type walking instead of the arena.
    /// Converts VirTypeId substitutions to TypeId before delegating.
    /// Uses a cache to avoid repeated lookups.
    pub fn substitute_type_id(&self, ty: TypeId, vir_table: &VirTypeTable) -> TypeId {
        if let Some(vir_subs) = self.substitutions {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            // Convert VirTypeId subs to TypeId subs for the VirTypeTable API.
            let sema_subs: FxHashMap<NameId, TypeId> = vir_subs
                .iter()
                .map(|(&name, &vir_ty)| {
                    let tid = vir_table.vir_to_type_id(vir_ty);
                    (name, tid)
                })
                .collect();
            let result =
                vir_table.expect_substitute(ty, &sema_subs, "FunctionCtx::substitute_type_id");
            // Cache the result
            self.substitution_cache.borrow_mut().insert(ty, result);
            result
        } else {
            ty
        }
    }
}
