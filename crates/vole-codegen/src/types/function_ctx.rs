// types/function_ctx.rs
//
// Per-function compilation context.

// Allow dead code during migration - FunctionCtx will be used as CompileCtx is phased out
#![allow(dead_code)]

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use vole_identity::{ModuleId, NameId};
use vole_sema::type_arena::{TypeArena, TypeId};

/// Per-function compilation context.
/// Contains state that varies for each function being compiled.
pub struct FunctionCtx<'a> {
    /// Return type of the current function (for raise statements)
    pub return_type: Option<TypeId>,
    /// Module being compiled (None for main program)
    pub current_module: Option<ModuleId>,
    /// Type parameter substitutions for monomorphized generics
    pub substitutions: Option<&'a HashMap<NameId, TypeId>>,
    /// Cache for substituted types (avoids repeated HashMap conversion and arena mutations)
    pub(crate) substitution_cache: RefCell<HashMap<TypeId, TypeId>>,
}

impl<'a> FunctionCtx<'a> {
    /// Create context for main program function (no module, no substitutions)
    pub fn main(return_type: Option<TypeId>) -> Self {
        Self {
            return_type,
            current_module: None,
            substitutions: None,
            substitution_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Create context for module function
    pub fn module(return_type: Option<TypeId>, module_id: ModuleId) -> Self {
        Self {
            return_type,
            current_module: Some(module_id),
            substitutions: None,
            substitution_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Create context for monomorphized generic function
    pub fn monomorphized(
        return_type: Option<TypeId>,
        substitutions: &'a HashMap<NameId, TypeId>,
    ) -> Self {
        Self {
            return_type,
            current_module: None,
            substitutions: Some(substitutions),
            substitution_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Create context for test function (no return type)
    pub fn test() -> Self {
        Self {
            return_type: None,
            current_module: None,
            substitutions: None,
            substitution_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Substitute type parameters with concrete types using TypeId directly.
    /// Uses a cache to avoid repeated HashMap conversion and arena mutations.
    pub fn substitute_type_id(&self, ty: TypeId, arena: &Rc<RefCell<TypeArena>>) -> TypeId {
        if let Some(substitutions) = self.substitutions {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            // Convert std HashMap to FxHashMap for arena compatibility
            let subs: FxHashMap<NameId, TypeId> =
                substitutions.iter().map(|(&k, &v)| (k, v)).collect();
            let update = vole_sema::ProgramUpdate::new(arena);
            let result = update.substitute(ty, &subs);
            // Cache the result
            self.substitution_cache.borrow_mut().insert(ty, result);
            result
        } else {
            ty
        }
    }
}
