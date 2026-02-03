//! Central registry for all language entities.
//!
//! EntityRegistry stores type definitions, methods, fields, and functions,
//! providing type-safe lookups by ID and name.
//!
//! This module is split into submodules by functionality:
//! - `types` - Type registration and lookup
//! - `methods` - Method registration, lookup, and inheritance
//! - `fields` - Field registration, lookup, and substitution helpers
//! - `functions` - Free function registration and lookup
//! - `accessors` - Convenience methods that return owned data to avoid borrow conflicts

mod accessors;
mod fields;
mod functions;
mod globals;
mod method_builder;
mod methods;
mod types;

pub use method_builder::MethodDefBuilder;

use std::collections::HashSet;

use rustc_hash::FxHashMap;

use crate::entity_defs::{FieldDef, FunctionDef, GlobalDef, MethodDef, TypeDef, TypeDefKind};
use crate::generic::{ClassMethodMonomorphCache, MonomorphCache, StaticMethodMonomorphCache};
use crate::implement_registry::PrimitiveTypeId;
use crate::type_arena::{TypeId as ArenaTypeId, TypeIdVec};
use vole_identity::{FieldId, FunctionId, GlobalId, MethodId, NameId, TypeDefId};

pub use fields::{FieldSubstitutionCache, FieldSubstitutionKey};

/// Central registry for all language entities
#[derive(Debug, Clone)]
pub struct EntityRegistry {
    // Storage - IDs are indices into these vectors
    pub(crate) type_defs: Vec<TypeDef>,
    pub(crate) method_defs: Vec<MethodDef>,
    pub(crate) field_defs: Vec<FieldDef>,
    pub(crate) function_defs: Vec<FunctionDef>,
    pub(crate) global_defs: Vec<GlobalDef>,

    // Primary lookups by NameId
    pub(crate) type_by_name: FxHashMap<NameId, TypeDefId>,
    pub(crate) method_by_full_name: FxHashMap<NameId, MethodId>,
    pub(crate) field_by_full_name: FxHashMap<NameId, FieldId>,
    pub(crate) function_by_name: FxHashMap<NameId, FunctionId>,
    pub(crate) global_by_name: FxHashMap<NameId, GlobalId>,

    // Scoped lookups: (type, method_name) -> MethodId
    pub(crate) methods_by_type: FxHashMap<TypeDefId, FxHashMap<NameId, MethodId>>,
    pub(crate) fields_by_type: FxHashMap<TypeDefId, FxHashMap<NameId, FieldId>>,
    // Static method lookups: (type, static_method_name) -> MethodId
    pub(crate) static_methods_by_type: FxHashMap<TypeDefId, FxHashMap<NameId, MethodId>>,

    // Alias index: maps a TypeId to all aliases that resolve to that type
    pub(crate) alias_index: FxHashMap<ArenaTypeId, Vec<TypeDefId>>,

    /// NameIds for primitive types (for method dispatch)
    pub(crate) primitive_names: FxHashMap<PrimitiveTypeId, NameId>,
    /// NameId for the array type (for method dispatch)
    pub(crate) array_name: Option<NameId>,

    /// Cache of monomorphized generic function instances
    pub monomorph_cache: MonomorphCache,

    /// Cache of monomorphized generic class method instances
    pub class_method_monomorph_cache: ClassMethodMonomorphCache,

    /// Cache of monomorphized generic static method instances
    pub static_method_monomorph_cache: StaticMethodMonomorphCache,

    /// Cache of substituted field types for generic type instantiations
    pub field_substitution_cache: FieldSubstitutionCache,

    /// Lazy cache: short name (last segment) → TypeDefIds for class/interface/sentinel lookups.
    /// Built on first use, invalidated when new types are registered.
    /// Uses `RefCell` for interior mutability so `&self` lookup methods can populate lazily.
    pub(crate) short_name_cache: std::cell::RefCell<Option<FxHashMap<String, Vec<TypeDefId>>>>,
}

impl EntityRegistry {
    pub fn new() -> Self {
        Self {
            type_defs: Vec::new(),
            method_defs: Vec::new(),
            field_defs: Vec::new(),
            function_defs: Vec::new(),
            global_defs: Vec::new(),
            type_by_name: FxHashMap::default(),
            method_by_full_name: FxHashMap::default(),
            field_by_full_name: FxHashMap::default(),
            function_by_name: FxHashMap::default(),
            global_by_name: FxHashMap::default(),
            methods_by_type: FxHashMap::default(),
            fields_by_type: FxHashMap::default(),
            static_methods_by_type: FxHashMap::default(),
            alias_index: FxHashMap::default(),
            primitive_names: FxHashMap::default(),
            array_name: None,
            monomorph_cache: MonomorphCache::new(),
            class_method_monomorph_cache: ClassMethodMonomorphCache::new(),
            static_method_monomorph_cache: StaticMethodMonomorphCache::new(),
            field_substitution_cache: FieldSubstitutionCache::new(),
            short_name_cache: std::cell::RefCell::new(None),
        }
    }

    // ===== Type Relationships =====

    /// Add an extends relationship (derived extends base)
    pub fn add_extends(&mut self, derived: TypeDefId, base: TypeDefId) {
        self.type_defs[derived.index() as usize].extends.push(base);
    }

    /// Set type parameters for a generic type
    pub fn set_type_params(&mut self, type_id: TypeDefId, type_params: Vec<NameId>) {
        self.type_defs[type_id.index() as usize].type_params = type_params;
    }

    /// Set generic type info (type params, field names/types) for a class
    pub fn set_generic_info(
        &mut self,
        type_id: TypeDefId,
        info: crate::entity_defs::GenericTypeInfo,
    ) {
        self.type_defs[type_id.index() as usize].generic_info = Some(info);
    }

    /// Get generic type info (type params with constraints) for a class
    pub fn get_generic_info(
        &self,
        type_id: TypeDefId,
    ) -> Option<&crate::entity_defs::GenericTypeInfo> {
        self.type_defs[type_id.index() as usize]
            .generic_info
            .as_ref()
    }

    /// Set error type info for an error type
    pub fn set_error_info(&mut self, type_id: TypeDefId, info: crate::ErrorTypeInfo) {
        self.type_defs[type_id.index() as usize].error_info = Some(info);
    }

    /// Set the aliased type for a type alias
    pub fn set_aliased_type(&mut self, type_id: TypeDefId, aliased_type: ArenaTypeId) {
        self.type_defs[type_id.index() as usize].aliased_type = Some(aliased_type);
        // Update the alias index for inverse lookups (use TypeId directly as key)
        self.alias_index
            .entry(aliased_type)
            .or_default()
            .push(type_id);
    }

    /// Check if derived extends base (transitive)
    pub fn type_extends(&self, derived: TypeDefId, base: TypeDefId) -> bool {
        if derived == base {
            return true;
        }
        let mut stack = vec![derived];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            for parent in &self.type_defs[current.index() as usize].extends {
                if *parent == base {
                    return true;
                }
                stack.push(*parent);
            }
        }
        false
    }

    // ===== Interface Implementations =====

    /// Add an interface implementation to a type
    pub fn add_implementation(
        &mut self,
        type_id: TypeDefId,
        interface_id: TypeDefId,
        type_args: Vec<crate::type_arena::TypeId>,
    ) {
        self.add_implementation_with_target_args(type_id, interface_id, type_args, Vec::new());
    }

    /// Add an interface implementation to a type with target type specialization args.
    /// `target_type_args` records the concrete type args of the implementing type
    /// (e.g., [i64] for `implement Describable for Box<i64>`).
    pub fn add_implementation_with_target_args(
        &mut self,
        type_id: TypeDefId,
        interface_id: TypeDefId,
        type_args: Vec<crate::type_arena::TypeId>,
        target_type_args: Vec<crate::type_arena::TypeId>,
    ) {
        use crate::entity_defs::Implementation;
        self.type_defs[type_id.index() as usize]
            .implements
            .push(Implementation {
                interface: interface_id,
                type_args,
                target_type_args,
                method_bindings: Vec::new(),
            });
    }

    /// Add a method binding to an existing implementation
    pub fn add_method_binding(
        &mut self,
        type_id: TypeDefId,
        interface_id: TypeDefId,
        binding: crate::entity_defs::MethodBinding,
    ) {
        let type_def = &mut self.type_defs[type_id.index() as usize];
        // Find the implementation for this interface
        for impl_ in &mut type_def.implements {
            if impl_.interface == interface_id {
                impl_.method_bindings.push(binding);
                return;
            }
        }
        // If no implementation exists yet, create one (with empty type_args for implement blocks)
        use crate::entity_defs::Implementation;
        type_def.implements.push(Implementation {
            interface: interface_id,
            type_args: Vec::new(),
            target_type_args: Vec::new(),
            method_bindings: vec![binding],
        });
    }

    /// Get type arguments for a specific interface implementation
    #[must_use]
    pub fn get_implementation_type_args(
        &self,
        type_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> &[crate::type_arena::TypeId] {
        let type_def = &self.type_defs[type_id.index() as usize];
        for impl_ in &type_def.implements {
            if impl_.interface == interface_id {
                return &impl_.type_args;
            }
        }
        &[]
    }

    /// Get the target type args for a specific interface implementation.
    /// Returns the type args that the implementation targets (e.g., [i64] for
    /// `implement Describable for Box<i64>`). Empty if non-specialized.
    #[must_use]
    pub fn get_implementation_target_type_args(
        &self,
        type_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> &[crate::type_arena::TypeId] {
        let type_def = &self.type_defs[type_id.index() as usize];
        for impl_ in &type_def.implements {
            if impl_.interface == interface_id {
                return &impl_.target_type_args;
            }
        }
        &[]
    }

    /// Get all interface TypeDefIds that a type implements
    pub fn get_implemented_interfaces(&self, type_id: TypeDefId) -> Vec<TypeDefId> {
        self.type_defs[type_id.index() as usize]
            .implements
            .iter()
            .map(|impl_| impl_.interface)
            .collect()
    }

    /// Find a method binding for a type's interface implementation
    #[must_use]
    pub fn find_method_binding(
        &self,
        type_id: TypeDefId,
        method_name: NameId,
    ) -> Option<&crate::entity_defs::MethodBinding> {
        let type_def = &self.type_defs[type_id.index() as usize];
        for impl_ in &type_def.implements {
            for binding in &impl_.method_bindings {
                if binding.method_name == method_name {
                    return Some(binding);
                }
            }
        }
        None
    }

    /// Find a method binding with interface info for a type
    #[must_use]
    pub fn find_method_binding_with_interface(
        &self,
        type_id: TypeDefId,
        method_name: NameId,
    ) -> Option<(TypeDefId, &crate::entity_defs::MethodBinding)> {
        let type_def = &self.type_defs[type_id.index() as usize];
        for impl_ in &type_def.implements {
            for binding in &impl_.method_bindings {
                if binding.method_name == method_name {
                    return Some((impl_.interface, binding));
                }
            }
        }
        None
    }

    // ===== Type Builders =====

    /// Build a ClassType from a TypeDefId (for types registered as Class)
    pub fn build_class_type(&self, type_id: TypeDefId) -> Option<crate::ClassType> {
        use crate::ClassType;

        let type_def = self.get_type(type_id);
        if type_def.kind != TypeDefKind::Class {
            return None;
        }

        Some(ClassType {
            type_def_id: type_id,
            type_args_id: TypeIdVec::new(),
        })
    }

    /// Get the name_id for a ClassType
    pub fn class_name_id(&self, class_type: &crate::ClassType) -> NameId {
        self.get_type(class_type.type_def_id).name_id
    }

    // ===== Alias Management =====

    /// Get all type aliases that resolve to a given type.
    /// Returns an empty slice if no aliases point to this type.
    pub fn aliases_for(&self, type_id: ArenaTypeId) -> &[TypeDefId] {
        self.alias_index.get(&type_id).map_or(&[], |v| v.as_slice())
    }

    /// Register a type alias and update the alias index.
    pub fn register_alias(
        &mut self,
        name_id: NameId,
        module: vole_identity::ModuleId,
        aliased_type: ArenaTypeId,
    ) -> TypeDefId {
        // Register the type with kind Alias
        let id = TypeDefId::new(self.type_defs.len() as u32);
        self.type_defs.push(TypeDef {
            id,
            name_id,
            kind: TypeDefKind::Alias,
            module,
            methods: Vec::new(),
            fields: Vec::new(),
            extends: Vec::new(),
            type_params: Vec::new(),
            static_methods: Vec::new(),
            aliased_type: Some(aliased_type),
            generic_info: None,
            error_info: None,
            implements: Vec::new(),
            base_type_id: None,
        });
        self.type_by_name.insert(name_id, id);
        self.methods_by_type.insert(id, FxHashMap::default());
        self.fields_by_type.insert(id, FxHashMap::default());
        self.static_methods_by_type.insert(id, FxHashMap::default());
        *self.short_name_cache.borrow_mut() = None; // Invalidate short name cache

        // Update the alias index for inverse lookups (use TypeId directly as key)
        self.alias_index.entry(aliased_type).or_default().push(id);

        id
    }

    // ===== Registry Merge =====

    /// Merge another registry into this one.
    /// This is used when merging prelude definitions into the main analyzer.
    pub fn merge(&mut self, other: &EntityRegistry) {
        // Build a mapping from other's IDs to our new IDs
        let mut type_id_map: FxHashMap<TypeDefId, TypeDefId> = FxHashMap::default();

        // First pass: register all types (without methods/fields to avoid ID confusion)
        for other_type in &other.type_defs {
            // Check if we already have a type with this name
            if self.type_by_name.contains_key(&other_type.name_id) {
                // Type already exists, map to existing ID
                let existing_id = self.type_by_name[&other_type.name_id];
                type_id_map.insert(other_type.id, existing_id);
                // Note: implements merging happens after type_id_map is complete (see below)
            } else {
                // New type - add it
                let new_id = TypeDefId::new(self.type_defs.len() as u32);
                let mut new_type = other_type.clone();
                new_type.id = new_id;
                new_type.methods = Vec::new(); // Will be filled in later
                new_type.fields = Vec::new();
                new_type.extends = Vec::new(); // Will be remapped
                new_type.static_methods = Vec::new(); // Will be filled in later
                self.type_defs.push(new_type);
                self.type_by_name.insert(other_type.name_id, new_id);
                self.methods_by_type.insert(new_id, FxHashMap::default());
                self.fields_by_type.insert(new_id, FxHashMap::default());
                self.static_methods_by_type
                    .insert(new_id, FxHashMap::default());
                type_id_map.insert(other_type.id, new_id);
            }
        }

        // Second pass: register all methods (both regular and static)
        for other_method in &other.method_defs {
            let new_defining_type = type_id_map[&other_method.defining_type];
            let new_id = MethodId::new(self.method_defs.len() as u32);
            let mut new_method = other_method.clone();
            new_method.id = new_id;
            new_method.defining_type = new_defining_type;
            self.method_defs.push(new_method);
            self.method_by_full_name
                .insert(other_method.full_name_id, new_id);

            if other_method.is_static {
                self.type_defs[new_defining_type.index() as usize]
                    .static_methods
                    .push(new_id);
                self.static_methods_by_type
                    .entry(new_defining_type)
                    .or_default()
                    .insert(other_method.name_id, new_id);
            } else {
                self.type_defs[new_defining_type.index() as usize]
                    .methods
                    .push(new_id);
                self.methods_by_type
                    .entry(new_defining_type)
                    .or_default()
                    .insert(other_method.name_id, new_id);
            }
        }

        // Third pass: register all fields
        for other_field in &other.field_defs {
            let new_defining_type = type_id_map[&other_field.defining_type];
            let new_id = FieldId::new(self.field_defs.len() as u32);
            let mut new_field = other_field.clone();
            new_field.id = new_id;
            new_field.defining_type = new_defining_type;
            self.field_defs.push(new_field);
            self.type_defs[new_defining_type.index() as usize]
                .fields
                .push(new_id);
            self.field_by_full_name
                .insert(other_field.full_name_id, new_id);
            self.fields_by_type
                .entry(new_defining_type)
                .or_default()
                .insert(other_field.name_id, new_id);
        }

        // Fourth pass: fix extends relationships
        for other_type in &other.type_defs {
            let new_id = type_id_map[&other_type.id];
            let extends: Vec<TypeDefId> = other_type
                .extends
                .iter()
                .map(|&parent_id| type_id_map[&parent_id])
                .collect();
            self.type_defs[new_id.index() as usize].extends = extends;
        }

        // Fifth pass: merge implements (interface implementations with method bindings)
        // This is crucial for primitives which are registered early but get
        // their interface implementations (like Hashable for i64) from prelude.
        // We do this after type_id_map is complete so we can remap interface IDs.
        for other_type in &other.type_defs {
            let new_id = type_id_map[&other_type.id];
            for other_impl in &other_type.implements {
                // Remap the interface ID
                let mapped_interface = type_id_map
                    .get(&other_impl.interface)
                    .copied()
                    .unwrap_or(other_impl.interface);

                let existing_type = &mut self.type_defs[new_id.index() as usize];
                // Check if this interface is already implemented
                let interface_exists = existing_type
                    .implements
                    .iter()
                    .any(|i| i.interface == mapped_interface);
                if !interface_exists {
                    // Clone and remap the implementation
                    let mut new_impl = other_impl.clone();
                    new_impl.interface = mapped_interface;
                    existing_type.implements.push(new_impl);
                } else {
                    // Merge method bindings for existing interface implementation
                    for binding in &other_impl.method_bindings {
                        let existing_impl = existing_type
                            .implements
                            .iter_mut()
                            .find(|i| i.interface == mapped_interface)
                            .unwrap();
                        let binding_exists = existing_impl
                            .method_bindings
                            .iter()
                            .any(|b| b.method_name == binding.method_name);
                        if !binding_exists {
                            existing_impl.method_bindings.push(binding.clone());
                        }
                    }
                }
            }
        }

        // Merge functions
        for (name_id, func_id) in &other.function_by_name {
            if !self.function_by_name.contains_key(name_id) {
                let other_func = &other.function_defs[func_id.index() as usize];
                let new_id = FunctionId::new(self.function_defs.len() as u32);
                let mut new_func = other_func.clone();
                new_func.id = new_id;
                self.function_defs.push(new_func);
                self.function_by_name.insert(*name_id, new_id);
            }
        }

        // Primitive names and array name: merge from other
        for (prim, name_id) in &other.primitive_names {
            self.primitive_names.entry(*prim).or_insert(*name_id);
        }
        if self.array_name.is_none() {
            self.array_name = other.array_name;
        }

        // Monomorph cache: take other's (it was cloned from ours, so it has all our instances plus new ones)
        self.monomorph_cache = other.monomorph_cache.clone();

        // Invalidate short name cache since types were merged
        *self.short_name_cache.borrow_mut() = None;
    }

    // ===== Primitive/Array Names =====

    /// Register a NameId for a primitive type
    pub fn register_primitive_name(&mut self, prim: PrimitiveTypeId, name_id: NameId) {
        self.primitive_names.entry(prim).or_insert(name_id);
    }

    /// Register the NameId for the array type
    pub fn register_array_name(&mut self, name_id: NameId) {
        if self.array_name.is_none() {
            self.array_name = Some(name_id);
        }
    }

    /// Get the NameId for a primitive type
    pub fn primitive_name_id(&self, prim: PrimitiveTypeId) -> Option<NameId> {
        self.primitive_names.get(&prim).copied()
    }

    /// Get the NameId for the array type
    pub fn array_name_id(&self) -> Option<NameId> {
        self.array_name
    }

    /// Clear monomorph caches.
    ///
    /// Call this at the start of each main program analysis when using a shared cache.
    /// The monomorph caches store instances created during analysis of generic code,
    /// and these instances are specific to each program being analyzed.
    /// Prelude modules don't have generic classes that get monomorphized in the main
    /// program, so clearing these caches between test files is safe.
    pub fn clear_monomorph_caches(&mut self) {
        self.monomorph_cache = MonomorphCache::new();
        self.class_method_monomorph_cache = ClassMethodMonomorphCache::new();
        self.static_method_monomorph_cache = StaticMethodMonomorphCache::new();
        self.field_substitution_cache.clear();
    }
}

impl Default for EntityRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FunctionType;
    use crate::TypeArena;
    use vole_identity::NameTable;

    #[test]
    fn register_and_lookup_type() {
        let mut names = NameTable::new();
        let name_id = names.intern_raw(names.main_module(), &["TestType"]);

        let mut registry = EntityRegistry::new();
        let type_id = registry.register_type(name_id, TypeDefKind::Class, names.main_module());

        assert_eq!(registry.type_by_name(name_id), Some(type_id));
        assert_eq!(registry.get_type(type_id).name_id, name_id);
        assert_eq!(registry.get_type(type_id).kind, TypeDefKind::Class);
    }

    #[test]
    fn register_and_lookup_method() {
        let mut arena = TypeArena::new();
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["Iterator"]);
        let method_name = names.intern_raw(builtin_mod, &["next"]);
        let full_method_name = names.intern_raw(main_mod, &["Iterator", "next"]);

        let mut registry = EntityRegistry::new();
        let type_id = registry.register_type(type_name, TypeDefKind::Interface, main_mod);

        let signature = FunctionType::from_ids(&[], arena.i32(), false);
        let signature_id = signature.intern(&mut arena);

        let method_id =
            registry.register_method(type_id, method_name, full_method_name, signature_id, false);

        assert_eq!(
            registry.find_method_on_type(type_id, method_name),
            Some(method_id)
        );
        assert_eq!(registry.get_method(method_id).defining_type, type_id);
        assert_eq!(
            registry.methods_on_type(type_id).collect::<Vec<_>>(),
            vec![method_id]
        );
    }

    #[test]
    fn register_and_lookup_field() {
        let arena = TypeArena::new();
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["Point"]);
        let field_name = names.intern_raw(builtin_mod, &["x"]);
        let full_field_name = names.intern_raw(main_mod, &["Point", "x"]);

        let mut registry = EntityRegistry::new();
        let type_id = registry.register_type(type_name, TypeDefKind::Class, main_mod);

        let field_type_id = arena.i32();

        let field_id =
            registry.register_field(type_id, field_name, full_field_name, field_type_id, 0);

        assert_eq!(
            registry.find_field_on_type(type_id, field_name),
            Some(field_id)
        );
        assert_eq!(registry.get_field(field_id).defining_type, type_id);
        assert_eq!(registry.get_field(field_id).slot, 0);
        assert_eq!(
            registry.fields_on_type(type_id).collect::<Vec<_>>(),
            vec![field_id]
        );
    }

    #[test]
    fn register_and_lookup_function() {
        let arena = TypeArena::new();
        let mut names = NameTable::new();
        let math_mod = names.module_id("math");
        let func_name = names.intern_raw(math_mod, &["sin"]);

        let mut registry = EntityRegistry::new();

        let signature = FunctionType::from_ids(&[arena.f64()], arena.f64(), false);

        let func_id = registry.register_function(
            func_name, func_name, // For simple functions, name_id == full_name_id
            math_mod, signature,
        );

        assert_eq!(registry.function_by_name(func_name), Some(func_id));
        assert_eq!(registry.get_function(func_id).module, math_mod);
    }

    #[test]
    fn hierarchy_extends() {
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let base_name = names.intern_raw(main_mod, &["Base"]);
        let derived_name = names.intern_raw(main_mod, &["Derived"]);

        let mut registry = EntityRegistry::new();
        let base_id = registry.register_type(base_name, TypeDefKind::Interface, main_mod);
        let derived_id = registry.register_type(derived_name, TypeDefKind::Interface, main_mod);

        registry.add_extends(derived_id, base_id);

        assert!(registry.type_extends(derived_id, base_id));
        assert!(registry.type_extends(derived_id, derived_id)); // reflexive
        assert!(!registry.type_extends(base_id, derived_id)); // not reverse
    }

    #[test]
    fn resolve_inherited_method() {
        let mut arena = TypeArena::new();
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();

        let base_name = names.intern_raw(main_mod, &["Base"]);
        let derived_name = names.intern_raw(main_mod, &["Derived"]);
        let method_name = names.intern_raw(builtin_mod, &["foo"]);
        let full_method_name = names.intern_raw(main_mod, &["Base", "foo"]);

        let mut registry = EntityRegistry::new();
        let base_id = registry.register_type(base_name, TypeDefKind::Interface, main_mod);
        let derived_id = registry.register_type(derived_name, TypeDefKind::Interface, main_mod);

        let signature = FunctionType::from_ids(&[], arena.void(), false);
        let signature_id = signature.intern(&mut arena);

        let method_id =
            registry.register_method(base_id, method_name, full_method_name, signature_id, false);
        registry.add_extends(derived_id, base_id);

        // Method should be found on base directly
        assert_eq!(
            registry.find_method_on_type(base_id, method_name),
            Some(method_id)
        );
        // Method should NOT be found directly on derived
        assert_eq!(registry.find_method_on_type(derived_id, method_name), None);
        // But resolve_method should find it via inheritance
        assert_eq!(
            registry.resolve_method(derived_id, method_name),
            Some(method_id)
        );
        // all_methods should include inherited
        assert_eq!(registry.all_methods(derived_id), vec![method_id]);
    }
}
