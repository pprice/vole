use rustc_hash::FxHashMap;

use super::{Compiler, SelfParam};
use crate::FunctionKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{MethodInfo, TypeMetadata};
use vole_identity::{Interner, MethodId, ModuleId, NameId, Symbol, TypeDefId, TypeId};
use vole_runtime::type_registry::{FieldTypeTag, alloc_type_id, register_instance_type};

/// Convert a TypeId to a FieldTypeTag for runtime cleanup.
///
/// With RcHeader v2, we only need to distinguish Value (no cleanup) from Rc (needs rc_dec).
/// Each RC allocation's own drop_fn handles type-specific cleanup.
fn type_id_to_field_tag(ty: TypeId, arena: &vole_sema::type_arena::TypeArena) -> FieldTypeTag {
    if arena.is_unknown(ty) {
        FieldTypeTag::UnknownHeap
    } else if arena.is_interface(ty) {
        FieldTypeTag::Interface
    } else if arena.is_string(ty)
        || arena.is_array(ty)
        || arena.is_class(ty)
        || arena.is_handle(ty)
        || arena.is_function(ty)
    {
        FieldTypeTag::Rc
    } else if let Some(variants) = arena.unwrap_union(ty) {
        // Union fields use heap buffers. If any variant is RC, the buffer
        // needs union_heap_cleanup (not plain rc_dec) to handle the inner
        // payload and free the buffer.
        for &variant in variants {
            if type_id_to_field_tag(variant, arena).needs_cleanup() {
                return FieldTypeTag::UnionHeap;
            }
        }
        FieldTypeTag::Value
    } else {
        FieldTypeTag::Value
    }
}

impl Compiler<'_> {
    /// Register a method's func_key in the unified lookup map, keyed by type name + method name.
    fn register_method_func_key(
        &mut self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
        func_key: FunctionKey,
    ) {
        let type_name_id = self.analyzed.entity_type_name_id(type_def_id);
        self.state
            .method_func_keys
            .insert((type_name_id, method_name_id), func_key);
    }

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    pub(super) fn pre_register_class(&mut self, name: Symbol) -> CodegenResult<()> {
        let type_id = alloc_type_id();

        let query = self.analyzed;
        let module_id = self.program_module();
        let name_id = query.name_id(module_id, &[name]);

        // Look up the TypeDefId from EntityRegistry
        let type_def_id = self.analyzed.try_type_def_id(name_id).ok_or_else(|| {
            CodegenError::internal("pre_register_class: class not in entity registry")
        })?;

        // Use pre-computed base_type_id from sema (no mutable arena access needed)
        let vole_type_id = self
            .analyzed
            .get_type(type_def_id)
            .base_type_id
            .ok_or_else(|| {
                CodegenError::internal("pre_register_class: missing base_type_id from sema")
            })?;

        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id,
                field_slots: FxHashMap::default(),
                physical_slot_count: 0,
                vole_type: vole_type_id,
                method_infos: FxHashMap::default(),
            },
        );

        Ok(())
    }

    /// Finalize a class type: fill in field types and declare methods
    pub(super) fn finalize_class(&mut self, name: Symbol) -> CodegenResult<()> {
        let module_id = self.program_module();
        let type_def_id = self
            .analyzed
            .try_name_id(module_id, &[name])
            .and_then(|name_id| self.analyzed.try_type_def_id(name_id))
            .ok_or_else(|| {
                CodegenError::internal("finalize_class: class not in entity registry")
            })?;
        self.finalize_type(type_def_id, true)
    }

    /// Core implementation for finalizing a type (class or struct).
    /// - For classes: includes runtime type registration and interface handling
    /// - For structs: simpler path without runtime registration
    fn finalize_type(
        &mut self,
        type_def_id: TypeDefId,
        register_defaults: bool,
    ) -> CodegenResult<()> {
        let type_def = self.analyzed.get_type(type_def_id);
        let type_kind = type_def.type_kind();
        let is_class = type_def.is_class();

        // Get type_id: for classes, use pre-registered value; for structs, use 0
        let type_id = if is_class {
            self.state
                .type_metadata
                .get(&type_def_id)
                .ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "finalize_type: type not pre-registered",
                        type_kind.to_string(),
                    )
                })?
                .type_id
        } else {
            0 // Structs don't need runtime type IDs
        };

        // Build field slots map and optionally collect field type tags (classes only)
        let (field_slots, physical_slot_count, field_type_tags) =
            self.build_field_slots_and_tags(type_def_id, is_class)?;

        // Register field types in runtime type registry for cleanup (classes only)
        if is_class {
            register_instance_type(type_id, field_type_tags);
        }

        // Register instance methods (read method_ids from VirTypeDef)
        let method_ids: Vec<MethodId> = self.analyzed.get_type(type_def_id).methods.clone();
        let mut method_infos =
            self.register_type_instance_methods(&method_ids, type_def_id, type_kind)?;

        // Handle interface default methods (classes only)
        if is_class && register_defaults {
            let direct_method_ids: Vec<MethodId> =
                self.analyzed.get_type(type_def_id).methods.clone();
            self.register_interface_default_methods(
                &direct_method_ids,
                type_def_id,
                &mut method_infos,
            )?;
        }

        // Register static methods
        let static_method_ids: Vec<MethodId> =
            self.analyzed.get_type(type_def_id).static_methods.clone();
        if !static_method_ids.is_empty() {
            self.register_static_methods(&static_method_ids, type_def_id)?;
        }

        // Reuse the vole_type_id from pre_register
        let vole_type_id = self
            .state
            .type_metadata
            .get(&type_def_id)
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "finalize_type: type not pre-registered for vole_type",
                    type_kind.to_string(),
                )
            })?
            .vole_type;
        let name_id = self.analyzed.entity_type_name_id(type_def_id);
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id,
                field_slots,
                physical_slot_count,
                vole_type: vole_type_id,
                method_infos,
            },
        );
        Ok(())
    }

    /// Build field slots map and optionally field type tags for runtime cleanup.
    /// Build field slot mapping and optional type tags.
    /// Returns (field_slots, physical_slot_count, field_type_tags).
    /// For classes: i128 fields use 2 consecutive u64 slots in runtime storage,
    /// so field_slots maps to physical slot indices and physical_slot_count may exceed field count.
    /// For structs: field_slots maps to ordinal (sema) indices since struct_field_byte_offset
    /// computes byte offsets by iterating field_types up to the given index.
    fn build_field_slots_and_tags(
        &self,
        type_def_id: TypeDefId,
        is_class: bool,
    ) -> CodegenResult<(FxHashMap<String, usize>, usize, Vec<FieldTypeTag>)> {
        let mut field_slots = FxHashMap::default();
        let mut field_type_tags = Vec::new();

        let field_ids: Vec<_> = self.analyzed.fields_on_type(type_def_id).collect();

        // Remap sema slots to physical slots: i128 fields need 2 u64 slots.
        // Sort by sema slot to ensure deterministic physical slot assignment.
        let mut fields_by_slot: Vec<_> = field_ids
            .iter()
            .map(|&fid| {
                let fd = self.analyzed.get_field(fid);
                (fd.slot, fid)
            })
            .collect();
        fields_by_slot.sort_by_key(|(slot, _)| *slot);

        let arena = self.arena();
        let mut physical_slot = 0usize;
        for (ordinal, (_, field_id)) in fields_by_slot.iter().enumerate() {
            let field_def = self.analyzed.get_field(*field_id);
            let field_name = self
                .analyzed
                .last_segment(field_def.name_id)
                .ok_or_else(|| CodegenError::internal("field lookup: field has no name"))?;
            // Classes use physical slot indices (runtime instance storage).
            // Structs use ordinal indices (struct_field_byte_offset iterates field_types).
            let slot_key = if is_class { physical_slot } else { ordinal };
            field_slots.insert(field_name, slot_key);
            if is_class {
                field_type_tags.push(type_id_to_field_tag(field_def.sema_type_id, arena));
                // i128 uses 2 physical slots; add a Value tag for the high half
                if crate::types::is_wide_type(field_def.sema_type_id, arena) {
                    field_type_tags.push(FieldTypeTag::Value);
                }
            }
            physical_slot += crate::types::field_slot_count(field_def.sema_type_id, arena);
        }

        Ok((field_slots, physical_slot, field_type_tags))
    }

    /// Register instance methods for a type and return the method_infos map.
    ///
    /// Takes a slice of MethodId from VirTypeDef.methods instead of iterating
    /// AST FuncDecl nodes.  Inherited default methods (has_default=true) are
    /// skipped here — they are declared by `register_interface_default_methods`.
    fn register_type_instance_methods(
        &mut self,
        method_ids: &[MethodId],
        type_def_id: TypeDefId,
        _type_kind: &str,
    ) -> CodegenResult<FxHashMap<NameId, MethodInfo>> {
        let mut method_infos = FxHashMap::default();

        for &method_id in method_ids {
            let method_def = self.analyzed.get_method(method_id);
            // Skip inherited default methods — they are declared separately
            // by register_interface_default_methods.
            if method_def.has_default {
                continue;
            }
            let method_name_id = method_def.name_id;
            let sig = self.build_signature_for_method(method_id, SelfParam::Pointer);
            let full_name_id = self.analyzed.method_full_name(method_id);
            let func_key = self.func_registry.intern_name_id(full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);
            method_infos.insert(method_name_id, MethodInfo { func_key });
            self.register_method_func_key(type_def_id, method_name_id, func_key);
        }

        Ok(method_infos)
    }

    /// Register interface default methods on implementing class.
    ///
    /// This registers default methods from all implemented interfaces, including
    /// interfaces imported from stdlib modules. It works entirely from entity
    /// registry data so it does not need to search the AST.
    fn register_interface_default_methods(
        &mut self,
        direct_method_ids: &[MethodId],
        type_def_id: TypeDefId,
        method_infos: &mut FxHashMap<NameId, MethodInfo>,
    ) -> CodegenResult<()> {
        // Collect direct (non-default) method name strings to filter out explicitly
        // implemented methods.  We compare by string (cross-interner safe) rather than Symbol.
        // Only non-default methods count as "explicitly implemented" — inherited defaults
        // should NOT suppress the default method registration.
        let direct_method_name_strs: std::collections::HashSet<String> = direct_method_ids
            .iter()
            .filter_map(|&mid| {
                let md = self.analyzed.get_method(mid);
                if md.has_default {
                    return None;
                }
                self.analyzed.last_segment(md.name_id)
            })
            .collect();

        // Collect (interface_tdef_id, default_method_name_id pairs) from entity registry.
        // Works for interfaces from any program (main, stdlib, user modules) since
        // the entity registry is populated by sema regardless of which program the
        // interface was defined in.
        let default_method_ids: Vec<(TypeDefId, MethodId, NameId)> = {
            let query = self.analyzed;
            let mut results = Vec::new();
            for interface_tdef_id in query.implemented_interfaces(type_def_id) {
                let interface_method_ids = query.type_methods(interface_tdef_id);
                for method_id in interface_method_ids {
                    let method_def = query.get_method(method_id);
                    if !method_def.has_default {
                        continue;
                    }
                    // Skip external default methods - they are provided by the runtime,
                    // not compiled from Vole source. Declaring them without compiling
                    // would cause a JIT "can't resolve symbol" relocation error.
                    if method_def.external_binding.is_some() {
                        continue;
                    }
                    // Get method name string from name_table (cross-interner safe)
                    let method_name_str =
                        query.last_segment(method_def.name_id).unwrap_or_default();
                    if direct_method_name_strs.contains(&method_name_str) {
                        continue; // Explicitly implemented, skip
                    }
                    // NameId for this method on the implementing type (registered by sema)
                    let implementing_method_name_id = method_def.name_id;
                    // Find the method as registered on the implementing type
                    let implementing_method_id =
                        query.find_method(type_def_id, implementing_method_name_id);
                    if let Some(impl_method_id) = implementing_method_id {
                        results.push((
                            interface_tdef_id,
                            impl_method_id,
                            implementing_method_name_id,
                        ));
                    }
                }
            }
            results
        };

        // Register each default method in the JIT function registry
        for (_interface_tdef_id, semantic_method_id, method_name_id) in default_method_ids {
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
            let method_def = self.analyzed.get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);
            method_infos.insert(method_name_id, MethodInfo { func_key });
            self.register_method_func_key(type_def_id, method_name_id, func_key);
        }
        Ok(())
    }

    /// Pre-register a struct type (just the name and type_id)
    /// Structs are stack-allocated value types, so no runtime type registration is needed.
    pub(super) fn pre_register_struct(&mut self, name: Symbol) -> CodegenResult<()> {
        let query = self.analyzed;
        let module_id = self.program_module();
        let name_id = query.name_id(module_id, &[name]);

        let type_def_id = self.analyzed.try_type_def_id(name_id).ok_or_else(|| {
            CodegenError::internal("pre_register_struct: struct not in entity registry")
        })?;

        let vole_type_id = self
            .analyzed
            .get_type(type_def_id)
            .base_type_id
            .ok_or_else(|| {
                CodegenError::internal("pre_register_struct: missing base_type_id from sema")
            })?;

        // Structs don't need a runtime type_id since they're stack-allocated,
        // but we still need type_metadata for field slot lookup during codegen.
        // Use type_id 0 as a sentinel since it won't be used at runtime.
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id: 0,
                field_slots: FxHashMap::default(),
                physical_slot_count: 0,
                vole_type: vole_type_id,
                method_infos: FxHashMap::default(),
            },
        );

        Ok(())
    }

    /// Pre-register a sentinel type in codegen.
    /// Sentinels are zero-field structs, so they need minimal metadata.
    pub(super) fn pre_register_sentinel(&mut self, name: Symbol) -> CodegenResult<()> {
        let query = self.analyzed;
        let module_id = self.program_module();
        let name_id = query.name_id(module_id, &[name]);

        let type_def_id = self.analyzed.try_type_def_id(name_id).ok_or_else(|| {
            CodegenError::internal("pre_register_sentinel: sentinel not in entity registry")
        })?;

        let vole_type_id = self
            .analyzed
            .get_type(type_def_id)
            .base_type_id
            .ok_or_else(|| {
                CodegenError::internal("pre_register_sentinel: missing base_type_id from sema")
            })?;

        // Sentinels are zero-field structs, use type_id 0 as a placeholder.
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id: 0,
                field_slots: FxHashMap::default(),
                physical_slot_count: 0,
                vole_type: vole_type_id,
                method_infos: FxHashMap::default(),
            },
        );

        Ok(())
    }

    /// Register a module sentinel type in codegen.
    /// Sentinels from imported modules (like prelude's Done and nil) need metadata
    /// registered so that struct literal codegen can find them.
    pub(super) fn finalize_module_sentinel(
        &mut self,
        name: Symbol,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let type_name_str = module_interner.resolve(name);
        tracing::debug!(type_name = %type_name_str, "finalize_module_sentinel called");

        // Look up the TypeDefId using the sentinel name via full resolution chain
        let query = self.analyzed;
        let Some(type_def_id) = query.resolve_type_def_by_str(module_id, type_name_str) else {
            tracing::warn!(type_name = %type_name_str, "Could not find TypeDefId for module sentinel");
            return Ok(());
        };

        // Skip if already registered
        if self.state.type_metadata.contains_key(&type_def_id) {
            tracing::debug!(type_name = %type_name_str, "Skipping - already registered in type_metadata");
            return Ok(());
        }

        let vole_type_id = self
            .analyzed
            .get_type(type_def_id)
            .base_type_id
            .ok_or_else(|| {
                CodegenError::internal("finalize_module_sentinel: missing base_type_id from sema")
            })?;

        // Sentinels are zero-field structs, use type_id 0 as a placeholder.
        let name_id = self.analyzed.entity_type_name_id(type_def_id);
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id: 0,
                field_slots: FxHashMap::default(),
                physical_slot_count: 0,
                vole_type: vole_type_id,
                method_infos: FxHashMap::default(),
            },
        );

        Ok(())
    }

    /// Finalize a struct type: fill in field slots and register instance methods.
    pub(super) fn finalize_struct(&mut self, name: Symbol) -> CodegenResult<()> {
        let module_id = self.program_module();
        let type_def_id = self
            .analyzed
            .try_name_id(module_id, &[name])
            .and_then(|name_id| self.analyzed.try_type_def_id(name_id))
            .ok_or_else(|| {
                CodegenError::internal("finalize_struct: struct not in entity registry")
            })?;
        // Structs don't implement interfaces, so no default method registration
        self.finalize_type(type_def_id, false)
    }

    /// Register static methods for a type from VIR metadata.
    ///
    /// Takes a slice of static MethodId from VirTypeDef.static_methods.
    fn register_static_methods(
        &mut self,
        static_method_ids: &[MethodId],
        type_def_id: TypeDefId,
    ) -> CodegenResult<()> {
        for &method_id in static_method_ids {
            let method_def = self.analyzed.get_method(method_id);

            // Skip external-only statics (no Vole body to compile)
            if method_def.external_binding.is_some() {
                continue;
            }

            let method_name_id = method_def.name_id;

            let sig = self.build_signature_for_method(method_id, SelfParam::None);

            // Function key from method full name
            let func_key = self
                .func_registry
                .intern_name_id(self.analyzed.method_full_name(method_id));
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            self.register_method_func_key(type_def_id, method_name_id, func_key);
        }
        Ok(())
    }

    /// Register and finalize a module class (uses module interner)
    pub(super) fn finalize_module_class(
        &mut self,
        name: Symbol,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let type_name_str = module_interner.resolve(name);
        self.finalize_module_type_by_name(type_name_str, module_id)
    }

    /// Register and finalize a module struct (uses module interner).
    pub(super) fn finalize_module_struct(
        &mut self,
        name: Symbol,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let type_name_str = module_interner.resolve(name);
        self.finalize_module_type_by_name(type_name_str, module_id)
    }

    /// Core implementation for finalizing a module type (class or struct).
    /// Resolves the type by name string and delegates to VIR-based registration.
    /// - For classes: includes runtime type registration with field_type_tags
    /// - For structs: simpler path without runtime registration
    fn finalize_module_type_by_name(
        &mut self,
        type_name_str: &str,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        tracing::debug!(type_name = %type_name_str, "finalize_module_type called");

        // Look up the TypeDefId via full resolution chain
        let query = self.analyzed;
        let Some(type_def_id) = query.resolve_type_def_by_str(module_id, type_name_str) else {
            tracing::warn!(type_name = %type_name_str, "Could not find TypeDefId for module type");
            return Ok(());
        };
        tracing::debug!(type_name = %type_name_str, ?type_def_id, "Found TypeDefId for module type");

        // Skip if already registered
        if self.state.type_metadata.contains_key(&type_def_id) {
            tracing::debug!(type_name = %type_name_str, "Skipping - already registered in type_metadata");
            return Ok(());
        }

        let type_def = self.analyzed.get_type(type_def_id);
        let type_kind = type_def.type_kind();
        let is_class = type_def.is_class();
        let is_generic_type = type_def.has_type_params();

        tracing::debug!(type_name = %type_name_str, type_kind, "finalizing module type");

        // Allocate type_id for classes; structs use 0
        let type_id = if is_class { alloc_type_id() } else { 0 };

        // Build field slots and optionally collect field_type_tags (classes only)
        let (field_slots, physical_slot_count, field_type_tags) =
            self.build_field_slots_and_tags(type_def_id, is_class)?;

        // Register field types in runtime type registry (classes only)
        if is_class {
            register_instance_type(type_id, field_type_tags);
        }

        // Register instance methods using VIR metadata.
        // Generic types are compiled via monomorphized instances, so skip direct
        // method declaration here to avoid declaring functions that never compile.
        let method_infos = if is_generic_type {
            FxHashMap::default()
        } else {
            let method_ids: Vec<MethodId> = self.analyzed.get_type(type_def_id).methods.clone();
            self.register_module_type_instance_methods(&method_ids, type_def_id, type_name_str)?
        };

        // Register type metadata
        let vole_type_id = self
            .analyzed
            .get_type(type_def_id)
            .base_type_id
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "finalize_module_type: missing base_type_id from sema",
                    type_kind.to_string(),
                )
            })?;
        let name_id = self.analyzed.entity_type_name_id(type_def_id);
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id,
                field_slots,
                physical_slot_count,
                vole_type: vole_type_id,
                method_infos,
            },
        );

        // Register static methods for non-generic types.
        // Generic type statics are emitted from static-method monomorph instances.
        if !is_generic_type {
            let static_method_ids: Vec<MethodId> =
                self.analyzed.get_type(type_def_id).static_methods.clone();
            if !static_method_ids.is_empty() {
                self.register_module_type_static_methods(
                    &static_method_ids,
                    type_def_id,
                    type_name_str,
                )?;
            }
        }

        Ok(())
    }

    /// Register instance methods for a module type using VIR metadata.
    ///
    /// Iterates MethodId from VirTypeDef.methods to register each method in the
    /// JIT function registry.  Inherited default methods (has_default=true) are
    /// skipped — they are declared and compiled through the implement block path.
    fn register_module_type_instance_methods(
        &mut self,
        method_ids: &[MethodId],
        type_def_id: TypeDefId,
        type_name_str: &str,
    ) -> CodegenResult<FxHashMap<NameId, MethodInfo>> {
        let mut method_infos = FxHashMap::default();

        tracing::debug!(
            type_name = %type_name_str,
            method_count = method_ids.len(),
            "Registering instance methods"
        );

        for &method_id in method_ids {
            let method_def = self.analyzed.get_method(method_id);
            // Skip inherited default methods — they are declared and compiled
            // through the implement block path, not the module type path.
            if method_def.has_default {
                continue;
            }
            let method_name_id = method_def.name_id;
            let method_name_str = self
                .analyzed
                .last_segment(method_name_id)
                .unwrap_or_default();
            tracing::debug!(
                type_name = %type_name_str,
                method_name = %method_name_str,
                "Processing instance method"
            );

            let sig = self.build_signature_for_method(method_id, SelfParam::Pointer);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            tracing::debug!(
                type_name = %type_name_str,
                method_name = %method_name_str,
                method_name_id = ?method_name_id,
                "Registered instance method"
            );
            method_infos.insert(method_name_id, MethodInfo { func_key });
            self.register_method_func_key(type_def_id, method_name_id, func_key);
        }

        tracing::debug!(
            type_name = %type_name_str,
            registered_count = method_infos.len(),
            "Finished registering instance methods"
        );

        Ok(method_infos)
    }

    /// Register static methods for a module type using VIR metadata.
    ///
    /// Iterates MethodId from VirTypeDef.static_methods to register each static
    /// method in the JIT function registry.
    fn register_module_type_static_methods(
        &mut self,
        static_method_ids: &[MethodId],
        type_def_id: TypeDefId,
        type_name_str: &str,
    ) -> CodegenResult<()> {
        for &method_id in static_method_ids {
            let method_def = self.analyzed.get_method(method_id);

            // Skip external-only statics (no Vole body to compile)
            if method_def.external_binding.is_some() {
                continue;
            }

            let method_name_id = method_def.name_id;
            let method_name_str_local = self
                .analyzed
                .last_segment(method_name_id)
                .unwrap_or_default();

            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            tracing::debug!(
                type_name = %type_name_str,
                method_name = %method_name_str_local,
                "Registering static method"
            );

            self.register_method_func_key(type_def_id, method_name_id, func_key);
        }

        Ok(())
    }
}
