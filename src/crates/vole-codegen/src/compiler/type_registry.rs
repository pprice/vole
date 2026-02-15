use rustc_hash::FxHashMap;

use super::impls::TypeDeclInfo;
use super::{Compiler, SelfParam};
use crate::FunctionKey;
use crate::errors::CodegenResult;
use crate::types::{MethodInfo, TypeMetadata, method_name_id_with_interner};
use vole_frontend::ast::{ClassDecl, InterfaceDecl, SentinelDecl, StaticsBlock, StructDecl};
use vole_frontend::{Decl, Interner, Program, Symbol};
use vole_identity::{ModuleId, NameId, TypeDefId};
use vole_runtime::type_registry::{FieldTypeTag, alloc_type_id, register_instance_type};
use vole_sema::type_arena::TypeId;

/// Convert a TypeId to a FieldTypeTag for runtime cleanup.
///
/// With RcHeader v2, we only need to distinguish Value (no cleanup) from Rc (needs rc_dec).
/// Each RC allocation's own drop_fn handles type-specific cleanup.
fn type_id_to_field_tag(ty: TypeId, arena: &vole_sema::type_arena::TypeArena) -> FieldTypeTag {
    if arena.is_interface(ty) {
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
        let type_name_id = self.query().get_type(type_def_id).name_id;
        self.state
            .method_func_keys
            .insert((type_name_id, method_name_id), func_key);
    }

    /// Find an interface declaration by name in the program
    pub(super) fn find_interface_decl<'b>(
        &self,
        program: &'b Program,
        interface_name: Symbol,
    ) -> Option<&'b InterfaceDecl> {
        for decl in &program.declarations {
            if let Decl::Interface(iface) = decl
                && iface.name == interface_name
            {
                return Some(iface);
            }
        }
        None
    }

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    pub(super) fn pre_register_class(&mut self, class: &ClassDecl) {
        let type_id = alloc_type_id();

        let query = self.query();
        let module_id = self.program_module();
        let name_id = query.name_id(module_id, &[class.name]);

        // Look up the TypeDefId from EntityRegistry
        let type_def_id = self
            .query()
            .try_type_def_id(name_id)
            .expect("INTERNAL: pre_register_class: class not in entity registry");

        // Use pre-computed base_type_id from sema (no mutable arena access needed)
        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .expect("INTERNAL: pre_register_class: missing base_type_id from sema");

        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id,
                field_slots: FxHashMap::default(),
                physical_slot_count: 0,
                vole_type: vole_type_id,
                type_def_id,
                method_infos: FxHashMap::default(),
            },
        );
    }

    /// Finalize a class type: fill in field types and declare methods
    pub(super) fn finalize_class(
        &mut self,
        class: &ClassDecl,
        program: &Program,
    ) -> CodegenResult<()> {
        self.finalize_type(class, Some(program))
    }

    /// Core implementation for finalizing a type (class or struct).
    /// - For classes: includes runtime type registration and interface handling
    /// - For structs: simpler path without runtime registration
    fn finalize_type<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        program: Option<&Program>,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        let type_kind = type_decl.type_kind();
        let is_class = type_decl.is_class();

        // Look up TypeDefId first (needed as key for type_metadata)
        let type_def_id = self
            .query()
            .try_name_id(module_id, &[type_decl.name()])
            .and_then(|name_id| self.query().try_type_def_id(name_id))
            .unwrap_or_else(|| {
                panic!(
                    "INTERNAL: finalize_{}: {} not in entity registry",
                    type_kind, type_kind
                )
            });

        // Get type_id: for classes, use pre-registered value; for structs, use 0
        let type_id = if is_class {
            self.state
                .type_metadata
                .get(&type_def_id)
                .unwrap_or_else(|| {
                    panic!(
                        "INTERNAL: finalize_{}: {} not pre-registered",
                        type_kind, type_kind
                    )
                })
                .type_id
        } else {
            0 // Structs don't need runtime type IDs
        };

        // Build field slots map and optionally collect field type tags (classes only)
        let (field_slots, physical_slot_count, field_type_tags) =
            self.build_field_slots_and_tags(type_def_id, is_class);

        // Register field types in runtime type registry for cleanup (classes only)
        if is_class {
            register_instance_type(type_id, field_type_tags);
        }

        // Register instance methods
        let mut method_infos =
            self.register_type_instance_methods(type_decl, type_def_id, type_kind)?;

        // Handle interface default methods (classes only, requires program)
        if is_class && let Some(prog) = program {
            self.register_interface_default_methods(
                type_decl,
                type_def_id,
                module_id,
                prog,
                &mut method_infos,
            )?;
        }

        // Register static methods from statics block
        if let Some(statics) = type_decl.statics() {
            self.register_static_methods(statics, type_decl.name())?;
        }

        // Reuse the vole_type_id from pre_register
        let vole_type_id = self
            .state
            .type_metadata
            .get(&type_def_id)
            .unwrap_or_else(|| {
                panic!(
                    "INTERNAL: finalize_{}: {} not pre-registered for vole_type",
                    type_kind, type_kind
                )
            })
            .vole_type;
        let name_id = self.query().get_type(type_def_id).name_id;
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id,
                field_slots,
                physical_slot_count,
                vole_type: vole_type_id,
                type_def_id,
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
    ) -> (FxHashMap<String, usize>, usize, Vec<FieldTypeTag>) {
        let mut field_slots = FxHashMap::default();
        let mut field_type_tags = Vec::new();

        let field_ids: Vec<_> = self
            .analyzed
            .entity_registry()
            .fields_on_type(type_def_id)
            .collect();

        // Remap sema slots to physical slots: i128 fields need 2 u64 slots.
        // Sort by sema slot to ensure deterministic physical slot assignment.
        let mut fields_by_slot: Vec<_> = field_ids
            .iter()
            .map(|&fid| {
                let fd = self.registry().get_field(fid);
                (fd.slot, fid)
            })
            .collect();
        fields_by_slot.sort_by_key(|(slot, _)| *slot);

        let arena = self.arena();
        let mut physical_slot = 0usize;
        for (ordinal, (_, field_id)) in fields_by_slot.iter().enumerate() {
            let field_def = self.registry().get_field(*field_id);
            let field_name = self
                .query()
                .last_segment(field_def.name_id)
                .expect("INTERNAL: field lookup: field has no name");
            // Classes use physical slot indices (runtime instance storage).
            // Structs use ordinal indices (struct_field_byte_offset iterates field_types).
            let slot_key = if is_class { physical_slot } else { ordinal };
            field_slots.insert(field_name, slot_key);
            if is_class {
                field_type_tags.push(type_id_to_field_tag(field_def.ty, arena));
                // i128 uses 2 physical slots; add a Value tag for the high half
                if crate::types::is_wide_type(field_def.ty, arena) {
                    field_type_tags.push(FieldTypeTag::Value);
                }
            }
            physical_slot += crate::types::field_slot_count(field_def.ty, arena);
        }

        (field_slots, physical_slot, field_type_tags)
    }

    /// Register instance methods for a type and return the method_infos map.
    fn register_type_instance_methods<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        type_def_id: TypeDefId,
        type_kind: &str,
    ) -> CodegenResult<FxHashMap<NameId, MethodInfo>> {
        let mut method_infos = FxHashMap::default();

        for method in type_decl.methods() {
            let method_name_id = self.method_name_id(method.name)?;
            let method_id = self
                .analyzed
                .entity_registry()
                .find_method_on_type(type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    panic!(
                        "INTERNAL: finalize_{}: method not in entity registry",
                        type_kind
                    )
                });
            let sig = self.build_signature_for_method(method_id, SelfParam::Pointer);
            let full_name_id = self
                .analyzed
                .entity_registry()
                .get_method(method_id)
                .full_name_id;
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
    fn register_interface_default_methods<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        type_def_id: TypeDefId,
        module_id: ModuleId,
        program: &Program,
        method_infos: &mut FxHashMap<NameId, MethodInfo>,
    ) -> CodegenResult<()> {
        // Collect method names that the type directly defines
        let direct_methods: std::collections::HashSet<_> =
            type_decl.methods().iter().map(|m| m.name).collect();

        // Collect interface info first to avoid borrow conflicts
        let interfaces_to_process: Vec<_> = {
            let query = self.query();
            query
                .try_name_id(module_id, &[type_decl.name()])
                .and_then(|name_id| query.try_type_def_id(name_id))
                .map(|tdef_id| {
                    query
                        .implemented_interfaces(tdef_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            let interface_def = query.get_type(interface_id);
                            let interface_name_str = query.last_segment(interface_def.name_id)?;
                            let interface_name = query.try_symbol(&interface_name_str)?;
                            Some(interface_name)
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        for interface_name in interfaces_to_process {
            if let Some(interface_decl) = self.find_interface_decl(program, interface_name) {
                for method in &interface_decl.methods {
                    if method.body.is_some() && !direct_methods.contains(&method.name) {
                        let method_name_id = self.method_name_id(method.name)?;
                        let semantic_method_id = self
                            .analyzed
                            .entity_registry()
                            .find_method_on_type(type_def_id, method_name_id)
                            .unwrap_or_else(|| {
                                let type_name_str = self.resolve_symbol(type_decl.name());
                                let method_name_str = self.resolve_symbol(method.name);
                                panic!(
                                    "interface default method not registered on implementing {}: {}::{} (type_def_id={:?}, method_name_id={:?})",
                                    type_decl.type_kind(), type_name_str, method_name_str, type_def_id, method_name_id
                                )
                            });
                        let sig =
                            self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
                        let method_def = self
                            .analyzed
                            .entity_registry()
                            .get_method(semantic_method_id);
                        let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
                        let display_name = self.func_registry.display(func_key);
                        let jit_func_id = self.jit.declare_function(&display_name, &sig);
                        self.func_registry.set_func_id(func_key, jit_func_id);
                        method_infos.insert(method_name_id, MethodInfo { func_key });
                        self.register_method_func_key(type_def_id, method_name_id, func_key);
                    }
                }
            }
        }
        Ok(())
    }

    /// Pre-register a struct type (just the name and type_id)
    /// Structs are stack-allocated value types, so no runtime type registration is needed.
    pub(super) fn pre_register_struct(&mut self, struct_decl: &StructDecl) {
        let query = self.query();
        let module_id = self.program_module();
        let name_id = query.name_id(module_id, &[struct_decl.name]);

        let type_def_id = self
            .query()
            .try_type_def_id(name_id)
            .expect("INTERNAL: pre_register_struct: struct not in entity registry");

        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .expect("INTERNAL: pre_register_struct: missing base_type_id from sema");

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
                type_def_id,
                method_infos: FxHashMap::default(),
            },
        );
    }

    /// Pre-register a sentinel type in codegen.
    /// Sentinels are zero-field structs, so they need minimal metadata.
    pub(super) fn pre_register_sentinel(&mut self, sentinel_decl: &SentinelDecl) {
        let query = self.query();
        let module_id = self.program_module();
        let name_id = query.name_id(module_id, &[sentinel_decl.name]);

        let type_def_id = self
            .query()
            .try_type_def_id(name_id)
            .expect("INTERNAL: pre_register_sentinel: sentinel not in entity registry");

        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .expect("INTERNAL: pre_register_sentinel: missing base_type_id from sema");

        // Sentinels are zero-field structs, use type_id 0 as a placeholder.
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id: 0,
                field_slots: FxHashMap::default(),
                physical_slot_count: 0,
                vole_type: vole_type_id,
                type_def_id,
                method_infos: FxHashMap::default(),
            },
        );
    }

    /// Register a module sentinel type in codegen.
    /// Sentinels from imported modules (like prelude's Done and nil) need metadata
    /// registered so that struct literal codegen can find them.
    pub(super) fn finalize_module_sentinel(
        &mut self,
        sentinel_decl: &SentinelDecl,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        let type_name_str = module_interner.resolve(sentinel_decl.name);
        tracing::debug!(type_name = %type_name_str, "finalize_module_sentinel called");

        // Look up the TypeDefId using the sentinel name via full resolution chain
        let query = self.query();
        let Some(type_def_id) = query.resolve_type_def_by_str(module_id, type_name_str) else {
            tracing::warn!(type_name = %type_name_str, "Could not find TypeDefId for module sentinel");
            return;
        };

        // Skip if already registered
        if self.state.type_metadata.contains_key(&type_def_id) {
            tracing::debug!(type_name = %type_name_str, "Skipping - already registered in type_metadata");
            return;
        }

        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .expect("INTERNAL: finalize_module_sentinel: missing base_type_id from sema");

        // Sentinels are zero-field structs, use type_id 0 as a placeholder.
        let name_id = self.query().get_type(type_def_id).name_id;
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id: 0,
                field_slots: FxHashMap::default(),
                physical_slot_count: 0,
                vole_type: vole_type_id,
                type_def_id,
                method_infos: FxHashMap::default(),
            },
        );
    }

    /// Finalize a struct type: fill in field slots and register instance methods.
    pub(super) fn finalize_struct(&mut self, struct_decl: &StructDecl) -> CodegenResult<()> {
        // Structs don't implement interfaces, so no program needed
        self.finalize_type(struct_decl, None)
    }

    /// Register static methods from a statics block for a type
    fn register_static_methods(
        &mut self,
        statics: &StaticsBlock,
        type_name: Symbol,
    ) -> CodegenResult<()> {
        // Get the TypeDefId for this type from entity_registry
        let query = self.query();
        let module_id = self.program_module();
        let type_name_id = query.name_id(module_id, &[type_name]);
        let type_def_id = query
            .try_type_def_id(type_name_id)
            .expect("INTERNAL: register_static_methods: type not in entity registry");

        for method in &statics.methods {
            // Only register methods with bodies (not abstract ones)
            if method.body.is_none() {
                continue;
            }

            let method_name_id = self.method_name_id(method.name)?;

            // Get MethodId and build signature from pre-resolved types
            let method_id = self
                .analyzed
                .entity_registry()
                .find_static_method_on_type(type_def_id, method_name_id)
                .expect("INTERNAL: register_static_methods: static method not in entity registry");
            let sig = self.build_signature_for_method(method_id, SelfParam::None);

            // Function key from entity registry
            let method_def = self.registry().get_method(method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
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
        class: &ClassDecl,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        self.finalize_module_type(class, module_interner, module_id);
    }

    /// Register and finalize a module struct (uses module interner).
    pub(super) fn finalize_module_struct(
        &mut self,
        struct_decl: &StructDecl,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        self.finalize_module_type(struct_decl, module_interner, module_id);
    }

    /// Core implementation for finalizing a module type (class or struct).
    /// - For classes: includes runtime type registration with field_type_tags
    /// - For structs: simpler path without runtime registration
    fn finalize_module_type<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        let type_name_str = module_interner.resolve(type_decl.name());
        let type_kind = type_decl.type_kind();
        let is_class = type_decl.is_class();
        let is_generic_type = type_decl.has_type_params();

        tracing::debug!(type_name = %type_name_str, type_kind, "finalize_module_type called");

        // Look up the TypeDefId via full resolution chain
        let query = self.query();
        let Some(type_def_id) = query.resolve_type_def_by_str(module_id, type_name_str) else {
            tracing::warn!(type_name = %type_name_str, type_kind, "Could not find TypeDefId for module type");
            return;
        };
        tracing::debug!(type_name = %type_name_str, ?type_def_id, "Found TypeDefId for module type");

        // Skip if already registered
        if self.state.type_metadata.contains_key(&type_def_id) {
            tracing::debug!(type_name = %type_name_str, "Skipping - already registered in type_metadata");
            return;
        }

        // Allocate type_id for classes; structs use 0
        let type_id = if is_class { alloc_type_id() } else { 0 };

        // Build field slots and optionally collect field_type_tags (classes only)
        let (field_slots, physical_slot_count, field_type_tags) =
            self.build_field_slots_and_tags(type_def_id, is_class);

        // Register field types in runtime type registry (classes only)
        if is_class {
            register_instance_type(type_id, field_type_tags);
        }

        // Register instance methods using module interner.
        // Generic types are compiled via monomorphized instances, so skip direct
        // method declaration here to avoid declaring functions that never compile.
        let method_infos = if is_generic_type {
            FxHashMap::default()
        } else {
            self.register_module_type_instance_methods(
                type_decl,
                type_def_id,
                module_interner,
                type_name_str,
            )
        };

        // Register type metadata
        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .unwrap_or_else(|| {
                panic!(
                    "INTERNAL: finalize_module_{}: missing base_type_id from sema",
                    type_kind
                )
            });
        let name_id = self.query().get_type(type_def_id).name_id;
        self.state.type_metadata.insert_with_name_id(
            type_def_id,
            name_id,
            TypeMetadata {
                type_id,
                field_slots,
                physical_slot_count,
                vole_type: vole_type_id,
                type_def_id,
                method_infos,
            },
        );

        // Register static methods for non-generic types.
        // Generic type statics are emitted from static-method monomorph instances.
        if !is_generic_type && let Some(statics) = type_decl.statics() {
            self.register_module_type_static_methods(
                statics,
                type_def_id,
                module_interner,
                type_name_str,
                type_kind,
            );
        }
    }

    /// Register instance methods for a module type using the module interner.
    fn register_module_type_instance_methods<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        type_def_id: TypeDefId,
        module_interner: &Interner,
        type_name_str: &str,
    ) -> FxHashMap<NameId, MethodInfo> {
        let type_kind = type_decl.type_kind();
        let mut method_infos = FxHashMap::default();

        tracing::debug!(
            type_name = %type_name_str,
            method_count = type_decl.methods().len(),
            "Registering instance methods"
        );

        for method in type_decl.methods() {
            let method_name_str = module_interner.resolve(method.name);
            tracing::debug!(
                type_name = %type_name_str,
                method_name = %method_name_str,
                "Processing instance method"
            );

            let method_name_id =
                method_name_id_with_interner(self.analyzed, module_interner, method.name)
                    .unwrap_or_else(|| {
                        panic!(
                            "module {} method name not found in name_table: {}::{}",
                            type_kind, type_name_str, method_name_str
                        )
                    });

            let semantic_method_id = self
                .analyzed
                .entity_registry()
                .find_method_on_type(type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    panic!(
                        "module {} method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_kind, type_name_str, method_name_str, type_def_id, method_name_id
                    )
                });

            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
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

        method_infos
    }

    /// Register static methods for a module type using the module interner.
    fn register_module_type_static_methods(
        &mut self,
        statics: &StaticsBlock,
        type_def_id: TypeDefId,
        module_interner: &Interner,
        type_name_str: &str,
        type_kind: &str,
    ) {
        for method in &statics.methods {
            if method.body.is_none() {
                continue;
            }

            let method_name_str = module_interner.resolve(method.name);
            let method_name_id =
                method_name_id_with_interner(self.analyzed, module_interner, method.name)
                    .unwrap_or_else(|| {
                        panic!(
                            "module {} static method name not found in name_table: {}::{}",
                            type_kind, type_name_str, method_name_str
                        )
                    });

            let semantic_method_id = self
                .analyzed
                .entity_registry()
                .find_static_method_on_type(type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    panic!(
                        "module {} static method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_kind, type_name_str, method_name_str, type_def_id, method_name_id
                    )
                });

            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            tracing::debug!(
                type_name = %type_name_str,
                method_name = %method_name_str,
                "Registering static method"
            );

            self.register_method_func_key(type_def_id, method_name_id, func_key);
        }
    }
}
