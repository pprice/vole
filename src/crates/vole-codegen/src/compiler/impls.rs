use std::rc::Rc;

use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use cranelift_module::Module;

use super::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::{Compiler, SelfParam};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{
    CodegenCtx, MethodInfo, TypeMetadata, method_name_id_with_interner, type_id_to_cranelift,
};
use vole_frontend::ast::PrimitiveType as AstPrimitive;
use vole_frontend::{
    ClassDecl, Expr, FuncDecl, ImplementBlock, InterfaceMethod, Interner, StaticsBlock, StructDecl,
    Symbol, TypeExpr,
};
use vole_identity::ModuleId;
use vole_sema::type_arena::TypeId;

/// Get the canonical name for an AST primitive type
fn primitive_type_name(p: AstPrimitive) -> &'static str {
    match p {
        AstPrimitive::I8 => "i8",
        AstPrimitive::I16 => "i16",
        AstPrimitive::I32 => "i32",
        AstPrimitive::I64 => "i64",
        AstPrimitive::I128 => "i128",
        AstPrimitive::U8 => "u8",
        AstPrimitive::U16 => "u16",
        AstPrimitive::U32 => "u32",
        AstPrimitive::U64 => "u64",
        AstPrimitive::F32 => "f32",
        AstPrimitive::F64 => "f64",
        AstPrimitive::Bool => "bool",
        AstPrimitive::String => "string",
    }
}

/// Data needed to compile methods for a type (class or struct)
struct TypeMethodsData<'a> {
    /// Type name symbol
    name: Symbol,
    /// Methods to compile
    methods: &'a [FuncDecl],
    /// Optional static methods block
    statics: Option<&'a StaticsBlock>,
    /// Type kind for error messages ("class" or "struct")
    type_kind: &'static str,
}

impl<'a> TypeMethodsData<'a> {
    /// Create from any type implementing TypeDeclInfo
    fn from_decl<T: TypeDeclInfo>(decl: &'a T) -> Self {
        Self {
            name: decl.name(),
            methods: decl.methods(),
            statics: decl.statics(),
            type_kind: decl.type_kind(),
        }
    }
}

/// Trait to abstract over class and struct declarations for unified method compilation.
/// This allows consolidating the parallel compile_module_class_methods/compile_module_struct_methods.
pub(crate) trait TypeDeclInfo {
    /// Get the type name symbol
    fn name(&self) -> Symbol;
    /// Get the instance methods
    fn methods(&self) -> &[FuncDecl];
    /// Get the statics block (if present)
    fn statics(&self) -> Option<&StaticsBlock>;
    /// Get the type kind string for error messages ("class" or "struct")
    fn type_kind(&self) -> &'static str;
    /// Whether this is a class (vs struct). Classes need runtime type registration.
    fn is_class(&self) -> bool;
    /// Whether this type has generic type parameters (classes can be generic, structs too)
    fn has_type_params(&self) -> bool;
}

impl TypeDeclInfo for ClassDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn type_kind(&self) -> &'static str {
        "class"
    }
    fn is_class(&self) -> bool {
        true
    }
    fn has_type_params(&self) -> bool {
        !self.type_params.is_empty()
    }
}

impl TypeDeclInfo for StructDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn type_kind(&self) -> &'static str {
        "struct"
    }
    fn is_class(&self) -> bool {
        false
    }
    fn has_type_params(&self) -> bool {
        !self.type_params.is_empty()
    }
}

impl Compiler<'_> {
    /// Compile methods for a class
    pub(super) fn compile_class_methods(
        &mut self,
        class: &ClassDecl,
        program: &vole_frontend::Program,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        self.compile_class_methods_in_module(class, program, module_id)
    }

    /// Compile instance methods for a struct type.
    pub(super) fn compile_struct_methods(
        &mut self,
        struct_decl: &StructDecl,
        program: &vole_frontend::Program,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        self.compile_type_methods(TypeMethodsData::from_decl(struct_decl), program, module_id)
    }

    /// Compile methods for a class using a specific module for type lookups.
    pub(super) fn compile_class_methods_in_module(
        &mut self,
        class: &ClassDecl,
        program: &vole_frontend::Program,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Skip generic classes - they're compiled via monomorphized instances
        if class.has_type_params() {
            return Ok(());
        }
        self.compile_type_methods(TypeMethodsData::from_decl(class), program, module_id)
    }

    /// Core implementation for compiling methods of a class or struct
    fn compile_type_methods(
        &mut self,
        data: TypeMethodsData<'_>,
        program: &vole_frontend::Program,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Look up TypeDefId from name (needed as key for type_metadata)
        let query = self.query();
        let type_def_id = query
            .try_name_id(module_id, &[data.name])
            .and_then(|name_id| query.try_type_def_id(name_id))
            .ok_or_else(|| {
                format!(
                    "Internal error: {} {} not found in entity registry",
                    data.type_kind,
                    self.query().resolve_symbol(data.name)
                )
            })?;

        let metadata = self
            .state
            .type_metadata
            .get(&type_def_id)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Internal error: {} {} not registered in type_metadata",
                    data.type_kind,
                    self.query().resolve_symbol(data.name)
                )
            })?;

        for method in data.methods {
            self.compile_method(method, data.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces
        let direct_methods: std::collections::HashSet<_> =
            data.methods.iter().map(|m| m.name).collect();

        // Collect interface names using query (avoids borrow conflicts with compile_default_method)
        let interface_names: Vec<Symbol> = {
            let query = self.query();
            query
                .try_name_id(module_id, &[data.name])
                .and_then(|type_name_id| query.try_type_def_id(type_name_id))
                .map(|type_def_id| {
                    query
                        .implemented_interfaces(type_def_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            let interface_def = query.get_type(interface_id);
                            query
                                .last_segment(interface_def.name_id)
                                .and_then(|name_str| query.try_symbol(&name_str))
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        // Compile default methods for each interface
        for interface_name in interface_names {
            if let Some(interface_decl) = self.find_interface_decl(program, interface_name) {
                for method in &interface_decl.methods {
                    if method.body.is_some() && !direct_methods.contains(&method.name) {
                        self.compile_default_method(method, data.name, &metadata)?;
                    }
                }
            }
        }

        // Compile static methods
        if let Some(statics) = data.statics {
            self.compile_static_methods(statics, data.name, module_id)?;
        }

        Ok(())
    }

    /// Get the type name string from a TypeExpr (works for primitives, named types,
    /// and generic specializations like `Tagged<i64>`)
    fn get_type_name_from_expr(&self, ty: &TypeExpr) -> Option<String> {
        match ty {
            TypeExpr::Primitive(p) => Some(primitive_type_name(*p).to_string()),
            TypeExpr::Handle => Some("handle".to_string()),
            TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                Some(self.query().resolve_symbol(*sym).to_string())
            }
            _ => None,
        }
    }

    /// Register implement block methods (first pass)
    pub(super) fn register_implement_block(&mut self, impl_block: &ImplementBlock) {
        let module_id = self.program_module();
        self.register_implement_block_in_module(impl_block, module_id)
    }

    /// Register implement block methods using a specific module for type lookups.
    pub(super) fn register_implement_block_in_module(
        &mut self,
        impl_block: &ImplementBlock,
        module_id: ModuleId,
    ) {
        let interner = self.analyzed.interner.clone();
        self.register_implement_block_with_interner(impl_block, &interner, module_id)
    }

    /// Import all methods (instance + static) from a module implement block.
    /// Uses Linkage::Import for pre-compiled modules in shared cache.
    pub(super) fn import_module_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
        module_id: ModuleId,
    ) {
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return;
        };

        // Get TypeId for self binding (same as register_implement_block_with_interner)
        let (self_type_id, impl_type_id) =
            match &impl_block.target_type {
                TypeExpr::Primitive(p) => {
                    let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                    let type_id = self.analyzed.type_arena().primitive(prim_type);
                    let impl_id = self.impl_type_id_from_type_id(type_id);
                    (type_id, impl_id)
                }
                TypeExpr::Handle => {
                    let type_id = TypeId::HANDLE;
                    let impl_id = self.impl_type_id_from_type_id(type_id);
                    (type_id, impl_id)
                }
                TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                    let type_def_id = self
                        .query()
                        .try_name_id(module_id, &[*sym])
                        .and_then(|name_id| self.query().try_type_def_id(name_id))
                        .unwrap_or_else(|| {
                            panic!(
                                "import_module_implement_block: type not found: {}",
                                type_name
                            )
                        });
                    let metadata = self.state.type_metadata.get(&type_def_id).unwrap_or_else(
                        || {
                            panic!(
                                "import_module_implement_block: type not in type_metadata: {:?}",
                                type_def_id
                            )
                        },
                    );
                    let impl_id = self.impl_type_id_from_type_id(metadata.vole_type);
                    (metadata.vole_type, impl_id)
                }
                _ => unreachable!(),
            };

        // Import instance methods
        for method in &impl_block.methods {
            let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name);
            let type_def_id =
                impl_type_id.and_then(|impl_id| self.query().try_type_def_id(impl_id.name_id()));

            let (sig, semantic_method_id) = {
                let tdef_id = type_def_id.unwrap_or_else(|| {
                    panic!(
                        "import: type_def_id missing for {}.{}",
                        type_name,
                        interner.resolve(method.name)
                    )
                });
                let name_id = method_name_id.unwrap_or_else(|| {
                    panic!(
                        "import: method_name_id missing for {}.{}",
                        type_name,
                        interner.resolve(method.name)
                    )
                });
                let method_id = self
                    .analyzed
                    .entity_registry()
                    .find_method_on_type(tdef_id, name_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "import: method {}.{} not in entity_registry",
                            type_name,
                            interner.resolve(method.name)
                        )
                    });
                let sig =
                    self.build_signature_for_method(method_id, SelfParam::TypedId(self_type_id));
                (sig, method_id)
            };
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.import_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            if let Some(tdef_id) = type_def_id
                && let Some(name_id) = method_name_id
            {
                let type_name_id = self.query().get_type(tdef_id).name_id;
                self.state
                    .method_func_keys
                    .insert((type_name_id, name_id), func_key);
            }
        }

        // Import static methods
        if let Some(ref statics) = impl_block.statics {
            self.import_implement_statics_block(statics, &type_name, interner, module_id);
        }
    }

    /// Import static methods from a statics block.
    fn import_implement_statics_block(
        &mut self,
        statics: &StaticsBlock,
        type_name: &str,
        interner: &Interner,
        module_id: ModuleId,
    ) {
        let type_def_id = self.query().resolve_type_def_by_str(module_id, type_name);

        for method in &statics.methods {
            if method.body.is_none() {
                continue;
            }
            let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name);
            let (sig, semantic_method_id) = {
                let tdef_id = type_def_id.unwrap_or_else(|| {
                    panic!(
                        "import: type_def_id missing for static {}.{}",
                        type_name,
                        interner.resolve(method.name)
                    )
                });
                let name_id = method_name_id.unwrap_or_else(|| {
                    panic!(
                        "import: method_name_id missing for static {}.{}",
                        type_name,
                        interner.resolve(method.name)
                    )
                });
                let method_id = self
                    .query()
                    .registry()
                    .find_static_method_on_type(tdef_id, name_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "import: static method {}.{} not in entity_registry",
                            type_name,
                            interner.resolve(method.name)
                        )
                    });
                let sig = self.build_signature_for_method(method_id, SelfParam::None);
                (sig, method_id)
            };
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.import_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            let type_name_id =
                self.query()
                    .get_type(type_def_id.expect(
                        "INTERNAL: register_interface_default_methods: missing type_def_id",
                    ))
                    .name_id;
            self.state.method_func_keys.insert(
                (
                    type_name_id,
                    method_name_id.expect(
                        "INTERNAL: register_interface_default_methods: missing method_name_id",
                    ),
                ),
                func_key,
            );
        }
    }

    /// Register implement block methods with a specific interner and module (for module programs)
    pub(super) fn register_implement_block_with_interner(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
        module_id: ModuleId,
    ) {
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return; // Unsupported type for implement block
        };

        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        // Get type_id directly from metadata to avoid to_type() conversion
        let (self_type_id, impl_type_id) =
            match &impl_block.target_type {
                TypeExpr::Primitive(p) => {
                    let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                    let type_id = self.analyzed.type_arena().primitive(prim_type);
                    let impl_id = self.impl_type_id_from_type_id(type_id);
                    (type_id, impl_id)
                }
                TypeExpr::Handle => {
                    let type_id = TypeId::HANDLE;
                    let impl_id = self.impl_type_id_from_type_id(type_id);
                    (type_id, impl_id)
                }
                TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                    // Look up TypeDefId from Symbol (for Generic, uses the base class name)
                    // Try given module first, then fall back to program module
                    // (implement blocks in tests blocks may target parent-scope types)
                    let type_def_id = self
                    .query()
                    .try_name_id(module_id, &[*sym])
                    .and_then(|name_id| self.query().try_type_def_id(name_id))
                    .or_else(|| {
                        let prog_mod = self.program_module();
                        if prog_mod != module_id {
                            self.query()
                                .try_name_id(prog_mod, &[*sym])
                                .and_then(|name_id| self.query().try_type_def_id(name_id))
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| {
                        panic!(
                            "INTERNAL ERROR: implement block target type not in entity registry\n\
                             sym: {:?}",
                            sym
                        )
                    });
                    let metadata = self.state.type_metadata.get(&type_def_id).unwrap_or_else(
                        || {
                            panic!(
                                "INTERNAL ERROR: implement block target type not in type_metadata\n\
                         type_def_id: {:?}",
                                type_def_id
                            )
                        },
                    );
                    // Use TypeId directly
                    let impl_id = self.impl_type_id_from_type_id(metadata.vole_type);
                    (metadata.vole_type, impl_id)
                }
                _ => {
                    unreachable!(
                        "target_type was neither Primitive, Handle, Named, nor Generic, \
                         but passed get_type_name_from_expr check"
                    )
                }
            };

        // Declare methods as functions: TypeName::methodName (implement block convention)
        for method in &impl_block.methods {
            let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name);
            // Get TypeDefId if available
            let type_def_id =
                impl_type_id.and_then(|impl_id| self.query().try_type_def_id(impl_id.name_id()));

            // Build signature from pre-resolved types via sema
            let (sig, semantic_method_id) = {
                let tdef_id = type_def_id.unwrap_or_else(|| {
                    panic!(
                        "implement block instance method without TypeDefId: {}.{}",
                        type_name,
                        interner.resolve(method.name)
                    )
                });
                let name_id = method_name_id.unwrap_or_else(|| {
                    panic!(
                        "implement block instance method without NameId: {}.{}",
                        type_name,
                        interner.resolve(method.name)
                    )
                });
                let semantic_method_id = self
                    .analyzed
                    .entity_registry()
                    .find_method_on_type(tdef_id, name_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "implement block instance method not in entity_registry: {}.{} (type_def_id={:?}, method_name_id={:?})",
                            type_name,
                            interner.resolve(method.name),
                            tdef_id,
                            name_id
                        )
                    });
                let sig = self.build_signature_for_method(
                    semantic_method_id,
                    SelfParam::TypedId(self_type_id),
                );
                (sig, semantic_method_id)
            };
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);
            // Populate method_func_keys for method lookup using type's NameId for stable lookup
            if let Some(tdef_id) = type_def_id
                && let Some(name_id) = method_name_id
            {
                let type_name_id = self.query().get_type(tdef_id).name_id;
                self.state
                    .method_func_keys
                    .insert((type_name_id, name_id), func_key);
            }
        }

        // Register static methods from statics block (if present)
        if let Some(ref statics) = impl_block.statics {
            // Get TypeDefId for this type
            let type_def_id = {
                let name_table = self.analyzed.name_table();
                match &impl_block.target_type {
                    TypeExpr::Primitive(p) => {
                        let name_id = name_table.primitives.from_ast(*p);
                        self.query().try_type_def_id(name_id)
                    }
                    TypeExpr::Handle => {
                        let name_id = name_table.primitives.handle;
                        self.query().try_type_def_id(name_id)
                    }
                    TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                        let name_id = name_table.name_id(self.program_module(), &[*sym], interner);
                        name_id.and_then(|id| self.query().try_type_def_id(id))
                    }
                    _ => None,
                }
            };

            for method in &statics.methods {
                // Only register methods with bodies
                if method.body.is_none() {
                    continue;
                }

                // Get method name id for lookup
                let method_name_id =
                    method_name_id_with_interner(self.analyzed, interner, method.name);

                // Build signature from pre-resolved types via sema
                let (sig, semantic_method_id) = {
                    let tdef_id = type_def_id.unwrap_or_else(|| {
                        panic!(
                            "implement statics method without TypeDefId: {}.{}",
                            type_name,
                            interner.resolve(method.name)
                        )
                    });
                    let name_id = method_name_id.unwrap_or_else(|| {
                        panic!(
                            "implement statics method without NameId: {}.{}",
                            type_name,
                            interner.resolve(method.name)
                        )
                    });
                    let method_id = self
                        .query()
                        .registry()
                        .find_static_method_on_type(tdef_id, name_id)
                        .unwrap_or_else(|| {
                            panic!(
                                "implement statics method not in entity_registry: {}.{} (type_def_id={:?}, method_name_id={:?})",
                                type_name,
                                interner.resolve(method.name),
                                tdef_id,
                                name_id
                            )
                        });
                    let sig = self.build_signature_for_method(method_id, SelfParam::None);
                    (sig, method_id)
                };

                // Function key via entity registry full_name_id
                let method_def = self
                    .analyzed
                    .entity_registry()
                    .get_method(semantic_method_id);
                let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
                let display_name = self.func_registry.display(func_key);
                let func_id = self.jit.declare_function(&display_name, &sig);
                self.func_registry.set_func_id(func_key, func_id);

                // Register in method_func_keys for codegen lookup using type's NameId for stable lookup
                let type_name_id = self
                    .query()
                    .get_type(
                        type_def_id
                            .expect("INTERNAL: register_implement_block: missing type_def_id"),
                    )
                    .name_id;
                self.state.method_func_keys.insert(
                    (
                        type_name_id,
                        method_name_id
                            .expect("INTERNAL: register_implement_block: missing method_name_id"),
                    ),
                    func_key,
                );
            }
        }
    }

    /// Compile implement block methods (second pass)
    pub(super) fn compile_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        self.compile_implement_block_in_module(impl_block, module_id)
    }

    /// Compile implement block methods using a specific module for type lookups.
    pub(super) fn compile_implement_block_in_module(
        &mut self,
        impl_block: &ImplementBlock,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Get type name string (works for primitives and named types)
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return Ok(()); // Unsupported type for implement block
        };

        // Get the TypeId for `self` binding
        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        let self_type_id = match &impl_block.target_type {
            TypeExpr::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                self.analyzed.type_arena().primitive(prim_type)
            }
            TypeExpr::Handle => TypeId::HANDLE,
            TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                // Try given module first, then fall back to program module
                let type_def_id = self
                    .query()
                    .try_name_id(module_id, &[*sym])
                    .and_then(|name_id| self.query().try_type_def_id(name_id))
                    .or_else(|| {
                        let prog_mod = self.program_module();
                        if prog_mod != module_id {
                            self.query()
                                .try_name_id(prog_mod, &[*sym])
                                .and_then(|name_id| self.query().try_type_def_id(name_id))
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| {
                        panic!(
                            "INTERNAL ERROR: implement block self type not in entity registry\n\
                             sym: {:?}",
                            sym
                        )
                    });
                self.state
                    .type_metadata
                    .get(&type_def_id)
                    .map(|m| m.vole_type)
                    .unwrap_or_else(|| {
                        panic!(
                            "INTERNAL ERROR: implement block self type not in type_metadata\n\
                             type_def_id: {:?}",
                            type_def_id
                        )
                    })
            }
            _ => {
                unreachable!(
                    "target_type was neither Primitive, Handle, Named, nor Generic, \
                     but passed get_type_name_from_expr check"
                )
            }
        };
        // Get TypeDefId for method lookup via method_func_keys
        let impl_type_id = self.impl_type_id_from_type_id(self_type_id);
        let type_def_id = impl_type_id.and_then(|id| self.query().try_type_def_id(id.name_id()));

        for method in &impl_block.methods {
            let method_key = type_def_id.and_then(|type_def_id| {
                // Use type's NameId for stable lookup across analyzer instances
                let type_name_id = self.query().get_type(type_def_id).name_id;
                let method_id = self.method_name_id(method.name);
                self.state
                    .method_func_keys
                    .get(&(type_name_id, method_id))
                    .map(|&func_key| MethodInfo { func_key })
            });
            self.compile_implement_method(method, self_type_id, method_key)?;
        }

        // Compile static methods from statics block (if present)
        if let Some(ref statics) = impl_block.statics {
            let interner = self.analyzed.interner.clone();
            self.compile_implement_statics(statics, &type_name, None, &interner)?;
        }

        Ok(())
    }

    /// Compile implement block methods from a module, using the module interner.
    /// Handles both instance methods and statics.
    pub(super) fn compile_module_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
        module_id: ModuleId,
        module_path: Option<&str>,
    ) -> CodegenResult<()> {
        let Some(type_name) = self.get_type_name_from_expr(&impl_block.target_type) else {
            return Ok(());
        };

        // Get the TypeId for `self` binding
        let self_type_id = match &impl_block.target_type {
            TypeExpr::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                self.analyzed.type_arena().primitive(prim_type)
            }
            TypeExpr::Handle => TypeId::HANDLE,
            TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                let type_def_id = self
                    .query()
                    .try_name_id(module_id, &[*sym])
                    .and_then(|name_id| self.query().try_type_def_id(name_id))
                    .unwrap_or_else(|| {
                        panic!(
                            "INTERNAL ERROR: implement block self type not in entity registry: {:?}",
                            sym
                        )
                    });
                self.state
                    .type_metadata
                    .get(&type_def_id)
                    .map(|m| m.vole_type)
                    .unwrap_or_else(|| {
                        panic!(
                            "INTERNAL ERROR: implement block self type not in type_metadata: {:?}",
                            type_def_id
                        )
                    })
            }
            _ => unreachable!("target_type was neither Primitive, Handle, Named, nor Generic"),
        };

        let impl_type_id = self.impl_type_id_from_type_id(self_type_id);
        let type_def_id = impl_type_id.and_then(|id| self.query().try_type_def_id(id.name_id()));

        // Compile instance methods using module interner for name resolution
        for method in &impl_block.methods {
            let method_key = type_def_id.and_then(|type_def_id| {
                let type_name_id = self.query().get_type(type_def_id).name_id;
                // Use module interner for method name lookup (cross-interner safe)
                let method_name_id =
                    method_name_id_with_interner(self.analyzed, interner, method.name);
                method_name_id.and_then(|mid| {
                    self.state
                        .method_func_keys
                        .get(&(type_name_id, mid))
                        .map(|&func_key| MethodInfo { func_key })
                })
            });
            self.compile_module_implement_method(
                method,
                self_type_id,
                method_key,
                interner,
                module_id,
            )?;
        }

        // Compile static methods
        if let Some(ref statics) = impl_block.statics {
            self.compile_implement_statics(statics, &type_name, module_path, interner)?;
        }

        Ok(())
    }

    /// Compile a single method from a module implement block, using a module interner.
    fn compile_module_implement_method(
        &mut self,
        method: &FuncDecl,
        self_type_id: TypeId,
        method_info: Option<MethodInfo>,
        interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let impl_type_id = self.impl_type_id_from_type_id(self_type_id);
        let type_def_id =
            impl_type_id.and_then(|impl_id| self.query().try_type_def_id(impl_id.name_id()));
        let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name)
            .unwrap_or_else(|| {
                panic!(
                    "method name_id not found for '{}'",
                    interner.resolve(method.name)
                )
            });

        let semantic_method_id = type_def_id
            .and_then(|tdef_id| {
                self.analyzed
                    .entity_registry()
                    .find_method_on_type(tdef_id, method_name_id)
            })
            .unwrap_or_else(|| {
                panic!(
                    "implement block method not registered: {} (type_def_id={:?})",
                    interner.resolve(method.name),
                    type_def_id
                )
            });

        let func_key = if let Some(info) = method_info {
            info.func_key
        } else {
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            self.func_registry.intern_name_id(method_def.full_name_id)
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: implement method {} not declared", display)
        })?;

        let sig =
            self.build_signature_for_method(semantic_method_id, SelfParam::TypedId(self_type_id));
        self.jit.ctx.func.signature = sig;

        let self_cranelift_type =
            type_id_to_cranelift(self_type_id, self.analyzed.type_arena(), self.pointer_type);

        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.analyzed.type_arena();
            let (param_type_ids, _, _) = arena
                .unwrap_function(method_def.signature_id)
                .expect("INTERNAL: method compilation: missing function signature");
            method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .map(|(param, &type_id)| {
                    let cranelift_type = type_id_to_cranelift(type_id, arena, self.pointer_type);
                    (param.name, type_id, cranelift_type)
                })
                .collect()
        };

        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        let method_return_type_id = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.analyzed.type_arena();
            arena
                .unwrap_function(method_def.signature_id)
                .map(|(_, ret, _)| ret)
        };

        let no_global_inits = FxHashMap::default();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            // Use module interner for compilation
            let env = compile_env!(self, interner, &no_global_inits, source_file_ptr, module_id);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let self_binding = (self_sym, self_type_id, self_cranelift_type);
            let config = FunctionCompileConfig::method(
                &method.body,
                params,
                self_binding,
                method_return_type_id,
            );
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                Some(module_id),
                None,
            )?;
        }

        self.finalize_function(func_id)?;
        Ok(())
    }

    /// Compile static methods from an implement block's statics section (TypeId-native)
    fn compile_implement_statics(
        &mut self,
        statics: &StaticsBlock,
        type_name: &str,
        module_path: Option<&str>,
        interner: &Interner,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        // Try to get TypeDefId for looking up pre-resolved method signatures
        let type_def_id = self.query().resolve_type_def_by_str(module_id, type_name);

        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Resolve MethodId for this static method
            let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name);
            let semantic_method_id =
                type_def_id
                    .zip(method_name_id)
                    .and_then(|(tdef_id, name_id)| {
                        self.analyzed
                            .entity_registry()
                            .find_static_method_on_type(tdef_id, name_id)
                    });

            let method_id = semantic_method_id.unwrap_or_else(|| {
                let method_name_str = interner.resolve(method.name);
                panic!(
                    "INTERNAL ERROR: static method {}::{} not found in entity registry",
                    type_name, method_name_str
                )
            });

            // Look up the registered function via EntityRegistry full_name_id
            let method_def = self.analyzed.entity_registry().get_method(method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let jit_func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                let method_name_str = interner.resolve(method.name);
                format!(
                    "Internal error: static method {}::{} not declared",
                    type_name, method_name_str
                )
            })?;

            // Use pre-resolved signature from MethodDef
            let method_def = self.query().get_method(method_id);
            let arena = self.analyzed.type_arena();
            let (params, ret, _) = arena
                .unwrap_function(method_def.signature_id)
                .expect("INTERNAL: method compilation: missing function signature");
            let sig = self.build_signature_for_method(method_id, SelfParam::None);
            let (param_type_ids, return_type_id) =
                (params.to_vec(), Some(ret).filter(|r| !r.is_void()));
            self.jit.ctx.func.signature = sig;

            // Build param info for compilation
            let param_cranelift_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_cranelift_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();

            // Get source file pointer and module_id
            let source_file_ptr = self.source_file_ptr();
            let resolved_module_id = module_path.and_then(|path| {
                let name_table = self.analyzed.name_table();
                name_table.module_id_if_known(path)
            });

            // Create function builder and compile
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(self, source_file_ptr);
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let config = FunctionCompileConfig::top_level(body, params, return_type_id);
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    resolved_module_id,
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(jit_func_id)?;
        }

        Ok(())
    }

    /// Compile a method from an implement block (TypeId-native version)
    fn compile_implement_method(
        &mut self,
        method: &FuncDecl,
        self_type_id: TypeId,
        method_info: Option<MethodInfo>,
    ) -> CodegenResult<()> {
        // Look up MethodId from entity_registry first (needed for func_key and signature)
        let type_def_id = self
            .impl_type_id_from_type_id(self_type_id)
            .and_then(|impl_id| self.query().try_type_def_id(impl_id.name_id()));
        let method_name_id = self.method_name_id(method.name);

        let semantic_method_id = type_def_id
            .and_then(|tdef_id| {
                self.analyzed
                    .entity_registry()
                    .find_method_on_type(tdef_id, method_name_id)
            })
            .unwrap_or_else(|| {
                let method_name_str = self.resolve_symbol(method.name);
                panic!(
                    "implement block method not registered in entity_registry: {} (type_def_id={:?}, method_name_id={:?})",
                    method_name_str, type_def_id, method_name_id
                )
            });

        let func_key = if let Some(info) = method_info {
            info.func_key
        } else {
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            self.func_registry.intern_name_id(method_def.full_name_id)
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: implement method {} not declared", display)
        })?;

        let sig =
            self.build_signature_for_method(semantic_method_id, SelfParam::TypedId(self_type_id));
        self.jit.ctx.func.signature = sig;

        // Get the Cranelift type for self (using TypeId)
        let self_cranelift_type =
            type_id_to_cranelift(self_type_id, self.analyzed.type_arena(), self.pointer_type);

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Get param TypeIds from the method signature and pair with AST param names
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.analyzed.type_arena();
            let (param_type_ids, _, _) = arena
                .unwrap_function(method_def.signature_id)
                .expect("INTERNAL: method compilation: missing function signature");
            method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .map(|(param, &type_id)| {
                    let cranelift_type = type_id_to_cranelift(type_id, arena, self.pointer_type);
                    (param.name, type_id, cranelift_type)
                })
                .collect()
        };

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Get the method's return type from the pre-resolved signature
        let method_return_type_id = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.analyzed.type_arena();
            arena
                .unwrap_function(method_def.signature_id)
                .map(|(_, ret, _)| ret)
        };

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let self_binding = (self_sym, self_type_id, self_cranelift_type);
            let config = FunctionCompileConfig::method(
                &method.body,
                params,
                self_binding,
                method_return_type_id,
            );
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                None,
            )?;
        }

        // Define the function
        self.jit
            .module
            .define_function(func_id, &mut self.jit.ctx)
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;
        self.jit.module.clear_context(&mut self.jit.ctx);

        Ok(())
    }

    /// Compile a single method
    fn compile_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> CodegenResult<()> {
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = self.query().resolve_symbol(method.name).to_string();

        let method_name_id = self.method_name_id(method.name);
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            format!(
                "Internal error: method {} not registered on {}",
                method_name_str, type_name_str
            )
        })?;
        let func_key = method_info.func_key;

        // Look up MethodId from entity_registry for pre-computed signature
        let semantic_method_id = self
            .analyzed
            .entity_registry()
            .find_method_on_type(metadata.type_def_id, method_name_id)
            .unwrap_or_else(|| {
                panic!(
                    "class instance method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                    type_name_str, method_name_str, metadata.type_def_id, method_name_id
                )
            });

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: method {} not declared", display)
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Use TypeId directly for self binding
        let self_type_id = metadata.vole_type;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, method_return_type_id) = {
            let arena = self.analyzed.type_arena();
            let (params, ret, _) = arena
                .unwrap_function(method_def.signature_id)
                .expect("INTERNAL: method signature: expected function type");
            (params.to_vec(), Some(ret))
        };

        // Build params: Vec<(Symbol, TypeId, Type)>
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.analyzed.type_arena();
            method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .map(|(param, &type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, arena_ref, self.pointer_type);
                    (param.name, type_id, cranelift_type)
                })
                .collect()
        };

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);
            let self_binding = (self_sym, self_type_id, self.pointer_type);
            let config = FunctionCompileConfig::method(
                &method.body,
                params,
                self_binding,
                method_return_type_id,
            );
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                None,
            )?;
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Compile a default method from an interface, monomorphized for a concrete type
    fn compile_default_method(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        metadata: &TypeMetadata,
    ) -> CodegenResult<()> {
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = self.query().resolve_symbol(method.name).to_string();

        let method_name_id = self.method_name_id(method.name);
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            format!(
                "Internal error: default method {} not registered on {}",
                method_name_str, type_name_str
            )
        })?;
        let func_key = method_info.func_key;

        // Look up MethodId - interface default methods are now registered on implementing types
        let semantic_method_id = self
            .analyzed
            .entity_registry()
            .find_method_on_type(metadata.type_def_id, method_name_id)
            .unwrap_or_else(|| {
                panic!(
                    "interface default method not registered on implementing type: {}::{} (type_def_id={:?}, method_name_id={:?})",
                    type_name_str, method_name_str, metadata.type_def_id, method_name_id
                )
            });

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            let display = self.func_registry.display(func_key);
            format!("Internal error: default method {} not declared", display)
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, return_type_id) = {
            let arena = self.analyzed.type_arena();
            let (params, ret, _) = arena
                .unwrap_function(method_def.signature_id)
                .expect("INTERNAL: method signature: expected function type");
            (params.to_vec(), ret)
        };

        let param_types = self.type_ids_to_cranelift(&param_type_ids);
        let params: Vec<_> = method
            .params
            .iter()
            .zip(param_type_ids.iter())
            .zip(param_types.iter())
            .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
            .collect();

        // Compile method body (must exist for default methods)
        let body = method.body.as_ref().ok_or_else(|| {
            format!(
                "Internal error: default method {} has no body",
                method_name_str
            )
        })?;

        // Get source file pointer and self binding (use metadata.vole_type for self type)
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();
        let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

            let config =
                FunctionCompileConfig::method(body, params, self_binding, Some(return_type_id));
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                None,
                None,
            )?;
        }

        // Define the function
        self.jit.define_function(func_id)?;
        self.jit.clear();

        Ok(())
    }

    /// Compile static methods from a statics block
    fn compile_static_methods(
        &mut self,
        statics: &StaticsBlock,
        type_name: Symbol,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Get the TypeDefId for looking up method info
        let type_name_id = self.query().name_id(module_id, &[type_name]);
        let type_def_id = self
            .query()
            .try_type_def_id(type_name_id)
            .unwrap_or_else(|| {
                let type_name_str = self.resolve_symbol(type_name);
                panic!(
                    "static method type not registered in entity_registry: {} (type_name_id={:?})",
                    type_name_str, type_name_id
                )
            });

        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Look up MethodId from entity_registry for pre-computed signature
            let method_name_id = self.method_name_id(method.name);
            let semantic_method_id = self
                .analyzed
                .entity_registry()
                .find_static_method_on_type(type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    let type_name_str = self.resolve_symbol(type_name);
                    let method_name_str = self.resolve_symbol(method.name);
                    panic!(
                        "static method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, type_def_id, method_name_id
                    )
                });

            // Function key from EntityRegistry full_name_id
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                let type_name_str = self.query().resolve_symbol(type_name);
                let method_name_str = self.query().resolve_symbol(method.name);
                format!(
                    "Internal error: static method {}::{} not declared",
                    type_name_str, method_name_str
                )
            })?;

            // Create signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema (pre-resolved signature)
            let (param_type_ids, return_type_id) = {
                let arena = self.analyzed.type_arena();
                let (params, ret, _) = arena
                    .unwrap_function(method_def.signature_id)
                    .expect("INTERNAL: static method signature: expected function type");
                (params.to_vec(), ret)
            };

            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(self, source_file_ptr);
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let config = FunctionCompileConfig::top_level(body, params, Some(return_type_id));
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    None,
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile methods for a module type (class or struct) using module interner.
    /// This is the unified implementation for compile_module_class_methods and
    /// compile_module_struct_methods.
    fn compile_module_type_methods<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        module_interner: &Interner,
        module_path: &str,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
    ) -> CodegenResult<()> {
        let type_name_str = module_interner.resolve(type_decl.name());
        let type_kind = type_decl.type_kind();
        let is_class = type_decl.is_class();

        // Look up the actual module_id from the module_path (not main_module!)
        let module_id = self
            .analyzed
            .name_table()
            .module_id_if_known(module_path)
            .unwrap_or_else(|| self.program_module());

        // Find the type metadata by looking for the type name string
        let metadata = self
            .state
            .type_metadata
            .values()
            .find(|meta| {
                let arena = self.analyzed.type_arena();
                // Use unwrap_class for classes, unwrap_struct for structs
                let type_def_id = if is_class {
                    arena.unwrap_class(meta.vole_type).map(|(id, _)| id)
                } else {
                    arena.unwrap_struct(meta.vole_type).map(|(id, _)| id)
                };
                type_def_id.is_some_and(|id| {
                    let name_id = self.query().get_type(id).name_id;
                    self.analyzed
                        .name_table()
                        .last_segment_str(name_id)
                        .is_some_and(|name| name == type_name_str)
                })
            })
            .cloned();

        let Some(metadata) = metadata else {
            tracing::warn!(type_name = %type_name_str, type_kind, "Could not find metadata for module type");
            return Ok(());
        };

        // Compile instance methods
        self.compile_module_type_instance_methods(
            type_decl,
            &metadata,
            module_interner,
            module_id,
            module_global_inits,
            type_name_str,
        )?;

        // Compile static methods
        if let Some(statics) = type_decl.statics() {
            self.compile_module_type_static_methods(
                statics,
                &metadata,
                module_interner,
                module_id,
                module_global_inits,
                type_name_str,
                type_kind,
            )?;
        }

        Ok(())
    }

    /// Compile instance methods for a module type.
    /// Helper for compile_module_type_methods to keep functions under ~80 lines.
    fn compile_module_type_instance_methods<T: TypeDeclInfo>(
        &mut self,
        type_decl: &T,
        metadata: &TypeMetadata,
        module_interner: &Interner,
        module_id: ModuleId,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
        type_name_str: &str,
    ) -> CodegenResult<()> {
        let type_kind = type_decl.type_kind();

        for method in type_decl.methods() {
            let method_name_str = module_interner.resolve(method.name);

            // Look up MethodId from sema to get pre-computed signature
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
                .find_method_on_type(metadata.type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    panic!(
                        "module {} method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_kind, type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    )
                });

            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                format!(
                    "Internal error: method {}::{} not declared",
                    type_name_str, method_name_str
                )
            })?;

            // Create method signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.query().get_method(semantic_method_id);
            let (param_type_ids, return_type_id) = {
                let arena = self.analyzed.type_arena();
                let (params, ret, _) = arena
                    .unwrap_function(method_def.signature_id)
                    .expect("INTERNAL: method signature: expected function type");
                (params.to_vec(), Some(ret))
            };

            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();
            let self_sym = module_interner
                .lookup("self")
                .expect("INTERNAL: method compilation: 'self' not interned");
            let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(
                    self,
                    module_interner,
                    module_global_inits,
                    source_file_ptr,
                    module_id
                );
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let config = FunctionCompileConfig::method(
                    &method.body,
                    params,
                    self_binding,
                    return_type_id,
                );
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    Some(module_id),
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
        }

        Ok(())
    }

    /// Compile static methods for a module type.
    /// Helper for compile_module_type_methods to keep functions under ~80 lines.
    #[allow(clippy::too_many_arguments)]
    fn compile_module_type_static_methods(
        &mut self,
        statics: &StaticsBlock,
        metadata: &TypeMetadata,
        module_interner: &Interner,
        module_id: ModuleId,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
        type_name_str: &str,
        type_kind: &str,
    ) -> CodegenResult<()> {
        for method in &statics.methods {
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            let method_name_str = module_interner.resolve(method.name);

            // Look up MethodId from sema to get pre-computed signature
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
                .find_static_method_on_type(metadata.type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    panic!(
                        "module {} static method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_kind, type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    )
                });

            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                format!(
                    "Internal error: static method {}::{} not declared",
                    type_name_str, method_name_str
                )
            })?;

            // Create signature using pre-resolved MethodId (no self parameter for static)
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.query().get_method(semantic_method_id);
            let (param_type_ids, return_type_id) = {
                let arena = self.analyzed.type_arena();
                let (params, ret, _) = arena
                    .unwrap_function(method_def.signature_id)
                    .expect("INTERNAL: static method signature: expected function type");
                (params.to_vec(), Some(ret))
            };

            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(
                    self,
                    module_interner,
                    module_global_inits,
                    source_file_ptr,
                    module_id
                );
                let mut codegen_ctx =
                    CodegenCtx::new(&mut self.jit.module, &mut self.func_registry);

                let config = FunctionCompileConfig::top_level(body, params, return_type_id);
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    Some(module_id),
                    None,
                )?;
            }

            // Define the function
            self.jit.define_function(func_id)?;
            self.jit.clear();
        }

        Ok(())
    }

    /// Compile methods for a module class (uses module interner)
    pub(super) fn compile_module_class_methods(
        &mut self,
        class: &ClassDecl,
        module_interner: &Interner,
        module_path: &str,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
    ) -> CodegenResult<()> {
        self.compile_module_type_methods(class, module_interner, module_path, module_global_inits)
    }

    /// Compile methods for a module struct (uses module interner)
    pub(super) fn compile_module_struct_methods(
        &mut self,
        struct_decl: &StructDecl,
        module_interner: &Interner,
        module_path: &str,
        module_global_inits: &FxHashMap<Symbol, Rc<Expr>>,
    ) -> CodegenResult<()> {
        self.compile_module_type_methods(
            struct_decl,
            module_interner,
            module_path,
            module_global_inits,
        )
    }
}
