use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::{Compiler, DeclareMode, SelfParam};
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{
    CodegenCtx, MethodInfo, TypeMetadata, method_name_id_with_interner, type_id_to_cranelift,
};
use cranelift::prelude::{FunctionBuilder, FunctionBuilderContext, types};
use vole_frontend::ast::PrimitiveType as AstPrimitive;
use vole_frontend::ast::{ClassDecl, ImplementBlock, InterfaceMethod, StaticsBlock, StructDecl};
use vole_frontend::{Expr, FuncDecl, Interner, Symbol, TypeExpr, TypeExprKind};
use vole_identity::{MethodId, ModuleId, NameId, TypeDefId};
use vole_sema::implement_registry::ImplTypeId;
use vole_sema::type_arena::TypeId;

/// Map a primitive type name string to its TypeId constant.
/// Used for `extend range with Iterable<i64>` and similar Named-primitive target blocks.
fn primitive_type_id_by_name(name: &str) -> TypeId {
    match name {
        "i8" => TypeId::I8,
        "i16" => TypeId::I16,
        "i32" => TypeId::I32,
        "i64" => TypeId::I64,
        "i128" => TypeId::I128,
        "u8" => TypeId::U8,
        "u16" => TypeId::U16,
        "u32" => TypeId::U32,
        "u64" => TypeId::U64,
        "f32" => TypeId::F32,
        "f64" => TypeId::F64,
        "f128" => TypeId::F128,
        "bool" => TypeId::BOOL,
        "string" => TypeId::STRING,
        "handle" => TypeId::HANDLE,
        "range" => TypeId::RANGE,
        _ => TypeId::INVALID,
    }
}

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
        AstPrimitive::F128 => "f128",
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

/// Module-specific compilation context passed to method compilation helpers.
struct ModuleCompileInfo<'a> {
    interner: &'a Interner,
    module_id: ModuleId,
    global_inits: &'a FxHashMap<Symbol, Rc<Expr>>,
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
        // Skip generic structs - they're compiled via monomorphized instances
        if struct_decl.has_type_params() {
            return Ok(());
        }
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

    /// Register a method in the JIT function registry if not already registered.
    ///
    /// Returns the function key for downstream use (method_func_keys, compilation).
    /// If the method is already registered (e.g. from overlapping implement blocks),
    /// returns the existing key without re-declaring.
    fn register_method_func(
        &mut self,
        method_id: MethodId,
        sig: &cranelift::prelude::Signature,
        mode: DeclareMode,
    ) -> crate::function_registry::FunctionKey {
        let full_name_id = self.query().method_full_name(method_id);
        let func_key = self.func_registry.intern_name_id(full_name_id);
        if self.func_registry.func_id(func_key).is_none() {
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = match mode {
                DeclareMode::Declare => self.jit.declare_function(&display_name, sig),
                DeclareMode::Import => self.jit.import_function(&display_name, sig),
            };
            self.func_registry.set_func_id(func_key, jit_func_id);
        }
        func_key
    }

    /// Core implementation for compiling methods of a class or struct
    fn compile_type_methods(
        &mut self,
        data: TypeMethodsData<'_>,
        _program: &vole_frontend::Program,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Look up TypeDefId from name (needed as key for type_metadata)
        let query = self.query();
        let type_def_id = query
            .try_name_id(module_id, &[data.name])
            .and_then(|name_id| query.try_type_def_id(name_id))
            .ok_or_else(|| {
                CodegenError::not_found(
                    "type",
                    format!(
                        "{} {}",
                        data.type_kind,
                        self.query().resolve_symbol(data.name)
                    ),
                )
            })?;

        let metadata = self
            .state
            .type_metadata
            .get(&type_def_id)
            .cloned()
            .ok_or_else(|| {
                CodegenError::not_found(
                    "type_metadata",
                    format!(
                        "{} {}",
                        data.type_kind,
                        self.query().resolve_symbol(data.name)
                    ),
                )
            })?;

        for method in data.methods {
            self.compile_method(method, data.name, &metadata)?;
        }

        // Compile default methods from implemented interfaces.
        // Direct method names (for skipping explicitly implemented methods, cross-interner safe).
        let direct_method_name_strs: std::collections::HashSet<String> = data
            .methods
            .iter()
            .map(|m| self.resolve_symbol(m.name))
            .collect();

        // Collect interface name strings using query (avoids borrow conflicts with compile calls).
        let interface_name_strs: Vec<String> = {
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
                            query.last_segment(interface_def.name_id)
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        // Collect (InterfaceMethod, is_from_module) pairs before any mutable operations.
        // We clone the method data so we can release the borrow on self.analyzed.
        struct DefaultMethodInfo {
            method: InterfaceMethod,
            /// True if from a module program (needs module interner for compilation).
            from_module: bool,
            /// The interner key (module path) if from_module is true.
            module_path: Option<String>,
        }
        let mut default_methods_to_compile: Vec<DefaultMethodInfo> = Vec::new();
        for interface_name_str in &interface_name_strs {
            // Search main program first
            let found_in_main = self.analyzed.program.declarations.iter().find_map(|decl| {
                if let vole_frontend::Decl::Interface(iface) = decl {
                    let name_str = self.analyzed.interner.resolve(iface.name);
                    if name_str == interface_name_str {
                        return Some(iface.methods.clone());
                    }
                }
                None
            });
            if let Some(methods) = found_in_main {
                for method in methods {
                    let method_name_str = self.analyzed.interner.resolve(method.name).to_string();
                    if method.body.is_some() && !direct_method_name_strs.contains(&method_name_str)
                    {
                        default_methods_to_compile.push(DefaultMethodInfo {
                            method,
                            from_module: false,
                            module_path: None,
                        });
                    }
                }
                continue; // Found in main, no need to search modules
            }

            // Search module programs
            let module_paths: Vec<String> = self.analyzed.module_programs.keys().cloned().collect();
            for module_path in module_paths {
                let found = {
                    let (prog, interner) = &self.analyzed.module_programs[&module_path];
                    prog.declarations.iter().find_map(|decl| {
                        if let vole_frontend::Decl::Interface(iface) = decl {
                            let name_str = interner.resolve(iface.name);
                            if name_str == interface_name_str {
                                return Some((iface.methods.clone(), interner.clone()));
                            }
                        }
                        None
                    })
                };
                if let Some((methods, mod_interner)) = found {
                    for method in methods {
                        let method_name_str = mod_interner.resolve(method.name).to_string();
                        if method.body.is_some()
                            && !direct_method_name_strs.contains(&method_name_str)
                        {
                            default_methods_to_compile.push(DefaultMethodInfo {
                                method,
                                from_module: true,
                                module_path: Some(module_path.clone()),
                            });
                        }
                    }
                    break; // Found in this module, no need to search further
                }
            }
        }

        for info in default_methods_to_compile {
            if info.from_module {
                let module_path = info.module_path.as_deref().unwrap_or("");
                let module_id = self.query().module_id_or_main(module_path);
                let module_interner = self.analyzed.module_programs[module_path].1.clone();
                self.compile_default_method_with_interner(
                    &info.method,
                    data.name,
                    &metadata,
                    &module_interner,
                    Some(module_id),
                )?;
            } else {
                self.compile_default_method(&info.method, data.name, &metadata)?;
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
        match &ty.kind {
            TypeExprKind::Primitive(p) => Some(primitive_type_name(*p).to_string()),
            TypeExprKind::Handle => Some("handle".to_string()),
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                Some(self.query().resolve_symbol(*sym).to_string())
            }
            // `extend [T] with Iterable<T>` has an Array target type.
            TypeExprKind::Array(_) => Some("array".to_string()),
            _ => None,
        }
    }

    /// Get the type name string from a TypeExpr using a specific interner
    /// (for module-specific symbols)
    fn get_type_name_from_expr_with_interner(
        &self,
        ty: &TypeExpr,
        interner: &Interner,
    ) -> Option<String> {
        match &ty.kind {
            TypeExprKind::Primitive(p) => Some(primitive_type_name(*p).to_string()),
            TypeExprKind::Handle => Some("handle".to_string()),
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                Some(interner.resolve(*sym).to_string())
            }
            // `extend [T] with Iterable<T>` has an Array target type.
            TypeExprKind::Array(_) => Some("array".to_string()),
            _ => None,
        }
    }

    /// Register implement block methods (first pass)
    pub(super) fn register_implement_block(
        &mut self,
        impl_block: &ImplementBlock,
    ) -> CodegenResult<()> {
        let module_id = self.program_module();
        self.register_implement_block_in_module(impl_block, module_id)
    }

    /// Register implement block methods using a specific module for type lookups.
    pub(super) fn register_implement_block_in_module(
        &mut self,
        impl_block: &ImplementBlock,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
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
    ) -> CodegenResult<()> {
        // Use module-specific interner for symbol resolution
        let Some(type_name) =
            self.get_type_name_from_expr_with_interner(&impl_block.target_type, interner)
        else {
            return Ok(());
        };

        // Get TypeId for self binding (same as register_implement_block_with_interner).
        // Handles primitive types, handle, array, and named/generic types.
        let (self_type_id, impl_type_id) = match &impl_block.target_type.kind {
            TypeExprKind::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                let type_id = self.arena().primitive(prim_type);
                let impl_id = self.impl_type_id_from_type_id(type_id);
                (type_id, impl_id)
            }
            TypeExprKind::Handle => {
                let type_id = TypeId::HANDLE;
                let impl_id = self.impl_type_id_from_type_id(type_id);
                (type_id, impl_id)
            }
            // Array target type: `extend [T] with Iterable<T>`.
            TypeExprKind::Array(_) => {
                let type_id = match self.arena().lookup_any_array() {
                    Some(id) => id,
                    None => return Ok(()), // No array type in arena yet, skip
                };
                let array_name_id = match self.registry().array_name_id() {
                    Some(id) => id,
                    None => return Ok(()),
                };
                let impl_id = Some(ImplTypeId::from_name_id(array_name_id));
                (type_id, impl_id)
            }
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                // Check if this is a named primitive (e.g., "range").
                let type_name_str = interner.resolve(*sym).to_string();
                let primitive_type_id = primitive_type_id_by_name(&type_name_str);
                if !primitive_type_id.is_invalid() {
                    let impl_id = self.impl_type_id_from_type_id(primitive_type_id);
                    (primitive_type_id, impl_id)
                } else {
                    // Use module-specific interner for symbol resolution
                    let type_def_id = self
                        .query()
                        .try_name_id_with_interner(module_id, &[*sym], interner)
                        .and_then(|name_id| self.query().try_type_def_id(name_id))
                        .ok_or_else(|| {
                            CodegenError::internal_with_context(
                                "import_module_implement_block: type not found",
                                type_name.clone(),
                            )
                        })?;
                    let metadata = self.state.type_metadata.get(&type_def_id).ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "import_module_implement_block: type not in type_metadata",
                            format!("{:?}", type_def_id),
                        )
                    })?;
                    let impl_id = self.impl_type_id_from_type_id(metadata.vole_type);
                    (metadata.vole_type, impl_id)
                }
            }
            _ => {
                return Err(CodegenError::internal(
                    "import_module_implement_block: unsupported target type",
                ));
            }
        };

        let impl_type_id_for_def = impl_type_id;
        let type_def_id_opt =
            impl_type_id_for_def.and_then(|id| self.query().try_type_def_id(id.name_id()));

        // Import explicitly declared instance methods
        for method in &impl_block.methods {
            let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name);
            let type_def_id = impl_type_id_for_def
                .and_then(|impl_id| self.query().try_type_def_id(impl_id.name_id()));

            let (sig, semantic_method_id) = {
                let tdef_id = type_def_id.ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "import: type_def_id missing for instance method",
                        format!("{}.{}", type_name, interner.resolve(method.name)),
                    )
                })?;
                let name_id = method_name_id.ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "import: method_name_id missing for instance method",
                        format!("{}.{}", type_name, interner.resolve(method.name)),
                    )
                })?;
                let method_id = self.query().find_method(tdef_id, name_id).ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "import: method not in entity_registry",
                        format!("{}.{}", type_name, interner.resolve(method.name)),
                    )
                })?;
                let sig =
                    self.build_signature_for_method(method_id, SelfParam::TypedId(self_type_id));
                (sig, method_id)
            };
            let func_key = self.register_method_func(semantic_method_id, &sig, DeclareMode::Import);

            if let Some(tdef_id) = type_def_id
                && let Some(name_id) = method_name_id
            {
                let type_name_id = self.query().get_type(tdef_id).name_id;
                self.state
                    .method_func_keys
                    .insert((type_name_id, name_id), func_key);
            }
        }

        // Import interface default methods (concrete ones, not abstract/generic).
        // These were compiled as part of the module (in register_implement_block_with_interner
        // + compile_module_implement_block) and must be imported when using the module cache.
        if let Some(type_def_id) = type_def_id_opt {
            let direct_method_name_strs: std::collections::HashSet<String> = impl_block
                .methods
                .iter()
                .map(|m| interner.resolve(m.name).to_string())
                .collect();

            let iface_default_methods: Vec<(MethodId, NameId, TypeDefId)> = {
                let query = self.query();
                let mut results = Vec::new();
                for interface_tdef_id in query.implemented_interfaces(type_def_id) {
                    for iface_method_id in query.type_methods(interface_tdef_id) {
                        let method_def = query.get_method(iface_method_id);
                        if !method_def.has_default || method_def.external_binding.is_some() {
                            continue;
                        }
                        let method_name_str =
                            query.last_segment(method_def.name_id).unwrap_or_default();
                        if direct_method_name_strs.contains(&method_name_str) {
                            continue;
                        }
                        if let Some(impl_method_id) =
                            query.find_method(type_def_id, method_def.name_id)
                        {
                            results.push((impl_method_id, method_def.name_id, interface_tdef_id));
                        }
                    }
                }
                results
            };

            let type_name_id = self.query().get_type(type_def_id).name_id;
            for (semantic_method_id, method_name_id, interface_tdef_id) in iface_default_methods {
                // Build TypeParam substitution map for this interface implementation.
                let type_param_subs = self
                    .query()
                    .interface_impl_type_param_subs(type_def_id, interface_tdef_id);
                // Skip abstract/generic default methods (not compiled in the module).
                if !type_param_subs.is_empty() {
                    let arena = self.arena();
                    let has_abstract = type_param_subs
                        .values()
                        .any(|&v| arena.unwrap_type_param(v).is_some());
                    if has_abstract {
                        continue;
                    }
                }
                let sig = {
                    let method_def = self.query().get_method(semantic_method_id);
                    let arena = self.arena();
                    let (param_type_ids, return_type_id) = match arena
                        .unwrap_function(method_def.signature_id)
                    {
                        Some((params, ret, _)) => {
                            let subst_params: Vec<TypeId> = params
                                .iter()
                                .map(|&p| {
                                    if arena.is_self_type(p) {
                                        self_type_id
                                    } else {
                                        arena.lookup_substitute(p, &type_param_subs).unwrap_or(p)
                                    }
                                })
                                .collect();
                            let subst_ret = if arena.is_self_type(ret) {
                                self_type_id
                            } else {
                                arena
                                    .lookup_substitute(ret, &type_param_subs)
                                    .unwrap_or(ret)
                            };
                            (subst_params, subst_ret)
                        }
                        None => (vec![], self.arena().void()),
                    };
                    self.build_signature_from_type_ids(
                        &param_type_ids,
                        Some(return_type_id),
                        SelfParam::TypedId(self_type_id),
                    )
                };
                let func_key =
                    self.register_method_func(semantic_method_id, &sig, DeclareMode::Import);
                self.state
                    .method_func_keys
                    .insert((type_name_id, method_name_id), func_key);
            }
        }

        // Import static methods
        if let Some(ref statics) = impl_block.statics {
            self.import_implement_statics_block(statics, &type_name, interner, module_id)?;
        }

        Ok(())
    }

    /// Import static methods from a statics block.
    fn import_implement_statics_block(
        &mut self,
        statics: &StaticsBlock,
        type_name: &str,
        interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        let type_def_id = self.query().resolve_type_def_by_str(module_id, type_name);

        for method in &statics.methods {
            if method.body.is_none() {
                continue;
            }
            let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name);
            let (sig, semantic_method_id) = {
                let tdef_id = type_def_id.ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "import: type_def_id missing for static method",
                        format!("{}.{}", type_name, interner.resolve(method.name)),
                    )
                })?;
                let name_id = method_name_id.ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "import: method_name_id missing for static method",
                        format!("{}.{}", type_name, interner.resolve(method.name)),
                    )
                })?;
                let method_id = self
                    .query()
                    .find_static_method(tdef_id, name_id)
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "import: static method not in entity_registry",
                            format!("{}.{}", type_name, interner.resolve(method.name)),
                        )
                    })?;
                let sig = self.build_signature_for_method(method_id, SelfParam::None);
                (sig, method_id)
            };
            let func_key = self.register_method_func(semantic_method_id, &sig, DeclareMode::Import);

            let type_name_id =
                self.query()
                    .get_type(type_def_id.ok_or_else(|| {
                        CodegenError::internal("import statics: missing type_def_id")
                    })?)
                    .name_id;
            self.state.method_func_keys.insert(
                (
                    type_name_id,
                    method_name_id.ok_or_else(|| {
                        CodegenError::internal("import statics: missing method_name_id")
                    })?,
                ),
                func_key,
            );
        }

        Ok(())
    }

    /// Register implement block methods with a specific interner and module (for module programs)
    pub(super) fn register_implement_block_with_interner(
        &mut self,
        impl_block: &ImplementBlock,
        interner: &Interner,
        module_id: ModuleId,
    ) -> CodegenResult<()> {
        // Get type name string using module-specific interner
        let Some(type_name) =
            self.get_type_name_from_expr_with_interner(&impl_block.target_type, interner)
        else {
            return Ok(()); // Unsupported type for implement block
        };

        // For named types (records/classes), look up in type_metadata since they're not in type_aliases
        // Get type_id directly from metadata to avoid to_type() conversion
        let (self_type_id, impl_type_id) = match &impl_block.target_type.kind {
            TypeExprKind::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                let type_id = self.arena().primitive(prim_type);
                let impl_id = self.impl_type_id_from_type_id(type_id);
                (type_id, impl_id)
            }
            TypeExprKind::Handle => {
                let type_id = TypeId::HANDLE;
                let impl_id = self.impl_type_id_from_type_id(type_id);
                (type_id, impl_id)
            }
            // Array target type: `extend [T] with Iterable<T>`.
            // All array TypeIds map to pointer_type in Cranelift, so any existing
            // array TypeId can be used as self_type_id for signature building.
            // The ImplTypeId is derived from the entity registry's array_name_id,
            // which is independent of the element type.
            TypeExprKind::Array(_) => {
                // Find any existing array TypeId (arena is immutable in codegen).
                // The prelude always interns [i64] arrays, so this should succeed.
                let type_id = self.arena().lookup_any_array().ok_or_else(|| {
                    CodegenError::internal(
                        "extend [T] with Iterable<T>: no array type found in arena (prelude not loaded?)",
                    )
                })?;
                // Construct ImplTypeId directly from array_name_id (avoids need for specific TypeId).
                let array_name_id = self.registry().array_name_id().ok_or_else(|| {
                    CodegenError::internal(
                        "extend [T] with Iterable<T>: array_name_id not registered in entity registry",
                    )
                })?;
                let impl_id = Some(ImplTypeId::from_name_id(array_name_id));
                (type_id, impl_id)
            }
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                // Resolve the symbol string first. If it matches a known primitive name
                // (e.g. "range", which parses as Named since it is not a lexer keyword),
                // use primitive_type_id_by_name directly instead of looking up in the
                // entity registry (builtins are only registered in the builtin module's
                // namespace, not in module-specific namespace).
                let type_name_str = interner.resolve(*sym).to_string();
                let primitive_type_id = primitive_type_id_by_name(&type_name_str);
                if !primitive_type_id.is_invalid() {
                    let type_id = primitive_type_id;
                    let impl_id = self.impl_type_id_from_type_id(type_id);
                    (type_id, impl_id)
                } else {
                    // Look up TypeDefId from Symbol (for Generic, uses the base class name)
                    // Use the module-specific interner to resolve symbols from that module's AST
                    // Try given module first, then fall back to program module
                    // (implement blocks in tests blocks may target parent-scope types)
                    let type_def_id = self
                        .query()
                        .try_name_id_with_interner(module_id, &[*sym], interner)
                        .and_then(|name_id| self.query().try_type_def_id(name_id))
                        .or_else(|| {
                            let prog_mod = self.program_module();
                            if prog_mod != module_id {
                                // Fall back to program module using its interner
                                self.query()
                                    .try_name_id(prog_mod, &[*sym])
                                    .and_then(|name_id| self.query().try_type_def_id(name_id))
                            } else {
                                None
                            }
                        })
                        .ok_or_else(|| {
                            CodegenError::internal_with_context(
                                "implement block target type not in entity registry",
                                format!("{:?}", sym),
                            )
                        })?;
                    let metadata = self.state.type_metadata.get(&type_def_id).ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "implement block target type not in type_metadata",
                            format!("{:?}", type_def_id),
                        )
                    })?;
                    // Use TypeId directly
                    let impl_id = self.impl_type_id_from_type_id(metadata.vole_type);
                    (metadata.vole_type, impl_id)
                }
            }
            _ => {
                return Err(CodegenError::internal(
                    "register_implement_block: target type was not Primitive, Handle, Named, Generic, or Array, but passed get_type_name_from_expr check",
                ));
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
                let tdef_id = type_def_id.ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "implement block instance method without TypeDefId",
                        format!("{}.{}", type_name, interner.resolve(method.name)),
                    )
                })?;
                let name_id = method_name_id.ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "implement block instance method without NameId",
                        format!("{}.{}", type_name, interner.resolve(method.name)),
                    )
                })?;
                let semantic_method_id =
                    self.query().find_method(tdef_id, name_id).ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "implement block instance method not in entity_registry",
                            format!(
                                "{}.{} (type_def_id={:?}, method_name_id={:?})",
                                type_name,
                                interner.resolve(method.name),
                                tdef_id,
                                name_id
                            ),
                        )
                    })?;
                let sig = self.build_signature_for_method(
                    semantic_method_id,
                    SelfParam::TypedId(self_type_id),
                );
                (sig, semantic_method_id)
            };
            let func_key =
                self.register_method_func(semantic_method_id, &sig, DeclareMode::Declare);
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

        // Register interface default methods (if this is an implement block with a trait).
        // The explicit methods in impl_block.methods have been registered above.
        // Default methods (not overridden) also need to be registered so that
        // codegen can find them via method_func_keys at call sites.
        if let Some(type_def_id) =
            impl_type_id.and_then(|impl_id| self.query().try_type_def_id(impl_id.name_id()))
        {
            // Collect direct method names (to skip explicitly implemented ones)
            let direct_method_name_strs: std::collections::HashSet<String> = impl_block
                .methods
                .iter()
                .map(|m| interner.resolve(m.name).to_string())
                .collect();

            // Get all interface default methods registered on this type by sema.
            // Sema's register_interface_default_methods_on_implementing_type already
            // copied default methods onto the implementing type in the entity registry.
            // We just need to find them and register their JIT functions.
            let iface_default_methods: Vec<(MethodId, NameId, TypeDefId)> = {
                let query = self.query();
                // For each interface the type implements, collect its default methods
                let mut results = Vec::new();
                for interface_tdef_id in query.implemented_interfaces(type_def_id) {
                    for iface_method_id in query.type_methods(interface_tdef_id) {
                        let method_def = query.get_method(iface_method_id);
                        if !method_def.has_default {
                            continue;
                        }
                        // Skip external default methods - they are provided by the runtime,
                        // not compiled from Vole source. Declaring them without compiling
                        // would cause a JIT "function must be compiled before finalized" panic.
                        if method_def.external_binding.is_some() {
                            continue;
                        }
                        let method_name_str =
                            query.last_segment(method_def.name_id).unwrap_or_default();
                        if direct_method_name_strs.contains(&method_name_str) {
                            continue; // Explicitly implemented, skip
                        }
                        // Find the method as registered on the implementing type
                        if let Some(impl_method_id) =
                            query.find_method(type_def_id, method_def.name_id)
                        {
                            results.push((impl_method_id, method_def.name_id, interface_tdef_id));
                        }
                    }
                }
                results
            };

            // Register each default method in the JIT function registry and method_func_keys.
            // Build signatures with Placeholder(SelfType) substituted by self_type_id, and
            // TypeParam(T) substituted with the concrete interface type arg (e.g., i64 for
            // Iterable<i64>), so that the JIT function declaration signature matches what
            // the compiler will emit.
            let type_name_id = self.query().get_type(type_def_id).name_id;
            for (semantic_method_id, method_name_id, interface_tdef_id) in iface_default_methods {
                // Build TypeParam substitution map for this interface's implementation.
                let type_param_subs = self
                    .query()
                    .interface_impl_type_param_subs(type_def_id, interface_tdef_id);
                // Skip registration if any substitution value is still a TypeParam (abstract).
                // Generic interface implementations (e.g., `extend [T] with Iterable<T>`) are
                // handled via monomorphization at the call site, not registered here.
                if !type_param_subs.is_empty() {
                    let arena = self.arena();
                    let has_abstract = type_param_subs
                        .values()
                        .any(|&v| arena.unwrap_type_param(v).is_some());
                    if has_abstract {
                        continue;
                    }
                }
                let sig = {
                    let method_def = self.query().get_method(semantic_method_id);
                    let arena = self.arena();
                    let (param_type_ids, return_type_id) = match arena
                        .unwrap_function(method_def.signature_id)
                    {
                        Some((params, ret, _)) => {
                            let subst_params: Vec<TypeId> = params
                                .iter()
                                .map(|&p| {
                                    if arena.is_self_type(p) {
                                        self_type_id
                                    } else {
                                        arena.lookup_substitute(p, &type_param_subs).unwrap_or(p)
                                    }
                                })
                                .collect();
                            let subst_ret = if arena.is_self_type(ret) {
                                self_type_id
                            } else {
                                arena
                                    .lookup_substitute(ret, &type_param_subs)
                                    .unwrap_or(ret)
                            };
                            (subst_params, subst_ret)
                        }
                        None => (vec![], self.arena().void()),
                    };
                    self.build_signature_from_type_ids(
                        &param_type_ids,
                        Some(return_type_id),
                        SelfParam::TypedId(self_type_id),
                    )
                };
                let func_key =
                    self.register_method_func(semantic_method_id, &sig, DeclareMode::Declare);
                self.state
                    .method_func_keys
                    .insert((type_name_id, method_name_id), func_key);
            }
        }

        // Register static methods from statics block (if present)
        if let Some(ref statics) = impl_block.statics {
            // Reuse the already-resolved impl type identity.
            // This works for module-local types and avoids program_module()-only lookup.
            let type_def_id =
                impl_type_id.and_then(|impl_id| self.query().try_type_def_id(impl_id.name_id()));

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
                    let tdef_id = type_def_id.ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "implement statics method without TypeDefId",
                            format!("{}.{}", type_name, interner.resolve(method.name)),
                        )
                    })?;
                    let name_id = method_name_id.ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "implement statics method without NameId",
                            format!("{}.{}", type_name, interner.resolve(method.name)),
                        )
                    })?;
                    let method_id = self
                        .query()
                        .find_static_method(tdef_id, name_id)
                        .ok_or_else(|| {
                            CodegenError::internal_with_context(
                                "implement statics method not in entity_registry",
                                format!(
                                    "{}.{} (type_def_id={:?}, method_name_id={:?})",
                                    type_name,
                                    interner.resolve(method.name),
                                    tdef_id,
                                    name_id
                                ),
                            )
                        })?;
                    let sig = self.build_signature_for_method(method_id, SelfParam::None);
                    (sig, method_id)
                };

                let func_key =
                    self.register_method_func(semantic_method_id, &sig, DeclareMode::Declare);

                // Register in method_func_keys for codegen lookup using type's NameId for stable lookup
                let tdef_id = type_def_id.ok_or_else(|| {
                    CodegenError::internal("register_implement_block statics: missing type_def_id")
                })?;
                let type_name_id = self.query().get_type(tdef_id).name_id;
                self.state.method_func_keys.insert(
                    (
                        type_name_id,
                        method_name_id.ok_or_else(|| {
                            CodegenError::internal(
                                "register_implement_block statics: missing method_name_id",
                            )
                        })?,
                    ),
                    func_key,
                );
            }
        }

        Ok(())
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
        let self_type_id = match &impl_block.target_type.kind {
            TypeExprKind::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                self.arena().primitive(prim_type)
            }
            TypeExprKind::Handle => TypeId::HANDLE,
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
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
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "implement block self type not in entity registry",
                            format!("{:?}", sym),
                        )
                    })?;
                self.state
                    .type_metadata
                    .get(&type_def_id)
                    .map(|m| m.vole_type)
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "implement block self type not in type_metadata",
                            format!("{:?}", type_def_id),
                        )
                    })?
            }
            _ => {
                return Err(CodegenError::internal(
                    "compile_implement_block: self type was not Primitive, Handle, Named, or Generic, but passed get_type_name_from_expr check",
                ));
            }
        };
        // Get TypeDefId for method lookup via method_func_keys
        let impl_type_id = self.impl_type_id_from_type_id(self_type_id);
        let type_def_id = impl_type_id.and_then(|id| self.query().try_type_def_id(id.name_id()));

        for method in &impl_block.methods {
            let method_key = if let Some(type_def_id) = type_def_id {
                // Use type's NameId for stable lookup across analyzer instances
                let type_name_id = self.query().get_type(type_def_id).name_id;
                let method_id = self.method_name_id(method.name)?;
                self.state
                    .method_func_keys
                    .get(&(type_name_id, method_id))
                    .map(|&func_key| MethodInfo { func_key })
            } else {
                None
            };
            self.compile_implement_method(method, self_type_id, method_key)?;
        }

        // Compile interface default methods (if this is a trait implement block).
        // These are default methods from the interface that are NOT explicitly implemented
        // in impl_block.methods. They've been registered in pass 1; now compile their bodies.
        if let Some(type_def_id) = type_def_id {
            let direct_method_name_strs: std::collections::HashSet<String> = impl_block
                .methods
                .iter()
                .map(|m| self.resolve_symbol(m.name))
                .collect();

            // Collect (interface_name_str, default_method_name_id, interface_tdef_id) triples.
            let iface_default_method_ids: Vec<(String, MethodId, NameId, TypeDefId)> = {
                let query = self.query();
                let mut results = Vec::new();
                for interface_tdef_id in query.implemented_interfaces(type_def_id) {
                    let iface_name_str = {
                        let interface_def = query.get_type(interface_tdef_id);
                        query
                            .last_segment(interface_def.name_id)
                            .unwrap_or_default()
                    };
                    for iface_method_id in query.type_methods(interface_tdef_id) {
                        let method_def = query.get_method(iface_method_id);
                        if !method_def.has_default {
                            continue;
                        }
                        // Skip external default methods - only Vole-implemented defaults have bodies.
                        if method_def.external_binding.is_some() {
                            continue;
                        }
                        let method_name_str =
                            query.last_segment(method_def.name_id).unwrap_or_default();
                        if direct_method_name_strs.contains(&method_name_str) {
                            continue;
                        }
                        if let Some(impl_method_id) =
                            query.find_method(type_def_id, method_def.name_id)
                        {
                            results.push((
                                iface_name_str.clone(),
                                impl_method_id,
                                method_def.name_id,
                                interface_tdef_id,
                            ));
                        }
                    }
                }
                results
            };

            // Compile each default method body using the appropriate interner.
            // We need the InterfaceMethod AST node (with the body) from the right program.
            for (iface_name_str, semantic_method_id, method_name_id, interface_tdef_id) in
                iface_default_method_ids
            {
                // Look up function key (registered in pass 1)
                let type_name_id = self.query().get_type(type_def_id).name_id;
                let func_key = match self
                    .state
                    .method_func_keys
                    .get(&(type_name_id, method_name_id))
                {
                    Some(&k) => k,
                    None => continue, // Not registered, skip
                };
                let func_id = match self.func_registry.func_id(func_key) {
                    Some(id) => id,
                    None => continue,
                };

                // Skip if the function was imported from cache (Import linkage), not declared
                // for local compilation (Export linkage). This happens when a user file has
                // `implement string { ... }` and the prelude (which already compiled string::lt,
                // string::gt, etc.) is cached — those default methods are already available as
                // imports and must not be redefined.
                if !self.jit.is_local_func_id(func_id) {
                    continue;
                }

                // Collect method_name_str for searching the interface decl
                let method_name_str = self
                    .analyzed
                    .name_table()
                    .last_segment_str(method_name_id)
                    .unwrap_or_default();

                // Find the interface AST decl and compile the method body
                let iface_info =
                    self.collect_interface_method_body(&iface_name_str, &method_name_str);
                let Some((body, method_params, iface_interner, iface_module_id)) = iface_info
                else {
                    continue;
                };

                // Build type-parameter substitution map for this interface implementation.
                // E.g., for `extend range with Iterable<i64>`, maps T_name_id -> i64.
                let type_param_subs = self
                    .query()
                    .interface_impl_type_param_subs(type_def_id, interface_tdef_id);

                // Skip compilation if any substitution value is still a TypeParam (abstract/generic).
                // This handles `extend [T] with Iterable<T>` where T is unresolved — those default
                // methods are instantiated at the call site via monomorphization, not compiled here.
                if !type_param_subs.is_empty() {
                    let arena = self.arena();
                    let has_abstract = type_param_subs
                        .values()
                        .any(|&v| arena.unwrap_type_param(v).is_some());
                    if has_abstract {
                        continue;
                    }
                }

                // Get signature data from sema, substituting:
                //   1. Placeholder(SelfType) -> self_type_id
                //   2. TypeParam(T) -> concrete element type (via type_param_subs)
                let (param_type_ids, return_type_id) = {
                    let method_def = self.query().get_method(semantic_method_id);
                    let arena = self.arena();
                    match arena.unwrap_function(method_def.signature_id) {
                        Some((params, ret, _)) => {
                            let subst_params: Vec<TypeId> = params
                                .iter()
                                .map(|&p| {
                                    if arena.is_self_type(p) {
                                        self_type_id
                                    } else {
                                        arena.lookup_substitute(p, &type_param_subs).unwrap_or(p)
                                    }
                                })
                                .collect();
                            let subst_ret = if arena.is_self_type(ret) {
                                self_type_id
                            } else {
                                arena
                                    .lookup_substitute(ret, &type_param_subs)
                                    .unwrap_or(ret)
                            };
                            (subst_params, subst_ret)
                        }
                        None => continue,
                    }
                };

                // Build signature from substituted types (not via build_signature_for_method
                // which uses the unsubstituted signature_id from sema).
                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    SelfParam::TypedId(self_type_id),
                );
                self.jit.ctx.func.signature = sig;

                let param_types = self.type_ids_to_cranelift(&param_type_ids);
                let params: Vec<_> = method_params
                    .iter()
                    .zip(param_type_ids.iter())
                    .zip(param_types.iter())
                    .map(|((p, &type_id), &cranelift_type)| (*p, type_id, cranelift_type))
                    .collect();

                let self_sym = iface_interner
                    .lookup("self")
                    .unwrap_or_else(|| self.self_symbol());

                let source_file_ptr = self.source_file_ptr();
                let self_cranelift_type =
                    type_id_to_cranelift(self_type_id, self.arena(), self.pointer_type);
                let self_binding = (self_sym, self_type_id, self_cranelift_type);

                let no_global_inits = FxHashMap::default();
                let mut builder_ctx = FunctionBuilderContext::new();
                {
                    let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                    let env =
                        compile_env!(self, &iface_interner, &no_global_inits, source_file_ptr);
                    let mut codegen_ctx = CodegenCtx::new(
                        &mut self.jit.module,
                        &mut self.func_registry,
                        &mut self.pending_monomorphs,
                    );
                    let mut config = FunctionCompileConfig::method(
                        &body,
                        params,
                        self_binding,
                        Some(return_type_id),
                    );
                    // Iterable default method bodies have special RC ownership semantics:
                    // the outer call-site (used_array_iterable_path) transfers closure
                    // ownership to the body, so pipeline methods must NOT rc_inc and
                    // terminal methods must emit rc_dec after the runtime call.
                    if self
                        .analyzed
                        .name_table()
                        .well_known
                        .is_iterable_type_def(interface_tdef_id)
                    {
                        config = config.with_iterable_default_body();
                    }
                    // Pass type parameter substitutions so that abstract type params
                    // (e.g. T in Iterable<T>) are resolved to concrete types (e.g. string)
                    // when compiling the default method body. Without this, calls like
                    // `self.iter().take(n)` inside the Iterable::take default body would
                    // see the return of self.iter() as Iterator<T> (abstract interface type)
                    // and use vtable dispatch for the chained .take(n) call, causing a
                    // segfault when the actual runtime value is a raw *mut RcIterator.
                    compile_function_inner_with_params(
                        builder,
                        &mut codegen_ctx,
                        &env,
                        config,
                        iface_module_id,
                        if type_param_subs.is_empty() {
                            None
                        } else {
                            Some(&type_param_subs)
                        },
                    )?;
                }
                self.finalize_function(func_id)?;
            }
        }

        // Compile static methods from statics block (if present)
        if let Some(ref statics) = impl_block.statics {
            let interner = self.analyzed.interner.clone();
            self.compile_implement_statics(statics, &type_name, type_def_id, None, &interner)?;
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
    ) -> CodegenResult<()> {
        // Use module-specific interner for symbol resolution
        let Some(type_name) =
            self.get_type_name_from_expr_with_interner(&impl_block.target_type, interner)
        else {
            return Ok(());
        };

        // Get the TypeId for `self` binding
        let self_type_id = match &impl_block.target_type.kind {
            TypeExprKind::Primitive(p) => {
                let prim_type = vole_sema::PrimitiveType::from_ast(*p);
                self.arena().primitive(prim_type)
            }
            TypeExprKind::Handle => TypeId::HANDLE,
            // Array target type: `extend [T] with Iterable<T>`.
            // All array TypeIds map to pointer_type in Cranelift, so use any existing
            // array TypeId from the arena as self_type_id.
            TypeExprKind::Array(_) => self.arena().lookup_any_array().ok_or_else(|| {
                CodegenError::internal(
                    "compile_module_implement_block: extend [T] with ...: no array type in arena",
                )
            })?,
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                // Resolve the symbol string first. If it matches a known primitive name
                // (e.g. "range", which parses as Named since it is not a lexer keyword),
                // use primitive_type_id_by_name directly instead of looking up in the
                // entity registry (builtins are only registered in the builtin module's
                // namespace, not in module-specific namespaces).
                let type_name_str = interner.resolve(*sym).to_string();
                let primitive_type_id = primitive_type_id_by_name(&type_name_str);
                if !primitive_type_id.is_invalid() {
                    primitive_type_id
                } else {
                    // Use module-specific interner for symbol resolution
                    let type_def_id = self
                        .query()
                        .try_name_id_with_interner(module_id, &[*sym], interner)
                        .and_then(|name_id| self.query().try_type_def_id(name_id))
                        .ok_or_else(|| {
                            CodegenError::internal_with_context(
                                "implement block self type not in entity registry",
                                format!("{:?}", sym),
                            )
                        })?;
                    self.state
                        .type_metadata
                        .get(&type_def_id)
                        .map(|m| m.vole_type)
                        .ok_or_else(|| {
                            CodegenError::internal_with_context(
                                "implement block self type not in type_metadata",
                                format!("{:?}", type_def_id),
                            )
                        })?
                }
            }
            _ => {
                return Err(CodegenError::internal(
                    "compile_implement_block: target type was not Primitive, Handle, Named, Generic, or Array",
                ));
            }
        };

        let impl_type_id = self.impl_type_id_from_type_id(self_type_id);
        let type_def_id =
            impl_type_id.and_then(|id: ImplTypeId| self.query().try_type_def_id(id.name_id()));

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

        // Compile interface default methods (if this is a trait implement block).
        // These are default methods from the interface that are NOT explicitly implemented
        // in impl_block.methods. They've been registered in pass 1; now compile their bodies.
        if let Some(type_def_id) = type_def_id {
            let direct_method_name_strs: std::collections::HashSet<String> = impl_block
                .methods
                .iter()
                .map(|m| interner.resolve(m.name).to_string())
                .collect();

            // Collect (interface_name_str, default_method_name_id, interface_tdef_id) triples.
            let iface_default_method_ids: Vec<(String, MethodId, NameId, TypeDefId)> = {
                let query = self.query();
                let mut results = Vec::new();
                for interface_tdef_id in query.implemented_interfaces(type_def_id) {
                    let iface_name_str = {
                        let interface_def = query.get_type(interface_tdef_id);
                        query
                            .last_segment(interface_def.name_id)
                            .unwrap_or_default()
                    };
                    for iface_method_id in query.type_methods(interface_tdef_id) {
                        let method_def = query.get_method(iface_method_id);
                        if !method_def.has_default {
                            continue;
                        }
                        // Skip external default methods - only Vole-implemented defaults have bodies.
                        if method_def.external_binding.is_some() {
                            continue;
                        }
                        let method_name_str =
                            query.last_segment(method_def.name_id).unwrap_or_default();
                        if direct_method_name_strs.contains(&method_name_str) {
                            continue;
                        }
                        if let Some(impl_method_id) =
                            query.find_method(type_def_id, method_def.name_id)
                        {
                            results.push((
                                iface_name_str.clone(),
                                impl_method_id,
                                method_def.name_id,
                                interface_tdef_id,
                            ));
                        }
                    }
                }
                results
            };

            // Compile each default method body using the appropriate interner.
            for (iface_name_str, semantic_method_id, method_name_id, interface_tdef_id) in
                iface_default_method_ids
            {
                // Look up function key (registered in pass 1)
                let type_name_id = self.query().get_type(type_def_id).name_id;
                let func_key = match self
                    .state
                    .method_func_keys
                    .get(&(type_name_id, method_name_id))
                {
                    Some(&k) => k,
                    None => continue, // Not registered, skip
                };
                let func_id = match self.func_registry.func_id(func_key) {
                    Some(id) => id,
                    None => continue,
                };

                // Skip if the function was imported from cache (Import linkage), not declared
                // for local compilation (Export linkage). This happens when a user file has
                // `implement string { ... }` and the prelude (which already compiled string::lt,
                // string::gt, etc.) is cached — those default methods are already available as
                // imports and must not be redefined.
                if !self.jit.is_local_func_id(func_id) {
                    continue;
                }

                // Collect method_name_str for searching the interface decl
                let method_name_str = self
                    .analyzed
                    .name_table()
                    .last_segment_str(method_name_id)
                    .unwrap_or_default();

                // Find the interface AST decl and compile the method body
                let iface_info =
                    self.collect_interface_method_body(&iface_name_str, &method_name_str);
                let Some((body, method_params, iface_interner, iface_module_id)) = iface_info
                else {
                    continue;
                };

                // Build type-parameter substitution map for this interface implementation.
                // E.g., for `extend range with Iterable<i64>`, maps T_name_id -> i64.
                let type_param_subs = self
                    .query()
                    .interface_impl_type_param_subs(type_def_id, interface_tdef_id);

                // Skip compilation if any substitution value is still a TypeParam (abstract/generic).
                // This handles `extend [T] with Iterable<T>` where T is unresolved — those default
                // methods are instantiated at the call site via monomorphization, not compiled here.
                if !type_param_subs.is_empty() {
                    let arena = self.arena();
                    let has_abstract = type_param_subs
                        .values()
                        .any(|&v| arena.unwrap_type_param(v).is_some());
                    if has_abstract {
                        continue;
                    }
                }

                // Get signature data from sema, substituting:
                //   1. Placeholder(SelfType) -> self_type_id
                //   2. TypeParam(T) -> concrete element type (via type_param_subs)
                let (param_type_ids, return_type_id) = {
                    let method_def = self.query().get_method(semantic_method_id);
                    let arena = self.arena();
                    match arena.unwrap_function(method_def.signature_id) {
                        Some((params, ret, _)) => {
                            let subst_params: Vec<TypeId> = params
                                .iter()
                                .map(|&p| {
                                    if arena.is_self_type(p) {
                                        self_type_id
                                    } else {
                                        arena.lookup_substitute(p, &type_param_subs).unwrap_or(p)
                                    }
                                })
                                .collect();
                            let subst_ret = if arena.is_self_type(ret) {
                                self_type_id
                            } else {
                                arena
                                    .lookup_substitute(ret, &type_param_subs)
                                    .unwrap_or(ret)
                            };
                            (subst_params, subst_ret)
                        }
                        None => continue,
                    }
                };

                // Build signature from substituted types (not via build_signature_for_method
                // which uses the unsubstituted signature_id from sema).
                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    SelfParam::TypedId(self_type_id),
                );
                self.jit.ctx.func.signature = sig;

                let param_types = self.type_ids_to_cranelift(&param_type_ids);
                let params: Vec<_> = method_params
                    .iter()
                    .zip(param_type_ids.iter())
                    .zip(param_types.iter())
                    .map(|((p, &type_id), &cranelift_type)| (*p, type_id, cranelift_type))
                    .collect();

                let self_sym = iface_interner
                    .lookup("self")
                    .unwrap_or_else(|| self.self_symbol());

                let source_file_ptr = self.source_file_ptr();
                let self_cranelift_type =
                    type_id_to_cranelift(self_type_id, self.arena(), self.pointer_type);
                let self_binding = (self_sym, self_type_id, self_cranelift_type);

                let no_global_inits = FxHashMap::default();
                let mut builder_ctx = FunctionBuilderContext::new();
                {
                    let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                    let env =
                        compile_env!(self, &iface_interner, &no_global_inits, source_file_ptr);
                    let mut codegen_ctx = CodegenCtx::new(
                        &mut self.jit.module,
                        &mut self.func_registry,
                        &mut self.pending_monomorphs,
                    );
                    let mut config = FunctionCompileConfig::method(
                        &body,
                        params,
                        self_binding,
                        Some(return_type_id),
                    );
                    // Iterable default method bodies have special RC ownership semantics:
                    // the outer call-site (used_array_iterable_path) transfers closure
                    // ownership to the body, so pipeline methods must NOT rc_inc and
                    // terminal methods must emit rc_dec after the runtime call.
                    if self
                        .analyzed
                        .name_table()
                        .well_known
                        .is_iterable_type_def(interface_tdef_id)
                    {
                        config = config.with_iterable_default_body();
                    }
                    // Pass type parameter substitutions so that abstract type params
                    // (e.g. T in Iterable<T>) are resolved to concrete types (e.g. string)
                    // when compiling the default method body. Without this, calls like
                    // `self.iter().take(n)` inside the Iterable::take default body would
                    // see the return of self.iter() as Iterator<T> (abstract interface type)
                    // and use vtable dispatch for the chained .take(n) call, causing a
                    // segfault when the actual runtime value is a raw *mut RcIterator.
                    compile_function_inner_with_params(
                        builder,
                        &mut codegen_ctx,
                        &env,
                        config,
                        iface_module_id,
                        if type_param_subs.is_empty() {
                            None
                        } else {
                            Some(&type_param_subs)
                        },
                    )?;
                }
                self.finalize_function(func_id)?;
            }
        }

        // Compile static methods
        if let Some(ref statics) = impl_block.statics {
            self.compile_implement_statics(
                statics,
                &type_name,
                type_def_id,
                Some(module_id),
                interner,
            )?;
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
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "method name_id not found",
                    interner.resolve(method.name).to_string(),
                )
            })?;

        let semantic_method_id = type_def_id
            .and_then(|tdef_id| self.query().find_method(tdef_id, method_name_id))
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "implement block method not registered",
                    format!(
                        "{} (type_def_id={:?})",
                        interner.resolve(method.name),
                        type_def_id
                    ),
                )
            })?;

        let func_key = if let Some(info) = method_info {
            info.func_key
        } else {
            let method_def = self.query().get_method(semantic_method_id);
            self.func_registry.intern_name_id(method_def.full_name_id)
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("method", self.func_registry.display(func_key))
        })?;

        let sig =
            self.build_signature_for_method(semantic_method_id, SelfParam::TypedId(self_type_id));
        self.jit.ctx.func.signature = sig;

        let self_cranelift_type =
            type_id_to_cranelift(self_type_id, self.arena(), self.pointer_type);

        let source_file_ptr = self.source_file_ptr();
        // Use module interner to look up "self" since param names come from the module AST
        let self_sym = interner.lookup("self").ok_or_else(|| {
            CodegenError::internal("'self' keyword not interned in module interner")
        })?;

        // Build params: skip explicit `self` params — they are handled via the separate self_binding.
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.arena();
            let (param_type_ids, _, _) = arena
                .unwrap_function(method_def.signature_id)
                .ok_or_else(|| {
                    CodegenError::internal("method compilation: missing function signature")
                })?;
            method
                .params
                .iter()
                .filter(|p| p.name != self_sym)
                .zip(param_type_ids.iter())
                .map(|(param, &type_id)| {
                    let cranelift_type = type_id_to_cranelift(type_id, arena, self.pointer_type);
                    (param.name, type_id, cranelift_type)
                })
                .collect()
        };

        let method_return_type_id = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.arena();
            arena
                .unwrap_function(method_def.signature_id)
                .map(|(_, ret, _)| ret)
        };

        let no_global_inits = FxHashMap::default();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            // Use module interner for compilation
            let env = compile_env!(self, interner, &no_global_inits, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

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
        type_def_id: Option<TypeDefId>,
        module_id: Option<ModuleId>,
        interner: &Interner,
    ) -> CodegenResult<()> {
        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Resolve MethodId for this static method
            let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name);
            let semantic_method_id = type_def_id
                .zip(method_name_id)
                .and_then(|(tdef_id, name_id)| self.query().find_static_method(tdef_id, name_id));

            let method_id = semantic_method_id.ok_or_else(|| {
                let method_name_str = interner.resolve(method.name);
                CodegenError::internal_with_context(
                    "static method not found in entity registry",
                    format!("{}::{}", type_name, method_name_str),
                )
            })?;

            // Look up the registered function via its full NameId
            let func_key = self
                .func_registry
                .intern_name_id(self.query().method_full_name(method_id));
            let jit_func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!("{}::{}", type_name, interner.resolve(method.name)),
                )
            })?;

            // Use pre-resolved signature from MethodDef
            let method_def = self.query().get_method(method_id);
            let arena = self.arena();
            let (params, ret, _) =
                arena
                    .unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method compilation: missing function signature")
                    })?;
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
            let resolved_module_id = module_id;

            // Create function builder and compile
            let no_global_inits = FxHashMap::default();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                // Use module interner + module_id when compiling module statics,
                // otherwise AST Symbols from the module interner are resolved against
                // the main program interner (which has different indices).
                let env = if let Some(_mid) = resolved_module_id {
                    compile_env!(self, interner, &no_global_inits, source_file_ptr)
                } else {
                    compile_env!(self, source_file_ptr)
                };
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

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
        let method_name_id = self.method_name_id(method.name)?;

        let semantic_method_id = type_def_id
            .and_then(|tdef_id| self.query().find_method(tdef_id, method_name_id))
            .ok_or_else(|| {
                let method_name_str = self.resolve_symbol(method.name);
                CodegenError::internal_with_context(
                    "implement block method not registered in entity_registry",
                    format!(
                        "{} (type_def_id={:?}, method_name_id={:?})",
                        method_name_str, type_def_id, method_name_id
                    ),
                )
            })?;

        let func_key = if let Some(info) = method_info {
            info.func_key
        } else {
            let method_def = self.query().get_method(semantic_method_id);
            self.func_registry.intern_name_id(method_def.full_name_id)
        };
        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("method", self.func_registry.display(func_key))
        })?;

        let sig =
            self.build_signature_for_method(semantic_method_id, SelfParam::TypedId(self_type_id));
        self.jit.ctx.func.signature = sig;

        // Get the Cranelift type for self (using TypeId)
        let self_cranelift_type =
            type_id_to_cranelift(self_type_id, self.arena(), self.pointer_type);

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Get param TypeIds from the method signature and pair with AST param names.
        // Skip explicit `self` params — they are handled via the separate self_binding.
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.arena();
            let (param_type_ids, _, _) = arena
                .unwrap_function(method_def.signature_id)
                .ok_or_else(|| {
                    CodegenError::internal("method compilation: missing function signature")
                })?;
            method
                .params
                .iter()
                .filter(|p| p.name != self_sym)
                .zip(param_type_ids.iter())
                .map(|(param, &type_id)| {
                    let cranelift_type = type_id_to_cranelift(type_id, arena, self.pointer_type);
                    (param.name, type_id, cranelift_type)
                })
                .collect()
        };

        // Get the method's return type from the pre-resolved signature
        let method_return_type_id = {
            let method_def = self.query().get_method(semantic_method_id);
            let arena = self.arena();
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
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

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

        // Define the function (skip if already defined by an overlapping implement block)
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Collect the body and parameter names for a default method from an interface.
    ///
    /// Searches main program and all module programs for the interface by name,
    /// then finds the method by name. Returns the body, parameter symbols,
    /// the interner that owns those symbols, and the module_id (if from a module).
    ///
    /// Returns None if the interface or method is not found.
    #[allow(clippy::type_complexity)]
    fn collect_interface_method_body(
        &self,
        interface_name_str: &str,
        method_name_str: &str,
    ) -> Option<(
        vole_frontend::FuncBody,
        Vec<Symbol>,
        Rc<Interner>,
        Option<ModuleId>,
    )> {
        // Search main program first
        for decl in &self.analyzed.program.declarations {
            if let vole_frontend::Decl::Interface(iface) = decl {
                let iface_name = self.analyzed.interner.resolve(iface.name);
                if iface_name != interface_name_str {
                    continue;
                }
                for method in &iface.methods {
                    let m_name = self.analyzed.interner.resolve(method.name);
                    if m_name == method_name_str
                        && let Some(body) = &method.body
                    {
                        let param_syms: Vec<Symbol> =
                            method.params.iter().map(|p| p.name).collect();
                        return Some((
                            body.clone(),
                            param_syms,
                            self.analyzed.interner.clone(),
                            None,
                        ));
                    }
                }
            }
        }

        // Search module programs
        for (module_path, (program, interner)) in &self.analyzed.module_programs {
            for decl in &program.declarations {
                if let vole_frontend::Decl::Interface(iface) = decl {
                    let iface_name = interner.resolve(iface.name);
                    if iface_name != interface_name_str {
                        continue;
                    }
                    for method in &iface.methods {
                        let m_name = interner.resolve(method.name);
                        if m_name == method_name_str
                            && let Some(body) = &method.body
                        {
                            let param_syms: Vec<Symbol> =
                                method.params.iter().map(|p| p.name).collect();
                            let module_id = self.query().module_id_if_known(module_path);
                            return Some((body.clone(), param_syms, interner.clone(), module_id));
                        }
                    }
                }
            }
        }

        None
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

        let method_name_id = self.method_name_id(method.name)?;
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        // Look up MethodId from entity_registry for pre-computed signature
        let semantic_method_id = self
            .query()
            .find_method(metadata.type_def_id, method_name_id)
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "class instance method not registered in entity_registry",
                    format!(
                        "{}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    ),
                )
            })?;

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("method", self.func_registry.display(func_key))
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Use TypeId directly for self binding
        let self_type_id = metadata.vole_type;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, method_return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) =
                arena
                    .unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method signature: expected function type")
                    })?;
            (params.to_vec(), Some(ret))
        };

        // Get source file pointer and self symbol before borrowing ctx.func
        let source_file_ptr = self.source_file_ptr();
        let self_sym = self.self_symbol();

        // Build params: Vec<(Symbol, TypeId, Type)>
        // Skip explicit `self` params — they are handled via the separate self_binding.
        let params: Vec<(Symbol, TypeId, types::Type)> = {
            let arena_ref = self.arena();
            method
                .params
                .iter()
                .filter(|p| p.name != self_sym)
                .zip(param_type_ids.iter())
                .map(|(param, &type_id)| {
                    let cranelift_type =
                        type_id_to_cranelift(type_id, arena_ref, self.pointer_type);
                    (param.name, type_id, cranelift_type)
                })
                .collect()
        };

        // Create function builder and compile
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);

            // Create split contexts
            let env = compile_env!(self, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );
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
        self.finalize_function(func_id)?;

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

        let method_name_id = self.method_name_id(method.name)?;
        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "default method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        // Look up MethodId - interface default methods are now registered on implementing types
        let semantic_method_id = self
            .query()
            .find_method(metadata.type_def_id, method_name_id)
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "interface default method not registered on implementing type",
                    format!(
                        "{}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    ),
                )
            })?;

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("default method", self.func_registry.display(func_key))
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) =
                arena
                    .unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method signature: expected function type")
                    })?;
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
            CodegenError::internal_with_context("default method has no body", &*method_name_str)
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
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

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
        self.finalize_function(func_id)?;

        Ok(())
    }

    /// Compile a default method from a module interface, using the module interner.
    ///
    /// This is needed when the default method body uses symbols from a module interner
    /// (e.g., stdlib `Comparable.lt` uses stdlib symbols for `self` and `compare`).
    fn compile_default_method_with_interner(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        metadata: &TypeMetadata,
        interner: &Interner,
        module_id: Option<ModuleId>,
    ) -> CodegenResult<()> {
        let type_name_str = self.query().resolve_symbol(type_name).to_string();
        let method_name_str = interner.resolve(method.name).to_string();

        // Look up method NameId using the module interner (cross-interner safe)
        let method_name_id = method_name_id_with_interner(self.analyzed, interner, method.name)
            .ok_or_else(|| CodegenError::not_found("method name_id", &method_name_str))?;

        let method_info = metadata.method_infos.get(&method_name_id).ok_or_else(|| {
            CodegenError::not_found(
                "default method info",
                format!("{}::{}", type_name_str, method_name_str),
            )
        })?;
        let func_key = method_info.func_key;

        let semantic_method_id = self
            .query()
            .find_method(metadata.type_def_id, method_name_id)
            .ok_or_else(|| {
                CodegenError::internal_with_context(
                    "interface default method not registered on implementing type",
                    format!(
                        "{}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, metadata.type_def_id, method_name_id
                    ),
                )
            })?;

        let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
            CodegenError::not_found("default method", self.func_registry.display(func_key))
        })?;

        // Create method signature using pre-resolved MethodId
        let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
        self.jit.ctx.func.signature = sig;

        // Get param and return types from sema (pre-resolved signature)
        let method_def = self.query().get_method(semantic_method_id);
        let (param_type_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) =
                arena
                    .unwrap_function(method_def.signature_id)
                    .ok_or_else(|| {
                        CodegenError::internal("method signature: expected function type")
                    })?;
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
            CodegenError::internal_with_context("default method has no body", &*method_name_str)
        })?;

        // Use the module interner's "self" symbol so the body's identifier references
        // for `self` (which use the module interner) bind correctly.
        let source_file_ptr = self.source_file_ptr();
        let self_sym = interner
            .lookup("self")
            .ok_or_else(|| CodegenError::internal("'self' not interned in module interner"))?;
        let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

        // Create function builder and compile using the module interner
        let no_global_inits = FxHashMap::default();
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
            let env = compile_env!(self, interner, &no_global_inits, source_file_ptr);
            let mut codegen_ctx = CodegenCtx::new(
                &mut self.jit.module,
                &mut self.func_registry,
                &mut self.pending_monomorphs,
            );

            let config =
                FunctionCompileConfig::method(body, params, self_binding, Some(return_type_id));
            compile_function_inner_with_params(
                builder,
                &mut codegen_ctx,
                &env,
                config,
                module_id,
                None,
            )?;
        }

        // Define the function
        self.finalize_function(func_id)?;

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
        let type_def_id = self.query().try_type_def_id(type_name_id).ok_or_else(|| {
            let type_name_str = self.resolve_symbol(type_name);
            CodegenError::internal_with_context(
                "static method type not registered in entity_registry",
                format!("{} (type_name_id={:?})", type_name_str, type_name_id),
            )
        })?;

        for method in &statics.methods {
            // Only compile methods with bodies
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            // Look up MethodId from entity_registry for pre-computed signature
            let method_name_id = self.method_name_id(method.name)?;
            let semantic_method_id = self
                .query()
                .find_static_method(type_def_id, method_name_id)
                .ok_or_else(|| {
                    let type_name_str = self.resolve_symbol(type_name);
                    let method_name_str = self.resolve_symbol(method.name);
                    CodegenError::internal_with_context(
                        "static method not registered in entity_registry",
                        format!(
                            "{}::{} (type_def_id={:?}, method_name_id={:?})",
                            type_name_str, method_name_str, type_def_id, method_name_id
                        ),
                    )
                })?;

            // Function key from EntityRegistry full_name_id
            let method_def = self.analyzed.query().get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!(
                        "{}::{}",
                        self.query().resolve_symbol(type_name),
                        self.query().resolve_symbol(method.name),
                    ),
                )
            })?;

            // Create signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema (pre-resolved signature)
            let (param_type_ids, return_type_id) = {
                let arena = self.arena();
                let (params, ret, _) =
                    arena
                        .unwrap_function(method_def.signature_id)
                        .ok_or_else(|| {
                            CodegenError::internal(
                                "static method signature: expected function type",
                            )
                        })?;
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
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

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
        // Generic types are compiled via monomorphized instances.
        if type_decl.has_type_params() {
            return Ok(());
        }

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
                let arena = self.arena();
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

        let module_info = ModuleCompileInfo {
            interner: module_interner,
            module_id,
            global_inits: module_global_inits,
        };

        // Compile instance methods
        self.compile_module_type_instance_methods(
            type_decl,
            &metadata,
            &module_info,
            type_name_str,
        )?;

        // Compile static methods
        if let Some(statics) = type_decl.statics() {
            self.compile_module_type_static_methods(
                statics,
                &metadata,
                &module_info,
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
        module_info: &ModuleCompileInfo<'_>,
        type_name_str: &str,
    ) -> CodegenResult<()> {
        let type_kind = type_decl.type_kind();

        for method in type_decl.methods() {
            let method_name_str = module_info.interner.resolve(method.name);

            // Look up MethodId from sema to get pre-computed signature
            let method_name_id =
                method_name_id_with_interner(self.analyzed, module_info.interner, method.name)
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "module method name not found in name_table",
                            format!("{}::{}::{}", type_kind, type_name_str, method_name_str),
                        )
                    })?;

            let semantic_method_id = self
                .query()
                .find_method(metadata.type_def_id, method_name_id)
                .ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "module method not registered in entity_registry",
                        format!(
                            "{}::{}::{} (type_def_id={:?}, method_name_id={:?})",
                            type_kind,
                            type_name_str,
                            method_name_str,
                            metadata.type_def_id,
                            method_name_id
                        ),
                    )
                })?;

            let method_def = self.query().get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found("method", format!("{}::{}", type_name_str, method_name_str))
            })?;

            // Create method signature using pre-resolved MethodId
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.query().get_method(semantic_method_id);
            let (param_type_ids, return_type_id) = {
                let arena = self.arena();
                let (params, ret, _) =
                    arena
                        .unwrap_function(method_def.signature_id)
                        .ok_or_else(|| {
                            CodegenError::internal("method signature: expected function type")
                        })?;
                (params.to_vec(), Some(ret))
            };

            let self_sym = module_info
                .interner
                .lookup("self")
                .ok_or_else(|| CodegenError::internal("method compilation: 'self' not interned"))?;
            // Skip explicit `self` params — they are handled via the separate self_binding.
            let param_types = self.type_ids_to_cranelift(&param_type_ids);
            let params: Vec<_> = method
                .params
                .iter()
                .filter(|p| p.name != self_sym)
                .zip(param_type_ids.iter())
                .zip(param_types.iter())
                .map(|((p, &type_id), &cranelift_type)| (p.name, type_id, cranelift_type))
                .collect();
            let self_binding = (self_sym, metadata.vole_type, self.pointer_type);

            // Create function builder and compile
            let source_file_ptr = self.source_file_ptr();
            let mut builder_ctx = FunctionBuilderContext::new();
            {
                let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                let env = compile_env!(
                    self,
                    module_info.interner,
                    module_info.global_inits,
                    source_file_ptr
                );
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

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
                    Some(module_info.module_id),
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
    fn compile_module_type_static_methods(
        &mut self,
        statics: &StaticsBlock,
        metadata: &TypeMetadata,
        module_info: &ModuleCompileInfo<'_>,
        type_name_str: &str,
        type_kind: &str,
    ) -> CodegenResult<()> {
        for method in &statics.methods {
            let body = match &method.body {
                Some(body) => body,
                None => continue,
            };

            let method_name_str = module_info.interner.resolve(method.name);

            // Look up MethodId from sema to get pre-computed signature
            let method_name_id =
                method_name_id_with_interner(self.analyzed, module_info.interner, method.name)
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "module static method name not found in name_table",
                            format!("{}::{}::{}", type_kind, type_name_str, method_name_str),
                        )
                    })?;

            let semantic_method_id = self
                .query()
                .find_static_method(metadata.type_def_id, method_name_id)
                .ok_or_else(|| {
                    CodegenError::internal_with_context(
                        "module static method not registered in entity_registry",
                        format!(
                            "{}::{}::{} (type_def_id={:?}, method_name_id={:?})",
                            type_kind,
                            type_name_str,
                            method_name_str,
                            metadata.type_def_id,
                            method_name_id
                        ),
                    )
                })?;

            let method_def = self.query().get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let func_id = self.func_registry.func_id(func_key).ok_or_else(|| {
                CodegenError::not_found(
                    "static method",
                    format!("{}::{}", type_name_str, method_name_str),
                )
            })?;

            // Create signature using pre-resolved MethodId (no self parameter for static)
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
            self.jit.ctx.func.signature = sig;

            // Get param and return types from sema
            let method_def = self.query().get_method(semantic_method_id);
            let (param_type_ids, return_type_id) = {
                let arena = self.arena();
                let (params, ret, _) =
                    arena
                        .unwrap_function(method_def.signature_id)
                        .ok_or_else(|| {
                            CodegenError::internal(
                                "static method signature: expected function type",
                            )
                        })?;
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
                    module_info.interner,
                    module_info.global_inits,
                    source_file_ptr
                );
                let mut codegen_ctx = CodegenCtx::new(
                    &mut self.jit.module,
                    &mut self.func_registry,
                    &mut self.pending_monomorphs,
                );

                let config = FunctionCompileConfig::top_level(body, params, return_type_id);
                compile_function_inner_with_params(
                    builder,
                    &mut codegen_ctx,
                    &env,
                    config,
                    Some(module_info.module_id),
                    None,
                )?;
            }

            // Define the function
            self.finalize_function(func_id)?;
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

    /// Declare and compile array Iterable default methods for each concrete element type.
    ///
    /// Called after `declare_module_types_and_functions` so all types are registered.
    ///
    /// For each concrete RuntimeIterator element type (e.g. i64, string) found in the arena,
    /// and for each non-external Iterable default method registered on the array TypeDef,
    /// this function:
    ///   1. Builds a concrete substitution `{T_name_id -> elem_type}`
    ///   2. Declares a JIT function with a mangled name (e.g. "__array_iterable_4_count")
    ///   3. Registers the func_key in `state.array_iterable_func_keys[(method_name_id, elem_type)]`
    ///   4. Compiles the Iterable default method body with the concrete substitution
    pub(super) fn compile_array_iterable_default_methods(&mut self) -> CodegenResult<()> {
        // Get array TypeDefId and Iterable TypeDefId
        let array_tdef_id = {
            let array_name_id = match self.registry().array_name_id() {
                Some(id) => id,
                None => return Ok(()), // array not registered, nothing to do
            };
            match self.query().try_type_def_id(array_name_id) {
                Some(id) => id,
                None => return Ok(()),
            }
        };

        // Find Iterable TypeDefId (the interface array implements)
        let iterable_tdef_id = {
            let interfaces = self.query().implemented_interfaces(array_tdef_id);
            if interfaces.is_empty() {
                return Ok(());
            }
            interfaces[0] // array implements exactly one interface: Iterable<T>
        };

        // Find T's NameId from the abstract substitution map {T_name_id -> TypeParam(T)}
        let t_name_id: NameId = {
            let subs = self
                .query()
                .interface_impl_type_param_subs(array_tdef_id, iterable_tdef_id);
            if subs.is_empty() {
                return Ok(());
            }
            // For `extend [T] with Iterable<T>`, T's value is TypeParam(T_name_id)
            // Get the first (only) T's NameId — the key in the subs map IS T's NameId
            match subs.into_keys().next() {
                Some(name_id) => name_id,
                None => return Ok(()),
            }
        };

        // Get the interface name string for collect_interface_method_body
        let iface_name_str: String = {
            let iface_name_id = self.query().get_type(iterable_tdef_id).name_id;
            self.analyzed
                .name_table()
                .last_segment_str(iface_name_id)
                .unwrap_or("Iterable".to_string())
        };

        // Collect non-external Iterable default methods registered on the array type
        // We skip external methods (provided by runtime, not compiled from Vole source)
        let default_methods: Vec<(MethodId, NameId, String)> = {
            let query = self.query();
            let mut results = Vec::new();
            for iface_method_id in query.type_methods(iterable_tdef_id) {
                let method_def = query.get_method(iface_method_id);
                if !method_def.has_default {
                    continue;
                }
                if method_def.external_binding.is_some() {
                    continue; // External methods are already handled by runtime
                }
                let method_name_str = query
                    .last_segment(method_def.name_id)
                    .unwrap_or_default()
                    .to_string();
                // Find this method as registered on the array implementing type
                if let Some(array_method_id) = query.find_method(array_tdef_id, method_def.name_id)
                {
                    results.push((array_method_id, method_def.name_id, method_name_str));
                }
            }
            results
        };

        if default_methods.is_empty() {
            return Ok(());
        }

        // Get all concrete element types for which we need to compile array Iterable methods
        let elem_types: Vec<TypeId> = self.arena().all_concrete_runtime_iterator_elem_types();

        for elem_type in elem_types {
            // Get the concrete array TypeId for this element type
            let self_type_id = match self.arena().lookup_array(elem_type) {
                Some(tid) => tid,
                None => continue, // No array of this elem type in arena, skip
            };

            // Skip element types whose iterable methods were already imported from
            // the module cache. Check the first default method as a sentinel — all
            // methods for an element type are imported/compiled as a batch.
            if let Some((_, first_name_id, _)) = default_methods.first()
                && self
                    .state
                    .array_iterable_func_keys
                    .contains_key(&(*first_name_id, self_type_id))
            {
                continue;
            }

            // Build concrete substitution: T_name_id -> elem_type
            let mut concrete_subs = FxHashMap::default();
            concrete_subs.insert(t_name_id, elem_type);

            for (semantic_method_id, method_name_id, method_name_str) in &default_methods {
                // Build a unique mangled name: "__array_iterable_{elem_type_idx}_{method_name}"
                // elem_type.index() is a stable u32 index that uniquely identifies the type.
                let mangled_name =
                    format!("__array_iterable_{}_{}", elem_type.index(), method_name_str);

                // Build the concrete signature (substituting Self -> self_type_id, T -> elem_type)
                // If any return type substitution fails (e.g. T? not registered in arena for
                // this elem_type), skip this method — it can't be compiled without a concrete
                // return type. Params fall back to abstract type on failure (safe for ptr-size).
                let maybe_type_ids: Option<(Vec<TypeId>, TypeId)> = {
                    let method_def = self.query().get_method(*semantic_method_id);
                    let arena = self.arena();
                    arena
                        .unwrap_function(method_def.signature_id)
                        .and_then(|(params, ret, _)| {
                            let subst_params: Vec<TypeId> = params
                                .iter()
                                .map(|&p| {
                                    if arena.is_self_type(p) {
                                        self_type_id
                                    } else {
                                        arena.lookup_substitute(p, &concrete_subs).unwrap_or(p)
                                    }
                                })
                                .collect();
                            let subst_ret = if arena.is_self_type(ret) {
                                Some(self_type_id)
                            } else {
                                arena.lookup_substitute(ret, &concrete_subs)
                            };
                            subst_ret.map(|ret| (subst_params, ret))
                        })
                };
                let (param_type_ids, return_type_id) = match maybe_type_ids {
                    Some(x) => x,
                    None => continue, // return type unresolvable for this elem_type; skip
                };

                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    SelfParam::TypedId(self_type_id),
                );

                // Declare JIT function with the mangled name and register in func_registry
                let func_id = self.jit.declare_function(&mangled_name, &sig);
                let func_key = self.func_registry.intern_raw(mangled_name);
                self.func_registry.set_func_id(func_key, func_id);

                // Register in array_iterable_func_keys for call-site lookup.
                // Key is (method_name_id, self_type_id) so arrays and primitives (range)
                // can each have their own compiled function for the same method.
                self.state
                    .array_iterable_func_keys
                    .insert((*method_name_id, self_type_id), func_key);

                // Find the interface AST method body and compile it
                let iface_info =
                    self.collect_interface_method_body(&iface_name_str, method_name_str);
                let Some((body, method_params, iface_interner, iface_module_id)) = iface_info
                else {
                    continue;
                };

                // Set the function signature for compilation
                self.jit.ctx.func.signature = sig;

                let param_types = self.type_ids_to_cranelift(&param_type_ids);
                let params: Vec<_> = method_params
                    .iter()
                    .zip(param_type_ids.iter())
                    .zip(param_types.iter())
                    .map(|((p, &type_id), &cranelift_type)| (*p, type_id, cranelift_type))
                    .collect();

                let self_sym = iface_interner
                    .lookup("self")
                    .unwrap_or_else(|| self.self_symbol());

                let source_file_ptr = self.source_file_ptr();
                let self_cranelift_type =
                    type_id_to_cranelift(self_type_id, self.arena(), self.pointer_type);
                let self_binding = (self_sym, self_type_id, self_cranelift_type);

                let no_global_inits = FxHashMap::default();
                let mut builder_ctx = FunctionBuilderContext::new();
                {
                    let builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut builder_ctx);
                    let env =
                        compile_env!(self, &iface_interner, &no_global_inits, source_file_ptr);
                    let mut codegen_ctx = CodegenCtx::new(
                        &mut self.jit.module,
                        &mut self.func_registry,
                        &mut self.pending_monomorphs,
                    );
                    let config = FunctionCompileConfig::method(
                        &body,
                        params,
                        self_binding,
                        Some(return_type_id),
                    )
                    .with_iterable_default_body();
                    compile_function_inner_with_params(
                        builder,
                        &mut codegen_ctx,
                        &env,
                        config,
                        iface_module_id,
                        Some(&concrete_subs),
                    )?;
                }
                self.finalize_function(func_id)?;
            }
        }

        Ok(())
    }

    /// Import (not compile) array Iterable default methods from a pre-compiled module cache.
    ///
    /// Called in the module cache path (when `can_use_cache == true`) instead of
    /// `compile_array_iterable_default_methods`. The functions were already compiled
    /// and stored in `CompiledModules`. This function:
    ///   1. Rebuilds the same mangled names as `compile_array_iterable_default_methods`
    ///   2. Declares them with Import linkage in the new JIT context
    ///   3. Registers them in `state.array_iterable_func_keys[(method_name_id, self_type_id)]`
    ///
    /// Must be called after `import_module_functions` sets up type metadata.
    pub(super) fn import_array_iterable_default_methods(&mut self) -> CodegenResult<()> {
        // Get array TypeDefId and Iterable TypeDefId
        let array_tdef_id = {
            let array_name_id = match self.registry().array_name_id() {
                Some(id) => id,
                None => return Ok(()),
            };
            match self.query().try_type_def_id(array_name_id) {
                Some(id) => id,
                None => return Ok(()),
            }
        };

        let iterable_tdef_id = {
            let interfaces = self.query().implemented_interfaces(array_tdef_id);
            if interfaces.is_empty() {
                return Ok(());
            }
            interfaces[0]
        };

        let t_name_id: NameId = {
            let subs = self
                .query()
                .interface_impl_type_param_subs(array_tdef_id, iterable_tdef_id);
            if subs.is_empty() {
                return Ok(());
            }
            match subs.into_keys().next() {
                Some(name_id) => name_id,
                None => return Ok(()),
            }
        };

        let default_methods: Vec<(MethodId, NameId, String)> = {
            let query = self.query();
            let mut results = Vec::new();
            for iface_method_id in query.type_methods(iterable_tdef_id) {
                let method_def = query.get_method(iface_method_id);
                if !method_def.has_default || method_def.external_binding.is_some() {
                    continue;
                }
                let method_name_str = query
                    .last_segment(method_def.name_id)
                    .unwrap_or_default()
                    .to_string();
                if let Some(array_method_id) = query.find_method(array_tdef_id, method_def.name_id)
                {
                    results.push((array_method_id, method_def.name_id, method_name_str));
                }
            }
            results
        };

        if default_methods.is_empty() {
            return Ok(());
        }

        let elem_types: Vec<TypeId> = self.arena().all_concrete_runtime_iterator_elem_types();

        for elem_type in elem_types {
            let self_type_id = match self.arena().lookup_array(elem_type) {
                Some(tid) => tid,
                None => continue,
            };

            let mut concrete_subs = FxHashMap::default();
            concrete_subs.insert(t_name_id, elem_type);

            for (semantic_method_id, method_name_id, method_name_str) in &default_methods {
                let mangled_name =
                    format!("__array_iterable_{}_{}", elem_type.index(), method_name_str);

                // Build the concrete signature (same as compile path)
                let maybe_type_ids: Option<(Vec<TypeId>, TypeId)> = {
                    let method_def = self.query().get_method(*semantic_method_id);
                    let arena = self.arena();
                    arena
                        .unwrap_function(method_def.signature_id)
                        .and_then(|(params, ret, _)| {
                            let subst_params: Vec<TypeId> = params
                                .iter()
                                .map(|&p| {
                                    if arena.is_self_type(p) {
                                        self_type_id
                                    } else {
                                        arena.lookup_substitute(p, &concrete_subs).unwrap_or(p)
                                    }
                                })
                                .collect();
                            let subst_ret = if arena.is_self_type(ret) {
                                Some(self_type_id)
                            } else {
                                arena.lookup_substitute(ret, &concrete_subs)
                            };
                            subst_ret.map(|ret| (subst_params, ret))
                        })
                };
                let (param_type_ids, return_type_id) = match maybe_type_ids {
                    Some(x) => x,
                    None => continue,
                };

                let sig = self.build_signature_from_type_ids(
                    &param_type_ids,
                    Some(return_type_id),
                    SelfParam::TypedId(self_type_id),
                );

                // Only import functions that exist in the pre-compiled module cache.
                // Element types from non-module code (e.g. test files) won't have
                // compiled iterable methods in the cache.
                if !self.jit.has_precompiled_symbol(&mangled_name) {
                    continue;
                }
                let func_id = self.jit.import_function(&mangled_name, &sig);
                let func_key = self.func_registry.intern_raw(mangled_name);
                self.func_registry.set_func_id(func_key, func_id);

                self.state
                    .array_iterable_func_keys
                    .insert((*method_name_id, self_type_id), func_key);
            }
        }

        Ok(())
    }
}
