use rustc_hash::FxHashMap;

use super::Compiler;

use vole_frontend::ast::{InterfaceMethod, StaticsBlock};
use vole_frontend::{Decl, FuncDecl, Program, TypeExprKind};
use vole_identity::{ModuleId, NameId};

/// A lightweight view into the methods and statics of a generic type declaration
/// (class or struct). Used during monomorphization to find method ASTs.
pub(super) struct GenericTypeMethodsAst<'a> {
    pub(super) methods: &'a [FuncDecl],
    pub(super) statics: Option<&'a StaticsBlock>,
}

impl Compiler<'_> {
    /// Build maps of generic type NameIds to their method/statics ASTs.
    /// Covers both classes and structs with type parameters.
    /// Used by both class method and static method monomorphization.
    /// Recursively walks into tests blocks to find generic types declared there.
    pub(super) fn build_generic_type_asts<'a>(
        &self,
        program: &'a Program,
    ) -> FxHashMap<NameId, GenericTypeMethodsAst<'a>> {
        let mut result = FxHashMap::default();
        let program_module = self.program_module();
        self.collect_generic_type_asts(&program.declarations, program_module, &mut result);
        result
    }

    /// Recursively collect generic type ASTs from declarations, including tests blocks.
    fn collect_generic_type_asts<'a>(
        &self,
        decls: &'a [Decl],
        module_id: ModuleId,
        result: &mut FxHashMap<NameId, GenericTypeMethodsAst<'a>>,
    ) {
        for decl in decls {
            match decl {
                Decl::Class(class) if !class.type_params.is_empty() => {
                    let query = self.query();
                    if let Some(name_id) = query.try_name_id(module_id, &[class.name]) {
                        result.insert(
                            name_id,
                            GenericTypeMethodsAst {
                                methods: &class.methods,
                                statics: class.statics.as_ref(),
                            },
                        );
                    }
                }
                Decl::Struct(s) if !s.type_params.is_empty() => {
                    let query = self.query();
                    if let Some(name_id) = query.try_name_id(module_id, &[s.name]) {
                        result.insert(
                            name_id,
                            GenericTypeMethodsAst {
                                methods: &s.methods,
                                statics: s.statics.as_ref(),
                            },
                        );
                    }
                }
                Decl::Tests(tests_decl) => {
                    // Use the virtual module for tests-block-scoped types
                    let vm_id = self
                        .query()
                        .tests_virtual_module(tests_decl.span)
                        .unwrap_or(module_id);
                    self.collect_generic_type_asts(&tests_decl.decls, vm_id, result);
                }
                _ => {}
            }
        }
    }

    /// Find a method in implement blocks targeting a generic class.
    /// Searches through all declarations (including tests blocks) for implement blocks
    /// whose target type matches the given class NameId and returns the matching method.
    pub(super) fn find_implement_block_method<'a>(
        &self,
        decls: &'a [Decl],
        class_name_id: NameId,
        method_name_str: &str,
        module_id: ModuleId,
    ) -> Option<&'a FuncDecl> {
        for decl in decls {
            match decl {
                Decl::Implement(impl_block) => {
                    // Get the base type name from the target type
                    let target_sym = match &impl_block.target_type.kind {
                        TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                            Some(*sym)
                        }
                        _ => None,
                    };
                    if let Some(sym) = target_sym {
                        let query = self.query();
                        if let Some(name_id) = query.try_name_id(module_id, &[sym])
                            && name_id == class_name_id
                        {
                            // Found matching implement block - search its methods
                            if let Some(method) = impl_block
                                .methods
                                .iter()
                                .find(|m| self.query().resolve_symbol(m.name) == method_name_str)
                            {
                                return Some(method);
                            }
                        }
                    }
                }
                Decl::Tests(tests_decl) => {
                    let vm_id = self
                        .query()
                        .tests_virtual_module(tests_decl.span)
                        .unwrap_or(module_id);
                    // Search both the parent module and virtual module for implement blocks
                    if let Some(method) = self.find_implement_block_method(
                        &tests_decl.decls,
                        class_name_id,
                        method_name_str,
                        vm_id,
                    ) {
                        return Some(method);
                    }
                    // Also try with the parent module_id (implement blocks may target
                    // types from the parent module)
                    if vm_id != module_id
                        && let Some(method) = self.find_implement_block_method(
                            &tests_decl.decls,
                            class_name_id,
                            method_name_str,
                            module_id,
                        )
                    {
                        return Some(method);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Find an instance method in a generic class or struct defined in a loaded module.
    /// Searches module_programs for the type's module and looks for the method in
    /// the generic type declaration found there.
    pub(super) fn find_class_method_in_modules(
        &self,
        class_name_id: NameId,
        method_name_str: &str,
    ) -> Option<&FuncDecl> {
        // Determine which module this class belongs to
        let module_id = self.analyzed.name_table().module_of(class_name_id);
        let module_path = self
            .analyzed
            .name_table()
            .module_path(module_id)
            .to_string();

        // Look up the module program and its interner
        let (module_program, module_interner) = self.analyzed.module_programs.get(&module_path)?;

        // Search for the generic class or struct in this module's declarations
        for decl in &module_program.declarations {
            match decl {
                Decl::Class(class) if !class.type_params.is_empty() => {
                    let query = self.query();
                    if let Some(name_id) =
                        query.try_name_id_with_interner(module_id, &[class.name], module_interner)
                        && name_id == class_name_id
                    {
                        return class
                            .methods
                            .iter()
                            .find(|m| module_interner.resolve(m.name) == method_name_str);
                    }
                }
                Decl::Struct(s) if !s.type_params.is_empty() => {
                    let query = self.query();
                    if let Some(name_id) =
                        query.try_name_id_with_interner(module_id, &[s.name], module_interner)
                        && name_id == class_name_id
                    {
                        return s
                            .methods
                            .iter()
                            .find(|m| module_interner.resolve(m.name) == method_name_str);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Find a static method in a generic class or struct defined in a loaded module.
    /// Searches module_programs for the type's module and looks for the static method
    /// in the generic type declaration found there.
    pub(super) fn find_static_method_in_modules(
        &self,
        class_name_id: NameId,
        method_name_str: &str,
    ) -> Option<&InterfaceMethod> {
        let module_id = self.analyzed.name_table().module_of(class_name_id);
        let module_path = self
            .analyzed
            .name_table()
            .module_path(module_id)
            .to_string();

        let (module_program, module_interner) = self.analyzed.module_programs.get(&module_path)?;

        for decl in &module_program.declarations {
            match decl {
                Decl::Class(class) if !class.type_params.is_empty() => {
                    if let Some(name_id) = self.query().try_name_id_with_interner(
                        module_id,
                        &[class.name],
                        module_interner,
                    ) && name_id == class_name_id
                        && let Some(ref statics) = class.statics
                    {
                        return statics
                            .methods
                            .iter()
                            .find(|m| module_interner.resolve(m.name) == method_name_str);
                    }
                }
                Decl::Struct(s) if !s.type_params.is_empty() => {
                    if let Some(name_id) = self.query().try_name_id_with_interner(
                        module_id,
                        &[s.name],
                        module_interner,
                    ) && name_id == class_name_id
                        && let Some(ref statics) = s.statics
                    {
                        return statics
                            .methods
                            .iter()
                            .find(|m| module_interner.resolve(m.name) == method_name_str);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Recursively collect generic function ASTs from declarations, including tests blocks.
    /// Generic functions inside tests blocks are registered under the program module
    /// (not the virtual module), but their ASTs are only reachable by walking into tests blocks.
    pub(super) fn collect_generic_func_asts<'a>(
        &self,
        decls: &'a [Decl],
        module_id: ModuleId,
        result: &mut FxHashMap<NameId, &'a FuncDecl>,
    ) {
        for decl in decls {
            match decl {
                Decl::Function(func) => {
                    let query = self.query();
                    let name_id = query.function_name_id(module_id, func.name);

                    // Check if function has explicit type params OR implicit generic_info
                    let has_explicit_type_params = !func.type_params.is_empty();
                    let has_implicit_generic_info = self
                        .analyzed
                        .entity_registry()
                        .function_by_name(name_id)
                        .map(|func_id| {
                            self.analyzed
                                .entity_registry()
                                .get_function(func_id)
                                .generic_info
                                .is_some()
                        })
                        .unwrap_or(false);

                    if has_explicit_type_params || has_implicit_generic_info {
                        result.insert(name_id, func);
                    }
                }
                Decl::Tests(tests_decl) => {
                    // Functions in tests blocks are registered under the program module
                    // (not the virtual module), so keep using the same module_id.
                    self.collect_generic_func_asts(&tests_decl.decls, module_id, result);
                }
                _ => {}
            }
        }
    }
}
