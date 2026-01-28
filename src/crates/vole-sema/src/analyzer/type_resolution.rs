use super::*;

use crate::resolve::{TypeResolutionContext, resolve_type_to_id};
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Resolve a type expression to TypeId.
    pub(crate) fn resolve_type_id(&mut self, ty: &TypeExpr, interner: &Interner) -> ArenaTypeId {
        self.resolve_type_id_with_self(ty, interner, None)
    }

    /// Resolve a type expression to TypeId with optional Self type for method signatures
    pub(crate) fn resolve_type_id_with_self(
        &mut self,
        ty: &TypeExpr,
        interner: &Interner,
        self_type_id: Option<ArenaTypeId>,
    ) -> ArenaTypeId {
        // Handle QualifiedPath specially - we need scope access for module bindings.
        // This is not in TypeResolutionContext because it requires scope access.
        if let TypeExpr::QualifiedPath { segments, args } = ty {
            return self.resolve_qualified_type_id(segments, args, interner, self_type_id);
        }

        // Handle container types that might have QualifiedPath elements.
        // We need to handle these here so the recursive calls go through this method
        // rather than resolve_type_to_id (which can't resolve QualifiedPath).
        match ty {
            TypeExpr::Array(elem) => {
                let elem_id = self.resolve_type_id_with_self(elem, interner, self_type_id);
                return self.type_arena_mut().array(elem_id);
            }
            TypeExpr::Optional(inner) => {
                let inner_id = self.resolve_type_id_with_self(inner, interner, self_type_id);
                return self.type_arena_mut().optional(inner_id);
            }
            TypeExpr::FixedArray { element, size } => {
                let elem_id = self.resolve_type_id_with_self(element, interner, self_type_id);
                return self.type_arena_mut().fixed_array(elem_id, *size);
            }
            TypeExpr::Tuple(elements) => {
                let elem_ids: crate::type_arena::TypeIdVec = elements
                    .iter()
                    .map(|e| self.resolve_type_id_with_self(e, interner, self_type_id))
                    .collect();
                return self.type_arena_mut().tuple(elem_ids);
            }
            TypeExpr::Union(variants) => {
                let variant_ids: crate::type_arena::TypeIdVec = variants
                    .iter()
                    .map(|t| self.resolve_type_id_with_self(t, interner, self_type_id))
                    .collect();
                return self.type_arena_mut().union(variant_ids);
            }
            TypeExpr::Function {
                params,
                return_type,
            } => {
                let param_ids: crate::type_arena::TypeIdVec = params
                    .iter()
                    .map(|p| self.resolve_type_id_with_self(p, interner, self_type_id))
                    .collect();
                let ret_id = self.resolve_type_id_with_self(return_type, interner, self_type_id);
                return self.type_arena_mut().function(param_ids, ret_id, false);
            }
            TypeExpr::Fallible {
                success_type,
                error_type,
            } => {
                let success_id =
                    self.resolve_type_id_with_self(success_type, interner, self_type_id);
                let error_id = self.resolve_type_id_with_self(error_type, interner, self_type_id);
                return self.type_arena_mut().fallible(success_id, error_id);
            }
            // All other types can fall through to resolve_type_to_id
            _ => {}
        }

        let module_id = self.current_module;
        let mut ctx = TypeResolutionContext {
            db: &self.ctx.db,
            interner,
            module_id,
            type_params: self.type_param_stack.current(),
            self_type: self_type_id,
        };
        resolve_type_to_id(ty, &mut ctx)
    }

    /// Resolve a module-qualified type path like `time.Duration` or `http.Response<T>`.
    ///
    /// This handles the QualifiedPath variant of TypeExpr which allows types to be
    /// referenced via their module binding: `let time = import "std:time"; let d: time.Duration`
    fn resolve_qualified_type_id(
        &mut self,
        segments: &[Symbol],
        args: &[TypeExpr],
        interner: &Interner,
        self_type_id: Option<ArenaTypeId>,
    ) -> ArenaTypeId {
        // Must have at least two segments: module.Type
        if segments.len() < 2 {
            tracing::debug!("qualified_type: too few segments");
            return self.ty_invalid_traced_id("qualified_path_too_short");
        }

        // Look up first segment in scope to find the module binding
        let module_sym = segments[0];
        let module_name = interner.resolve(module_sym);
        tracing::debug!(module_name, "qualified_type: looking up module in scope");

        let module_var = self.scope.get(module_sym);

        let Some(var) = module_var else {
            // First segment not found in scope - this will be caught as undefined variable
            tracing::debug!(module_name, "qualified_type: module not found in scope");
            return self.ty_invalid_traced_id("qualified_path_module_not_found");
        };

        let module_type_id = var.ty;
        tracing::debug!(?module_type_id, "qualified_type: found module binding");

        // Check if the variable is a module type
        let module_info = self.type_arena().unwrap_module(module_type_id).cloned();
        let Some(module_info) = module_info else {
            // Not a module type - emit appropriate error
            let found_type = self.type_display_id(module_type_id);
            tracing::debug!(module_name, found_type, "qualified_type: not a module type");
            // We don't have the span here, but the caller will handle the invalid type
            // For better errors, we would need to pass spans through
            return self.ty_invalid_traced_id(&format!(
                "expected_module:{}:found:{}",
                module_name, found_type
            ));
        };

        // Now look up the type name in the module's exports
        let type_sym = segments[1];
        let type_name = interner.resolve(type_sym);
        tracing::debug!(type_name, ?module_info.module_id, "qualified_type: looking up type in module exports");

        // Find the export by comparing names
        let export_type_id = self
            .module_name_id(module_info.module_id, type_name)
            .and_then(|name_id| {
                tracing::debug!(?name_id, "qualified_type: got name_id for type");
                module_info
                    .exports
                    .iter()
                    .find(|(n, _)| *n == name_id)
                    .map(|&(_, type_id)| type_id)
            });

        let Some(base_type_id) = export_type_id else {
            // Export not found in module
            let module_path = self
                .name_table()
                .module_path(module_info.module_id)
                .to_string();
            tracing::debug!(
                module_path,
                type_name,
                "qualified_type: type not found in exports"
            );
            return self
                .ty_invalid_traced_id(&format!("module_no_export:{}:{}", module_path, type_name));
        };

        tracing::debug!(?base_type_id, "qualified_type: resolved type successfully");

        // If there are more than 2 segments, we don't support nested module paths yet
        if segments.len() > 2 {
            return self.ty_invalid_traced_id("nested_module_paths_not_supported");
        }

        // If there are generic type arguments, apply them
        if !args.is_empty() {
            // Resolve the type arguments
            let type_args: crate::type_arena::TypeIdVec = args
                .iter()
                .map(|arg| self.resolve_type_id_with_self(arg, interner, self_type_id))
                .collect();

            // Get the base type and apply type arguments
            use crate::type_arena::NominalKind;
            let arena = self.type_arena();
            if let Some((type_def_id, _, kind)) = arena.unwrap_nominal(base_type_id) {
                return match kind {
                    NominalKind::Record => self.type_arena_mut().record(type_def_id, type_args),
                    NominalKind::Class => self.type_arena_mut().class(type_def_id, type_args),
                    NominalKind::Interface => {
                        self.type_arena_mut().interface(type_def_id, type_args)
                    }
                    NominalKind::Error => self.type_arena_mut().error_type(type_def_id),
                };
            }
            // For other types, just return the base type (args might be ignored)
        }

        base_type_id
    }

    pub(super) fn analyze_error_decl(&mut self, decl: &ErrorDecl, interner: &Interner) {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[decl.name], interner);

        // Register in EntityRegistry first to get TypeDefId
        let entity_type_id = self.entity_registry_mut().register_type(
            name_id,
            TypeDefKind::ErrorType,
            self.current_module,
        );

        let error_info = ErrorTypeInfo {
            type_def_id: entity_type_id,
        };

        // Set error info for lookup
        self.entity_registry_mut()
            .set_error_info(entity_type_id, error_info);

        // Register fields in EntityRegistry - resolve types directly to TypeId
        let builtin_module = self.name_table_mut().builtin_module();
        let type_name_str = interner.resolve(decl.name);
        for (i, field) in decl.fields.iter().enumerate() {
            let field_name_str = interner.resolve(field.name);
            let field_name_id = self
                .name_table_mut()
                .intern_raw(builtin_module, &[field_name_str]);
            let full_field_name_id = self
                .name_table_mut()
                .intern_raw(self.current_module, &[type_name_str, field_name_str]);

            // Resolve field type directly to TypeId
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext {
                db: &self.ctx.db,
                interner,
                module_id,
                type_params: None,
                self_type: None,
            };
            let field_type_id = resolve_type_to_id(&field.ty, &mut ctx);

            self.entity_registry_mut().register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                field_type_id,
                i,
            );
        }
    }
}
