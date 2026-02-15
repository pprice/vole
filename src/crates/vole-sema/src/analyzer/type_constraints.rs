// Type constraint checking and related utilities.

use super::*;

/// Trait for items that can have default values (parameters, fields).
/// Used for unified validation of default value ordering.
pub trait Defaultable {
    fn name(&self) -> Symbol;
    fn has_default(&self) -> bool;
    fn span(&self) -> Span;
}

impl Defaultable for Param {
    fn name(&self) -> Symbol {
        self.name
    }
    fn has_default(&self) -> bool {
        self.default_value.is_some()
    }
    fn span(&self) -> Span {
        self.span
    }
}

impl Defaultable for FieldDef {
    fn name(&self) -> Symbol {
        self.name
    }
    fn has_default(&self) -> bool {
        self.default_value.is_some()
    }
    fn span(&self) -> Span {
        self.span
    }
}

impl Defaultable for LambdaParam {
    fn name(&self) -> Symbol {
        self.name
    }
    fn has_default(&self) -> bool {
        self.default_value.is_some()
    }
    fn span(&self) -> Span {
        self.span
    }
}

/// Unified validation for default value ordering.
/// Returns (required_count, has_default_vec) where:
/// - required_count: number of items without defaults
/// - has_default_vec: whether each item has a default
///
/// The error_fn callback is called for each item that violates ordering rules
/// (a non-defaulted item appearing after a defaulted item).
pub fn validate_defaults<T: Defaultable, F>(
    items: &[T],
    interner: &Interner,
    mut error_fn: F,
) -> (usize, Vec<bool>)
where
    F: FnMut(String, Span),
{
    let mut seen_default = false;
    let mut required_count = 0;
    let mut has_default_vec = Vec::with_capacity(items.len());

    for item in items {
        let has_default = item.has_default();
        has_default_vec.push(has_default);

        if has_default {
            seen_default = true;
        } else if seen_default {
            // Non-default item after a default item - report error
            let name = interner.resolve(item.name()).to_string();
            error_fn(name, item.span());
        } else {
            required_count += 1;
        }
    }

    (required_count, has_default_vec)
}

/// Check if a type param's constraint (found) satisfies a required constraint.
/// Returns true if found has at least as strong constraints as required.
fn constraint_satisfied(
    found: &Option<crate::generic::TypeConstraint>,
    required: &crate::generic::TypeConstraint,
) -> bool {
    use crate::generic::TypeConstraint;

    let Some(found) = found else {
        // Found has no constraint - can only satisfy if required is empty
        return false;
    };

    match (found, required) {
        // Interface constraints: found must have all interfaces that required has
        (
            TypeConstraint::Interface(found_interfaces),
            TypeConstraint::Interface(required_interfaces),
        ) => {
            // All required interfaces must be in the found interfaces
            required_interfaces
                .iter()
                .all(|req| found_interfaces.contains(req))
        }
        // Union constraints: found must be a subset of or equal to required (TypeId version)
        (TypeConstraint::UnionId(found_ids), TypeConstraint::UnionId(required_ids)) => {
            // All found TypeIds must be in the required TypeIds
            found_ids
                .iter()
                .all(|f| required_ids.iter().any(|r| f == r))
        }
        // Structural constraints: more complex matching needed, for now require exact match
        (TypeConstraint::Structural(found_struct), TypeConstraint::Structural(required_struct)) => {
            found_struct == required_struct
        }
        // Different constraint kinds don't satisfy each other
        (
            TypeConstraint::Interface(_),
            TypeConstraint::UnionId(_) | TypeConstraint::Structural(_),
        )
        | (
            TypeConstraint::UnionId(_),
            TypeConstraint::Interface(_) | TypeConstraint::Structural(_),
        )
        | (
            TypeConstraint::Structural(_),
            TypeConstraint::Interface(_) | TypeConstraint::UnionId(_),
        ) => false,
    }
}

impl Analyzer {
    /// Pre-compute substituted field types for a generic class instantiation.
    ///
    /// When creating a type like Box<String>, this ensures that the substituted field
    /// types (e.g., String for a field of type T) exist in the arena. This allows
    /// codegen to use lookup_substitute instead of substitute, making it fully read-only.
    pub(super) fn precompute_field_substitutions(
        &self,
        type_def_id: TypeDefId,
        type_args: &[ArenaTypeId],
    ) {
        // Skip if no type arguments (no substitution needed)
        if type_args.is_empty() {
            return;
        }

        // Get field types and type params from the type definition
        let Some(generic_info) = self.entity_registry().type_generic_info(type_def_id) else {
            return;
        };
        let field_types = generic_info.field_types;
        let type_params = self.entity_registry().type_params(type_def_id);

        // Build substitution map: type param NameId -> concrete TypeId
        let subs: FxHashMap<NameId, ArenaTypeId> = type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        // Pre-compute substituted types for all fields
        // This ensures they exist in the arena for codegen's lookup_substitute
        let mut arena = self.type_arena_mut();
        for field_type in field_types {
            arena.substitute(field_type, &subs);
        }
    }

    /// Pre-compute substituted method signatures for an interface instantiation.
    ///
    /// When a concrete type implements an interface (via implements clause or interface boxing),
    /// this ensures that the substituted method param/return types exist in the arena.
    /// This allows codegen to use lookup_substitute instead of substitute when building vtables.
    pub(super) fn precompute_interface_method_substitutions(
        &self,
        interface_type_def_id: TypeDefId,
        type_args: &[ArenaTypeId],
    ) {
        // Skip if no type arguments (no substitution needed)
        if type_args.is_empty() {
            return;
        }

        // Get interface type params and method signature IDs upfront
        // to avoid borrow conflicts with the arena
        let registry = self.entity_registry();
        let type_params = registry.type_params(interface_type_def_id);
        let method_ids = registry.interface_methods_ordered(interface_type_def_id);
        let signature_ids: Vec<ArenaTypeId> = method_ids
            .iter()
            .map(|&mid| registry.method_signature(mid))
            .collect();
        drop(registry);

        // Skip if type params and args don't match (error case handled elsewhere)
        if type_params.len() != type_args.len() {
            return;
        }

        // Build substitution map: type param NameId -> concrete TypeId
        let subs: FxHashMap<NameId, ArenaTypeId> = type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        // Pre-compute substituted types for all method signatures
        // This ensures they exist in the arena for codegen's lookup_substitute
        let mut arena = self.type_arena_mut();
        for signature_id in signature_ids {
            // Get method param and return types
            if let Some((params, ret, _)) = arena.unwrap_function(signature_id) {
                // Substitute each param type
                let params = params.to_vec();
                for param in params {
                    arena.substitute(param, &subs);
                }
                // Substitute return type
                arena.substitute(ret, &subs);
            }
        }
    }

    pub(super) fn resolve_type_param_constraint(
        &mut self,
        constraint: &TypeConstraint,
        type_param_scope: &TypeParamScope,
        interner: &Interner,
        span: Span,
    ) -> Option<crate::generic::TypeConstraint> {
        tracing::debug!(?constraint, "resolve_type_param_constraint");
        match constraint {
            TypeConstraint::Interface(ifaces) => {
                tracing::debug!(
                    num_interfaces = ifaces.len(),
                    "processing interface constraint"
                );
                // For single interface, check if it's a type alias first
                if ifaces.len() == 1 && ifaces[0].type_args.is_empty() {
                    let sym = ifaces[0].name;
                    if let Some(type_def_id) = self
                        .resolver(interner)
                        .resolve_type(sym, &self.entity_registry())
                    {
                        let kind = self.entity_registry().type_kind(type_def_id);
                        let aliased_type = self.entity_registry().type_aliased(type_def_id);
                        if kind == TypeDefKind::Alias
                            && let Some(aliased_type_id) = aliased_type
                        {
                            // Use TypeId directly - check what kind of type it is
                            let arena = self.type_arena();

                            // Check if the aliased type is an interface - keep as Interface constraint
                            if arena.is_interface(aliased_type_id) {
                                // Don't convert interface aliases to UnionId;
                                // fall through to the Interface validation below
                            } else {
                                // Check if it's a structural type - return as Structural constraint
                                if let Some(structural) = arena.unwrap_structural(aliased_type_id) {
                                    return Some(crate::generic::TypeConstraint::Structural(
                                        structural.clone(),
                                    ));
                                }

                                // Check if it's a union type
                                let type_ids =
                                    if let Some(variants) = arena.unwrap_union(aliased_type_id) {
                                        // It's a union - use the variant TypeIds
                                        variants.to_vec()
                                    } else {
                                        // Not a union - use the single TypeId
                                        vec![aliased_type_id]
                                    };
                                return Some(crate::generic::TypeConstraint::UnionId(type_ids));
                            }
                        }
                    }
                }

                // Validate all interfaces exist via EntityRegistry using resolver
                for iface in ifaces {
                    let iface_str = interner.resolve(iface.name);
                    let iface_exists = self
                        .resolver(interner)
                        .resolve_type_str_or_interface(iface_str, &self.entity_registry())
                        .is_some();

                    if !iface_exists {
                        self.add_error(
                            SemanticError::UnknownInterface {
                                name: iface_str.to_string(),
                                span: span.into(),
                            },
                            span,
                        );
                        return None;
                    }
                }

                // Resolve interface type arguments within the type param scope
                let module_id = self.module.current_module;
                Some(crate::generic::TypeConstraint::Interface(
                    ifaces
                        .iter()
                        .map(|iface| {
                            let name = interner.resolve(iface.name).to_string();
                            let type_args = iface
                                .type_args
                                .iter()
                                .map(|arg| {
                                    let mut ctx = TypeResolutionContext::with_type_params(
                                        &self.ctx.db,
                                        interner,
                                        module_id,
                                        type_param_scope,
                                    );
                                    resolve_type_to_id(arg, &mut ctx)
                                })
                                .collect();
                            crate::generic::ConstraintInterfaceItem { name, type_args }
                        })
                        .collect(),
                ))
            }
            TypeConstraint::Union(types) => {
                let module_id = self.module.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.ctx.db,
                    interner,
                    module_id,
                    type_param_scope,
                );
                let resolved_ids = types
                    .iter()
                    .map(|ty| resolve_type_to_id(ty, &mut ctx))
                    .collect();
                Some(crate::generic::TypeConstraint::UnionId(resolved_ids))
            }
            TypeConstraint::Structural { fields, methods } => {
                let module_id = self.module.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.ctx.db,
                    interner,
                    module_id,
                    type_param_scope,
                );
                // Convert AST structural to InternedStructural (TypeId-based)
                let resolved_fields: smallvec::SmallVec<[(NameId, ArenaTypeId); 4]> = fields
                    .iter()
                    .map(|f| {
                        let name =
                            ctx.name_table_mut()
                                .intern(ctx.module_id, &[f.name], ctx.interner);
                        let ty = resolve_type_to_id(&f.ty, &mut ctx);
                        (name, ty)
                    })
                    .collect();
                let resolved_methods: smallvec::SmallVec<
                    [crate::type_arena::InternedStructuralMethod; 2],
                > = methods
                    .iter()
                    .map(|m| {
                        let name =
                            ctx.name_table_mut()
                                .intern(ctx.module_id, &[m.name], ctx.interner);
                        let params = m
                            .params
                            .iter()
                            .map(|p| resolve_type_to_id(p, &mut ctx))
                            .collect();
                        let return_type = resolve_type_to_id(&m.return_type, &mut ctx);
                        crate::type_arena::InternedStructuralMethod {
                            name,
                            params,
                            return_type,
                        }
                    })
                    .collect();
                Some(crate::generic::TypeConstraint::Structural(
                    crate::type_arena::InternedStructural {
                        fields: resolved_fields,
                        methods: resolved_methods,
                    },
                ))
            }
        }
    }

    /// Check type param constraints.
    pub(super) fn check_type_param_constraints_id(
        &mut self,
        type_params: &[TypeParamInfo],
        inferred: &FxHashMap<NameId, ArenaTypeId>,
        span: Span,
        interner: &Interner,
    ) {
        use crate::compatibility::types_compatible_core_id;

        // First check: reject struct types as generic type arguments
        for param in type_params {
            let Some(&found_id) = inferred.get(&param.name_id) else {
                continue;
            };
            let is_struct = {
                let arena = self.type_arena();
                arena
                    .unwrap_nominal(found_id)
                    .is_some_and(|(_, _, kind)| kind == crate::type_arena::NominalKind::Struct)
            };
            if is_struct {
                let name = self.type_display_id(found_id);
                self.add_error(
                    SemanticError::StructAsTypeArg {
                        name,
                        span: span.into(),
                    },
                    span,
                );
            }
        }

        for param in type_params {
            let Some(constraint) = &param.constraint else {
                continue;
            };
            let Some(&found_id) = inferred.get(&param.name_id) else {
                continue;
            };

            // Check if found type is itself a type param with matching or stronger constraint
            let found_param = {
                let arena = self.type_arena();
                if let Some(found_name_id) = arena.unwrap_type_param(found_id) {
                    self.env.type_param_stack.get_by_name_id(found_name_id)
                } else if let Some(type_param_id) = arena.unwrap_type_param_ref(found_id) {
                    self.env
                        .type_param_stack
                        .get_by_type_param_id(type_param_id)
                } else {
                    None
                }
            };
            if let Some(found_param) = found_param
                && constraint_satisfied(&found_param.constraint, constraint)
            {
                continue; // Constraint is satisfied
            }

            match constraint {
                crate::generic::TypeConstraint::Interface(interface_items) => {
                    // Check each interface constraint by string name (cross-interner safe)
                    for iface_item in interface_items {
                        // For parameterized interfaces, substitute inferred type params
                        // in the type args before checking satisfaction
                        let substituted_args: Vec<ArenaTypeId> = iface_item
                            .type_args
                            .iter()
                            .map(|&arg| self.type_arena_mut().substitute(arg, inferred))
                            .collect();

                        let satisfied = if substituted_args.is_empty() {
                            // Non-parameterized: simple name check
                            self.satisfies_interface_by_name(found_id, &iface_item.name, interner)
                        } else {
                            // Parameterized: check with type args
                            self.satisfies_parameterized_interface(
                                found_id,
                                &iface_item.name,
                                &substituted_args,
                                interner,
                            )
                        };

                        if !satisfied {
                            let found_display = self.type_display_id(found_id);
                            self.add_error(
                                SemanticError::TypeParamConstraintMismatch {
                                    type_param: self.get_type_param_display_name(param, interner),
                                    expected: iface_item.name.clone(),
                                    found: found_display,
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                    }
                }
                crate::generic::TypeConstraint::UnionId(variant_ids) => {
                    // TypeId-based - check if the found type is compatible with the union,
                    // OR if it satisfies any interface variant in the union.
                    let expected_id = self.type_arena_mut().union(variant_ids.clone());
                    let is_compatible = {
                        let arena = self.type_arena();
                        types_compatible_core_id(found_id, expected_id, &arena)
                    };
                    if !is_compatible {
                        // Check if any variant is an interface the type satisfies
                        let satisfies_interface_variant = variant_ids.iter().any(|&vid| {
                            let iface_name: Option<String> = {
                                let arena = self.type_arena();
                                arena.unwrap_interface(vid).and_then(|(td, _)| {
                                    let name_id = self.entity_registry().name_id(td);
                                    self.name_table().last_segment_str(name_id)
                                })
                            };
                            if let Some(ref name) = iface_name {
                                self.satisfies_interface_by_name(found_id, name, interner)
                            } else {
                                false
                            }
                        });
                        if !satisfies_interface_variant {
                            let expected_display = self.type_display_id(expected_id);
                            let found_display = self.type_display_id(found_id);
                            self.add_error(
                                SemanticError::TypeParamConstraintMismatch {
                                    type_param: self.get_type_param_display_name(param, interner),
                                    expected: expected_display,
                                    found: found_display,
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                    }
                }
                crate::generic::TypeConstraint::Structural(structural) => {
                    // Substitute any type params in the structural constraint before checking.
                    // This handles cases like `func foo<T, __T0: { name: T }>(a: __T0)` where
                    // the structural constraint references another type param T.
                    let substituted_structural =
                        self.substitute_structural_constraint(structural, inferred);

                    // Use TypeId-based structural constraint checking
                    if let Some(mismatch) = self.check_structural_constraint_id(
                        found_id,
                        &substituted_structural,
                        interner,
                    ) {
                        let found_display = self.type_display_id(found_id);
                        let constraint_display = self.structural_display(&substituted_structural);
                        self.add_error(
                            SemanticError::StructuralConstraintMismatch {
                                constraint: constraint_display,
                                found: found_display,
                                mismatch,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                }
            }
        }
    }

    /// Substitute type parameters in a structural constraint.
    /// This is needed when the structural constraint references other type params,
    /// e.g., in `func foo<T, __T0: { name: T }>(a: __T0)`, the constraint `{ name: T }`
    /// needs T substituted with the inferred type before checking.
    pub(super) fn substitute_structural_constraint(
        &mut self,
        structural: &crate::type_arena::InternedStructural,
        inferred: &FxHashMap<NameId, ArenaTypeId>,
    ) -> crate::type_arena::InternedStructural {
        use crate::type_arena::{InternedStructural, InternedStructuralMethod};

        // Substitute field types
        let new_fields: smallvec::SmallVec<[(NameId, ArenaTypeId); 4]> = structural
            .fields
            .iter()
            .map(|&(name, ty)| {
                let new_ty = self.type_arena_mut().substitute(ty, inferred);
                (name, new_ty)
            })
            .collect();

        // Substitute method signatures
        let new_methods: smallvec::SmallVec<[InternedStructuralMethod; 2]> = structural
            .methods
            .iter()
            .map(|m| {
                let new_params: crate::type_arena::TypeIdVec = m
                    .params
                    .iter()
                    .map(|&p| self.type_arena_mut().substitute(p, inferred))
                    .collect();
                let new_return_type = self.type_arena_mut().substitute(m.return_type, inferred);
                InternedStructuralMethod {
                    name: m.name,
                    params: new_params,
                    return_type: new_return_type,
                }
            })
            .collect();

        InternedStructural {
            fields: new_fields,
            methods: new_methods,
        }
    }

    /// Type-check parameter default expressions against their declared types.
    /// Called during function body analysis when parameters are in scope.
    pub(super) fn check_param_defaults(
        &mut self,
        params: &[Param],
        param_types: &crate::type_arena::TypeIdVec,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for (param, &expected_type_id) in params.iter().zip(param_types.iter()) {
            if let Some(ref default_expr) = param.default_value {
                // Type-check the default expression
                let found_type_id = self.check_expr(default_expr, interner)?;

                // Check type compatibility
                if !self.types_compatible_id(expected_type_id, found_type_id, interner) {
                    let expected = self.type_display_id(expected_type_id);
                    let found = self.type_display_id(found_type_id);
                    self.add_error(
                        SemanticError::DefaultExprTypeMismatch {
                            expected,
                            found,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }

                // Check that the default is a constant expression
                if !self.is_constant_expr(default_expr) {
                    let name = interner.resolve(param.name).to_string();
                    self.add_error(
                        SemanticError::DefaultMustBeConstant {
                            name,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }
            }
        }
        Ok(())
    }

    /// Type-check field default expressions against their declared types.
    /// Called during class analysis.
    pub(super) fn check_field_defaults(
        &mut self,
        fields: &[FieldDef],
        field_type_ids: &[ArenaTypeId],
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for (field, &expected_type_id) in fields.iter().zip(field_type_ids.iter()) {
            if let Some(ref default_expr) = field.default_value {
                // Type-check the default expression
                let found_type_id = self.check_expr(default_expr, interner)?;

                // Check type compatibility
                if !self.types_compatible_id(expected_type_id, found_type_id, interner) {
                    let expected = self.type_display_id(expected_type_id);
                    let found = self.type_display_id(found_type_id);
                    let field_name = interner.resolve(field.name).to_string();
                    self.add_error(
                        SemanticError::FieldDefaultTypeMismatch {
                            expected,
                            found,
                            field: field_name,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }

                // Check that the default is a constant expression
                if !self.is_constant_expr(default_expr) {
                    let field_name = interner.resolve(field.name).to_string();
                    self.add_error(
                        SemanticError::DefaultMustBeConstant {
                            name: field_name,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }
            }
        }
        Ok(())
    }
}
