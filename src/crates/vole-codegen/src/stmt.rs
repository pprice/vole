// src/codegen/stmt.rs
//
// Statement and block compilation - impl Cg methods.

use cranelift::prelude::*;

use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;
use vole_frontend::{self, Symbol};
use vole_identity::{NameId, TypeId, VirTypeId};
use vole_vir::VirStmt;
use vole_vir::stmt::LetStorageHint;

use super::context::Cg;
use super::structs::{convert_to_i64_for_storage, split_i128_for_storage, store_value_to_stack};
use super::types::{CompiledValue, FALLIBLE_SUCCESS_TAG, convert_to_type};
use crate::ops::sextend_const;

#[derive(Clone, Copy)]
struct RaiseFieldLayout {
    name_id: NameId,
    ty: TypeId,
}

impl Cg<'_, '_, '_> {
    // NOTE: block(), stmt(), preregister_recursive_lambda() deleted.
    // All code now goes through compile_vir_body / compile_vir_stmt.

    /// Coerce a let-binding's initializer to match the declared type.
    ///
    /// Handles: unknown boxing, union wrapping, integer narrowing/widening,
    /// float promotion/demotion, and interface boxing. Returns the coerced
    /// value, its type, and whether a stack-allocated union was constructed.
    ///
    /// The `storage` hint (pre-computed during VIR lowering) drives the
    /// coercion branch instead of querying `TypeArena` at compile time.
    fn coerce_let_init(
        &mut self,
        init: &CompiledValue,
        declared_type_id_opt: Option<TypeId>,
        sentinel_hint_type_id: Option<TypeId>,
        storage: LetStorageHint,
    ) -> CodegenResult<(Value, TypeId, bool)> {
        let mut is_stack_union = false;

        let (mut final_value, mut final_type_id) = if let Some(declared_type_id) =
            declared_type_id_opt
        {
            match storage {
                LetStorageHint::Unknown if !init.type_id.is_unknown() => {
                    // Box value to unknown type (TaggedValue)
                    let boxed = self.box_to_unknown(*init)?;
                    (boxed.value, boxed.type_id)
                }
                LetStorageHint::Union { tag_hint } if !self.vir_query_is_union(init.type_id) => {
                    let wrapped = if let Some(hint) = tag_hint {
                        self.construct_union_from_hint(*init, declared_type_id, &hint)?
                    } else {
                        self.construct_union_id_with_hint(
                            *init,
                            declared_type_id,
                            sentinel_hint_type_id,
                        )?
                    };
                    is_stack_union = true;
                    (wrapped.value, wrapped.type_id)
                }
                LetStorageHint::Numeric if init.type_id.is_numeric() => {
                    let coerced = self.coerce_to_type(*init, declared_type_id)?;
                    (coerced.value, coerced.type_id)
                }
                LetStorageHint::Interface => {
                    // For functional interfaces, keep the actual function type
                    // from the lambda. This preserves the is_closure flag for
                    // proper calling convention.
                    (init.value, init.type_id)
                }
                _ => (init.value, declared_type_id),
            }
        } else {
            (init.value, init.type_id)
        };

        // Box value if assigning to interface type
        if let Some(declared_type_id) = declared_type_id_opt
            && storage == LetStorageHint::Interface
        {
            let is_final_interface = self.arena().is_interface(final_type_id);
            // RuntimeIterator is an internal concrete type that implements Iterator
            // dispatch directly via runtime_iterator_method; skip interface boxing.
            let is_runtime_iterator = self.arena().is_runtime_iterator(final_type_id);

            if !is_final_interface && !is_runtime_iterator {
                let cranelift_ty = self.cranelift_type(final_type_id);
                let boxed = self.box_interface_value(
                    CompiledValue::new(final_value, cranelift_ty, final_type_id),
                    declared_type_id,
                )?;
                final_value = boxed.value;
                final_type_id = boxed.type_id;
            }
        }

        Ok((final_value, final_type_id, is_stack_union))
    }

    /// Find the union variant tag for a value's type, with integer widening/narrowing fallback.
    /// Returns (tag_index, possibly_coerced_value, actual_type_id).
    pub(crate) fn find_union_variant_tag(
        &mut self,
        value: &CompiledValue,
        union_type_id: TypeId,
        variants: &[TypeId],
    ) -> CodegenResult<(usize, Value, TypeId)> {
        self.find_union_variant_tag_with_hint(value, union_type_id, variants, None)
    }

    fn find_union_variant_tag_with_hint(
        &mut self,
        value: &CompiledValue,
        union_type_id: TypeId,
        variants: &[TypeId],
        sentinel_hint_type_id: Option<TypeId>,
    ) -> CodegenResult<(usize, Value, TypeId)> {
        let resolved_value_type_id = self.try_substitute_type(value.type_id);

        // Direct type match
        if let Some(pos) = variants.iter().position(|&v| v == resolved_value_type_id) {
            return Ok((pos, value.value, resolved_value_type_id));
        }

        // Sentinel hint match (used when multiple sentinel variants share the same
        // lowered value shape, e.g. Empty/Deleted).
        if let Some(hint_type_id) = sentinel_hint_type_id
            && self.arena().is_sentinel(resolved_value_type_id)
            && let Some(pos) = variants.iter().position(|&v| v == hint_type_id)
        {
            return Ok((pos, value.value, hint_type_id));
        }

        // Try to find a compatible integer type for widening/narrowing
        let arena = self.arena();
        let value_is_integer = arena.is_integer(resolved_value_type_id);

        let compatible = if value_is_integer {
            variants
                .iter()
                .enumerate()
                .find(|(_, v)| arena.is_integer(**v))
                .map(|(pos, v)| (pos, *v))
        } else {
            None
        };

        match compatible {
            Some((pos, variant_type_id)) => {
                let target_ty = self.cranelift_type(variant_type_id);
                let actual = if target_ty.bytes() < value.ty.bytes() {
                    self.builder.ins().ireduce(target_ty, value.value)
                } else if target_ty.bytes() > value.ty.bytes() {
                    sextend_const(self.builder, target_ty, value.value)
                } else {
                    value.value
                };
                Ok((pos, actual, variant_type_id))
            }
            None if self.arena().is_sentinel(resolved_value_type_id) => {
                let sentinel_variants: Vec<(usize, TypeId)> = variants
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, &ty)| self.arena().is_sentinel(ty).then_some((idx, ty)))
                    .collect();
                if sentinel_variants.len() == 1 {
                    let (pos, ty) = sentinel_variants[0];
                    Ok((pos, value.value, ty))
                } else {
                    let expected = variants
                        .iter()
                        .map(|&variant| self.arena().display_basic(variant))
                        .collect::<Vec<_>>()
                        .join(" | ");
                    let found = self.arena().display_basic(resolved_value_type_id);
                    let subs = self
                        .substitutions
                        .map(|m| {
                            m.iter()
                                .map(|(k, v)| {
                                    format!(
                                        "{} ({:?}) -> {}",
                                        self.name_table().display(*k),
                                        k,
                                        self.arena().display_basic(*v)
                                    )
                                })
                                .collect::<Vec<_>>()
                                .join(", ")
                        })
                        .unwrap_or_else(|| "<none>".to_string());
                    Err(CodegenError::type_mismatch(
                        "union sentinel variant",
                        format!("compatible sentinel type ({expected})"),
                        format!(
                            "{found} (union={}, substitutions={subs})",
                            self.arena().display_basic(union_type_id)
                        ),
                    ))
                }
            }
            None => {
                let expected = variants
                    .iter()
                    .map(|&variant| self.arena().display_basic(variant))
                    .collect::<Vec<_>>()
                    .join(" | ");
                let found = if let Some(name_id) = self.arena().unwrap_type_param(value.type_id) {
                    format!("{} ({:?})", self.name_table().display(name_id), name_id)
                } else {
                    self.arena().display_basic(resolved_value_type_id)
                };
                let subs = self
                    .substitutions
                    .map(|m| {
                        m.iter()
                            .map(|(k, v)| {
                                format!(
                                    "{} ({:?}) -> {}",
                                    self.name_table().display(*k),
                                    k,
                                    self.arena().display_basic(*v)
                                )
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    })
                    .unwrap_or_else(|| "<none>".to_string());
                Err(CodegenError::type_mismatch(
                    "union variant",
                    format!("compatible type ({expected})"),
                    format!(
                        "{found} (union={}, substitutions={subs})",
                        self.arena().display_basic(union_type_id)
                    ),
                ))
            }
        }
    }

    /// Wrap a value in a union representation.
    pub fn construct_union_id(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.construct_union_id_with_hint(value, union_type_id, None)
    }

    /// Construct a stack-allocated union buffer using a pre-computed tag hint.
    ///
    /// This is the fast path for let-binding union coercion when VIR lowering
    /// has pre-computed the variant tag, RC state, and coercion target.  Skips
    /// the `unwrap_union` + `find_union_variant_tag` arena queries.
    fn construct_union_from_hint(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
        hint: &vole_vir::stmt::UnionTagHint,
    ) -> CodegenResult<CompiledValue> {
        // If the value is a struct, box it first (auto-boxing for union storage)
        let value = if self.vir_query_is_struct(value.type_id) {
            self.copy_struct_to_heap(value)?
        } else {
            value
        };

        // Coerce the payload value to the variant's Cranelift type if needed.
        let variant_type_id = self.sema_type_from_vir(hint.variant_type);
        let target_ty = self.cranelift_type(variant_type_id);
        let actual_value = if target_ty != value.ty && target_ty.is_int() && value.ty.is_int() {
            if target_ty.bytes() < value.ty.bytes() {
                self.builder.ins().ireduce(target_ty, value.value)
            } else {
                sextend_const(self.builder, target_ty, value.value)
            }
        } else {
            value.value
        };

        let union_size = self.type_size(union_type_id);
        let slot = self.alloc_stack(union_size);

        // Store tag byte at offset 0
        let tag_val = self.iconst_cached(types::I8, hint.tag as i64);
        self.builder.ins().stack_store(tag_val, slot, 0);

        // Store is_rc flag at offset 1
        let is_rc_val = self.iconst_cached(types::I8, hint.is_rc as i64);
        self.builder
            .ins()
            .stack_store(is_rc_val, slot, union_layout::IS_RC_OFFSET);

        if union_size > union_layout::TAG_ONLY_SIZE {
            // Sentinel variants have no payload data; zero the slot to avoid
            // undefined behaviour in generic cleanup paths.
            let is_sentinel = self.arena().is_sentinel(variant_type_id);
            let payload = if is_sentinel {
                self.iconst_cached(types::I64, 0)
            } else {
                actual_value
            };
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        Ok(CompiledValue::new(ptr, ptr_type, union_type_id))
    }

    pub fn construct_union_id_with_hint(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
        sentinel_hint_type_id: Option<TypeId>,
    ) -> CodegenResult<CompiledValue> {
        let arena = self.arena();
        let variants = arena.unwrap_union(union_type_id).ok_or_else(|| {
            CodegenError::type_mismatch("union construction", "union type", "non-union")
        })?;
        let variants = variants.clone();

        // If the value is already the same union type, just return it.
        // Also check the substituted type, since generic code may produce values
        // whose raw type_id is e.g. `T | nil` but after substitution matches the
        // concrete union type `i64 | nil`.
        let resolved_type_id = self.try_substitute_type(value.type_id);
        if value.type_id == union_type_id || resolved_type_id == union_type_id {
            return Ok(value);
        }

        // If the value is a struct, box it first (auto-boxing for union storage)
        let value = if self.vir_query_is_struct(value.type_id) {
            self.copy_struct_to_heap(value)?
        } else {
            value
        };

        // Find the position of value's type in variants
        let (tag, actual_value, actual_type_id) = self.find_union_variant_tag_with_hint(
            &value,
            union_type_id,
            &variants,
            sentinel_hint_type_id,
        )?;

        let union_size = self.type_size(union_type_id);
        let slot = self.alloc_stack(union_size);

        let tag_val = self.iconst_cached(types::I8, tag as i64);
        self.builder.ins().stack_store(tag_val, slot, 0);

        // Store is_rc flag at offset 1 (matches heap union layout used by
        // construct_union_heap_id). copy_union_to_heap reads this byte to
        // decide whether to rc_inc the payload when promoting to the heap.
        let is_rc = self.rc_state(actual_type_id).needs_cleanup();
        let is_rc_val = self.iconst_cached(types::I8, is_rc as i64);
        self.builder
            .ins()
            .stack_store(is_rc_val, slot, union_layout::IS_RC_OFFSET);

        if union_size > union_layout::TAG_ONLY_SIZE {
            // Initialize payload bytes for payload-carrying unions. Sentinel variants
            // don't carry data, but zeroing avoids undefined behavior when generic
            // cleanup/copy paths read the payload word.
            let payload = if self.arena().is_sentinel(actual_type_id) {
                self.iconst_cached(types::I64, 0)
            } else {
                actual_value
            };
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        Ok(CompiledValue::new(ptr, ptr_type, union_type_id))
    }

    /// Resolve the TypeDefId for the named error type from a fallible error type.
    ///
    /// Handles both single error types and unions of error types by matching
    /// the error name against the type definitions.
    fn resolve_raise_error_type_def(
        &self,
        error_type_id: TypeId,
        error_name_sym: Symbol,
    ) -> CodegenResult<vole_identity::TypeDefId> {
        let raise_error_name = self.interner().resolve(error_name_sym);
        let arena = self.arena();
        let name_table = self.name_table();
        let result = if let Some(type_def_id) = arena.unwrap_error(error_type_id) {
            // Single error type
            let name =
                name_table.last_segment_str(self.analyzed().entity_type_name_id(type_def_id));
            if name.as_deref() == Some(raise_error_name) {
                Some(type_def_id)
            } else {
                None
            }
        } else if let Some(variants) = arena.unwrap_union(error_type_id) {
            // Union of error types
            variants.iter().find_map(|&v| {
                if let Some(type_def_id) = arena.unwrap_error(v) {
                    let name = name_table
                        .last_segment_str(self.analyzed().entity_type_name_id(type_def_id));
                    if name.as_deref() == Some(raise_error_name) {
                        return Some(type_def_id);
                    }
                }
                None
            })
        } else {
            None
        };
        result.ok_or_else(|| {
            CodegenError::not_found("error type info", self.interner().resolve(error_name_sym))
        })
    }

    // =========================================================================
    // VIR body and statement compilation
    // =========================================================================

    /// Compile a VIR body (stmts + optional trailing expression).
    ///
    /// Used for test function compilation where the caller manages RC
    /// scopes and finalization externally.
    ///
    /// Returns `(terminated, Option<CompiledValue>)`:
    /// - If trailing is `Some`: compiles stmts then the trailing expr,
    ///   returns `(true, Some(value))`.
    /// - If trailing is `None`: compiles all stmts, returns `(terminated, None)`.
    pub fn compile_vir_body(
        &mut self,
        body: &vole_vir::VirBody,
    ) -> CodegenResult<(bool, Option<CompiledValue>)> {
        if let Some(trailing) = &body.trailing {
            // Expression body: compile preceding stmts then the trailing expr
            let mut terminated = false;
            for vir_stmt in &body.stmts {
                if terminated {
                    break;
                }
                terminated = self.compile_vir_stmt(vir_stmt)?;
            }
            if terminated {
                Ok((true, None))
            } else {
                let value = self.compile_vir_expr(trailing)?;
                Ok((true, Some(value)))
            }
        } else {
            // Block body: compile all stmts
            let mut terminated = false;
            for vir_stmt in &body.stmts {
                if terminated {
                    break;
                }
                terminated = self.compile_vir_stmt(vir_stmt)?;
            }
            Ok((terminated, None))
        }
    }

    /// Compile a VIR statement node.
    ///
    /// All VIR statement variants are handled directly.
    #[deny(clippy::wildcard_enum_match_arm)]
    pub fn compile_vir_stmt(&mut self, vir_stmt: &VirStmt) -> CodegenResult<bool> {
        match vir_stmt {
            VirStmt::Expr { value } => {
                let mut compiled = self.compile_vir_expr(value)?;
                if compiled.type_id == TypeId::NEVER {
                    // The expression diverges (e.g. exhaustive if/else with
                    // returns in all branches, `unreachable`, `panic`).
                    // The current block is already terminated by the expression
                    // compiler, so we must NOT emit another trap here.
                    compiled.mark_consumed();
                    Ok(true)
                } else {
                    // Consume RC value if the expression result is unused
                    // (e.g. standalone function call returning a string).
                    self.consume_rc_value(&mut compiled)?;
                    compiled.debug_assert_rc_handled("VirStmt::Expr");
                    Ok(false)
                }
            }
            VirStmt::While { cond, body } => self.compile_vir_while(cond, body),

            // -- Control flow (simple delegation) --------------------------------
            VirStmt::Return { value, convention } => {
                self.compile_vir_return(value.as_deref(), *convention)
            }
            VirStmt::Break => self.compile_vir_break(),
            VirStmt::Continue => self.compile_vir_continue(),

            // -- RC operations ---------------------------------------------------
            VirStmt::RcInc { value, cleanup } => {
                let compiled = self.compile_vir_expr(value)?;
                self.emit_rc_inc_with_cleanup(compiled.value, compiled.type_id, *cleanup)?;
                Ok(false)
            }
            VirStmt::RcDec { value, cleanup } => {
                let compiled = self.compile_vir_expr(value)?;
                self.emit_rc_dec_with_cleanup(compiled.value, compiled.type_id, *cleanup)?;
                Ok(false)
            }

            // -- Bindings -----------------------------------------------------------
            VirStmt::Let {
                name,
                value,
                mutable: _,
                ty,
                vir_ty,
                storage,
                declared_type,
            } => {
                let binding_ty = if *vir_ty != VirTypeId::UNKNOWN {
                    self.sema_type_from_vir(*vir_ty)
                } else {
                    self.sema_type_from_vir(*ty)
                };
                let declared = declared_type.map(|dt| self.sema_type_from_vir(dt));
                self.compile_vir_let(*name, value, binding_ty, *storage, declared)
            }
            VirStmt::LetTuple { pattern, value, .. } => self.compile_vir_let_tuple(pattern, value),
            VirStmt::Assign { target, value } => self.compile_vir_assign(target, value),
            VirStmt::For(vir_for) => self.compile_vir_for(vir_for),
            VirStmt::Raise { error_name, fields } => self.compile_vir_raise(*error_name, fields),

            // -- No-op -----------------------------------------------------------
            VirStmt::Noop => Ok(false),
        }
    }

    /// Compile a VIR return statement.
    ///
    /// Handles all return conventions: simple value return, interface boxing,
    /// unknown boxing, fallible returns, struct returns, union wrapping, and
    /// RC bookkeeping (skip-var for owned locals, inc for borrows).
    ///
    /// The `convention` parameter (pre-computed during VIR lowering) drives
    /// the return instruction emission instead of querying the type arena.
    fn compile_vir_return(
        &mut self,
        value: Option<&vole_vir::VirExpr>,
        convention: vole_vir::stmt::ReturnConvention,
    ) -> CodegenResult<bool> {
        let return_type_id = self.return_type;
        if let Some(value_expr) = value {
            // For Unresolved conventions, determine union-ness at codegen time.
            let is_union_return = matches!(convention, vole_vir::stmt::ReturnConvention::Union)
                || (matches!(convention, vole_vir::stmt::ReturnConvention::Unresolved)
                    && return_type_id.is_some_and(|ret_id| self.vir_query_is_union(ret_id)));
            let mut compiled = if is_union_return
                && let Some(ret_type_id) = return_type_id
                && matches!(value_expr, vole_vir::VirExpr::ArrayLiteral { .. })
                && let Some(expected_variant) = self.preferred_array_like_union_variant(ret_type_id)
            {
                self.compile_vir_expr_with_expected_type(value_expr, expected_variant)?
            } else {
                self.compile_vir_expr(value_expr)?
            };
            compiled.type_id = self.try_substitute_type(compiled.type_id);
            if is_union_return
                && let Some(ret_type_id) = return_type_id
                && self.arena().is_function(compiled.type_id)
                && let vole_vir::VirExpr::Match {
                    scrutinee, arms, ..
                } = value_expr
            {
                // Match-expression type metadata can degrade in generic module
                // bodies. Recompile with the declared return union as the
                // expected result type.
                compiled = self.compile_vir_match(scrutinee, arms, ret_type_id)?;
                compiled.type_id = self.try_substitute_type(compiled.type_id);
            }

            // RC bookkeeping: detect RC skip-var from VIR LocalLoad.
            let skip_var = self.extract_vir_return_skip_var(value_expr);
            if skip_var.is_none() && compiled.is_borrowed() {
                if self.rc_state(compiled.type_id).needs_cleanup() {
                    self.emit_rc_inc_for_type(compiled.value, compiled.type_id)?;
                } else if let Some(rc_tags) = self.rc_state(compiled.type_id).union_variants() {
                    self.emit_union_rc_inc(compiled.value, rc_tags)?;
                }
            }
            self.emit_rc_cleanup_all_scopes(skip_var)?;

            compiled.mark_consumed();
            compiled.debug_assert_rc_handled("VirStmt::Return");

            self.emit_return_value(compiled, return_type_id, convention)?;
        } else {
            self.emit_rc_cleanup_all_scopes(None)?;
            self.builder.ins().return_(&[]);
        }
        Ok(true)
    }

    /// Extract RC skip-var from a VIR return value expression.
    ///
    /// If the return value is a `LocalLoad` (lowered identifier) bound to
    /// an RC-tracked local, returns that variable so RC cleanup can skip it
    /// (ownership transfers to the caller).
    fn extract_vir_return_skip_var(&self, value_expr: &vole_vir::VirExpr) -> Option<Variable> {
        if let vole_vir::VirExpr::LocalLoad { name, .. } = value_expr
            && let Some((var, _)) = self.vars.get(name)
            && (self.rc_scopes.is_rc_local(*var)
                || self.rc_scopes.is_composite_rc_local(*var)
                || self.rc_scopes.is_union_rc_local(*var))
        {
            return Some(*var);
        }
        None
    }

    /// Pick a unique array-like variant from a union return type.
    ///
    /// Used to compile array literals in `return` statements with an expected
    /// target type when VIR expression metadata is degraded.
    pub(crate) fn preferred_array_like_union_variant(
        &self,
        union_type_id: TypeId,
    ) -> Option<TypeId> {
        let variants = self.arena().unwrap_union(union_type_id)?;
        let mut it = variants.iter().copied().filter(|&variant| {
            self.arena().is_array(variant)
                || self.arena().unwrap_tuple(variant).is_some()
                || self.arena().unwrap_fixed_array(variant).is_some()
        });
        let first = it.next()?;
        if it.next().is_some() {
            None
        } else {
            Some(first)
        }
    }

    /// Emit the actual return instruction, handling all return conventions.
    ///
    /// Dispatches on the pre-computed `ReturnConvention` from VIR lowering
    /// instead of querying the type arena at compile time.  The `return_type_id`
    /// is still needed for type-specific operations (vtable generation, union
    /// wrapping, struct layout) but the dispatch decision itself is read from
    /// the convention.
    fn emit_return_value(
        &mut self,
        compiled: CompiledValue,
        return_type_id: Option<TypeId>,
        convention: vole_vir::stmt::ReturnConvention,
    ) -> CodegenResult<()> {
        use vole_vir::stmt::ReturnConvention;

        // Resolve Unresolved conventions at codegen time.  This handles
        // sema-monomorphized methods whose return type contains type parameters
        // that sema couldn't fully substitute during VIR lowering.
        let convention = if convention == ReturnConvention::Unresolved {
            if let Some(ret_type_id) = return_type_id {
                if self.vir_query_is_interface(ret_type_id) {
                    ReturnConvention::InterfaceBox
                } else if self.vir_query_is_unknown(ret_type_id) {
                    ReturnConvention::UnknownBox
                } else if self.vir_query_is_fallible(ret_type_id) {
                    if self.vir_query_is_wide_fallible(ret_type_id) {
                        ReturnConvention::WideFallible
                    } else {
                        ReturnConvention::Fallible
                    }
                } else if self.vir_query_is_struct(ret_type_id) {
                    ReturnConvention::Struct
                } else if self.vir_query_is_union(ret_type_id) {
                    ReturnConvention::Union
                } else if self.arena().is_void(ret_type_id) {
                    ReturnConvention::Void
                } else {
                    ReturnConvention::Scalar
                }
            } else {
                ReturnConvention::Void
            }
        } else {
            convention
        };

        match convention {
            ReturnConvention::Void => {
                self.builder.ins().return_(&[]);
            }
            ReturnConvention::InterfaceBox => {
                // NOTE: box_interface_value requires sema TypeId for vtable generation.
                let ret_type_id =
                    return_type_id.expect("InterfaceBox convention requires return type");
                if !self.vir_query_is_interface(compiled.type_id)
                    && !self.arena().is_runtime_iterator(compiled.type_id)
                {
                    let boxed = self.box_interface_value(compiled, ret_type_id)?;
                    self.builder.ins().return_(&[boxed.value]);
                } else {
                    // Already an interface value — return directly.
                    self.builder.ins().return_(&[compiled.value]);
                }
            }
            ReturnConvention::UnknownBox => {
                if !self.vir_query_is_unknown(compiled.type_id) {
                    let boxed = self.box_to_unknown_no_inc(compiled)?;
                    self.builder.ins().return_(&[boxed.value]);
                } else {
                    // Already unknown — return directly.
                    self.builder.ins().return_(&[compiled.value]);
                }
            }
            ReturnConvention::Fallible => {
                let tag_val = self.iconst_cached(types::I64, FALLIBLE_SUCCESS_TAG);
                let payload_val = convert_to_i64_for_storage(self.builder, &compiled);
                self.builder.ins().return_(&[tag_val, payload_val]);
            }
            ReturnConvention::WideFallible => {
                let tag_val = self.iconst_cached(types::I64, FALLIBLE_SUCCESS_TAG);
                let (low, high) = split_i128_for_storage(self.builder, compiled.value);
                self.builder.ins().return_(&[tag_val, low, high]);
            }
            ReturnConvention::Struct => {
                let ret_type_id = return_type_id.expect("Struct convention requires return type");
                if self.is_small_struct_return(ret_type_id) {
                    self.emit_small_struct_return(compiled.value, ret_type_id)?;
                } else {
                    self.emit_sret_struct_return(compiled.value, ret_type_id)?;
                }
            }
            ReturnConvention::Union => {
                let ret_type_id = return_type_id.expect("Union convention requires return type");
                let wrapped = self.construct_union_id(compiled, ret_type_id)?;
                self.builder.ins().return_(&[wrapped.value]);
            }
            ReturnConvention::Scalar => {
                // Plain value return (with type conversion if needed).
                // NOTE: convert_to_type requires arena for detailed type inspection.
                // This is a boundary case retained until CompiledValue carries VirTypeId.
                let return_value = if let Some(ret_type_id) = return_type_id {
                    let target_ty = self.cranelift_type(ret_type_id);
                    convert_to_type(self.builder, compiled, target_ty, self.arena())
                } else {
                    compiled.value
                };
                self.builder.ins().return_(&[return_value]);
            }
            ReturnConvention::Unresolved => {
                unreachable!("Unresolved convention should have been resolved above");
            }
        }
        Ok(())
    }

    /// Compile a VIR break statement.
    ///
    /// Cleans up RC locals from inner loop scopes, then jumps to the
    /// loop exit block.
    fn compile_vir_break(&mut self) -> CodegenResult<bool> {
        if let Some(exit_block) = self.cf.loop_exit() {
            if let Some(depth) = self.cf.loop_rc_depth() {
                self.emit_rc_cleanup_from_depth(depth)?;
            }
            self.builder.ins().jump(exit_block, &[]);
        }
        Ok(true)
    }

    /// Compile a VIR continue statement.
    ///
    /// Cleans up RC locals from inner loop scopes, then jumps to the
    /// loop continue block. Creates an unreachable continuation block
    /// so Cranelift does not complain about subsequent dead code.
    fn compile_vir_continue(&mut self) -> CodegenResult<bool> {
        if let Some(continue_block) = self.cf.loop_continue() {
            if let Some(depth) = self.cf.loop_rc_depth() {
                self.emit_rc_cleanup_from_depth(depth)?;
            }
            self.builder.ins().jump(continue_block, &[]);
            let unreachable = self.builder.create_block();
            self.switch_to_block(unreachable);
            self.builder.seal_block(unreachable);
        }
        Ok(true)
    }

    /// Compile a VIR while loop.
    ///
    /// Creates header/body/exit blocks, compiles the condition and body using
    /// VIR compilation methods.  Mirrors the existing `Stmt::While` handling
    /// in `stmt()`.
    fn compile_vir_while(
        &mut self,
        cond: &vole_vir::VirExpr,
        body: &vole_vir::VirBody,
    ) -> CodegenResult<bool> {
        let header_block = self.builder.create_block();
        let body_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header_block, &[]);

        self.switch_to_block(header_block);
        let condition = self.compile_vir_expr(cond)?;
        self.emit_brif(condition.value, body_block, exit_block);

        self.switch_to_block(body_block);
        self.compile_vir_loop_body(body, exit_block, header_block)?;

        self.switch_to_block(exit_block);

        self.builder.seal_block(header_block);
        self.builder.seal_block(body_block);

        Ok(false)
    }

    /// Compile a VIR raise statement: `raise ErrorName { field: value, ... }`.
    ///
    /// Uses multi-value return `(tag, payload)`:
    /// - Tag: error tag (1+) from `fallible_error_tag_by_id`
    /// - Payload: 0 for no fields, inline for a single non-wide field,
    ///   or a stack pointer for multiple / wide fields.
    ///
    /// Mirrors [`raise_stmt`] + [`build_raise_payload`] but reads from
    /// VIR nodes instead of AST.
    fn compile_vir_raise(
        &mut self,
        error_name: Symbol,
        fields: &[(Symbol, vole_vir::refs::VirRef)],
    ) -> CodegenResult<bool> {
        let return_type_id = self.return_type.ok_or_else(|| {
            CodegenError::internal(
                "raise statement used outside of a function with declared return type",
            )
        })?;

        // NOTE: arena() retained — error_tag_for/resolve_raise_error_type_def
        // require sema TypeId.  Remove when error dispatch uses VirTypeId (Phase D).
        let (_success_type_id, error_type_id) = self
            .arena()
            .unwrap_fallible(return_type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "raise statement",
                    "fallible return type",
                    "non-fallible type",
                )
            })?;

        let error_tag = self
            .error_tag_for(error_type_id, error_name)
            .ok_or_else(|| {
                CodegenError::not_found("error type", self.interner().resolve(error_name))
            })?;

        let error_type_def_id = self.resolve_raise_error_type_def(error_type_id, error_name)?;

        let error_fields: Vec<_> = self
            .analyzed()
            .fields_on_type(error_type_def_id)
            .map(|field_id| {
                let field = self.analyzed().field_def(field_id);
                RaiseFieldLayout {
                    name_id: field.name_id,
                    ty: field.sema_type_id,
                }
            })
            .collect();

        let tag_val = self.iconst_cached(types::I64, error_tag);

        let payload_val = self.build_vir_raise_payload(&error_fields, fields)?;

        self.emit_rc_cleanup_all_scopes(None)?;

        if self.vir_query_is_wide_fallible(return_type_id) {
            let zero = self.iconst_cached(types::I64, 0);
            self.builder.ins().return_(&[tag_val, payload_val, zero]);
        } else {
            self.builder.ins().return_(&[tag_val, payload_val]);
        }

        Ok(true)
    }

    /// Build the error payload value for a VIR raise statement.
    ///
    /// Layout matches the runtime convention:
    /// - 0 fields: payload is 0
    /// - 1 field (non-wide): payload is the field value directly (inline)
    /// - 1 field (i128): payload is a pointer to stack-allocated i128 data
    /// - 2+ fields: payload is a pointer to field data
    ///
    /// Mirrors [`build_raise_payload`] but compiles field values from VIR
    /// expressions instead of AST expressions.
    fn build_vir_raise_payload(
        &mut self,
        error_fields: &[RaiseFieldLayout],
        raise_fields: &[(Symbol, vole_vir::refs::VirRef)],
    ) -> CodegenResult<Value> {
        if error_fields.is_empty() {
            return Ok(self.iconst_cached(types::I64, 0));
        }

        if error_fields.len() == 1 && !self.vir_query_is_wide(error_fields[0].ty) {
            let field_def = &error_fields[0];
            let field_name = self
                .name_table()
                .last_segment_str(field_def.name_id)
                .unwrap_or_default();
            let field_init = raise_fields
                .iter()
                .find(|(name, _)| self.interner().resolve(*name) == field_name)
                .ok_or_else(|| CodegenError::not_found("raise field", &field_name))?;

            let mut field_value = self.compile_vir_expr(&field_init.1)?;
            if self.rc_state(field_value.type_id).needs_cleanup() && field_value.is_borrowed() {
                self.emit_rc_inc_for_type(field_value.value, field_value.type_id)?;
            }
            field_value.mark_consumed();
            field_value.debug_assert_rc_handled("VirStmt::Raise (single field)");
            return Ok(convert_to_i64_for_storage(self.builder, &field_value));
        }

        // Multiple fields (or single i128 field) — heap-allocate payload.
        let error_payload_size: u32 = error_fields
            .iter()
            .map(|f| self.vir_query_field_byte_size(f.ty))
            .sum();
        let slot = self.alloc_stack(error_payload_size);

        let mut field_offset: i32 = 0;
        for field_def in error_fields {
            let field_name = self
                .name_table()
                .last_segment_str(field_def.name_id)
                .unwrap_or_default();
            let field_init = raise_fields
                .iter()
                .find(|(name, _)| self.interner().resolve(*name) == field_name)
                .ok_or_else(|| CodegenError::not_found("raise field", &field_name))?;

            let mut field_value = self.compile_vir_expr(&field_init.1)?;
            if self.rc_state(field_value.type_id).needs_cleanup() && field_value.is_borrowed() {
                self.emit_rc_inc_for_type(field_value.value, field_value.type_id)?;
            }
            field_value.mark_consumed();
            field_value.debug_assert_rc_handled("VirStmt::Raise (multi field)");
            let bytes_stored = store_value_to_stack(self.builder, &field_value, slot, field_offset);
            field_offset += bytes_stored;
        }

        let ptr_type = self.ptr_type();
        Ok(self.builder.ins().stack_addr(ptr_type, slot, 0))
    }

    /// Compile a VIR let binding: `let x = <init>`.
    ///
    /// Mirrors [`let_stmt`] but reads from VIR nodes instead of AST+NodeMap.
    /// The initializer is compiled through `compile_vir_expr`, then coerced
    /// to the declared type, and the variable is registered with RC tracking.
    fn compile_vir_let(
        &mut self,
        name: Symbol,
        value_expr: &vole_vir::VirExpr,
        binding_ty: TypeId,
        storage: LetStorageHint,
        declared_type: Option<TypeId>,
    ) -> CodegenResult<bool> {
        // Pre-register recursive lambdas so they can capture themselves.
        let preregistered_var = self.preregister_recursive_vir_lambda(name, value_expr);
        if preregistered_var.is_some() {
            self.self_capture = Some(name);
        }

        let declared_type_id_opt =
            self.vir_let_declared_type(value_expr, binding_ty, declared_type);

        let init = if let Some(declared_type_id) = declared_type_id_opt {
            self.compile_vir_let_init_with_declared_type(value_expr, declared_type_id)?
        } else {
            self.compile_vir_expr(value_expr)?
        };
        self.self_capture = None;

        // Struct copy: when binding a struct value, copy to a new stack slot
        // to maintain value semantics (structs are stack-allocated value types).
        let mut init = if self.vir_query_is_struct(init.type_id) {
            self.copy_struct_value(init)?
        } else {
            init
        };

        let sentinel_hint_type_id = self.sentinel_hint_type_id_from_vir_expr(value_expr);
        let (final_value, final_type_id, is_stack_union) =
            self.coerce_let_init(&init, declared_type_id_opt, sentinel_hint_type_id, storage)?;

        // Use preregistered var for recursive lambdas, otherwise declare new.
        let var = if let Some(var) = preregistered_var {
            self.builder.def_var(var, final_value);
            var
        } else {
            let cranelift_ty = self.cranelift_type(final_type_id);
            let actual_ty = self.builder.func.dfg.value_type(final_value);
            if cranelift_ty != actual_ty {
                return Err(CodegenError::internal_with_context(
                    "VIR let type mismatch",
                    format!(
                        "name={} binding_ty={binding_ty:?} init_ty={:?} final_type={final_type_id:?} declared={declared_type_id_opt:?} cranelift={cranelift_ty:?} actual={actual_ty:?} expr={value_expr:?}",
                        self.interner().resolve(name),
                        init.type_id,
                    ),
                ));
            }
            let var = self.builder.declare_var(cranelift_ty);
            self.builder.def_var(var, final_value);
            self.vars.insert(name, (var, final_type_id));
            var
        };

        // RC bookkeeping — identical to old let_stmt path.
        self.register_vir_let_rc(
            var,
            &init,
            value_expr,
            final_value,
            final_type_id,
            is_stack_union,
        )?;

        init.mark_consumed();
        init.debug_assert_rc_handled("VirStmt::Let");
        Ok(false)
    }

    /// Compile a VIR let initializer with a declared binding type hint.
    ///
    /// TEMP(N279-C): when VIR expression type IDs degrade to `unknown`, use the
    /// declared let-binding type to keep array/repeat literal element lowering
    /// coherent with the binding's concrete type.
    fn compile_vir_let_init_with_declared_type(
        &mut self,
        value_expr: &vole_vir::VirExpr,
        declared_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.compile_vir_expr_with_expected_type(value_expr, declared_type_id)
    }

    /// Compile a VIR let-tuple destructuring statement.
    ///
    /// Compiles the init expression, registers composite RC cleanup for
    /// owned temporaries, then delegates to `compile_vir_destructure_pattern`
    /// which handles tuple, fixed-array, record, module, and nested patterns.
    fn compile_vir_let_tuple(
        &mut self,
        pattern: &vole_vir::VirDestructurePattern,
        value_expr: &vole_vir::VirExpr,
    ) -> CodegenResult<bool> {
        let mut init = self.compile_vir_expr(value_expr)?;
        let is_borrow = init.is_borrowed();

        // Register composite RC cleanup for owned temporaries.
        if self.rc_scopes.has_active_scope()
            && !is_borrow
            && let Some(offsets) = self.rc_state(init.type_id).shallow_offsets()
        {
            let cr_type = self.cranelift_type(init.type_id);
            let temp_var = self.builder.declare_var(cr_type);
            self.builder.def_var(temp_var, init.value);
            let union_fields = self
                .rc_state(init.type_id)
                .composite_union_fields()
                .to_vec();
            let drop_flag =
                self.register_composite_rc_local(temp_var, offsets.to_vec(), union_fields);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        }

        self.compile_vir_destructure_pattern(pattern, init.value)?;
        init.mark_consumed();
        init.debug_assert_rc_handled("VirStmt::LetTuple");
        Ok(false)
    }

    /// Recursively compile a VIR destructuring pattern, binding variables
    /// for the values extracted from tuples, fixed arrays, records, and
    /// modules.
    ///
    /// Mirrors `compile_destructure_pattern` but reads from VIR-native
    /// `VirDestructurePattern` nodes instead of AST `PatternKind` nodes.
    /// All type/field information has been pre-resolved during lowering.
    fn compile_vir_destructure_pattern(
        &mut self,
        pattern: &vole_vir::VirDestructurePattern,
        value: Value,
    ) -> CodegenResult<()> {
        use vole_vir::VirDestructurePattern;
        match pattern {
            VirDestructurePattern::Bind { name, ty, .. } => {
                self.compile_vir_destructure_bind(*name, self.sema_type_from_vir(*ty), value)?;
            }
            VirDestructurePattern::Wildcard => {}
            VirDestructurePattern::Tuple { elements, kind } => {
                self.compile_vir_destructure_tuple(elements, *kind, value)?;
            }
            VirDestructurePattern::Record {
                fields,
                source_ty,
                is_struct,
                ..
            } => {
                self.compile_vir_destructure_record(
                    fields,
                    value,
                    self.sema_type_from_vir(*source_ty),
                    *is_struct,
                )?;
            }
            VirDestructurePattern::Module {
                bindings,
                module_id,
            } => {
                self.compile_vir_destructure_module(bindings, *module_id)?;
            }
        }
        Ok(())
    }

    /// Compile a binding in a destructure pattern.
    ///
    /// Declares a Cranelift variable, registers RC tracking if needed.
    fn compile_vir_destructure_bind(
        &mut self,
        name: Symbol,
        ty: TypeId,
        value: Value,
    ) -> CodegenResult<()> {
        let cr_type = self.cranelift_type(ty);
        let var = self.builder.declare_var(cr_type);
        self.builder.def_var(var, value);
        self.vars.insert(name, (var, ty));

        // Extracted elements borrow from the parent composite.
        // RC_inc + register so scope-exit dec balances the borrow.
        if self.rc_scopes.has_active_scope() && self.rc_state(ty).needs_cleanup() {
            self.emit_rc_inc_for_type(value, ty)?;
            let drop_flag = self.register_rc_local(var, ty);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        }
        Ok(())
    }

    /// Compile a tuple or fixed-array destructure pattern.
    ///
    /// Uses pre-resolved element types; computes byte offsets via
    /// `tuple_layout()` or element size arithmetic at codegen time.
    fn compile_vir_destructure_tuple(
        &mut self,
        elements: &[vole_vir::VirDestructureElement],
        kind: vole_vir::DestructureTupleKind,
        value: Value,
    ) -> CodegenResult<()> {
        match kind {
            vole_vir::DestructureTupleKind::Tuple => {
                // True tuple: compute layout from element types.
                let elem_type_ids: Vec<TypeId> = elements
                    .iter()
                    .map(|e| self.sema_type_from_vir(e.ty))
                    .collect();
                let (_, offsets) = self.tuple_layout(&elem_type_ids);
                for (i, elem) in elements.iter().enumerate() {
                    let offset = offsets[i];
                    let elem_ty = self.sema_type_from_vir(elem.ty);
                    let elem_cr_type = self.cranelift_type(elem_ty);
                    let elem_value =
                        self.builder
                            .ins()
                            .load(elem_cr_type, MemFlags::new(), value, offset);
                    self.compile_vir_destructure_pattern(&elem.pattern, elem_value)?;
                }
            }
            vole_vir::DestructureTupleKind::FixedArray { elem_ty, .. } => {
                // Fixed array: all elements have the same type and size.
                let elem_ty = self.sema_type_from_vir(elem_ty);
                let elem_cr_type = self.cranelift_type(elem_ty);
                let elem_size = self.type_size(elem_ty).div_ceil(8) * 8;
                for (i, elem) in elements.iter().enumerate() {
                    let offset = (i as i32) * (elem_size as i32);
                    let elem_value =
                        self.builder
                            .ins()
                            .load(elem_cr_type, MemFlags::new(), value, offset);
                    self.compile_vir_destructure_pattern(&elem.pattern, elem_value)?;
                }
            }
        }
        Ok(())
    }

    /// Compile a record (struct/class) destructure pattern.
    ///
    /// Uses pre-resolved field slots and types from lowering.
    fn compile_vir_destructure_record(
        &mut self,
        fields: &[vole_vir::VirDestructureField],
        value: Value,
        source_ty: TypeId,
        is_struct: bool,
    ) -> CodegenResult<()> {
        for field in fields {
            let field_ty = self.sema_type_from_vir(field.ty);
            let converted = if is_struct {
                // Structs are stack-allocated: load field directly from pointer + offset
                self.struct_field_load(value, field.slot as usize, field_ty, source_ty)?
            } else {
                // Classes are heap-allocated: use runtime field access
                self.get_instance_field(value, field.slot as usize, field_ty)?
            };

            let var = self.builder.declare_var(converted.ty);
            self.builder.def_var(var, converted.value);
            self.vars.insert(field.binding, (var, field_ty));
        }
        Ok(())
    }

    /// Compile a module destructure pattern.
    ///
    /// Module bindings are compile-time only — registers bindings in
    /// `local_module_bindings` for use by subsequent call compilation.
    /// No runtime code is generated.
    fn compile_vir_destructure_module(
        &mut self,
        bindings: &[vole_vir::VirModuleBinding],
        module_id: vole_identity::ModuleId,
    ) -> CodegenResult<()> {
        for binding in bindings {
            self.local_module_bindings.insert(
                binding.binding,
                (
                    module_id,
                    binding.export_name,
                    self.sema_type_from_vir(binding.export_ty),
                ),
            );
        }
        Ok(())
    }

    /// Pre-register a recursive lambda binding from a VIR init expression.
    ///
    /// For recursive lambdas (lambdas that capture themselves), we need
    /// the binding in `vars` before compiling so capture bindings get the
    /// correct type.  Returns `Some(var)` if pre-registered, `None` otherwise.
    fn preregister_recursive_vir_lambda(
        &mut self,
        name: Symbol,
        value_expr: &vole_vir::VirExpr,
    ) -> Option<Variable> {
        // VIR lambdas already carry captures — check directly.
        if let vole_vir::VirExpr::Lambda { captures, ty, .. } = value_expr {
            let has_self_capture = captures.iter().any(|c| c.name == name);
            if !has_self_capture {
                return None;
            }
            let sema_ty = self.sema_type_from_vir(*ty);
            let cranelift_ty = self.cranelift_type(sema_ty);
            let var = self.builder.declare_var(cranelift_ty);
            self.vars.insert(name, (var, sema_ty));
            return Some(var);
        }
        None
    }

    /// Determine the declared type for a VIR let binding.
    ///
    /// The lowering phase encodes the declared type (or inferred type)
    /// as `binding_ty`.  We pass this as the declared type to
    /// `coerce_let_init`, which is a no-op when the declared type
    /// matches the init value type at the Cranelift level.
    /// We must include `TypeId::UNKNOWN` (the Vole `unknown` type) since
    /// it triggers `box_to_unknown` in `coerce_let_init` when the init
    /// value is a concrete type.
    fn vir_let_declared_type(
        &self,
        value_expr: &vole_vir::VirExpr,
        binding_ty: TypeId,
        declared_type: Option<TypeId>,
    ) -> Option<TypeId> {
        // For MethodCall inits, use the VIR-carried declared type annotation.
        // Method calls may have codegen-computed return types that differ from
        // the sema expression type (e.g. sum() on Iterator<[i64]> returns i64
        // at runtime but sema records [i64]). Using the declared type returns
        // Some(annotated_type) for typed lets, None for untyped lets, which
        // lets coerce_let_init use init.type_id (the codegen-computed type).
        if matches!(value_expr, vole_vir::VirExpr::MethodCall { .. }) {
            return declared_type;
        }
        // For pure VIR inits: always pass binding_ty as declared type.
        Some(binding_ty)
    }

    /// Extract sentinel type hint from a VIR let initializer, if present.
    fn sentinel_hint_type_id_from_vir_expr(&self, expr: &vole_vir::VirExpr) -> Option<TypeId> {
        match expr {
            vole_vir::VirExpr::LocalLoad { name, .. } => self.sentinel_type_id_for_symbol(*name),
            _ => None,
        }
    }

    /// Resolve a symbol to a sentinel base `TypeId` in the current module context.
    fn sentinel_type_id_for_symbol(&self, sym: Symbol) -> Option<TypeId> {
        let name = self.interner().resolve(sym);
        let module_id = self.current_module.unwrap_or(self.env.analyzed.module_id());
        let type_def_id = self.analyzed().resolve_type_def_by_str(module_id, name)?;
        self.analyzed().sentinel_base_type(type_def_id)
    }

    /// Register RC tracking for a newly compiled VIR let binding.
    ///
    /// Handles: unknown boxing detection, direct RC inc for borrows,
    /// composite RC tracking for structs/tuples with RC fields, and
    /// union RC tracking.
    ///
    /// Mirrors the RC bookkeeping section of [`let_stmt`].
    fn register_vir_let_rc(
        &mut self,
        var: Variable,
        init: &CompiledValue,
        value_expr: &vole_vir::VirExpr,
        final_value: Value,
        final_type_id: TypeId,
        is_stack_union: bool,
    ) -> CodegenResult<()> {
        // Detect whether coerce_let_init called box_to_unknown (new TaggedValue).
        let created_tagged_value =
            self.vir_query_is_unknown(final_type_id) && !self.vir_query_is_unknown(init.type_id);

        if self.rc_scopes.has_active_scope() && created_tagged_value {
            let drop_flag = self.register_rc_local(var, final_type_id);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        } else if self.rc_scopes.has_active_scope()
            && final_type_id == TypeId::UNKNOWN
            && init.type_id == TypeId::UNKNOWN
            && matches!(value_expr, vole_vir::VirExpr::ArrayLiteral { .. })
        {
            // TEMP(N279-C): mixed VIR/sema metadata can degrade array-literal
            // let bindings to UNKNOWN while still carrying raw array pointers
            // (not boxed TaggedValue unknown). Register generic RC cleanup so
            // scope-exit emits rc_dec and array element closures are released.
            let drop_flag = self.register_rc_local(var, TypeId::HANDLE);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        } else if self.rc_scopes.has_active_scope() && self.rc_state(final_type_id).needs_cleanup()
        {
            let is_borrow = init.is_borrowed();
            if self.cf.in_loop() && is_borrow {
                // Borrow inside loop: skip inc and RC registration.
            } else {
                if is_borrow {
                    self.emit_rc_inc_for_type(final_value, final_type_id)?;
                }
                let drop_flag = self.register_rc_local(var, final_type_id);
                crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
            }
        } else if self.rc_scopes.has_active_scope() {
            self.register_vir_let_composite_rc(var, init, value_expr, final_value, final_type_id)?;
            self.register_vir_let_union_rc(var, init, final_value, final_type_id, is_stack_union)?;
        }
        Ok(())
    }

    /// Register composite RC tracking for struct/tuple fields with RC content.
    ///
    /// Detects struct copies (let b = a) and increments each RC field so
    /// both the original and the copy own their references.
    fn register_vir_let_composite_rc(
        &mut self,
        var: Variable,
        _init: &CompiledValue,
        value_expr: &vole_vir::VirExpr,
        final_value: Value,
        final_type_id: TypeId,
    ) -> CodegenResult<()> {
        let rc_state = self.rc_state(final_type_id);
        let Some(offsets) = rc_state.shallow_offsets() else {
            return Ok(());
        };
        let offsets = offsets.to_vec();
        let union_fields = rc_state.composite_union_fields().to_vec();

        // Detect struct copy: init is a variable that is already tracked as a
        // composite RC local.
        #[allow(clippy::wildcard_enum_match_arm)] // predicate query, not dispatch
        let is_struct_copy = match value_expr {
            vole_vir::VirExpr::LocalLoad { name, .. } => self
                .vars
                .get(name)
                .is_some_and(|&(v, _)| self.rc_scopes.is_composite_rc_local(v)),
            _ => false,
        };

        if is_struct_copy {
            for &off in &offsets {
                let field_ptr =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), final_value, off);
                self.emit_rc_inc(field_ptr)?;
            }
        }

        let drop_flag = self.register_composite_rc_local(var, offsets, union_fields);
        crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        Ok(())
    }

    /// Register union RC tracking for union-typed let bindings.
    fn register_vir_let_union_rc(
        &mut self,
        var: Variable,
        init: &CompiledValue,
        final_value: Value,
        final_type_id: TypeId,
        is_stack_union: bool,
    ) -> CodegenResult<()> {
        if !(is_stack_union || self.vir_query_is_union(final_type_id)) {
            return Ok(());
        }
        // Already handled by composite RC path.
        if self.rc_state(final_type_id).shallow_offsets().is_some() {
            return Ok(());
        }
        let rc_state = self.rc_state(final_type_id);
        let Some(rc_tags) = rc_state.union_variants() else {
            return Ok(());
        };
        let rc_tags = rc_tags.to_vec();
        if init.is_borrowed() {
            // Use final_value (the union stack slot pointer), NOT init.value.
            // emit_union_rc_inc reads the tag from the union layout to decide
            // whether the payload needs rc_inc.
            self.emit_union_rc_inc(final_value, &rc_tags)?;
        }
        let drop_flag = self.register_union_rc_local(var, rc_tags);
        crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        Ok(())
    }

    /// Compile a VIR assignment statement.
    ///
    /// Routes to the appropriate handler based on the assignment target:
    /// - Local: delegates to `compile_local_store` (existing VIR expression handler)
    /// - Field/Index: currently unsupported (lowering does not yet emit these)
    fn compile_vir_assign(
        &mut self,
        target: &vole_vir::AssignTarget,
        value: &vole_vir::VirExpr,
    ) -> CodegenResult<bool> {
        match target {
            vole_vir::AssignTarget::Local(sym) => {
                let mut result = self.compile_local_store(*sym, value)?;
                result.mark_consumed();
                result.debug_assert_rc_handled("VirStmt::Assign(Local)");
                Ok(false)
            }
            vole_vir::AssignTarget::Field { .. } | vole_vir::AssignTarget::Index { .. } => Err(
                CodegenError::internal("VirStmt::Assign with Field/Index target not yet lowered"),
            ),
        }
    }
}
