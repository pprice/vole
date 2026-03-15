use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use super::monomorph_functions::body_has_sema_data;
use crate::LoweringEntityLookup;
use crate::implement_registry::ImplementRegistry;
use crate::vir_lower::type_translate::translate_type_id;
use crate::vir_lower::{CrossModuleCtx, lower_interface_method, lower_method};
use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{MethodId, ModuleId, NameId, NameTable, Span};
use vole_log::compile_timed;
use vole_vir::VirFunction;
use vole_vir::func::ReturnAbi;
use vole_vir::monomorph::rewrite::{RewriteCtx, rewrite_function};
use vole_vir::monomorph::substitute::{TypeSubstitution, substitute_types};
use vole_vir::type_table::VirTypeTable;

/// Shared references used while lowering class/static method monomorphs to VIR.
pub struct MethodMonomorphLoweringCtx<'a> {
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub modules_with_errors: &'a HashSet<String>,
    pub cross_module: &'a CrossModuleCtx,
    pub implements: &'a ImplementRegistry,
}

/// Mutable state used while lowering class/static method monomorphs to VIR.
pub struct MethodMonomorphLoweringWork<'a> {
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    pub module_id: ModuleId,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

/// Lower class/static method monomorph cache entries into VIR.
#[compile_timed(DEBUG)]
pub fn lower_type_method_monomorphized_instances(
    work: &mut MethodMonomorphLoweringWork<'_>,
    ctx: &MethodMonomorphLoweringCtx<'_>,
) {
    lower_class_method_monomorphized_instances(work, ctx);
    lower_static_method_monomorphized_instances(work, ctx);
}

/// Lower all class method monomorph instances into VIR.
///
/// Includes abstract templates (TypeParam substitutions) so expanded abstract
/// class method monomorph compilation can reuse their VIR bodies with concrete
/// substitutions.
fn lower_class_method_monomorphized_instances(
    work: &mut MethodMonomorphLoweringWork<'_>,
    ctx: &MethodMonomorphLoweringCtx<'_>,
) {
    let instances = ctx.entities.class_method_monomorph_instances();
    for instance in instances {
        // External methods are runtime calls and have no Vole body to lower.
        if instance.external_info.is_some() {
            continue;
        }

        let method_name = ctx.names.display(instance.method_name);

        if let Some(method) = find_class_method_in_decls(
            &work.program.declarations,
            instance.class_name,
            &method_name,
            work.module_id,
            work.interner,
            ctx.names,
            Some(work.tests_virtual_modules),
        ) {
            if let Some(vir) = lower_class_method_monomorph_vir(
                method,
                &instance,
                work.interner,
                ctx,
                work.type_table,
                work.module_id,
            ) {
                work.vir_functions.push(vir);
            }
            continue;
        }

        let source_module_id = ctx.names.module_of(instance.class_name);
        let source_module_path = ctx.names.module_path(source_module_id).to_string();
        if ctx.modules_with_errors.contains(&source_module_path) {
            continue;
        }
        let Some((module_program, module_interner)) =
            work.module_programs.get_mut(&source_module_path)
        else {
            continue;
        };

        if let Some(method) = find_class_method_in_decls(
            &module_program.declarations,
            instance.class_name,
            &method_name,
            source_module_id,
            module_interner.as_ref(),
            ctx.names,
            None,
        ) {
            let module_interner = Rc::make_mut(module_interner);
            if let Some(vir) = lower_class_method_monomorph_vir(
                method,
                &instance,
                module_interner,
                ctx,
                work.type_table,
                source_module_id,
            ) {
                work.vir_functions.push(vir);
            }
        }
    }
}

/// Lower all static method monomorph instances into VIR.
fn lower_static_method_monomorphized_instances(
    work: &mut MethodMonomorphLoweringWork<'_>,
    ctx: &MethodMonomorphLoweringCtx<'_>,
) {
    let instances = ctx.entities.static_method_monomorph_instances();
    for instance in instances {
        let method_name = ctx.names.display(instance.method_name);

        if let Some(method) = find_static_method_in_decls(
            &work.program.declarations,
            instance.class_name,
            &method_name,
            work.module_id,
            work.interner,
            ctx.names,
            Some(work.tests_virtual_modules),
        ) {
            if let Some(vir) = lower_static_method_monomorph_vir(
                method,
                &instance,
                work.interner,
                ctx,
                work.type_table,
                work.module_id,
            ) {
                work.vir_functions.push(vir);
            }
            continue;
        }

        let source_module_id = ctx.names.module_of(instance.class_name);
        let source_module_path = ctx.names.module_path(source_module_id).to_string();
        if ctx.modules_with_errors.contains(&source_module_path) {
            continue;
        }
        let Some((module_program, module_interner)) =
            work.module_programs.get_mut(&source_module_path)
        else {
            continue;
        };

        if let Some(method) = find_static_method_in_decls(
            &module_program.declarations,
            instance.class_name,
            &method_name,
            source_module_id,
            module_interner.as_ref(),
            ctx.names,
            None,
        ) {
            let module_interner = Rc::make_mut(module_interner);
            if let Some(vir) = lower_static_method_monomorph_vir(
                method,
                &instance,
                module_interner,
                ctx,
                work.type_table,
                source_module_id,
            ) {
                work.vir_functions.push(vir);
            }
        }
    }
}

/// Lower a single class method monomorph to a VIR function tagged by mangled name.
fn lower_class_method_monomorph_vir(
    method: &vole_frontend::FuncDecl,
    instance: &crate::generic::ClassMethodMonomorphInstance,
    interner: &mut Interner,
    ctx: &MethodMonomorphLoweringCtx<'_>,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
) -> Option<VirFunction> {
    if method.params.len() != instance.func_type.params_id.len() {
        return None;
    }
    if !body_has_sema_data(&method.body, ctx.node_map) {
        return None;
    }
    let param_types: Vec<_> = method
        .params
        .iter()
        .zip(instance.func_type.params_id.iter())
        .map(|(p, &ty)| (p.name, ty))
        .collect();
    let mut vir = lower_method(
        method,
        MethodId::new(0),
        ctx.names.display(instance.mangled_name),
        &param_types,
        instance.func_type.return_type_id,
        ctx.node_map,
        interner,
        ctx.type_arena,
        ctx.entities.as_entity_registry(),
        ctx.names,
        type_table,
        module_id,
        ctx.cross_module,
        ctx.implements,
    );
    // Monomorphized method instances are looked up via mangled name map, not MethodId.
    vir.method_id = None;
    vir.mangled_name_id = Some(instance.mangled_name);
    Some(vir)
}

/// Lower a single static method monomorph to a VIR function tagged by mangled name.
fn lower_static_method_monomorph_vir(
    method: &vole_frontend::ast::InterfaceMethod,
    instance: &crate::generic::StaticMethodMonomorphInstance,
    interner: &mut Interner,
    ctx: &MethodMonomorphLoweringCtx<'_>,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
) -> Option<VirFunction> {
    let body = method.body.as_ref()?;
    if method.params.len() != instance.func_type.params_id.len() {
        return None;
    }
    if !body_has_sema_data(body, ctx.node_map) {
        return None;
    }
    let param_types: Vec<_> = method
        .params
        .iter()
        .zip(instance.func_type.params_id.iter())
        .map(|(p, &ty)| (p.name, ty))
        .collect();
    let mut vir = lower_interface_method(
        method,
        MethodId::new(0),
        ctx.names.display(instance.mangled_name),
        &param_types,
        instance.func_type.return_type_id,
        ctx.node_map,
        interner,
        ctx.type_arena,
        ctx.entities.as_entity_registry(),
        ctx.names,
        type_table,
        module_id,
        ctx.cross_module,
        ctx.implements,
    )?;
    // Monomorphized method instances are looked up via mangled name map, not MethodId.
    vir.method_id = None;
    vir.mangled_name_id = Some(instance.mangled_name);
    Some(vir)
}

/// Lower implement-block default method monomorph instances into concrete VIR.
///
/// For each instance in `implement_method_monomorph_cache` (registered by sema
/// for each element_type × Iterable default method combination), looks up the
/// generic VIR template (lowered earlier by `lower_implement_default_methods`),
/// clones it with type substitutions applied (T → concrete element type), and
/// adds the concrete function to `vir_functions`.
pub fn lower_implement_method_monomorphized_instances(
    work: &mut MethodMonomorphLoweringWork<'_>,
    ctx: &MethodMonomorphLoweringCtx<'_>,
) {
    lower_implement_method_monomorphs(
        work.vir_functions,
        work.type_table,
        ctx.entities,
        ctx.type_arena,
        ctx.names,
    );
}

/// Core logic for lowering implement-block default method monomorph instances.
///
/// Separated from `lower_implement_method_monomorphized_instances` so it can
/// be called from the module phase (with only the dependencies it actually
/// needs) without constructing file-specific `MethodMonomorphLoweringWork`.
pub fn lower_implement_method_monomorphs(
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
    entities: &dyn LoweringEntityLookup,
    type_arena: &TypeArena,
    names: &NameTable,
) {
    let instances = entities.implement_method_monomorph_instances();
    if instances.is_empty() {
        return;
    }

    // Collect the unique method IDs we need templates for, then build a
    // MethodId → cloned VirFunction map. This avoids an O(n) linear scan
    // per instance when multiple element types share the same method.
    let needed: rustc_hash::FxHashSet<MethodId> = instances.iter().map(|i| i.method_id).collect();
    let template_by_method: FxHashMap<MethodId, VirFunction> = vir_functions
        .iter()
        .filter(|f| f.method_id.is_some_and(|id| needed.contains(&id)))
        .map(|f| (f.method_id.unwrap(), f.clone()))
        .collect();

    // Snapshot the type table so substitute_types can read from source
    // while writing new entries into the (mutable) work type table.
    let source_table = type_table.clone();
    let mut count = 0usize;

    for instance in &instances {
        let Some(template) = template_by_method.get(&instance.method_id) else {
            continue;
        };

        // Build VirTypeId substitution map from sema's NameId→TypeId map.
        let mut vir_subs: TypeSubstitution = FxHashMap::default();
        for (&name_id, &sema_type_id) in &instance.substitutions {
            let vir_ty = translate_type_id(type_table, sema_type_id, type_arena);
            vir_subs.insert(name_id, vir_ty);
        }

        // Apply type substitution and rewrite the function body.
        let type_map = substitute_types(&source_table, type_table, &vir_subs);
        let rewrite_ctx = RewriteCtx::new(type_map);
        let mut concrete = rewrite_function(template, &rewrite_ctx);

        // Recompute return ABI from the now-concrete return type.
        concrete.return_abi = ReturnAbi::classify(concrete.vir_return_type, type_table, None);

        // Tag with mangled name; clear method_id (looked up by mangled name).
        concrete.method_id = None;
        concrete.mangled_name_id = Some(instance.mangled_name);
        concrete.type_params = Vec::new();

        let mangled_str = names.display(instance.mangled_name);
        concrete.name = mangled_str.to_string();

        vir_functions.push(concrete);
        count += 1;
    }

    if count > 0 {
        tracing::debug!(count, "lowered implement method monomorph VIR functions");
    }
}

/// Find an instance method AST on a generic class/struct or matching implement block.
fn find_class_method_in_decls<'a>(
    decls: &'a [Decl],
    class_name_id: NameId,
    method_name: &str,
    module_id: ModuleId,
    interner: &Interner,
    names: &NameTable,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
) -> Option<&'a vole_frontend::FuncDecl> {
    for decl in decls {
        match decl {
            Decl::Class(class) if !class.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[class.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(method) = class
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Struct(s) if !s.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[s.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(method) = s
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Implement(impl_block) => {
                use vole_frontend::TypeExprKind;
                let target_sym = match &impl_block.target_type.kind {
                    TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                        Some(*sym)
                    }
                    _ => None,
                };
                let Some(target_sym) = target_sym else {
                    continue;
                };
                let Some(target_name_id) = names.name_id(module_id, &[target_sym], interner) else {
                    continue;
                };
                if target_name_id == class_name_id
                    && let Some(method) = impl_block
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                if let Some(method) = find_class_method_in_decls(
                    &tests_decl.decls,
                    class_name_id,
                    method_name,
                    tests_module_id,
                    interner,
                    names,
                    tests_virtual_modules,
                ) {
                    return Some(method);
                }
                if tests_module_id != module_id
                    && let Some(method) = find_class_method_in_decls(
                        &tests_decl.decls,
                        class_name_id,
                        method_name,
                        module_id,
                        interner,
                        names,
                        tests_virtual_modules,
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

/// Find a static method AST on a generic class/struct.
fn find_static_method_in_decls<'a>(
    decls: &'a [Decl],
    class_name_id: NameId,
    method_name: &str,
    module_id: ModuleId,
    interner: &Interner,
    names: &NameTable,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
) -> Option<&'a vole_frontend::ast::InterfaceMethod> {
    for decl in decls {
        match decl {
            Decl::Class(class) if !class.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[class.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(statics) = class.statics.as_ref()
                    && let Some(method) = statics
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Struct(s) if !s.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[s.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(statics) = s.statics.as_ref()
                    && let Some(method) = statics
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                if let Some(method) = find_static_method_in_decls(
                    &tests_decl.decls,
                    class_name_id,
                    method_name,
                    tests_module_id,
                    interner,
                    names,
                    tests_virtual_modules,
                ) {
                    return Some(method);
                }
            }
            _ => {}
        }
    }
    None
}
