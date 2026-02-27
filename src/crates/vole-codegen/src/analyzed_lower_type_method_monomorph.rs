use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::analyzed_lower_monomorph_functions::body_has_sema_data;
use crate::analyzed_lowering_lookup::LoweringEntityLookup;
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{MethodId, ModuleId, NameId, NameTable, Span};
use vole_sema::vir_lower::{lower_interface_method, lower_method};
use vole_sema::{NodeMap, TypeArena};
use vole_vir::VirFunction;
use vole_vir::type_table::VirTypeTable;

/// Shared references used while lowering class/static method monomorphs to VIR.
pub(crate) struct MethodMonomorphLoweringCtx<'a> {
    pub names: &'a NameTable,
    pub entities: &'a dyn LoweringEntityLookup,
    pub type_arena: &'a TypeArena,
    pub node_map: &'a NodeMap,
    pub modules_with_errors: &'a HashSet<String>,
}

/// Mutable state used while lowering class/static method monomorphs to VIR.
pub(crate) struct MethodMonomorphLoweringWork<'a> {
    pub program: &'a Program,
    pub interner: &'a mut Interner,
    pub module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    pub tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    pub module_id: ModuleId,
    pub vir_functions: &'a mut Vec<VirFunction>,
    pub type_table: &'a mut VirTypeTable,
}

/// Lower class/static method monomorph cache entries into VIR.
pub(crate) fn lower_type_method_monomorphized_instances(
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
            ) {
                work.vir_functions.push(vir);
            }
        }
    }
}

/// Lower a single class method monomorph to a VIR function tagged by mangled name.
fn lower_class_method_monomorph_vir(
    method: &vole_frontend::FuncDecl,
    instance: &vole_sema::generic::ClassMethodMonomorphInstance,
    interner: &mut Interner,
    ctx: &MethodMonomorphLoweringCtx<'_>,
    type_table: &mut VirTypeTable,
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
    );
    // Monomorphized method instances are looked up via mangled name map, not MethodId.
    vir.method_id = None;
    vir.mangled_name_id = Some(instance.mangled_name);
    Some(vir)
}

/// Lower a single static method monomorph to a VIR function tagged by mangled name.
fn lower_static_method_monomorph_vir(
    method: &vole_frontend::ast::InterfaceMethod,
    instance: &vole_sema::generic::StaticMethodMonomorphInstance,
    interner: &mut Interner,
    ctx: &MethodMonomorphLoweringCtx<'_>,
    type_table: &mut VirTypeTable,
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
    )?;
    // Monomorphized method instances are looked up via mangled name map, not MethodId.
    vir.method_id = None;
    vir.mangled_name_id = Some(instance.mangled_name);
    Some(vir)
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
