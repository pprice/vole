//! Plan phase for generating declaration skeletons.
//!
//! The planner generates the structure of a synthetic codebase:
//! - Module hierarchy with import relationships
//! - Type declarations (classes, interfaces, errors)
//! - Function signatures
//! - Global variables
//!
//! This phase creates all names and type signatures without generating bodies,
//! enabling forward references in the fill phase.

use rand::Rng;

use crate::symbols::{
    ClassInfo, ErrorInfo, FieldInfo, FunctionInfo, GlobalInfo, ImplementBlockInfo, InterfaceInfo,
    MethodInfo, ModuleId, ParamInfo, PrimitiveType, SymbolId, SymbolKind, SymbolTable, TypeInfo,
    TypeParam,
};

/// Configuration for the planning phase.
#[derive(Debug, Clone)]
pub struct PlanConfig {
    /// Number of module layers (depth of import hierarchy).
    pub layers: usize,
    /// Number of modules per layer.
    pub modules_per_layer: usize,
    /// Number of classes per module (range).
    pub classes_per_module: (usize, usize),
    /// Number of interfaces per module (range).
    pub interfaces_per_module: (usize, usize),
    /// Number of errors per module (range).
    pub errors_per_module: (usize, usize),
    /// Number of functions per module (range).
    pub functions_per_module: (usize, usize),
    /// Number of globals per module (range).
    pub globals_per_module: (usize, usize),
    /// Number of fields per class (range).
    pub fields_per_class: (usize, usize),
    /// Number of methods per class (range).
    pub methods_per_class: (usize, usize),
    /// Number of methods per interface (range).
    pub methods_per_interface: (usize, usize),
    /// Number of fields per error (range).
    pub fields_per_error: (usize, usize),
    /// Number of parameters per function (range).
    pub params_per_function: (usize, usize),
    /// Number of type parameters per generic class (range).
    pub type_params_per_class: (usize, usize),
    /// Number of type parameters per generic interface (range).
    pub type_params_per_interface: (usize, usize),
    /// Number of type parameters per generic function (range).
    pub type_params_per_function: (usize, usize),
    /// Number of constraints per type parameter (range).
    pub constraints_per_type_param: (usize, usize),
    /// Probability (0.0-1.0) that an interface extends another.
    pub interface_extends_probability: f64,
    /// Number of implement blocks per module (range).
    pub implement_blocks_per_module: (usize, usize),
    /// Probability (0.0-1.0) for cross-layer imports (not just adjacent layer).
    pub cross_layer_import_probability: f64,
    /// Enable diamond dependency patterns in imports.
    pub enable_diamond_dependencies: bool,
}

impl Default for PlanConfig {
    fn default() -> Self {
        Self {
            layers: 3,
            modules_per_layer: 5,
            classes_per_module: (1, 3),
            interfaces_per_module: (0, 2),
            errors_per_module: (0, 2),
            functions_per_module: (2, 5),
            globals_per_module: (1, 3),
            fields_per_class: (1, 4),
            methods_per_class: (1, 3),
            methods_per_interface: (1, 2),
            fields_per_error: (0, 2),
            params_per_function: (0, 3),
            type_params_per_class: (0, 2),
            type_params_per_interface: (0, 1),
            type_params_per_function: (0, 2),
            constraints_per_type_param: (0, 2),
            interface_extends_probability: 0.3,
            implement_blocks_per_module: (0, 2),
            cross_layer_import_probability: 0.2,
            enable_diamond_dependencies: true,
        }
    }
}

/// Name generator for creating unique identifiers.
struct NameGen {
    counters: std::collections::HashMap<&'static str, usize>,
}

impl NameGen {
    fn new() -> Self {
        Self {
            counters: std::collections::HashMap::new(),
        }
    }

    /// Generate a unique name with the given prefix.
    fn next(&mut self, prefix: &'static str) -> String {
        let counter = self.counters.entry(prefix).or_insert(0);
        *counter += 1;
        format!("{}{}", prefix, counter)
    }

    /// Generate a unique module name for a layer.
    fn module_name(&mut self, layer: usize) -> String {
        let counter = self.counters.entry("module").or_insert(0);
        *counter += 1;
        format!("mod_l{}_{}", layer, counter)
    }
}

/// Plan the structure of a synthetic codebase.
pub fn plan<R: Rng>(rng: &mut R, config: &PlanConfig) -> SymbolTable {
    let mut table = SymbolTable::new();
    let mut names = NameGen::new();

    // Phase 1: Create all modules organized by layer
    let mut layers: Vec<Vec<ModuleId>> = Vec::new();
    for layer in 0..config.layers {
        let mut layer_modules = Vec::new();
        for _ in 0..config.modules_per_layer {
            let name = names.module_name(layer);
            let path = format!("{}.vole", name);
            let id = table.add_module(name, path);
            layer_modules.push(id);
        }
        layers.push(layer_modules);
    }

    // Phase 2: Set up import relationships (lower layers import from higher layers)
    plan_imports(rng, &mut table, &layers, config);

    // Phase 3: Create declarations in each module
    for module_id in 0..table.module_count() {
        let module_id = ModuleId(module_id);
        plan_module_declarations(rng, &mut table, &mut names, module_id, config);
    }

    // Phase 4: Add interface implementations to classes and interface extends
    plan_interface_implementations(rng, &mut table, config);

    // Phase 5: Add interface extends relationships
    plan_interface_extends(rng, &mut table, config);

    // Phase 6: Add standalone implement blocks
    plan_implement_blocks(rng, &mut table, &mut names, config);

    table
}

/// Set up import relationships between modules.
fn plan_imports<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    layers: &[Vec<ModuleId>],
    config: &PlanConfig,
) {
    // Collect all modules from later layers for cross-layer imports
    let later_layers: Vec<Vec<ModuleId>> = layers.iter().skip(1).cloned().collect();

    for layer_idx in 0..layers.len().saturating_sub(1) {
        let current_layer = &layers[layer_idx];
        let next_layer = &layers[layer_idx + 1];

        for &module_id in current_layer {
            // Each module imports 1-3 modules from the next layer
            let import_count = rng.gen_range(1..=next_layer.len().min(3));
            let mut imported: Vec<ModuleId> = Vec::new();

            while imported.len() < import_count {
                let target_idx = rng.gen_range(0..next_layer.len());
                let target = next_layer[target_idx];
                if !imported.contains(&target) {
                    imported.push(target);
                }
            }

            // Cross-layer imports: sometimes import from layers beyond the next one
            if config.cross_layer_import_probability > 0.0 && layer_idx + 2 < layers.len() {
                for far_layer in layers.iter().skip(layer_idx + 2) {
                    if rng.gen_bool(config.cross_layer_import_probability) && !far_layer.is_empty()
                    {
                        let target_idx = rng.gen_range(0..far_layer.len());
                        let target = far_layer[target_idx];
                        if !imported.contains(&target) {
                            imported.push(target);
                        }
                    }
                }
            }

            // Diamond dependencies: if enabled, try to ensure multiple modules
            // in this layer import a common module from a later layer
            if config.enable_diamond_dependencies && !later_layers.is_empty() {
                // Pick a "shared" module from some later layer (create diamond patterns)
                let flat_later: Vec<ModuleId> = later_layers.iter().flatten().copied().collect();
                if !flat_later.is_empty() && rng.gen_bool(0.4) {
                    // Use a deterministic "shared" module based on layer index
                    let shared_idx = layer_idx % flat_later.len();
                    let shared = flat_later[shared_idx];
                    if !imported.contains(&shared) {
                        imported.push(shared);
                    }
                }
            }

            // Collect target names first to avoid borrow conflict
            let imports_with_alias: Vec<(ModuleId, String)> = imported
                .iter()
                .filter_map(|&target| table.get_module(target).map(|m| (target, m.name.clone())))
                .collect();

            // Add imports to the module
            if let Some(module) = table.get_module_mut(module_id) {
                for (target, alias) in imports_with_alias {
                    module.add_import(target, alias);
                }
            }
        }
    }
}

/// Plan declarations for a single module.
fn plan_module_declarations<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
    config: &PlanConfig,
) {
    // Generate interfaces first (so classes can implement them)
    let interface_count =
        rng.gen_range(config.interfaces_per_module.0..=config.interfaces_per_module.1);
    for _ in 0..interface_count {
        plan_interface(rng, table, names, module_id, config);
    }

    // Generate classes
    let class_count = rng.gen_range(config.classes_per_module.0..=config.classes_per_module.1);
    for _ in 0..class_count {
        plan_class(rng, table, names, module_id, config);
    }

    // Generate errors
    let error_count = rng.gen_range(config.errors_per_module.0..=config.errors_per_module.1);
    for _ in 0..error_count {
        plan_error(rng, table, names, module_id, config);
    }

    // Generate functions
    let func_count = rng.gen_range(config.functions_per_module.0..=config.functions_per_module.1);
    for _ in 0..func_count {
        plan_function(rng, table, names, module_id, config);
    }

    // Generate globals
    let global_count = rng.gen_range(config.globals_per_module.0..=config.globals_per_module.1);
    for _ in 0..global_count {
        plan_global(rng, table, names, module_id);
    }
}

/// Plan an interface declaration.
fn plan_interface<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
    config: &PlanConfig,
) -> SymbolId {
    let name = names.next("IFace");

    // Generate type parameters (without constraints for now; constraints added later)
    let type_param_count =
        rng.gen_range(config.type_params_per_interface.0..=config.type_params_per_interface.1);
    let type_params = plan_type_params(names, type_param_count);

    let method_count =
        rng.gen_range(config.methods_per_interface.0..=config.methods_per_interface.1);
    let mut methods = Vec::new();

    for _ in 0..method_count {
        methods.push(plan_method_signature(rng, names, config));
    }

    let kind = SymbolKind::Interface(InterfaceInfo {
        type_params,
        extends: vec![],
        methods,
    });
    table
        .get_module_mut(module_id)
        .map(|m| m.add_symbol(name, kind))
        .unwrap_or(SymbolId(0))
}

/// Plan a class declaration.
fn plan_class<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
    config: &PlanConfig,
) -> SymbolId {
    let name = names.next("Class");

    // Generate type parameters (without constraints for now; constraints added later)
    let type_param_count =
        rng.gen_range(config.type_params_per_class.0..=config.type_params_per_class.1);
    let type_params = plan_type_params(names, type_param_count);

    // Generate fields (can include type parameters if class is generic)
    let field_count = rng.gen_range(config.fields_per_class.0..=config.fields_per_class.1);
    let mut fields = Vec::new();
    for _ in 0..field_count {
        fields.push(plan_field_with_type_params(rng, names, &type_params));
    }

    // Generate methods
    let method_count = rng.gen_range(config.methods_per_class.0..=config.methods_per_class.1);
    let mut methods = Vec::new();
    for _ in 0..method_count {
        methods.push(plan_method_signature_with_type_params(
            rng,
            names,
            config,
            &type_params,
        ));
    }

    let kind = SymbolKind::Class(ClassInfo {
        type_params,
        fields,
        methods,
        implements: vec![],
    });

    table
        .get_module_mut(module_id)
        .map(|m| m.add_symbol(name, kind))
        .unwrap_or(SymbolId(0))
}

/// Plan an error declaration.
fn plan_error<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
    config: &PlanConfig,
) -> SymbolId {
    let name = names.next("Err");
    let field_count = rng.gen_range(config.fields_per_error.0..=config.fields_per_error.1);
    let mut fields = Vec::new();

    for _ in 0..field_count {
        fields.push(plan_field(rng, names));
    }

    let kind = SymbolKind::Error(ErrorInfo { fields });
    table
        .get_module_mut(module_id)
        .map(|m| m.add_symbol(name, kind))
        .unwrap_or(SymbolId(0))
}

/// Plan a function declaration.
fn plan_function<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
    config: &PlanConfig,
) -> SymbolId {
    let name = names.next("func");

    // Generate type parameters (without constraints for now; constraints added later)
    let type_param_count =
        rng.gen_range(config.type_params_per_function.0..=config.type_params_per_function.1);
    let type_params = plan_type_params(names, type_param_count);

    let param_count = rng.gen_range(config.params_per_function.0..=config.params_per_function.1);
    let mut params = Vec::new();

    for _ in 0..param_count {
        params.push(plan_param_with_type_params(rng, names, &type_params));
    }

    let return_type = plan_return_type_with_type_params(rng, &type_params);
    let kind = SymbolKind::Function(FunctionInfo {
        type_params,
        params,
        return_type,
    });

    table
        .get_module_mut(module_id)
        .map(|m| m.add_symbol(name, kind))
        .unwrap_or(SymbolId(0))
}

/// Plan a global variable.
fn plan_global<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
) -> SymbolId {
    let name = names.next("GLOBAL");
    let value_type = TypeInfo::Primitive(PrimitiveType::random_field_type(rng));
    let is_mutable = rng.gen_bool(0.2); // 20% chance of mutable

    let kind = SymbolKind::Global(GlobalInfo {
        value_type,
        is_mutable,
    });

    table
        .get_module_mut(module_id)
        .map(|m| m.add_symbol(name, kind))
        .unwrap_or(SymbolId(0))
}

/// Plan a field with a random primitive type.
fn plan_field<R: Rng>(rng: &mut R, names: &mut NameGen) -> FieldInfo {
    FieldInfo {
        name: names.next("field"),
        field_type: TypeInfo::Primitive(PrimitiveType::random_field_type(rng)),
    }
}

/// Plan a method signature.
fn plan_method_signature<R: Rng>(
    rng: &mut R,
    names: &mut NameGen,
    config: &PlanConfig,
) -> MethodInfo {
    let name = names.next("method");
    let param_count = rng.gen_range(config.params_per_function.0..=config.params_per_function.1);
    let mut params = Vec::new();

    for _ in 0..param_count {
        params.push(plan_param(rng, names));
    }

    let return_type = plan_return_type(rng);
    MethodInfo {
        name,
        params,
        return_type,
    }
}

/// Plan a function/method parameter.
fn plan_param<R: Rng>(rng: &mut R, names: &mut NameGen) -> ParamInfo {
    ParamInfo {
        name: names.next("param"),
        param_type: TypeInfo::Primitive(PrimitiveType::random_expr_type(rng)),
    }
}

/// Plan a return type for a function/method.
fn plan_return_type<R: Rng>(rng: &mut R) -> TypeInfo {
    match rng.gen_range(0..6) {
        0 => TypeInfo::Void,
        1..=4 => TypeInfo::Primitive(PrimitiveType::random_expr_type(rng)),
        _ => TypeInfo::Optional(Box::new(TypeInfo::Primitive(
            PrimitiveType::random_expr_type(rng),
        ))),
    }
}

/// Generate type parameters with standard names (T, U, V, K, V2, etc.).
fn plan_type_params(names: &mut NameGen, count: usize) -> Vec<TypeParam> {
    let mut params = Vec::with_capacity(count);
    for _ in 0..count {
        params.push(TypeParam {
            name: names.next("T"),
            constraints: vec![],
        });
    }
    params
}

/// Plan a field that may use a type parameter.
fn plan_field_with_type_params<R: Rng>(
    rng: &mut R,
    names: &mut NameGen,
    type_params: &[TypeParam],
) -> FieldInfo {
    let field_type = if !type_params.is_empty() && rng.gen_bool(0.4) {
        // 40% chance to use a type parameter if available
        let idx = rng.gen_range(0..type_params.len());
        TypeInfo::TypeParam(type_params[idx].name.clone())
    } else {
        TypeInfo::Primitive(PrimitiveType::random_field_type(rng))
    };
    FieldInfo {
        name: names.next("field"),
        field_type,
    }
}

/// Plan a method signature that may use type parameters.
fn plan_method_signature_with_type_params<R: Rng>(
    rng: &mut R,
    names: &mut NameGen,
    config: &PlanConfig,
    type_params: &[TypeParam],
) -> MethodInfo {
    let name = names.next("method");
    let param_count = rng.gen_range(config.params_per_function.0..=config.params_per_function.1);
    let mut params = Vec::new();

    for _ in 0..param_count {
        params.push(plan_param_with_type_params(rng, names, type_params));
    }

    let return_type = plan_return_type_with_type_params(rng, type_params);
    MethodInfo {
        name,
        params,
        return_type,
    }
}

/// Plan a parameter that may use a type parameter.
fn plan_param_with_type_params<R: Rng>(
    rng: &mut R,
    names: &mut NameGen,
    type_params: &[TypeParam],
) -> ParamInfo {
    let param_type = if !type_params.is_empty() && rng.gen_bool(0.3) {
        // 30% chance to use a type parameter if available
        let idx = rng.gen_range(0..type_params.len());
        TypeInfo::TypeParam(type_params[idx].name.clone())
    } else {
        TypeInfo::Primitive(PrimitiveType::random_expr_type(rng))
    };
    ParamInfo {
        name: names.next("param"),
        param_type,
    }
}

/// Plan a return type that may use a type parameter.
fn plan_return_type_with_type_params<R: Rng>(rng: &mut R, type_params: &[TypeParam]) -> TypeInfo {
    if !type_params.is_empty() && rng.gen_bool(0.3) {
        // 30% chance to use a type parameter if available
        let idx = rng.gen_range(0..type_params.len());
        TypeInfo::TypeParam(type_params[idx].name.clone())
    } else {
        plan_return_type(rng)
    }
}

/// Add interface implementations to classes after all declarations exist.
/// Only implements interfaces from the same module to avoid cross-module reference issues.
fn plan_interface_implementations<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    _config: &PlanConfig,
) {
    // Process each module independently to avoid cross-module references
    for module_idx in 0..table.module_count() {
        let module_id = ModuleId(module_idx);

        // Collect non-generic interfaces in this module
        let interfaces: Vec<(SymbolId, Vec<MethodInfo>)> = table
            .get_module(module_id)
            .map(|m| {
                m.interfaces()
                    .filter_map(|s| {
                        if let SymbolKind::Interface(ref info) = s.kind {
                            if info.type_params.is_empty() {
                                Some((s.id, info.methods.clone()))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();

        if interfaces.is_empty() {
            continue;
        }

        // Collect non-generic classes in this module
        let classes: Vec<SymbolId> = table
            .get_module(module_id)
            .map(|m| {
                m.classes()
                    .filter_map(|s| {
                        if let SymbolKind::Class(ref info) = s.kind {
                            if info.type_params.is_empty() {
                                Some(s.id)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();

        // For each class, possibly implement an interface from the same module
        for class_id in classes {
            // 30% chance a class implements an interface
            if rng.gen_bool(0.3) {
                let iface_idx = rng.gen_range(0..interfaces.len());
                let (iface_id, ref iface_methods) = interfaces[iface_idx];

                if let Some(module) = table.get_module_mut(module_id)
                    && let Some(symbol) = module.get_symbol_mut(class_id)
                    && let SymbolKind::Class(ref mut info) = symbol.kind
                {
                    // Copy interface methods to class (if not already present)
                    for method in iface_methods {
                        if !info.methods.iter().any(|m| m.name == method.name) {
                            info.methods.push(method.clone());
                        }
                    }
                    info.implements.push((module_id, iface_id));
                }
            }
        }
    }
}

/// Add interface extends relationships.
fn plan_interface_extends<R: Rng>(rng: &mut R, table: &mut SymbolTable, config: &PlanConfig) {
    // Collect all non-generic interfaces
    let interfaces: Vec<(ModuleId, SymbolId)> = table
        .all_interfaces()
        .iter()
        .filter_map(|(mid, s)| {
            if let SymbolKind::Interface(ref info) = s.kind {
                if info.type_params.is_empty() {
                    Some((*mid, s.id))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    if interfaces.len() < 2 {
        return;
    }

    // For each interface, possibly extend another
    for i in 1..interfaces.len() {
        if rng.gen_bool(config.interface_extends_probability) {
            let (child_mod, child_id) = interfaces[i];
            // Pick a parent from earlier interfaces to avoid cycles
            let parent_idx = rng.gen_range(0..i);
            let (parent_mod, parent_id) = interfaces[parent_idx];

            // Get parent methods to copy
            let parent_methods: Vec<MethodInfo> = table
                .get_module(parent_mod)
                .and_then(|m| m.get_symbol(parent_id))
                .and_then(|s| {
                    if let SymbolKind::Interface(ref info) = s.kind {
                        Some(info.methods.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or_default();

            if let Some(module) = table.get_module_mut(child_mod)
                && let Some(symbol) = module.get_symbol_mut(child_id)
                && let SymbolKind::Interface(ref mut info) = symbol.kind
                && !info.extends.contains(&(parent_mod, parent_id))
            {
                info.extends.push((parent_mod, parent_id));
                // Don't copy methods - Vole interface extends just requires impl
            }

            // Silence unused warning
            let _ = parent_methods;
        }
    }
}

/// Add standalone implement blocks.
/// Only creates implement blocks for interfaces and classes within the same module
/// to avoid cross-module reference issues.
fn plan_implement_blocks<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    config: &PlanConfig,
) {
    // Create implement blocks for each module, using only local interfaces and classes
    for module_id in 0..table.module_count() {
        let module_id = ModuleId(module_id);

        // Get interfaces in this module
        let interfaces: Vec<(SymbolId, Vec<MethodInfo>)> = table
            .get_module(module_id)
            .map(|m| {
                m.interfaces()
                    .filter_map(|s| {
                        if let SymbolKind::Interface(ref info) = s.kind {
                            if info.type_params.is_empty() {
                                Some((s.id, info.methods.clone()))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();

        if interfaces.is_empty() {
            continue;
        }

        // Get non-generic classes in this module that don't already implement interfaces
        let classes: Vec<SymbolId> = table
            .get_module(module_id)
            .map(|m| {
                m.classes()
                    .filter_map(|s| {
                        if let SymbolKind::Class(ref info) = s.kind {
                            if info.type_params.is_empty() && info.implements.is_empty() {
                                Some(s.id)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();

        if classes.is_empty() {
            continue;
        }

        let block_count = rng
            .gen_range(config.implement_blocks_per_module.0..=config.implement_blocks_per_module.1);

        for _ in 0..block_count {
            // Pick a random interface and class from this module
            let iface_idx = rng.gen_range(0..interfaces.len());
            let class_idx = rng.gen_range(0..classes.len());

            let (iface_id, ref iface_methods) = interfaces[iface_idx];
            let class_id = classes[class_idx];

            // Generate method implementations
            let methods: Vec<MethodInfo> = iface_methods
                .iter()
                .map(|m| MethodInfo {
                    name: m.name.clone(),
                    params: m.params.clone(),
                    return_type: m.return_type.clone(),
                })
                .collect();

            // Use a synthetic name for the implement block symbol
            let impl_name = names.next("impl");

            let kind = SymbolKind::ImplementBlock(ImplementBlockInfo {
                interface: (module_id, iface_id),
                target_type: (module_id, class_id),
                methods,
            });

            if let Some(module) = table.get_module_mut(module_id) {
                module.add_symbol(impl_name, kind);
            }
        }
    }
}

/// Add constraints to type parameters based on available interfaces.
#[allow(dead_code)]
fn plan_type_param_constraints<R: Rng>(
    rng: &mut R,
    table: &SymbolTable,
    config: &PlanConfig,
) -> Vec<(ModuleId, SymbolId)> {
    let constraint_count =
        rng.gen_range(config.constraints_per_type_param.0..=config.constraints_per_type_param.1);

    if constraint_count == 0 {
        return vec![];
    }

    // Collect non-generic interfaces to use as constraints
    let interfaces: Vec<(ModuleId, SymbolId)> = table
        .all_interfaces()
        .iter()
        .filter_map(|(mid, s)| {
            if let SymbolKind::Interface(ref info) = s.kind {
                if info.type_params.is_empty() {
                    Some((*mid, s.id))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    if interfaces.is_empty() {
        return vec![];
    }

    let mut constraints = Vec::with_capacity(constraint_count);
    let mut used_indices = std::collections::HashSet::new();

    for _ in 0..constraint_count {
        if used_indices.len() >= interfaces.len() {
            break;
        }
        let mut idx = rng.gen_range(0..interfaces.len());
        while used_indices.contains(&idx) {
            idx = (idx + 1) % interfaces.len();
        }
        used_indices.insert(idx);
        constraints.push(interfaces[idx]);
    }

    constraints
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    #[test]
    fn plan_creates_modules() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 2,
            modules_per_layer: 3,
            ..Default::default()
        };

        let table = plan(&mut rng, &config);
        assert_eq!(table.module_count(), 6); // 2 layers * 3 modules
    }

    #[test]
    fn plan_creates_imports() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 2,
            modules_per_layer: 3,
            ..Default::default()
        };

        let table = plan(&mut rng, &config);

        // First layer modules should have imports to second layer
        let first_module = table.get_module(ModuleId(0)).unwrap();
        assert!(!first_module.imports.is_empty());
    }

    #[test]
    fn plan_creates_declarations() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 1,
            modules_per_layer: 1,
            classes_per_module: (2, 2),
            functions_per_module: (3, 3),
            ..Default::default()
        };

        let table = plan(&mut rng, &config);
        let module = table.get_module(ModuleId(0)).unwrap();

        assert_eq!(module.classes().count(), 2);
        assert_eq!(module.functions().count(), 3);
    }

    #[test]
    fn plan_is_deterministic() {
        let config = PlanConfig::default();

        let mut rng1 = rand::rngs::StdRng::seed_from_u64(12345);
        let table1 = plan(&mut rng1, &config);

        let mut rng2 = rand::rngs::StdRng::seed_from_u64(12345);
        let table2 = plan(&mut rng2, &config);

        assert_eq!(table1.module_count(), table2.module_count());

        for i in 0..table1.module_count() {
            let m1 = table1.get_module(ModuleId(i)).unwrap();
            let m2 = table2.get_module(ModuleId(i)).unwrap();
            assert_eq!(m1.name, m2.name);
            assert_eq!(m1.symbols().count(), m2.symbols().count());
        }
    }

    #[test]
    fn name_gen_creates_unique_names() {
        let mut names = NameGen::new();
        let n1 = names.next("func");
        let n2 = names.next("func");
        let n3 = names.next("Class");

        assert_eq!(n1, "func1");
        assert_eq!(n2, "func2");
        assert_eq!(n3, "Class1");
    }

    #[test]
    fn plan_creates_generic_classes() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 1,
            modules_per_layer: 1,
            classes_per_module: (3, 3),
            type_params_per_class: (1, 2),
            interfaces_per_module: (0, 0),
            errors_per_module: (0, 0),
            functions_per_module: (0, 0),
            globals_per_module: (0, 0),
            ..Default::default()
        };

        let table = plan(&mut rng, &config);
        let module = table.get_module(ModuleId(0)).unwrap();

        // Check that at least one class has type parameters
        let has_generic = module.classes().any(|s| {
            if let SymbolKind::Class(ref info) = s.kind {
                !info.type_params.is_empty()
            } else {
                false
            }
        });
        assert!(has_generic, "Expected at least one generic class");
    }

    #[test]
    fn plan_creates_interface_extends() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 1,
            modules_per_layer: 1,
            interfaces_per_module: (4, 4),
            interface_extends_probability: 1.0, // Always extend
            classes_per_module: (0, 0),
            errors_per_module: (0, 0),
            functions_per_module: (0, 0),
            globals_per_module: (0, 0),
            type_params_per_interface: (0, 0), // No generics for simple test
            ..Default::default()
        };

        let table = plan(&mut rng, &config);
        let module = table.get_module(ModuleId(0)).unwrap();

        // Check that at least one interface extends another
        let has_extends = module.interfaces().any(|s| {
            if let SymbolKind::Interface(ref info) = s.kind {
                !info.extends.is_empty()
            } else {
                false
            }
        });
        assert!(has_extends, "Expected at least one interface with extends");
    }

    #[test]
    fn plan_creates_implement_blocks() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 1,
            modules_per_layer: 1,
            interfaces_per_module: (2, 2),
            classes_per_module: (2, 2),
            implement_blocks_per_module: (2, 2),
            type_params_per_interface: (0, 0),
            type_params_per_class: (0, 0),
            errors_per_module: (0, 0),
            functions_per_module: (0, 0),
            globals_per_module: (0, 0),
            ..Default::default()
        };

        let table = plan(&mut rng, &config);
        let module = table.get_module(ModuleId(0)).unwrap();

        let impl_count = module.implement_blocks().count();
        assert!(impl_count >= 1, "Expected at least one implement block");
    }

    #[test]
    fn plan_cross_layer_imports() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 3,
            modules_per_layer: 2,
            cross_layer_import_probability: 1.0, // Always cross-layer
            classes_per_module: (0, 0),
            interfaces_per_module: (0, 0),
            errors_per_module: (0, 0),
            functions_per_module: (0, 0),
            globals_per_module: (0, 0),
            ..Default::default()
        };

        let table = plan(&mut rng, &config);

        // Layer 0 modules should have imports to layers beyond layer 1
        let first_module = table.get_module(ModuleId(0)).unwrap();

        // With 3 layers, modules in layer 0 should import from layers 1 and 2
        let imports_count = first_module.imports.len();
        assert!(
            imports_count >= 2,
            "Expected at least 2 imports with cross-layer enabled, got {}",
            imports_count
        );
    }
}
