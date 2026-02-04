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
    ClassInfo, ErrorInfo, FieldInfo, FunctionInfo, GlobalInfo, InterfaceInfo, MethodInfo, ModuleId,
    ParamInfo, PrimitiveType, SymbolId, SymbolKind, SymbolTable, TypeInfo,
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
    plan_imports(rng, &mut table, &layers);

    // Phase 3: Create declarations in each module
    for module_id in 0..table.module_count() {
        let module_id = ModuleId(module_id);
        plan_module_declarations(rng, &mut table, &mut names, module_id, config);
    }

    // Phase 4: Add interface implementations to classes
    plan_interface_implementations(rng, &mut table);

    table
}

/// Set up import relationships between modules.
fn plan_imports<R: Rng>(rng: &mut R, table: &mut SymbolTable, layers: &[Vec<ModuleId>]) {
    // Each module in layer N can import modules from layer N+1
    // This creates a dependency hierarchy where lower layers depend on higher ones
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
    let method_count =
        rng.gen_range(config.methods_per_interface.0..=config.methods_per_interface.1);
    let mut methods = Vec::new();

    for _ in 0..method_count {
        methods.push(plan_method_signature(rng, names, config));
    }

    let kind = SymbolKind::Interface(InterfaceInfo { methods });
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

    // Generate fields
    let field_count = rng.gen_range(config.fields_per_class.0..=config.fields_per_class.1);
    let mut fields = Vec::new();
    for _ in 0..field_count {
        fields.push(plan_field(rng, names));
    }

    // Generate methods
    let method_count = rng.gen_range(config.methods_per_class.0..=config.methods_per_class.1);
    let mut methods = Vec::new();
    for _ in 0..method_count {
        methods.push(plan_method_signature(rng, names, config));
    }

    let kind = SymbolKind::Class(ClassInfo {
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
    let param_count = rng.gen_range(config.params_per_function.0..=config.params_per_function.1);
    let mut params = Vec::new();

    for _ in 0..param_count {
        params.push(plan_param(rng, names));
    }

    let return_type = plan_return_type(rng);
    let kind = SymbolKind::Function(FunctionInfo {
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

/// Add interface implementations to classes after all declarations exist.
fn plan_interface_implementations<R: Rng>(rng: &mut R, table: &mut SymbolTable) {
    // Collect all interfaces with their methods
    let interfaces: Vec<(ModuleId, SymbolId, Vec<MethodInfo>)> = table
        .all_interfaces()
        .iter()
        .filter_map(|(mid, s)| {
            if let SymbolKind::Interface(ref info) = s.kind {
                Some((*mid, s.id, info.methods.clone()))
            } else {
                None
            }
        })
        .collect();

    if interfaces.is_empty() {
        return;
    }

    // Collect all class locations
    let class_locations: Vec<(ModuleId, SymbolId)> = table
        .all_classes()
        .iter()
        .map(|(mid, s)| (*mid, s.id))
        .collect();

    // For each class, possibly implement an interface
    for (module_id, class_id) in class_locations {
        // 30% chance a class implements an interface
        if rng.gen_bool(0.3) {
            let iface_idx = rng.gen_range(0..interfaces.len());
            let (iface_mod, iface_id, ref iface_methods) = interfaces[iface_idx];

            if let Some(module) = table.get_module_mut(module_id) {
                if let Some(symbol) = module.get_symbol_mut(class_id) {
                    if let SymbolKind::Class(ref mut info) = symbol.kind {
                        // Copy interface methods to class (if not already present)
                        for method in iface_methods {
                            if !info.methods.iter().any(|m| m.name == method.name) {
                                info.methods.push(method.clone());
                            }
                        }
                        info.implements.push((iface_mod, iface_id));
                    }
                }
            }
        }
    }
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
}
