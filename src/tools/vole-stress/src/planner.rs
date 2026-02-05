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
    MethodInfo, ModuleId, ParamInfo, PrimitiveType, StaticMethodInfo, StructInfo, SymbolId,
    SymbolKind, SymbolTable, TypeInfo, TypeParam,
};

/// Configuration for the planning phase.
#[derive(Debug, Clone)]
pub struct PlanConfig {
    /// Number of module layers (depth of import hierarchy).
    pub layers: usize,
    /// Number of modules per layer.
    pub modules_per_layer: usize,
    /// Number of structs per module (range).
    pub structs_per_module: (usize, usize),
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
    /// Number of fields per struct (range).
    pub fields_per_struct: (usize, usize),
    /// Number of fields per class (range).
    pub fields_per_class: (usize, usize),
    /// Number of methods per class (range).
    pub methods_per_class: (usize, usize),
    /// Number of static methods per class (range).
    /// Only applies to non-generic classes with fields. Static methods
    /// are constructor-like methods that return the class type.
    pub static_methods_per_class: (usize, usize),
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
    /// Probability (0.0-1.0) that a function has a fallible return type.
    pub fallible_probability: f64,
    /// Probability (0.0-1.0) that a planned function is a generator (returns Iterator<T>).
    pub generator_probability: f64,
    /// Probability (0.0-1.0) that a function has a never return type (diverging function).
    pub never_probability: f64,
    /// Probability (0.0-1.0) that a class field references another class type.
    /// Only applies to non-generic classes to avoid cyclic type references.
    pub nested_class_field_probability: f64,
}

impl Default for PlanConfig {
    fn default() -> Self {
        Self {
            layers: 3,
            modules_per_layer: 5,
            structs_per_module: (0, 2),
            classes_per_module: (1, 3),
            interfaces_per_module: (0, 2),
            errors_per_module: (0, 2),
            functions_per_module: (2, 5),
            globals_per_module: (1, 3),
            fields_per_struct: (2, 4),
            fields_per_class: (1, 4),
            methods_per_class: (1, 3),
            static_methods_per_class: (0, 2),
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
            fallible_probability: 0.15,
            generator_probability: 0.10,
            never_probability: 0.02,
            nested_class_field_probability: 0.20,
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
    // Only layer 0 modules can have generators (workaround for vol-67b9:
    // importing a module with generator functions fails with "yield outside
    // generator context"). Layer 0 modules are not imported by any other module.
    let layer0_modules: std::collections::HashSet<ModuleId> = layers
        .first()
        .map(|l| l.iter().copied().collect())
        .unwrap_or_default();
    for module_id in 0..table.module_count() {
        let module_id = ModuleId(module_id);
        let allow_generators = layer0_modules.contains(&module_id);
        plan_module_declarations(
            rng,
            &mut table,
            &mut names,
            module_id,
            config,
            allow_generators,
        );
    }

    // Phase 3.5: Assign interface constraints to type parameters
    // Now that all declarations exist, we can pick constraint interfaces from
    // the same module for each generic class/interface/function.
    plan_all_type_param_constraints(rng, &mut table, config);

    // Phase 3.6: Assign class-typed fields to some non-generic classes
    // This enables nested field access patterns (obj.inner.field).
    plan_nested_class_fields(rng, &mut table, config);

    // Phase 3.7: Add static methods to non-generic classes with fields
    // Static methods are constructor-like methods called on the class name.
    plan_static_methods(rng, &mut table, &mut names, config);

    // Phase 4: Add interface implementations to classes and interface extends
    plan_interface_implementations(rng, &mut table, config);

    // Phase 5: Add interface extends relationships
    plan_interface_extends(rng, &mut table, config);

    // Phase 5.5: Reconcile class implements after interface extends
    // Classes from Phase 4 may implement interfaces that gained extends in Phase 5.
    // Ensure all parent interface methods are present in those classes.
    reconcile_class_implements(&mut table);

    // Phase 6: Add standalone implement blocks
    plan_implement_blocks(rng, &mut table, &mut names, config);

    // Phase 7: Add standalone implement blocks with Self-returning methods
    plan_standalone_implement_blocks(rng, &mut table, &mut names, config);

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
                    if shared != module_id && !imported.contains(&shared) {
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
    allow_generators: bool,
) {
    // Generate interfaces first (so classes can implement them)
    let interface_count =
        rng.gen_range(config.interfaces_per_module.0..=config.interfaces_per_module.1);
    for _ in 0..interface_count {
        plan_interface(rng, table, names, module_id, config);
    }

    // Generate structs (value types with fields only)
    let struct_count = rng.gen_range(config.structs_per_module.0..=config.structs_per_module.1);
    for _ in 0..struct_count {
        plan_struct(rng, table, names, module_id, config);
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

    // Generate functions (some may become generators or never-returning functions).
    // Generators are only allowed in non-imported modules (layer 0) due to vol-67b9.
    let func_count = rng.gen_range(config.functions_per_module.0..=config.functions_per_module.1);
    for _ in 0..func_count {
        if allow_generators
            && config.generator_probability > 0.0
            && rng.gen_bool(config.generator_probability)
        {
            plan_generator(rng, table, names, module_id);
        } else if config.never_probability > 0.0 && rng.gen_bool(config.never_probability) {
            plan_never_function(rng, table, names, module_id, config);
        } else {
            plan_function(rng, table, names, module_id, config);
        }
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

/// Plan a struct declaration (value type with primitive-typed fields only).
fn plan_struct<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
    config: &PlanConfig,
) -> SymbolId {
    let name = names.next("Struct");
    let field_count = rng.gen_range(config.fields_per_struct.0..=config.fields_per_struct.1);
    let mut fields = Vec::new();

    for _ in 0..field_count {
        // Struct fields are always primitive types
        fields.push(plan_field(rng, names));
    }

    let kind = SymbolKind::Struct(StructInfo { fields });
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
        static_methods: vec![],
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

/// Plan a function-typed parameter with simple primitive param/return types.
///
/// Generates a parameter like `f: (i64, i64) -> i64` with 1-2 primitive param
/// types and a primitive return type. Avoids wide/complex types to keep lambda
/// generation straightforward.
fn plan_function_typed_param<R: Rng>(rng: &mut R, names: &mut NameGen) -> ParamInfo {
    let param_count = rng.gen_range(1..=2);
    let param_types: Vec<TypeInfo> = (0..param_count)
        .map(|_| {
            let prim = match rng.gen_range(0..3) {
                0 => PrimitiveType::I64,
                1 => PrimitiveType::Bool,
                _ => PrimitiveType::String,
            };
            TypeInfo::Primitive(prim)
        })
        .collect();
    let return_type = match rng.gen_range(0..3) {
        0 => PrimitiveType::I64,
        1 => PrimitiveType::Bool,
        _ => PrimitiveType::String,
    };
    ParamInfo {
        name: names.next("param"),
        param_type: TypeInfo::Function {
            param_types,
            return_type: Box::new(TypeInfo::Primitive(return_type)),
        },
    }
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

    // ~10% chance to add a function-typed parameter (only for non-generic functions)
    if type_params.is_empty() && rng.gen_bool(0.10) {
        params.push(plan_function_typed_param(rng, names));
    }

    // Possibly make this a fallible function if error types are available in the module
    // and the function has no type parameters (fallible generics are too complex)
    let return_type = if type_params.is_empty()
        && config.fallible_probability > 0.0
        && rng.gen_bool(config.fallible_probability)
    {
        plan_fallible_return_type(rng, table, module_id, &type_params)
            .unwrap_or_else(|| plan_return_type_with_type_params(rng, &type_params))
    } else {
        plan_return_type_with_type_params(rng, &type_params)
    };

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

/// Plan a generator function declaration (returns Iterator<T>).
///
/// Generators are always non-generic, have 0-2 parameters (used to control
/// the iteration), and return `Iterator<PrimitiveType>`. The yield type
/// is restricted to primitive types to keep the generated code simple.
fn plan_generator<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
) -> SymbolId {
    let name = names.next("gen");

    // Generators get 0-2 simple parameters (for controlling iteration bounds)
    let param_count = rng.gen_range(0..=2);
    let mut params = Vec::new();
    for _ in 0..param_count {
        params.push(plan_param(rng, names));
    }

    // Pick a primitive yield type (the Iterator element type)
    // Use core types only (i64, string, bool) for simplicity
    let yield_prim = match rng.gen_range(0..3) {
        0 => PrimitiveType::I64,
        1 => PrimitiveType::String,
        _ => PrimitiveType::Bool,
    };
    let return_type = TypeInfo::Iterator(Box::new(TypeInfo::Primitive(yield_prim)));

    let kind = SymbolKind::Function(FunctionInfo {
        type_params: vec![],
        params,
        return_type,
    });

    table
        .get_module_mut(module_id)
        .map(|m| m.add_symbol(name, kind))
        .unwrap_or(SymbolId(0))
}

/// Plan a never-returning function declaration (diverging function).
///
/// Never-returning functions are always non-generic, have 0-2 parameters,
/// and return the `never` type. The body will call `panic()` or `unreachable`.
fn plan_never_function<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    module_id: ModuleId,
    config: &PlanConfig,
) -> SymbolId {
    let name = names.next("diverge");

    // Never-returning functions get 0-2 simple parameters
    let param_count = rng.gen_range(config.params_per_function.0..=config.params_per_function.1);
    let mut params = Vec::new();
    for _ in 0..param_count.min(2) {
        params.push(plan_param(rng, names));
    }

    let kind = SymbolKind::Function(FunctionInfo {
        type_params: vec![],
        params,
        return_type: TypeInfo::Never,
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
    let param_type = if rng.gen_bool(0.15) {
        // 15% chance to generate a union type parameter
        plan_union_type(rng)
    } else {
        TypeInfo::Primitive(PrimitiveType::random_expr_type(rng))
    };
    ParamInfo {
        name: names.next("param"),
        param_type,
    }
}

/// Plan a union type with 2-3 primitive variants.
fn plan_union_type<R: Rng>(rng: &mut R) -> TypeInfo {
    let variant_count = rng.gen_range(2..=3);
    let mut variants = Vec::with_capacity(variant_count);
    let all_types = [
        PrimitiveType::I8,
        PrimitiveType::I16,
        PrimitiveType::I32,
        PrimitiveType::I64,
        PrimitiveType::I128,
        PrimitiveType::U8,
        PrimitiveType::U16,
        PrimitiveType::U32,
        PrimitiveType::U64,
        PrimitiveType::F32,
        PrimitiveType::F64,
        PrimitiveType::Bool,
        PrimitiveType::String,
    ];

    // Pick distinct primitive types for the union
    let mut used = std::collections::HashSet::new();
    while variants.len() < variant_count {
        let idx = rng.gen_range(0..all_types.len());
        if used.insert(idx) {
            variants.push(TypeInfo::Primitive(all_types[idx]));
        }
    }

    TypeInfo::Union(variants)
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

/// Plan a fallible return type using an error type from the same module.
///
/// Returns `None` if no error types are available in the module.
fn plan_fallible_return_type<R: Rng>(
    rng: &mut R,
    table: &SymbolTable,
    module_id: ModuleId,
    type_params: &[TypeParam],
) -> Option<TypeInfo> {
    // Collect error types from this module
    let errors: Vec<SymbolId> = table
        .get_module(module_id)?
        .errors()
        .map(|s| s.id)
        .collect();

    if errors.is_empty() {
        return None;
    }

    // Pick a random error type
    let error_idx = rng.gen_range(0..errors.len());
    let error_id = errors[error_idx];

    // Generate the success type (a primitive or type param)
    let success_type = plan_return_type_with_type_params(rng, type_params);
    // Fallible functions can't have void success type - use i64 as fallback
    let success_type = if matches!(success_type, TypeInfo::Void) {
        TypeInfo::Primitive(PrimitiveType::random_expr_type(rng))
    } else {
        success_type
    };
    // Unwrap optional since fallible already handles the error case
    let success_type = match success_type {
        TypeInfo::Optional(inner) => *inner,
        other => other,
    };

    Some(TypeInfo::Fallible {
        success: Box::new(success_type),
        error: Box::new(TypeInfo::Error(module_id, error_id)),
    })
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
/// Only creates extends relationships within the same module to avoid cross-module
/// reference issues (vole-stress doesn't generate imports for cross-module interface extends).
fn plan_interface_extends<R: Rng>(rng: &mut R, table: &mut SymbolTable, config: &PlanConfig) {
    // Process each module separately to keep extends within same module
    for module_id in 0..table.module_count() {
        let module_id = ModuleId(module_id);

        // Collect all non-generic interfaces in this module
        let interfaces: Vec<SymbolId> = table
            .get_module(module_id)
            .map(|m| {
                m.symbols()
                    .filter_map(|s| {
                        if let SymbolKind::Interface(ref info) = s.kind {
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

        if interfaces.len() < 2 {
            continue;
        }

        // For each interface, possibly extend another from the same module
        for i in 1..interfaces.len() {
            if rng.gen_bool(config.interface_extends_probability) {
                let child_id = interfaces[i];
                // Pick a parent from earlier interfaces to avoid cycles
                let parent_idx = rng.gen_range(0..i);
                let parent_id = interfaces[parent_idx];

                if let Some(module) = table.get_module_mut(module_id)
                    && let Some(symbol) = module.get_symbol_mut(child_id)
                    && let SymbolKind::Interface(ref mut info) = symbol.kind
                    && !info.extends.contains(&(module_id, parent_id))
                {
                    info.extends.push((module_id, parent_id));
                    // Don't copy methods - Vole interface extends just requires impl
                }
            }
        }
    }
}

/// Collect all methods required by an interface, including inherited methods from parent
/// interfaces (via extends). Returns methods with duplicates removed (by name).
fn collect_all_interface_methods(
    table: &SymbolTable,
    module_id: ModuleId,
    iface_id: SymbolId,
) -> Vec<MethodInfo> {
    let mut all_methods = Vec::new();
    let mut seen_names = std::collections::HashSet::new();
    let mut stack = vec![(module_id, iface_id)];
    let mut visited = std::collections::HashSet::new();

    while let Some((mid, sid)) = stack.pop() {
        if !visited.insert((mid, sid)) {
            continue; // Avoid infinite loops from cycles
        }

        if let Some(symbol) = table.get_symbol(mid, sid) {
            if let SymbolKind::Interface(ref info) = symbol.kind {
                // Add this interface's own methods
                for method in &info.methods {
                    if seen_names.insert(method.name.clone()) {
                        all_methods.push(method.clone());
                    }
                }
                // Push parent interfaces onto the stack
                for &(parent_mid, parent_sid) in &info.extends {
                    stack.push((parent_mid, parent_sid));
                }
            }
        }
    }

    all_methods
}

/// After interface extends are set up, ensure classes that implement interfaces
/// also have methods from all parent interfaces.
fn reconcile_class_implements(table: &mut SymbolTable) {
    for module_idx in 0..table.module_count() {
        let module_id = ModuleId(module_idx);

        // Collect classes that implement interfaces, along with their interface list
        let class_impls: Vec<(SymbolId, Vec<(ModuleId, SymbolId)>)> = table
            .get_module(module_id)
            .map(|m| {
                m.classes()
                    .filter_map(|s| {
                        if let SymbolKind::Class(ref info) = s.kind {
                            if !info.implements.is_empty() {
                                Some((s.id, info.implements.clone()))
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

        // For each class, collect all required methods from all implemented interfaces
        // (including ancestor methods) and add any missing ones to the class
        for (class_id, iface_refs) in class_impls {
            let mut required_methods = Vec::new();
            let mut seen_names = std::collections::HashSet::new();

            for (iface_mid, iface_sid) in &iface_refs {
                let methods = collect_all_interface_methods(table, *iface_mid, *iface_sid);
                for method in methods {
                    if seen_names.insert(method.name.clone()) {
                        required_methods.push(method);
                    }
                }
            }

            // Add missing methods to the class
            if let Some(module) = table.get_module_mut(module_id)
                && let Some(symbol) = module.get_symbol_mut(class_id)
                && let SymbolKind::Class(ref mut info) = symbol.kind
            {
                for method in &required_methods {
                    if !info.methods.iter().any(|m| m.name == method.name) {
                        info.methods.push(method.clone());
                    }
                }
            }
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

        // Get non-generic interfaces in this module, collecting ALL required methods
        // (including inherited methods from parent interfaces via extends)
        let iface_ids: Vec<SymbolId> = table
            .get_module(module_id)
            .map(|m| {
                m.interfaces()
                    .filter_map(|s| {
                        if let SymbolKind::Interface(ref info) = s.kind {
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

        // Collect all methods (including ancestors) for each interface
        let interfaces: Vec<(SymbolId, Vec<MethodInfo>)> = iface_ids
            .iter()
            .map(|&iface_id| {
                let methods = collect_all_interface_methods(table, module_id, iface_id);
                (iface_id, methods)
            })
            .collect();

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

        // Track (interface_id, class_id) pairs that have been used to avoid duplicates
        let mut used_pairs: std::collections::HashSet<(SymbolId, SymbolId)> =
            std::collections::HashSet::new();

        // Limit attempts to avoid infinite loop when all combinations are exhausted
        let max_attempts = block_count * 3;
        let mut attempts = 0;
        let mut created = 0;

        while created < block_count && attempts < max_attempts {
            attempts += 1;

            // Pick a random interface and class from this module
            let iface_idx = rng.gen_range(0..interfaces.len());
            let class_idx = rng.gen_range(0..classes.len());

            let (iface_id, ref iface_methods) = interfaces[iface_idx];
            let class_id = classes[class_idx];

            // Skip if this pair has already been used
            if used_pairs.contains(&(iface_id, class_id)) {
                continue;
            }
            used_pairs.insert((iface_id, class_id));

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
                interface: Some((module_id, iface_id)),
                target_type: (module_id, class_id),
                methods,
            });

            if let Some(module) = table.get_module_mut(module_id) {
                module.add_symbol(impl_name, kind);
                created += 1;
            }
        }
    }
}

/// Add standalone implement blocks with Self-returning methods.
///
/// Creates `implement ClassName { ... }` blocks (without interfaces) that add
/// methods returning Self to existing non-generic classes. These methods use
/// Self as the return type and construct instances of the implementing class.
fn plan_standalone_implement_blocks<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    config: &PlanConfig,
) {
    // Process each module
    for module_idx in 0..table.module_count() {
        let module_id = ModuleId(module_idx);

        // Get non-generic classes in this module that don't already have
        // a standalone implement block
        let classes: Vec<(SymbolId, String)> = table
            .get_module(module_id)
            .map(|m| {
                m.classes()
                    .filter_map(|s| {
                        if let SymbolKind::Class(ref info) = s.kind {
                            // Only non-generic classes with fields
                            if info.type_params.is_empty() && !info.fields.is_empty() {
                                Some((s.id, s.name.clone()))
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

        // ~30% chance per class to get a standalone implement block
        for (class_id, _class_name) in &classes {
            if !rng.gen_bool(0.30) {
                continue;
            }

            // Generate 1-2 Self-returning methods
            let method_count = rng.gen_range(1..=2);
            let mut methods = Vec::with_capacity(method_count);

            for _ in 0..method_count {
                methods.push(plan_self_returning_method(rng, names, config));
            }

            let impl_name = names.next("selfimpl");

            let kind = SymbolKind::ImplementBlock(ImplementBlockInfo {
                interface: None, // Standalone - no interface
                target_type: (module_id, *class_id),
                methods,
            });

            if let Some(module) = table.get_module_mut(module_id) {
                module.add_symbol(impl_name, kind);
            }
        }
    }
}

/// Plan a method that returns Self.
///
/// Generates a method with primitive parameters and a void return type
/// (the return type will be replaced with Self by the emitter).
fn plan_self_returning_method<R: Rng>(
    rng: &mut R,
    names: &mut NameGen,
    config: &PlanConfig,
) -> MethodInfo {
    let name = names.next("selfMethod");
    let param_count = rng.gen_range(config.params_per_function.0..=config.params_per_function.1);
    let mut params = Vec::new();

    for _ in 0..param_count {
        params.push(plan_param(rng, names));
    }

    // Use Void as a placeholder - the emitter will use Self as return type
    MethodInfo {
        name,
        params,
        return_type: TypeInfo::Void,
    }
}

/// Pick random non-generic interface constraints from the same module.
///
/// Returns up to `constraints_per_type_param` distinct interface references
/// from the given module, suitable for constraining a single type parameter.
fn pick_constraints_from_module<R: Rng>(
    rng: &mut R,
    config: &PlanConfig,
    local_interfaces: &[(ModuleId, SymbolId)],
) -> Vec<(ModuleId, SymbolId)> {
    let constraint_count =
        rng.gen_range(config.constraints_per_type_param.0..=config.constraints_per_type_param.1);

    if constraint_count == 0 || local_interfaces.is_empty() {
        return vec![];
    }

    let mut constraints = Vec::with_capacity(constraint_count);
    let mut used_indices = std::collections::HashSet::new();

    for _ in 0..constraint_count {
        if used_indices.len() >= local_interfaces.len() {
            break;
        }
        let mut idx = rng.gen_range(0..local_interfaces.len());
        while used_indices.contains(&idx) {
            idx = (idx + 1) % local_interfaces.len();
        }
        used_indices.insert(idx);
        constraints.push(local_interfaces[idx]);
    }

    constraints
}

/// Assign interface constraints to type parameters on all generic declarations.
///
/// Runs after all module declarations exist so that every non-generic interface
/// in a module is available as a potential constraint. Only uses interfaces from
/// the same module to avoid cross-module reference issues.
fn plan_all_type_param_constraints<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    config: &PlanConfig,
) {
    for module_idx in 0..table.module_count() {
        let module_id = ModuleId(module_idx);

        // Collect non-generic interfaces in this module
        let local_interfaces: Vec<(ModuleId, SymbolId)> = table
            .get_module(module_id)
            .map(|m| {
                m.interfaces()
                    .filter_map(|s| {
                        if let SymbolKind::Interface(ref info) = s.kind {
                            if info.type_params.is_empty() {
                                Some((module_id, s.id))
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

        if local_interfaces.is_empty() {
            continue;
        }

        // Collect symbol ids of generic declarations that need constraints
        let generic_symbol_ids: Vec<SymbolId> = table
            .get_module(module_id)
            .map(|m| {
                m.symbols()
                    .filter(|s| match &s.kind {
                        SymbolKind::Class(info) => !info.type_params.is_empty(),
                        SymbolKind::Interface(info) => !info.type_params.is_empty(),
                        SymbolKind::Function(info) => !info.type_params.is_empty(),
                        _ => false,
                    })
                    .map(|s| s.id)
                    .collect()
            })
            .unwrap_or_default();

        // Assign constraints to each type parameter of each generic symbol
        for sym_id in generic_symbol_ids {
            // Read type param count (immutable borrow), generate constraints,
            // then apply them (mutable borrow) -- two-phase borrow pattern.
            let type_param_count = table
                .get_symbol(module_id, sym_id)
                .map(|s| match &s.kind {
                    SymbolKind::Class(info) => info.type_params.len(),
                    SymbolKind::Interface(info) => info.type_params.len(),
                    SymbolKind::Function(info) => info.type_params.len(),
                    _ => 0,
                })
                .unwrap_or(0);

            let new_constraints: Vec<Vec<(ModuleId, SymbolId)>> = (0..type_param_count)
                .map(|_| pick_constraints_from_module(rng, config, &local_interfaces))
                .collect();

            if let Some(module) = table.get_module_mut(module_id)
                && let Some(symbol) = module.get_symbol_mut(sym_id)
            {
                let type_params = match &mut symbol.kind {
                    SymbolKind::Class(info) => &mut info.type_params,
                    SymbolKind::Interface(info) => &mut info.type_params,
                    SymbolKind::Function(info) => &mut info.type_params,
                    _ => continue,
                };

                for (tp, constraints) in type_params.iter_mut().zip(new_constraints) {
                    tp.constraints = constraints;
                }
            }
        }
    }
}

/// Assign class-typed fields to some non-generic classes.
///
/// This is done in a separate phase after all classes are created to ensure
/// non-cyclic references. A class can only reference classes declared before it
/// (lower SymbolId), ensuring acyclic dependencies.
///
/// Only non-generic classes can have class-typed fields, and only non-generic
/// classes can be referenced as field types. This avoids complex generic type
/// resolution during construction.
fn plan_nested_class_fields<R: Rng>(rng: &mut R, table: &mut SymbolTable, config: &PlanConfig) {
    if config.nested_class_field_probability <= 0.0 {
        return;
    }

    // Process each module independently
    for module_idx in 0..table.module_count() {
        let module_id = ModuleId(module_idx);

        // Collect non-generic classes with at least one primitive field
        let non_generic_classes: Vec<(SymbolId, String)> = table
            .get_module(module_id)
            .map(|m| {
                m.classes()
                    .filter_map(|s| {
                        if let SymbolKind::Class(ref info) = s.kind {
                            if info.type_params.is_empty() && !info.fields.is_empty() {
                                Some((s.id, s.name.clone()))
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

        // Need at least 2 classes to create nested references
        if non_generic_classes.len() < 2 {
            continue;
        }

        // For each class (except the first), possibly add a field referencing an earlier class
        for i in 1..non_generic_classes.len() {
            if !rng.gen_bool(config.nested_class_field_probability) {
                continue;
            }

            let (class_id, _) = non_generic_classes[i];

            // Pick a random earlier class to reference (ensures non-cyclic)
            let target_idx = rng.gen_range(0..i);
            let (target_class_id, target_class_name) = &non_generic_classes[target_idx];

            // Create the field with a name based on the target class
            let field_name = format!("nested_{}", target_class_name.to_lowercase());
            let field_type = TypeInfo::Class(module_id, *target_class_id);
            let new_field = FieldInfo {
                name: field_name,
                field_type,
            };

            // Add the field to the class
            if let Some(module) = table.get_module_mut(module_id)
                && let Some(symbol) = module.get_symbol_mut(class_id)
                && let SymbolKind::Class(ref mut info) = symbol.kind
            {
                info.fields.push(new_field);
            }
        }
    }
}

/// Add static methods to non-generic classes with fields.
///
/// Static methods are constructor-like methods that return the class type.
/// They are called on the class name: `ClassName.methodName(args)`.
///
/// Only non-generic classes with fields can have static methods, since the
/// static method body constructs an instance of the class.
fn plan_static_methods<R: Rng>(
    rng: &mut R,
    table: &mut SymbolTable,
    names: &mut NameGen,
    config: &PlanConfig,
) {
    // Skip if static methods are disabled
    if config.static_methods_per_class.1 == 0 {
        return;
    }

    // Process each module
    for module_idx in 0..table.module_count() {
        let module_id = ModuleId(module_idx);

        // Collect non-generic classes with fields
        let classes: Vec<SymbolId> = table
            .get_module(module_id)
            .map(|m| {
                m.classes()
                    .filter_map(|s| {
                        if let SymbolKind::Class(ref info) = s.kind {
                            // Only non-generic classes with at least one field
                            if info.type_params.is_empty() && !info.fields.is_empty() {
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

        // Add static methods to each eligible class
        for class_id in classes {
            let static_count = rng
                .gen_range(config.static_methods_per_class.0..=config.static_methods_per_class.1);

            if static_count == 0 {
                continue;
            }

            let mut static_methods = Vec::with_capacity(static_count);
            for _ in 0..static_count {
                static_methods.push(plan_static_method(rng, names, config));
            }

            // Add the static methods to the class
            if let Some(module) = table.get_module_mut(module_id)
                && let Some(symbol) = module.get_symbol_mut(class_id)
                && let SymbolKind::Class(ref mut info) = symbol.kind
            {
                info.static_methods = static_methods;
            }
        }
    }
}

/// Plan a single static method.
///
/// Static methods in vole-stress are constructor-like: they take primitive
/// parameters and return Self (the class type).
fn plan_static_method<R: Rng>(
    rng: &mut R,
    names: &mut NameGen,
    config: &PlanConfig,
) -> StaticMethodInfo {
    let name = names.next("static");

    // Generate 0-2 primitive parameters
    let param_count = rng.gen_range(config.params_per_function.0..=config.params_per_function.1);
    let param_count = param_count.min(2); // Limit to 0-2 params for statics
    let mut params = Vec::with_capacity(param_count);

    for _ in 0..param_count {
        params.push(plan_param(rng, names));
    }

    StaticMethodInfo {
        name,
        params,
        returns_self: true,
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
        let mut rng = rand::rngs::StdRng::seed_from_u64(55);
        let config = PlanConfig {
            layers: 1,
            modules_per_layer: 1,
            interfaces_per_module: (2, 2),
            structs_per_module: (0, 0),
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
    fn non_generic_classes_have_no_type_param_methods() {
        use crate::profile::get_profile;

        // Use the problematic seed that exposed the bug
        let profile = get_profile("full").unwrap();
        let mut rng = rand::rngs::StdRng::seed_from_u64(1770226963014480876);

        let table = plan(&mut rng, &profile.plan);

        // Check all classes for type param usage in methods
        for module in table.modules() {
            for symbol in module.classes() {
                if let SymbolKind::Class(ref info) = symbol.kind {
                    let is_generic = !info.type_params.is_empty();
                    let class_type_param_names: std::collections::HashSet<_> =
                        info.type_params.iter().map(|tp| tp.name.as_str()).collect();

                    for method in &info.methods {
                        for param in &method.params {
                            if let TypeInfo::TypeParam(ref name) = param.param_type {
                                if !is_generic {
                                    panic!(
                                        "Non-generic class {} has method {} with type param {}",
                                        symbol.name, method.name, name
                                    );
                                }
                                if !class_type_param_names.contains(name.as_str()) {
                                    panic!(
                                        "Class {} method {} uses type param {} which is not in class type params {:?}",
                                        symbol.name, method.name, name, class_type_param_names
                                    );
                                }
                            }
                        }
                        if let TypeInfo::TypeParam(ref name) = method.return_type {
                            if !is_generic {
                                panic!(
                                    "Non-generic class {} has method {} with return type param {}",
                                    symbol.name, method.name, name
                                );
                            }
                            if !class_type_param_names.contains(name.as_str()) {
                                panic!(
                                    "Class {} method {} returns type param {} which is not in class type params {:?}",
                                    symbol.name, method.name, name, class_type_param_names
                                );
                            }
                        }
                    }
                }
            }
        }
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

    #[test]
    fn plan_creates_structs() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = PlanConfig {
            layers: 1,
            modules_per_layer: 1,
            structs_per_module: (2, 2),
            classes_per_module: (0, 0),
            functions_per_module: (0, 0),
            interfaces_per_module: (0, 0),
            errors_per_module: (0, 0),
            globals_per_module: (0, 0),
            ..Default::default()
        };

        let table = plan(&mut rng, &config);
        let module = table.get_module(ModuleId(0)).unwrap();

        assert_eq!(module.structs().count(), 2);

        // Verify struct fields are primitive types only
        for symbol in module.structs() {
            if let SymbolKind::Struct(ref info) = symbol.kind {
                assert!(
                    !info.fields.is_empty(),
                    "Struct {} should have at least 2 fields",
                    symbol.name
                );
                for field in &info.fields {
                    assert!(
                        field.field_type.is_primitive(),
                        "Struct {} field {} should be a primitive type, got {:?}",
                        symbol.name,
                        field.name,
                        field.field_type
                    );
                }
            }
        }
    }

    #[test]
    fn plan_no_duplicate_implement_blocks() {
        use crate::profile::get_profile;

        // Use the problematic seed that exposed duplicate implement blocks
        let profile = get_profile("full").unwrap();
        let mut rng = rand::rngs::StdRng::seed_from_u64(1770226963014480876);

        let table = plan(&mut rng, &profile.plan);

        // Check for duplicate (interface, class) pairs in implement blocks
        for module in table.modules() {
            let mut seen_pairs: std::collections::HashSet<(
                (ModuleId, SymbolId),
                (ModuleId, SymbolId),
            )> = std::collections::HashSet::new();

            for symbol in module.implement_blocks() {
                if let SymbolKind::ImplementBlock(ref info) = symbol.kind {
                    // Only check interface implements (standalone blocks have interface=None)
                    if let Some(iface) = info.interface {
                        let pair = (iface, info.target_type);
                        assert!(
                            seen_pairs.insert(pair),
                            "Duplicate implement block found: {:?} for {:?} in module {}",
                            info.interface,
                            info.target_type,
                            module.name
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn plan_creates_static_methods() {
        // Use a config that ensures static methods are generated
        let config = PlanConfig {
            layers: 1,
            modules_per_layer: 1,
            classes_per_module: (2, 2),
            functions_per_module: (0, 0),
            interfaces_per_module: (0, 0),
            errors_per_module: (0, 0),
            globals_per_module: (0, 0),
            structs_per_module: (0, 0),
            type_params_per_class: (0, 0), // Non-generic classes
            fields_per_class: (2, 2),      // Must have fields
            methods_per_class: (0, 0),
            static_methods_per_class: (2, 2), // Force exactly 2 static methods
            ..Default::default()
        };

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let table = plan(&mut rng, &config);
        let module = table.get_module(ModuleId(0)).unwrap();

        let mut found_static = false;
        for symbol in module.classes() {
            if let SymbolKind::Class(ref info) = symbol.kind {
                if !info.static_methods.is_empty() {
                    found_static = true;
                    assert_eq!(
                        info.static_methods.len(),
                        2,
                        "Class {} should have exactly 2 static methods",
                        symbol.name
                    );
                    for static_method in &info.static_methods {
                        assert!(
                            static_method.name.starts_with("static"),
                            "Static method name should start with 'static', got: {}",
                            static_method.name
                        );
                        assert!(
                            static_method.returns_self,
                            "Static method should return Self"
                        );
                    }
                }
            }
        }
        assert!(
            found_static,
            "Expected at least one class with static methods"
        );
    }
}
