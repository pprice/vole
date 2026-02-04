//! Symbol table for tracking declarations across modules.
//!
//! This module implements a plan-then-fill architecture where:
//! 1. Plan phase: Generate skeleton of all declarations (names, signatures, imports)
//! 2. Fill phase: Generate bodies using complete symbol table for valid references
//!
//! This enables forward references (A uses B, B uses A) and type-correct expression
//! generation.

use rand::Rng;
use std::collections::HashMap;

/// Unique identifier for a symbol within a module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub usize);

/// Unique identifier for a module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub usize);

/// Type information for generating type-correct expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeInfo {
    /// Primitive types: i32, i64, f64, bool, string, nil
    Primitive(PrimitiveType),
    /// A user-defined class type
    Class(ModuleId, SymbolId),
    /// A user-defined interface type
    Interface(ModuleId, SymbolId),
    /// A user-defined error type
    Error(ModuleId, SymbolId),
    /// Optional type T?
    Optional(Box<TypeInfo>),
    /// Union type A | B
    Union(Vec<TypeInfo>),
    /// Array type [T]
    Array(Box<TypeInfo>),
    /// Void type (no return value)
    Void,
    /// A type parameter (e.g., T in Box<T>)
    TypeParam(String),
}

/// Primitive types in Vole.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    I32,
    I64,
    F64,
    Bool,
    String,
    Nil,
}

impl PrimitiveType {
    /// Return the Vole syntax for this primitive type.
    pub fn as_str(&self) -> &'static str {
        match self {
            PrimitiveType::I32 => "i32",
            PrimitiveType::I64 => "i64",
            PrimitiveType::F64 => "f64",
            PrimitiveType::Bool => "bool",
            PrimitiveType::String => "string",
            PrimitiveType::Nil => "nil",
        }
    }

    /// Select a random primitive type suitable for expressions.
    pub fn random_expr_type<R: Rng>(rng: &mut R) -> Self {
        match rng.gen_range(0..5) {
            0 => PrimitiveType::I32,
            1 => PrimitiveType::I64,
            2 => PrimitiveType::F64,
            3 => PrimitiveType::Bool,
            _ => PrimitiveType::String,
        }
    }

    /// Select a random primitive type suitable for fields.
    pub fn random_field_type<R: Rng>(rng: &mut R) -> Self {
        match rng.gen_range(0..5) {
            0 => PrimitiveType::I32,
            1 => PrimitiveType::I64,
            2 => PrimitiveType::F64,
            3 => PrimitiveType::Bool,
            _ => PrimitiveType::String,
        }
    }
}

impl TypeInfo {
    /// Check if this type is a primitive type.
    pub fn is_primitive(&self) -> bool {
        matches!(self, TypeInfo::Primitive(_))
    }

    /// Check if this type can be used as a return type.
    pub fn is_returnable(&self) -> bool {
        !matches!(self, TypeInfo::Void)
    }

    /// Generate Vole syntax for this type.
    pub fn to_vole_syntax(&self, table: &SymbolTable) -> String {
        match self {
            TypeInfo::Primitive(p) => p.as_str().to_string(),
            TypeInfo::Class(mod_id, sym_id) => table
                .get_symbol(*mod_id, *sym_id)
                .map_or_else(|| "UnknownClass".to_string(), |s| s.name.clone()),
            TypeInfo::Interface(mod_id, sym_id) => table
                .get_symbol(*mod_id, *sym_id)
                .map_or_else(|| "UnknownInterface".to_string(), |s| s.name.clone()),
            TypeInfo::Error(mod_id, sym_id) => table
                .get_symbol(*mod_id, *sym_id)
                .map_or_else(|| "UnknownError".to_string(), |s| s.name.clone()),
            TypeInfo::Optional(inner) => format!("{}?", inner.to_vole_syntax(table)),
            TypeInfo::Union(types) => types
                .iter()
                .map(|t| t.to_vole_syntax(table))
                .collect::<Vec<_>>()
                .join(" | "),
            TypeInfo::Array(elem) => format!("[{}]", elem.to_vole_syntax(table)),
            TypeInfo::Void => "void".to_string(),
            TypeInfo::TypeParam(name) => name.clone(),
        }
    }
}

/// A type parameter with optional constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParam {
    /// The name of the type parameter (e.g., "T", "A", "K").
    pub name: String,
    /// Constraint interfaces that the type parameter must implement.
    /// Multiple constraints are combined with + (e.g., T: Hashable + Eq).
    pub constraints: Vec<(ModuleId, SymbolId)>,
}

/// Kind of symbol declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    /// A class declaration with fields and methods.
    Class(ClassInfo),
    /// An interface declaration with method signatures.
    Interface(InterfaceInfo),
    /// An error type declaration with fields.
    Error(ErrorInfo),
    /// A function declaration.
    Function(FunctionInfo),
    /// A module-level global variable.
    Global(GlobalInfo),
    /// A standalone implement block (implements interface for existing type).
    ImplementBlock(ImplementBlockInfo),
}

/// Information about a class declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassInfo {
    /// Type parameters for generic classes (e.g., T in Box<T>).
    pub type_params: Vec<TypeParam>,
    /// Fields of the class.
    pub fields: Vec<FieldInfo>,
    /// Methods of the class.
    pub methods: Vec<MethodInfo>,
    /// Interfaces this class implements.
    pub implements: Vec<(ModuleId, SymbolId)>,
}

/// Information about a class/error field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldInfo {
    pub name: String,
    pub field_type: TypeInfo,
}

/// Information about a method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodInfo {
    pub name: String,
    pub params: Vec<ParamInfo>,
    pub return_type: TypeInfo,
}

/// Information about a function/method parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamInfo {
    pub name: String,
    pub param_type: TypeInfo,
}

/// Information about an interface declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceInfo {
    /// Type parameters for generic interfaces.
    pub type_params: Vec<TypeParam>,
    /// Parent interfaces this interface extends.
    pub extends: Vec<(ModuleId, SymbolId)>,
    /// Method signatures required by this interface.
    pub methods: Vec<MethodInfo>,
}

/// Information about a standalone implement block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplementBlockInfo {
    /// The interface being implemented.
    pub interface: (ModuleId, SymbolId),
    /// The type the interface is being implemented for.
    pub target_type: (ModuleId, SymbolId),
    /// Method implementations.
    pub methods: Vec<MethodInfo>,
}

/// Information about an error type declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrorInfo {
    /// Fields of the error.
    pub fields: Vec<FieldInfo>,
}

/// Information about a function declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionInfo {
    /// Type parameters for generic functions.
    pub type_params: Vec<TypeParam>,
    pub params: Vec<ParamInfo>,
    pub return_type: TypeInfo,
}

/// Information about a global variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalInfo {
    pub value_type: TypeInfo,
    pub is_mutable: bool,
}

/// A symbol in the symbol table.
#[derive(Debug, Clone)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: String,
    pub kind: SymbolKind,
}

/// Import relationship between modules.
#[derive(Debug, Clone)]
pub struct ModuleImport {
    /// The module being imported.
    pub target_module: ModuleId,
    /// The alias used for the import (e.g., `let alias = import "path"`).
    pub alias: String,
}

/// Symbols within a single module.
#[derive(Debug, Clone)]
pub struct ModuleSymbols {
    pub id: ModuleId,
    pub name: String,
    pub path: String,
    /// Symbols defined in this module.
    symbols: Vec<Symbol>,
    /// Modules imported by this module.
    pub imports: Vec<ModuleImport>,
}

impl ModuleSymbols {
    /// Create a new module with the given id, name, and path.
    pub fn new(id: ModuleId, name: String, path: String) -> Self {
        Self {
            id,
            name,
            path,
            symbols: Vec::new(),
            imports: Vec::new(),
        }
    }

    /// Add a symbol to this module and return its id.
    pub fn add_symbol(&mut self, name: String, kind: SymbolKind) -> SymbolId {
        let id = SymbolId(self.symbols.len());
        self.symbols.push(Symbol { id, name, kind });
        id
    }

    /// Get a symbol by id.
    pub fn get_symbol(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols.get(id.0)
    }

    /// Get a mutable reference to a symbol by id.
    pub fn get_symbol_mut(&mut self, id: SymbolId) -> Option<&mut Symbol> {
        self.symbols.get_mut(id.0)
    }

    /// Iterate over all symbols in this module.
    pub fn symbols(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols.iter()
    }

    /// Add an import to this module.
    pub fn add_import(&mut self, target_module: ModuleId, alias: String) {
        self.imports.push(ModuleImport {
            target_module,
            alias,
        });
    }

    /// Get all classes in this module.
    pub fn classes(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Class(_)))
    }

    /// Get all interfaces in this module.
    pub fn interfaces(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Interface(_)))
    }

    /// Get all errors in this module.
    pub fn errors(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Error(_)))
    }

    /// Get all functions in this module.
    pub fn functions(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Function(_)))
    }

    /// Get all globals in this module.
    pub fn globals(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Global(_)))
    }

    /// Get all implement blocks in this module.
    pub fn implement_blocks(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::ImplementBlock(_)))
    }
}

/// The complete symbol table tracking all modules and their symbols.
#[derive(Debug, Default)]
pub struct SymbolTable {
    modules: Vec<ModuleSymbols>,
    /// Map from module name to module id for quick lookup.
    module_by_name: HashMap<String, ModuleId>,
}

impl SymbolTable {
    /// Create a new empty symbol table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a new module to the symbol table.
    pub fn add_module(&mut self, name: String, path: String) -> ModuleId {
        let id = ModuleId(self.modules.len());
        self.module_by_name.insert(name.clone(), id);
        self.modules.push(ModuleSymbols::new(id, name, path));
        id
    }

    /// Get a module by id.
    pub fn get_module(&self, id: ModuleId) -> Option<&ModuleSymbols> {
        self.modules.get(id.0)
    }

    /// Get a mutable reference to a module by id.
    pub fn get_module_mut(&mut self, id: ModuleId) -> Option<&mut ModuleSymbols> {
        self.modules.get_mut(id.0)
    }

    /// Get a module by name.
    pub fn get_module_by_name(&self, name: &str) -> Option<&ModuleSymbols> {
        self.module_by_name
            .get(name)
            .and_then(|id| self.get_module(*id))
    }

    /// Get a symbol from a specific module.
    pub fn get_symbol(&self, module_id: ModuleId, symbol_id: SymbolId) -> Option<&Symbol> {
        self.get_module(module_id)?.get_symbol(symbol_id)
    }

    /// Iterate over all modules.
    pub fn modules(&self) -> impl Iterator<Item = &ModuleSymbols> {
        self.modules.iter()
    }

    /// Get the number of modules.
    pub fn module_count(&self) -> usize {
        self.modules.len()
    }

    /// Get all classes across all modules.
    pub fn all_classes(&self) -> Vec<(ModuleId, &Symbol)> {
        self.modules
            .iter()
            .flat_map(|m| m.classes().map(move |s| (m.id, s)))
            .collect()
    }

    /// Get all interfaces across all modules.
    pub fn all_interfaces(&self) -> Vec<(ModuleId, &Symbol)> {
        self.modules
            .iter()
            .flat_map(|m| m.interfaces().map(move |s| (m.id, s)))
            .collect()
    }

    /// Get all functions across all modules.
    pub fn all_functions(&self) -> Vec<(ModuleId, &Symbol)> {
        self.modules
            .iter()
            .flat_map(|m| m.functions().map(move |s| (m.id, s)))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitive_type_as_str() {
        assert_eq!(PrimitiveType::I32.as_str(), "i32");
        assert_eq!(PrimitiveType::I64.as_str(), "i64");
        assert_eq!(PrimitiveType::F64.as_str(), "f64");
        assert_eq!(PrimitiveType::Bool.as_str(), "bool");
        assert_eq!(PrimitiveType::String.as_str(), "string");
        assert_eq!(PrimitiveType::Nil.as_str(), "nil");
    }

    #[test]
    fn symbol_table_add_module() {
        let mut table = SymbolTable::new();
        let id = table.add_module("test_module".to_string(), "test_module.vole".to_string());
        assert_eq!(id.0, 0);
        assert_eq!(table.module_count(), 1);

        let module = table.get_module(id).unwrap();
        assert_eq!(module.name, "test_module");
        assert_eq!(module.path, "test_module.vole");
    }

    #[test]
    fn module_add_symbol() {
        let mut module =
            ModuleSymbols::new(ModuleId(0), "test".to_string(), "test.vole".to_string());

        let func_id = module.add_symbol(
            "my_func".to_string(),
            SymbolKind::Function(FunctionInfo {
                type_params: vec![],
                params: vec![],
                return_type: TypeInfo::Primitive(PrimitiveType::I64),
            }),
        );

        assert_eq!(func_id.0, 0);
        let symbol = module.get_symbol(func_id).unwrap();
        assert_eq!(symbol.name, "my_func");
    }

    #[test]
    fn type_info_to_vole_syntax() {
        let table = SymbolTable::new();

        let i64_type = TypeInfo::Primitive(PrimitiveType::I64);
        assert_eq!(i64_type.to_vole_syntax(&table), "i64");

        let optional = TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String)));
        assert_eq!(optional.to_vole_syntax(&table), "string?");

        let union = TypeInfo::Union(vec![
            TypeInfo::Primitive(PrimitiveType::I32),
            TypeInfo::Primitive(PrimitiveType::String),
        ]);
        assert_eq!(union.to_vole_syntax(&table), "i32 | string");

        let array = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
        assert_eq!(array.to_vole_syntax(&table), "[i64]");
    }

    #[test]
    fn module_filter_by_kind() {
        let mut module =
            ModuleSymbols::new(ModuleId(0), "test".to_string(), "test.vole".to_string());

        module.add_symbol(
            "MyClass".to_string(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![],
                methods: vec![],
                implements: vec![],
            }),
        );

        module.add_symbol(
            "my_func".to_string(),
            SymbolKind::Function(FunctionInfo {
                type_params: vec![],
                params: vec![],
                return_type: TypeInfo::Void,
            }),
        );

        module.add_symbol(
            "MyInterface".to_string(),
            SymbolKind::Interface(InterfaceInfo {
                type_params: vec![],
                extends: vec![],
                methods: vec![],
            }),
        );

        assert_eq!(module.classes().count(), 1);
        assert_eq!(module.functions().count(), 1);
        assert_eq!(module.interfaces().count(), 1);
    }

    #[test]
    fn symbol_table_lookup_by_name() {
        let mut table = SymbolTable::new();
        table.add_module("alpha".to_string(), "alpha.vole".to_string());
        table.add_module("beta".to_string(), "beta.vole".to_string());

        let alpha = table.get_module_by_name("alpha").unwrap();
        assert_eq!(alpha.name, "alpha");

        let beta = table.get_module_by_name("beta").unwrap();
        assert_eq!(beta.name, "beta");

        assert!(table.get_module_by_name("gamma").is_none());
    }
}
