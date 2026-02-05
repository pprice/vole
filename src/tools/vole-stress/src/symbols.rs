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
#[allow(dead_code)]
pub enum TypeInfo {
    /// Primitive types: i32, i64, f64, bool, string, nil
    Primitive(PrimitiveType),
    /// A user-defined class type
    Class(ModuleId, SymbolId),
    /// A user-defined struct type (value type)
    Struct(ModuleId, SymbolId),
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
    /// Fixed-size array type [T; N] (homogeneous, stack-allocated)
    FixedArray(Box<TypeInfo>, usize),
    /// Tuple type [T1, T2, ...] (heterogeneous, fixed-length)
    Tuple(Vec<TypeInfo>),
    /// Fallible type fallible(SuccessType, ErrorType)
    Fallible {
        success: Box<TypeInfo>,
        error: Box<TypeInfo>,
    },
    /// Function type (param_types) -> return_type
    Function {
        param_types: Vec<TypeInfo>,
        return_type: Box<TypeInfo>,
    },
    /// Iterator type (returned by generator functions)
    Iterator(Box<TypeInfo>),
    /// Void type (no return value)
    Void,
    /// A type parameter (e.g., T in Box<T>)
    TypeParam(String),
}

/// Primitive types in Vole.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum PrimitiveType {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    String,
    Nil,
}

impl PrimitiveType {
    /// Return the Vole syntax for this primitive type.
    pub fn as_str(&self) -> &'static str {
        match self {
            PrimitiveType::I8 => "i8",
            PrimitiveType::I16 => "i16",
            PrimitiveType::I32 => "i32",
            PrimitiveType::I64 => "i64",
            PrimitiveType::I128 => "i128",
            PrimitiveType::U8 => "u8",
            PrimitiveType::U16 => "u16",
            PrimitiveType::U32 => "u32",
            PrimitiveType::U64 => "u64",
            PrimitiveType::F32 => "f32",
            PrimitiveType::F64 => "f64",
            PrimitiveType::Bool => "bool",
            PrimitiveType::String => "string",
            PrimitiveType::Nil => "nil",
        }
    }

    /// Select a random primitive type suitable for expressions.
    ///
    /// The core types (i32, i64, f64, bool, string) appear ~90% of the time.
    /// Wider primitive types (i8, i16, i128, u8, u16, u32, u64, f32) share
    /// the remaining ~10% so they appear occasionally.
    pub fn random_expr_type<R: Rng>(rng: &mut R) -> Self {
        match rng.gen_range(0..50) {
            0..=8 => PrimitiveType::I32,
            9..=17 => PrimitiveType::I64,
            18..=26 => PrimitiveType::F64,
            27..=35 => PrimitiveType::Bool,
            36..=44 => PrimitiveType::String,
            // ~10% combined for wider types (1 slot each out of 50)
            45 => PrimitiveType::I8,
            46 => PrimitiveType::I16,
            47 => PrimitiveType::I128,
            48 => PrimitiveType::U8,
            _ => {
                // Spread remaining wider types across the last slot
                match rng.gen_range(0..4) {
                    0 => PrimitiveType::U16,
                    1 => PrimitiveType::U32,
                    2 => PrimitiveType::U64,
                    _ => PrimitiveType::F32,
                }
            }
        }
    }

    /// Select a random primitive type suitable for fields.
    ///
    /// Same distribution as `random_expr_type`: core types ~90%, wider types ~10%.
    pub fn random_field_type<R: Rng>(rng: &mut R) -> Self {
        // Reuse the same distribution as expr types
        Self::random_expr_type(rng)
    }

    /// Select a random primitive type suitable for array elements.
    ///
    /// Arrays in Vole require element types that fit in 64 bits, so i128 is
    /// excluded. Otherwise uses the same distribution as `random_expr_type`:
    /// core types ~90%, wider types ~10%.
    pub fn random_array_element_type<R: Rng>(rng: &mut R) -> Self {
        match rng.gen_range(0..50) {
            0..=8 => PrimitiveType::I32,
            9..=17 => PrimitiveType::I64,
            18..=26 => PrimitiveType::F64,
            27..=35 => PrimitiveType::Bool,
            36..=44 => PrimitiveType::String,
            // ~10% combined for wider types (1 slot each out of 50)
            // Note: i128 is excluded (not valid for array elements)
            45 => PrimitiveType::I8,
            46 => PrimitiveType::I16,
            47 => PrimitiveType::U8,
            48 => PrimitiveType::U16,
            _ => {
                // Spread remaining wider types across the last slot
                match rng.gen_range(0..3) {
                    0 => PrimitiveType::U32,
                    1 => PrimitiveType::U64,
                    _ => PrimitiveType::F32,
                }
            }
        }
    }
}

#[allow(dead_code)]
impl TypeInfo {
    /// Generate a random tuple type with 2-3 primitive element types.
    ///
    /// Uses core types (i32, i64, f64, bool, string) for element types to
    /// keep generated tuples simple and widely compatible.
    pub fn random_tuple_type<R: Rng>(rng: &mut R) -> Self {
        let elem_count = rng.gen_range(2..=3);
        let elems: Vec<TypeInfo> = (0..elem_count)
            .map(|_| TypeInfo::Primitive(PrimitiveType::random_expr_type(rng)))
            .collect();
        TypeInfo::Tuple(elems)
    }

    /// Check if this type is a primitive type.
    pub fn is_primitive(&self) -> bool {
        matches!(self, TypeInfo::Primitive(_))
    }

    /// Check if this type can be used as a return type.
    pub fn is_returnable(&self) -> bool {
        !matches!(self, TypeInfo::Void)
    }

    /// Check if this type is a fallible type.
    pub fn is_fallible(&self) -> bool {
        matches!(self, TypeInfo::Fallible { .. })
    }

    /// Check if this type is an iterator type (returned by generators).
    pub fn is_iterator(&self) -> bool {
        matches!(self, TypeInfo::Iterator(_))
    }

    /// Check if this type is a tuple type.
    pub fn is_tuple(&self) -> bool {
        matches!(self, TypeInfo::Tuple(_))
    }

    /// Check if this type is a fixed-size array type.
    pub fn is_fixed_array(&self) -> bool {
        matches!(self, TypeInfo::FixedArray(_, _))
    }

    /// Get the element type and size of a fixed-size array type.
    pub fn fixed_array_info(&self) -> Option<(&TypeInfo, usize)> {
        match self {
            TypeInfo::FixedArray(elem, size) => Some((elem, *size)),
            _ => None,
        }
    }

    /// Generate a random fixed-size array type with 2-4 elements.
    ///
    /// Uses primitive types suitable for arrays (excluding i128) for element types.
    pub fn random_fixed_array_type<R: Rng>(rng: &mut R) -> Self {
        let elem_type = PrimitiveType::random_array_element_type(rng);
        let size = rng.gen_range(2..=4);
        TypeInfo::FixedArray(Box::new(TypeInfo::Primitive(elem_type)), size)
    }

    /// Get the element types of a tuple type.
    pub fn tuple_element_types(&self) -> Option<&[TypeInfo]> {
        match self {
            TypeInfo::Tuple(elems) => Some(elems),
            _ => None,
        }
    }

    /// Get the element type of an iterator type.
    pub fn iterator_element_type(&self) -> Option<&TypeInfo> {
        match self {
            TypeInfo::Iterator(elem) => Some(elem),
            _ => None,
        }
    }

    /// Get the success type of a fallible type, or the type itself if not fallible.
    pub fn success_type(&self) -> &TypeInfo {
        match self {
            TypeInfo::Fallible { success, .. } => success,
            _ => self,
        }
    }

    /// Get the error type of a fallible type.
    pub fn error_type(&self) -> Option<&TypeInfo> {
        match self {
            TypeInfo::Fallible { error, .. } => Some(error),
            _ => None,
        }
    }

    /// Generate Vole syntax for this type.
    pub fn to_vole_syntax(&self, table: &SymbolTable) -> String {
        match self {
            TypeInfo::Primitive(p) => p.as_str().to_string(),
            TypeInfo::Class(mod_id, sym_id) => table
                .get_symbol(*mod_id, *sym_id)
                .map_or_else(|| "UnknownClass".to_string(), |s| s.name.clone()),
            TypeInfo::Struct(mod_id, sym_id) => table
                .get_symbol(*mod_id, *sym_id)
                .map_or_else(|| "UnknownStruct".to_string(), |s| s.name.clone()),
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
            TypeInfo::FixedArray(elem, size) => {
                format!("[{}; {}]", elem.to_vole_syntax(table), size)
            }
            TypeInfo::Tuple(elems) => {
                let parts: Vec<String> = elems.iter().map(|t| t.to_vole_syntax(table)).collect();
                format!("[{}]", parts.join(", "))
            }
            TypeInfo::Fallible { success, error } => format!(
                "fallible({}, {})",
                success.to_vole_syntax(table),
                error.to_vole_syntax(table)
            ),
            TypeInfo::Function {
                param_types,
                return_type,
            } => {
                let params = param_types
                    .iter()
                    .map(|t| t.to_vole_syntax(table))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({}) -> {}", params, return_type.to_vole_syntax(table))
            }
            TypeInfo::Iterator(elem) => {
                format!("Iterator<{}>", elem.to_vole_syntax(table))
            }
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
    /// A struct declaration with fields (value type, no methods).
    Struct(StructInfo),
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

/// Information about a struct declaration (value type, fields only).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructInfo {
    /// Fields of the struct. Only primitive types.
    pub fields: Vec<FieldInfo>,
}

/// Information about a class/error/struct field.
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
    #[allow(dead_code)]
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

    /// Get all structs in this module.
    pub fn structs(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Struct(_)))
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

    /// Get all generator functions in this module (functions returning Iterator<T>).
    #[allow(dead_code)]
    pub fn generators(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols.iter().filter(|s| {
            if let SymbolKind::Function(ref info) = s.kind {
                info.return_type.is_iterator()
            } else {
                false
            }
        })
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
    #[allow(dead_code)]
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
    #[allow(dead_code)]
    pub fn all_classes(&self) -> Vec<(ModuleId, &Symbol)> {
        self.modules
            .iter()
            .flat_map(|m| m.classes().map(move |s| (m.id, s)))
            .collect()
    }

    /// Get all interfaces across all modules.
    #[allow(dead_code)]
    pub fn all_interfaces(&self) -> Vec<(ModuleId, &Symbol)> {
        self.modules
            .iter()
            .flat_map(|m| m.interfaces().map(move |s| (m.id, s)))
            .collect()
    }

    /// Get all functions across all modules.
    #[allow(dead_code)]
    pub fn all_functions(&self) -> Vec<(ModuleId, &Symbol)> {
        self.modules
            .iter()
            .flat_map(|m| m.functions().map(move |s| (m.id, s)))
            .collect()
    }

    /// Get leaf modules (modules with no imports).
    ///
    /// In the layered module structure, leaf modules are in the highest layer
    /// and have no imports. They transitively provide access to all lower layers.
    pub fn leaf_modules(&self) -> Vec<&ModuleSymbols> {
        self.modules
            .iter()
            .filter(|m| m.imports.is_empty())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitive_type_as_str() {
        assert_eq!(PrimitiveType::I8.as_str(), "i8");
        assert_eq!(PrimitiveType::I16.as_str(), "i16");
        assert_eq!(PrimitiveType::I32.as_str(), "i32");
        assert_eq!(PrimitiveType::I64.as_str(), "i64");
        assert_eq!(PrimitiveType::I128.as_str(), "i128");
        assert_eq!(PrimitiveType::U8.as_str(), "u8");
        assert_eq!(PrimitiveType::U16.as_str(), "u16");
        assert_eq!(PrimitiveType::U32.as_str(), "u32");
        assert_eq!(PrimitiveType::U64.as_str(), "u64");
        assert_eq!(PrimitiveType::F32.as_str(), "f32");
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

        let tuple = TypeInfo::Tuple(vec![
            TypeInfo::Primitive(PrimitiveType::I64),
            TypeInfo::Primitive(PrimitiveType::String),
        ]);
        assert_eq!(tuple.to_vole_syntax(&table), "[i64, string]");

        let fallible = TypeInfo::Fallible {
            success: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            error: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
        };
        assert_eq!(fallible.to_vole_syntax(&table), "fallible(i64, string)");

        let func_type = TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
        };
        assert_eq!(func_type.to_vole_syntax(&table), "(i64) -> i64");

        let multi_param_func = TypeInfo::Function {
            param_types: vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Primitive(PrimitiveType::String),
            ],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::Bool)),
        };
        assert_eq!(
            multi_param_func.to_vole_syntax(&table),
            "(i64, string) -> bool"
        );
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

    #[test]
    fn leaf_modules_returns_modules_without_imports() {
        let mut table = SymbolTable::new();
        let leaf_id = table.add_module("leaf".to_string(), "leaf.vole".to_string());
        let parent_id = table.add_module("parent".to_string(), "parent.vole".to_string());

        // Add import from parent to leaf
        if let Some(parent) = table.get_module_mut(parent_id) {
            parent.add_import(leaf_id, "leaf".to_string());
        }

        let leaves = table.leaf_modules();
        assert_eq!(leaves.len(), 1);
        assert_eq!(leaves[0].name, "leaf");
    }

    #[test]
    fn leaf_modules_empty_when_all_have_imports() {
        let mut table = SymbolTable::new();
        let mod_a = table.add_module("mod_a".to_string(), "mod_a.vole".to_string());
        let mod_b = table.add_module("mod_b".to_string(), "mod_b.vole".to_string());

        // Circular imports (both have imports)
        if let Some(a) = table.get_module_mut(mod_a) {
            a.add_import(mod_b, "mod_b".to_string());
        }
        if let Some(b) = table.get_module_mut(mod_b) {
            b.add_import(mod_a, "mod_a".to_string());
        }

        let leaves = table.leaf_modules();
        assert!(leaves.is_empty());
    }
}
