// Scoped resolver for hierarchical name lookup.
// Bridges Symbol (AST) to NameId (semantic) with layered resolution.

use crate::{ModuleId, NameId, NameTable};
use vole_frontend::{Interner, Symbol};

/// Scoped resolver - the bridge from Symbol to NameId.
///
/// Resolution chain:
/// 1. Primitives (i32, i64, bool, string, etc.) - always available
/// 2. Current module definitions
/// 3. Explicit imports (non-transitive)
/// 4. Builtin module (stdlib types, interfaces)
///
/// Note: Entity resolution (NameId → TypeDefId) is handled in sema
/// via the EntityRegistry, not here.
pub struct Resolver<'a> {
    interner: &'a Interner,
    table: &'a NameTable,
    current_module: ModuleId,
    imports: &'a [ModuleId],
}

impl<'a> Resolver<'a> {
    pub fn new(
        interner: &'a Interner,
        table: &'a NameTable,
        current_module: ModuleId,
        imports: &'a [ModuleId],
    ) -> Self {
        Self {
            interner,
            table,
            current_module,
            imports,
        }
    }

    /// Get the NameTable this resolver uses.
    pub fn table(&self) -> &NameTable {
        self.table
    }

    /// Get the Interner this resolver uses.
    pub fn interner(&self) -> &Interner {
        self.interner
    }

    /// Primary API - resolve Symbol through the resolution chain.
    /// Returns None if the name is not found in any layer.
    pub fn resolve(&self, sym: Symbol) -> Option<NameId> {
        let name = self.interner.resolve(sym);
        self.resolve_str(name)
    }

    /// Resolve a string directly through the resolution chain.
    pub fn resolve_str(&self, name: &str) -> Option<NameId> {
        // 1. Primitives (always available)
        if let Some(id) = self.table.primitives.by_name(name) {
            return Some(id);
        }

        // 2. Current module
        if let Some(id) = self.table.name_id_raw(self.current_module, &[name]) {
            return Some(id);
        }

        // 3. Imports (non-transitive)
        for &import in self.imports {
            if let Some(id) = self.table.name_id_raw(import, &[name]) {
                return Some(id);
            }
        }

        // 4. Builtin module (stdlib types)
        if let Some(builtin) = self.table.builtin_module_id()
            && let Some(id) = self.table.name_id_raw(builtin, &[name])
        {
            return Some(id);
        }

        None
    }

    // --- Direct primitive access (zero lookup cost) ---

    pub fn i8(&self) -> NameId {
        self.table.primitives.i8
    }
    pub fn i16(&self) -> NameId {
        self.table.primitives.i16
    }
    pub fn i32(&self) -> NameId {
        self.table.primitives.i32
    }
    pub fn i64(&self) -> NameId {
        self.table.primitives.i64
    }
    pub fn i128(&self) -> NameId {
        self.table.primitives.i128
    }
    pub fn u8(&self) -> NameId {
        self.table.primitives.u8
    }
    pub fn u16(&self) -> NameId {
        self.table.primitives.u16
    }
    pub fn u32(&self) -> NameId {
        self.table.primitives.u32
    }
    pub fn u64(&self) -> NameId {
        self.table.primitives.u64
    }
    pub fn f32(&self) -> NameId {
        self.table.primitives.f32
    }
    pub fn f64(&self) -> NameId {
        self.table.primitives.f64
    }
    pub fn bool(&self) -> NameId {
        self.table.primitives.bool
    }
    pub fn string(&self) -> NameId {
        self.table.primitives.string
    }
    pub fn nil(&self) -> NameId {
        self.table.primitives.nil
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_primitives() {
        let interner = Interner::new();
        let table = NameTable::new();
        let resolver = Resolver::new(&interner, &table, table.main_module(), &[]);

        // Primitives should resolve
        assert_eq!(resolver.resolve_str("i32"), Some(table.primitives.i32));
        assert_eq!(resolver.resolve_str("i64"), Some(table.primitives.i64));
        assert_eq!(resolver.resolve_str("bool"), Some(table.primitives.bool));
        assert_eq!(
            resolver.resolve_str("string"),
            Some(table.primitives.string)
        );
        assert_eq!(resolver.resolve_str("nil"), Some(table.primitives.nil));
    }

    #[test]
    fn resolve_unknown_returns_none() {
        let interner = Interner::new();
        let table = NameTable::new();
        let resolver = Resolver::new(&interner, &table, table.main_module(), &[]);

        assert_eq!(resolver.resolve_str("unknown_type"), None);
        assert_eq!(resolver.resolve_str("MyClass"), None);
    }

    #[test]
    fn resolve_symbol() {
        let mut interner = Interner::new();
        let table = NameTable::new();

        // Intern symbols before creating resolver (to avoid borrow conflict)
        let i64_sym = interner.intern("i64");
        let unknown_sym = interner.intern("unknown");

        let resolver = Resolver::new(&interner, &table, table.main_module(), &[]);

        assert_eq!(resolver.resolve(i64_sym), Some(table.primitives.i64));
        assert_eq!(resolver.resolve(unknown_sym), None);
    }

    #[test]
    fn resolve_current_module() {
        let interner = Interner::new();
        let mut table = NameTable::new();
        let main = table.main_module();

        // Register a type in the main module
        let my_type = table.intern_raw(main, &["MyType"]);

        let resolver = Resolver::new(&interner, &table, main, &[]);
        assert_eq!(resolver.resolve_str("MyType"), Some(my_type));
    }

    #[test]
    fn resolve_imports() {
        let interner = Interner::new();
        let mut table = NameTable::new();
        let main = table.main_module();
        let other = table.module_id("other");

        // Register a type in another module
        let imported_type = table.intern_raw(other, &["ImportedType"]);

        // Without import, shouldn't resolve
        let resolver_no_import = Resolver::new(&interner, &table, main, &[]);
        assert_eq!(resolver_no_import.resolve_str("ImportedType"), None);

        // With import, should resolve
        let imports = vec![other];
        let resolver_with_import = Resolver::new(&interner, &table, main, &imports);
        assert_eq!(
            resolver_with_import.resolve_str("ImportedType"),
            Some(imported_type)
        );
    }

    #[test]
    fn resolve_builtin_module() {
        let interner = Interner::new();
        let mut table = NameTable::new();
        let main = table.main_module();
        let builtin = table.builtin_module();

        // Register a type in the builtin module (like Iterator)
        let iterator = table.intern_raw(builtin, &["Iterator"]);

        // Should resolve from builtin module
        let resolver = Resolver::new(&interner, &table, main, &[]);
        assert_eq!(resolver.resolve_str("Iterator"), Some(iterator));
    }

    #[test]
    fn primitives_take_precedence() {
        let interner = Interner::new();
        let mut table = NameTable::new();
        let main = table.main_module();

        // Try to shadow a primitive in the main module
        let shadowed_i32 = table.intern_raw(main, &["i32"]);

        // Primitive should still win
        let resolver = Resolver::new(&interner, &table, main, &[]);
        assert_eq!(resolver.resolve_str("i32"), Some(table.primitives.i32));
        assert_ne!(shadowed_i32, table.primitives.i32);
    }

    #[test]
    fn direct_primitive_access() {
        let interner = Interner::new();
        let table = NameTable::new();
        let resolver = Resolver::new(&interner, &table, table.main_module(), &[]);

        // Direct accessors should work
        assert_eq!(resolver.i32(), table.primitives.i32);
        assert_eq!(resolver.i64(), table.primitives.i64);
        assert_eq!(resolver.bool(), table.primitives.bool);
        assert_eq!(resolver.string(), table.primitives.string);
        assert_eq!(resolver.nil(), table.primitives.nil);
        assert_eq!(resolver.f64(), table.primitives.f64);
    }
}
