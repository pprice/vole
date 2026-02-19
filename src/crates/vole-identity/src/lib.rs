// src/identity.rs
//
// Shared name interning for fully-qualified item identities.
// Defines Symbol, Span, and Interner as foundational primitives.

use std::hash::{BuildHasher, Hash, Hasher};

use rustc_hash::{FxBuildHasher, FxHashMap};

mod intern;
mod primitive_type;
mod span;
mod symbol;

pub use intern::Interner;
pub use primitive_type::PrimitiveType;
pub use span::Span;
pub use symbol::Symbol;

mod entities;
mod namer;
mod resolver;
pub use entities::{FieldId, FunctionId, GlobalId, MethodId, TypeDefId, TypeParamId};
pub use namer::{Namer, NamerLookup, method_name_id_by_str};
pub use resolver::Resolver;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ModuleId(u32);

impl ModuleId {
    pub fn new(index: u32) -> Self {
        Self(index)
    }

    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NameId(u32);

impl NameId {
    /// Create a NameId for testing purposes only.
    /// Production code should use NameTable::intern() instead.
    #[doc(hidden)]
    pub fn new_for_test(index: u32) -> Self {
        Self(index)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualifiedName {
    module: ModuleId,
    segments: Vec<String>,
}

impl QualifiedName {
    /// Get the module this name belongs to.
    pub fn module(&self) -> ModuleId {
        self.module
    }

    /// Get the segments of this qualified name.
    pub fn segments(&self) -> &[String] {
        &self.segments
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct NameKey {
    module: ModuleId,
    segments: Vec<String>,
}

/// Source location where a name was defined (for diagnostics)
#[derive(Debug, Clone)]
pub struct DefLocation {
    pub file: String,
    pub span: Span,
}

/// Macro for defining name-based primitives with a single source of truth.
/// Each entry defines the field name (which is also used as the string key for by_name lookup).
macro_rules! define_name_primitives {
    ($($name:ident),* $(,)?) => {
        /// Cached NameIds for language primitives.
        /// Registered at NameTable creation, always available.
        #[derive(Debug, Clone)]
        pub struct Primitives {
            $(pub $name: NameId),*
        }

        impl Primitives {
            /// Look up a primitive by name
            pub fn by_name(&self, name: &str) -> Option<NameId> {
                match name {
                    $(stringify!($name) => Some(self.$name)),*,
                    _ => None,
                }
            }

            /// Initialize all fields to a placeholder value
            fn placeholder(placeholder: NameId) -> Self {
                Self {
                    $($name: placeholder),*
                }
            }

            /// Register all primitives in the given module, interning via the provided closure.
            /// Returns a new Primitives struct with all NameIds populated.
            fn register<F>(mut intern: F) -> Self
            where
                F: FnMut(&str) -> NameId,
            {
                Self {
                    $($name: intern(stringify!($name))),*
                }
            }

            /// Iterate over all primitive NameIds.
            /// Useful for registering all primitives in bulk.
            pub fn iter(&self) -> impl Iterator<Item = NameId> + '_ {
                [$(self.$name),*].into_iter()
            }
        }
    };
}

// Define all name-based primitives (16 types that have NameIds)
define_name_primitives!(
    i8, i16, i32, i64, i128, u8, u16, u32, u64, f32, f64, f128, bool, string, handle, nil
);

impl Primitives {
    /// Map PrimitiveType to NameId
    pub fn from_ast(&self, prim: PrimitiveType) -> NameId {
        match prim {
            PrimitiveType::I8 => self.i8,
            PrimitiveType::I16 => self.i16,
            PrimitiveType::I32 => self.i32,
            PrimitiveType::I64 => self.i64,
            PrimitiveType::I128 => self.i128,
            PrimitiveType::U8 => self.u8,
            PrimitiveType::U16 => self.u16,
            PrimitiveType::U32 => self.u32,
            PrimitiveType::U64 => self.u64,
            PrimitiveType::F32 => self.f32,
            PrimitiveType::F64 => self.f64,
            PrimitiveType::F128 => self.f128,
            PrimitiveType::Bool => self.bool,
            PrimitiveType::String => self.string,
        }
    }
}

/// Macro for defining well-known interface types with a single source of truth.
/// Each entry is (field_name, "InterfaceName") - the string is the name as it
/// appears in `std:prelude/traits`.
macro_rules! define_well_known_interfaces {
    ($(($field:ident, $name:expr)),* $(,)?) => {
        /// Well-known type identifiers from the stdlib prelude.
        /// These are populated after prelude loading for fast type identification.
        #[derive(Debug, Clone, Default)]
        pub struct WellKnownTypes {
            $(
                pub $field: Option<TypeDefId>,
            )*
        }

        impl WellKnownTypes {
            /// Create an empty WellKnownTypes (before prelude is loaded)
            pub fn new() -> Self {
                Self::default()
            }

            /// Build a fully populated WellKnownTypes.
            /// `lookup` resolves an interface name string to its TypeDefId.
            pub fn populated<F>(mut lookup: F) -> Self
            where
                F: FnMut(&str) -> Option<TypeDefId>,
            {
                Self {
                    $(
                        $field: lookup($name),
                    )*
                }
            }
        }
    };
}

// Single source of truth for well-known interface names.
// Adding a new well-known type is a single-line change here.
define_well_known_interfaces!(
    (iterator_type_def, "Iterator"),
    (iterable_type_def, "Iterable"),
    (equatable_type_def, "Equatable"),
    (comparable_type_def, "Comparable"),
    (hashable_type_def, "Hashable"),
    (stringable_type_def, "Stringable"),
    (transferable_type_def, "Transferable"),
);

impl WellKnownTypes {
    /// Check if a TypeDefId is the Iterator interface
    pub fn is_iterator_type_def(&self, type_def_id: TypeDefId) -> bool {
        self.iterator_type_def == Some(type_def_id)
    }

    /// Check if a TypeDefId is the Iterable interface
    pub fn is_iterable_type_def(&self, type_def_id: TypeDefId) -> bool {
        self.iterable_type_def == Some(type_def_id)
    }

    /// Check if a TypeDefId is the Transferable interface
    pub fn is_transferable_type_def(&self, type_def_id: TypeDefId) -> bool {
        self.transferable_type_def == Some(type_def_id)
    }
}

/// Well-known method MethodIds from the stdlib prelude.
#[derive(Debug, Clone, Default)]
pub struct WellKnownMethods {
    /// Iterator::next
    pub iterator_next: Option<MethodId>,
    /// Iterable::iter
    pub iterable_iter: Option<MethodId>,
    /// Stringable::to_string
    pub stringable_to_string: Option<MethodId>,
    /// Equatable::equals
    pub equatable_equals: Option<MethodId>,
    /// Comparable::compare
    pub comparable_compare: Option<MethodId>,
    /// Hashable::hash
    pub hashable_hash: Option<MethodId>,
}

impl WellKnownMethods {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Compute the hash for a `(ModuleId, segments)` pair using borrowed slices.
///
/// This produces the same hash as `NameKey::hash()` for the same logical content,
/// because `[&str]` and `[String]` hash identically (str and String have the same
/// Hash impl, and slice hashing is element-wise).
fn name_hash(hasher: &FxBuildHasher, module: ModuleId, segments: &[&str]) -> u64 {
    let mut state = hasher.build_hasher();
    module.hash(&mut state);
    segments.hash(&mut state);
    state.finish()
}

#[derive(Debug, Clone)]
pub struct NameTable {
    modules: Vec<String>,
    module_lookup: FxHashMap<String, ModuleId>,
    names: Vec<QualifiedName>,
    name_lookup: hashbrown::HashMap<NameKey, NameId, FxBuildHasher>,
    main_module: ModuleId,
    diagnostics: FxHashMap<NameId, DefLocation>,
    pub primitives: Primitives,
    pub well_known: WellKnownTypes,
}

impl NameTable {
    pub fn new() -> Self {
        // Use placeholder NameIds - they'll be overwritten before new() returns
        let mut table = Self {
            modules: Vec::new(),
            module_lookup: FxHashMap::default(),
            names: Vec::new(),
            name_lookup: hashbrown::HashMap::with_hasher(FxBuildHasher),
            main_module: ModuleId(0),
            diagnostics: FxHashMap::default(),
            primitives: Primitives::placeholder(NameId(0)),
            well_known: WellKnownTypes::new(),
        };
        let main_module = table.module_id("main");
        table.main_module = main_module;
        let _ = table.module_id("");

        // Register primitives in the builtin module
        table.primitives = table.register_primitives();
        table
    }

    /// Populate well-known type NameIds after prelude has been loaded.
    /// This is now a no-op - TypeDefIds are populated directly via populate_type_def_ids.
    pub fn populate_well_known(&mut self) {
        // TypeDefIds are populated via populate_type_def_ids after EntityRegistry is ready
    }

    /// Get the NameId for a well-known interface by name.
    /// Used internally by populate_type_def_ids.
    pub fn well_known_interface_name_id(&mut self, name: &str) -> NameId {
        let traits_module = self.module_id("std:prelude/traits");
        self.intern_raw(traits_module, &[name])
    }

    fn register_primitives(&mut self) -> Primitives {
        let builtin = self.builtin_module();
        Primitives::register(|name| self.intern_raw(builtin, &[name]))
    }

    pub fn main_module(&self) -> ModuleId {
        self.main_module
    }

    pub fn module_id(&mut self, path: &str) -> ModuleId {
        if let Some(id) = self.module_lookup.get(path) {
            return *id;
        }
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(path.to_string());
        self.module_lookup.insert(path.to_string(), id);
        id
    }

    pub fn module_id_if_known(&self, path: &str) -> Option<ModuleId> {
        self.module_lookup.get(path).copied()
    }

    pub fn builtin_module(&mut self) -> ModuleId {
        self.module_id("")
    }

    pub fn builtin_module_id(&self) -> Option<ModuleId> {
        self.module_id_if_known("")
    }

    pub fn module_path(&self, module: ModuleId) -> &str {
        &self.modules[module.0 as usize]
    }

    pub fn intern(&mut self, module: ModuleId, segments: &[Symbol], interner: &Interner) -> NameId {
        // Resolve symbols to &str without allocating Strings yet.
        // SmallVec-style: stack-allocate for the common case (<=4 segments).
        let resolved: Vec<&str> = segments.iter().map(|s| interner.resolve(*s)).collect();
        self.intern_raw(module, &resolved)
    }

    /// Intern a qualified name from borrowed string segments.
    ///
    /// Uses `raw_entry_mut` for zero-allocation lookups on cache hit.
    /// On cache miss, allocates one `Vec<String>` shared (via clone)
    /// between the lookup key and QualifiedName storage.
    pub fn intern_raw(&mut self, module: ModuleId, segments: &[&str]) -> NameId {
        use hashbrown::hash_map::RawEntryMut;

        let hash = name_hash(self.name_lookup.hasher(), module, segments);
        let entry = self.name_lookup.raw_entry_mut().from_hash(hash, |key| {
            key.module == module
                && key.segments.len() == segments.len()
                && key.segments.iter().zip(segments).all(|(a, b)| a == *b)
        });

        match entry {
            RawEntryMut::Occupied(e) => *e.get(),
            RawEntryMut::Vacant(e) => {
                let id = NameId(self.names.len() as u32);
                let owned: Vec<String> = segments.iter().map(|s| (*s).to_string()).collect();
                self.names.push(QualifiedName {
                    module,
                    segments: owned.clone(),
                });
                e.insert_hashed_nocheck(
                    hash,
                    NameKey {
                        module,
                        segments: owned,
                    },
                    id,
                );
                id
            }
        }
    }

    pub fn intern_indexed_raw(&mut self, module: ModuleId, prefix: &str, index: usize) -> NameId {
        let name = format!("{}{}", prefix, index);
        self.intern_raw(module, &[name.as_str()])
    }

    pub fn name_id(
        &self,
        module: ModuleId,
        segments: &[Symbol],
        interner: &Interner,
    ) -> Option<NameId> {
        // Resolve symbols to &str without allocating Strings.
        let resolved: Vec<&str> = segments.iter().map(|s| interner.resolve(*s)).collect();
        self.name_id_raw(module, &resolved)
    }

    /// Read-only lookup by borrowed segments. Zero allocations.
    pub fn name_id_raw(&self, module: ModuleId, segments: &[&str]) -> Option<NameId> {
        let hash = name_hash(self.name_lookup.hasher(), module, segments);
        self.name_lookup
            .raw_entry()
            .from_hash(hash, |key| {
                key.module == module
                    && key.segments.len() == segments.len()
                    && key.segments.iter().zip(segments).all(|(a, b)| a == *b)
            })
            .map(|(_, id)| *id)
    }

    pub fn name(&self, id: NameId) -> &QualifiedName {
        &self.names[id.0 as usize]
    }

    pub fn module_of(&self, id: NameId) -> ModuleId {
        self.name(id).module
    }

    pub fn intern_with_symbol(
        &mut self,
        prefix: NameId,
        symbol: Symbol,
        interner: &Interner,
    ) -> NameId {
        use hashbrown::hash_map::RawEntryMut;

        // Access names directly by index to allow disjoint borrows of
        // self.names and self.name_lookup.
        let name = &self.names[prefix.0 as usize];
        let module = name.module;
        let suffix = interner.resolve(symbol);

        // Build borrowed segments for hashing/comparison without allocating Strings.
        let mut all_strs: Vec<&str> = Vec::with_capacity(name.segments.len() + 1);
        for s in &name.segments {
            all_strs.push(s.as_str());
        }
        all_strs.push(suffix);

        let hash = name_hash(self.name_lookup.hasher(), module, &all_strs);
        let entry = self.name_lookup.raw_entry_mut().from_hash(hash, |key| {
            key.module == module
                && key.segments.len() == all_strs.len()
                && key.segments.iter().zip(&all_strs).all(|(a, b)| a == *b)
        });

        match entry {
            RawEntryMut::Occupied(e) => *e.get(),
            RawEntryMut::Vacant(e) => {
                let id = NameId(self.names.len() as u32);
                let owned: Vec<String> = all_strs.iter().map(|s| (*s).to_string()).collect();
                self.names.push(QualifiedName {
                    module,
                    segments: owned.clone(),
                });
                e.insert_hashed_nocheck(
                    hash,
                    NameKey {
                        module,
                        segments: owned,
                    },
                    id,
                );
                id
            }
        }
    }

    /// Read-only lookup for a name built from a prefix NameId plus a symbol segment.
    /// Returns `None` if the name has not been interned. Zero allocations.
    pub fn name_id_with_symbol(
        &self,
        prefix: NameId,
        symbol: Symbol,
        interner: &Interner,
    ) -> Option<NameId> {
        let name = self.name(prefix);
        let module = name.module;
        let suffix = interner.resolve(symbol);

        // Build borrowed segments for hashing/comparison without allocating Strings.
        let prefix_strs: Vec<&str> = name.segments.iter().map(|s| s.as_str()).collect();
        let mut all_strs: Vec<&str> = prefix_strs;
        all_strs.push(suffix);

        let hash = name_hash(self.name_lookup.hasher(), module, &all_strs);
        self.name_lookup
            .raw_entry()
            .from_hash(hash, |key| {
                key.module == module
                    && key.segments.len() == all_strs.len()
                    && key.segments.iter().zip(&all_strs).all(|(a, b)| a == *b)
            })
            .map(|(_, id)| *id)
    }

    pub fn display(&self, id: NameId) -> String {
        let name = self.name(id);
        let module = self.module_path(name.module);
        let mut out = String::new();
        if !module.is_empty() {
            out.push_str(module);
        }
        for (idx, segment) in name.segments.iter().enumerate() {
            if !out.is_empty() || idx > 0 {
                out.push_str("::");
            }
            out.push_str(segment);
        }
        out
    }

    pub fn last_segment_str(&self, id: NameId) -> Option<String> {
        let name = self.name(id);
        name.segments.last().cloned()
    }

    /// Record where a name was defined (for error messages)
    pub fn set_location(&mut self, id: NameId, file: &str, span: Span) {
        self.diagnostics.insert(
            id,
            DefLocation {
                file: file.to_string(),
                span,
            },
        );
    }

    /// Get the definition location for a name (if recorded)
    pub fn location(&self, id: NameId) -> Option<&DefLocation> {
        self.diagnostics.get(&id)
    }
}

impl Default for NameTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Interner;

    #[test]
    fn name_table_displays_module_and_segments() {
        let mut interner = Interner::new();
        let foo = interner.intern("foo");
        let bar = interner.intern("bar");

        let mut names = NameTable::new();
        let module = names.module_id("std:math");
        let name_id = names.intern(module, &[foo, bar], &interner);

        assert_eq!(names.display(name_id), "std:math::foo::bar");
    }

    #[test]
    fn primitives_registered_at_creation() {
        let names = NameTable::new();

        // All primitives should be registered and have valid NameIds
        assert_eq!(names.display(names.primitives.i32), "i32");
        assert_eq!(names.display(names.primitives.i64), "i64");
        assert_eq!(names.display(names.primitives.bool), "bool");
        assert_eq!(names.display(names.primitives.string), "string");
        assert_eq!(names.display(names.primitives.nil), "nil");
        assert_eq!(names.display(names.primitives.f64), "f64");
    }

    #[test]
    fn primitives_by_name_lookup() {
        let names = NameTable::new();

        // by_name should return the correct NameId
        assert_eq!(names.primitives.by_name("i32"), Some(names.primitives.i32));
        assert_eq!(names.primitives.by_name("i64"), Some(names.primitives.i64));
        assert_eq!(
            names.primitives.by_name("bool"),
            Some(names.primitives.bool)
        );
        assert_eq!(
            names.primitives.by_name("string"),
            Some(names.primitives.string)
        );
        assert_eq!(names.primitives.by_name("nil"), Some(names.primitives.nil));

        // Unknown names should return None
        assert_eq!(names.primitives.by_name("foo"), None);
        assert_eq!(names.primitives.by_name("int"), None);
    }

    #[test]
    fn primitives_in_builtin_module() {
        let names = NameTable::new();
        let builtin = names.builtin_module_id().unwrap();

        // Primitives should be in the builtin module
        assert_eq!(names.module_of(names.primitives.i32), builtin);
        assert_eq!(names.module_of(names.primitives.string), builtin);
    }
}
