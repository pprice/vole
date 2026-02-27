// entity_metadata.rs
//
// VIR-native entity metadata: type definitions, fields, methods, and
// implementations.  This data replaces codegen's `EntityView` dependency
// on sema's `EntityRegistry`.
//
// Populated once during VIR lowering (which has full sema access), then
// consumed by codegen without reaching back into sema.

use rustc_hash::FxHashMap;
use vole_identity::{FieldId, MethodId, NameId, TypeDefId, VirTypeId};

// ---------------------------------------------------------------------------
// Type definition kind
// ---------------------------------------------------------------------------

/// What kind of entity a type definition represents.
///
/// Mirrors `sema::entity_defs::TypeDefKind` without depending on sema.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VirTypeDefKind {
    Interface,
    Class,
    Struct,
    ErrorType,
    Primitive,
    Alias,
    Sentinel,
}

impl VirTypeDefKind {
    /// Whether this is a sentinel type (zero-field struct).
    pub fn is_sentinel(self) -> bool {
        matches!(self, Self::Sentinel)
    }

    /// Whether this is a class, struct, or sentinel.
    pub fn is_class_struct_or_sentinel(self) -> bool {
        matches!(self, Self::Class | Self::Struct | Self::Sentinel)
    }

    /// Whether this is an interface.
    pub fn is_interface(self) -> bool {
        matches!(self, Self::Interface)
    }
}

// ---------------------------------------------------------------------------
// Type definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a type definition.
///
/// Carries the entity-level data that codegen queries via `EntityView`:
/// kind, fields, methods, implemented interfaces, and type parameters.
#[derive(Debug, Clone)]
pub struct VirTypeDef {
    /// The sema entity ID for this type.
    pub id: TypeDefId,
    /// The canonical name of this type.
    pub name_id: NameId,
    /// What kind of type this is.
    pub kind: VirTypeDefKind,
    /// Field IDs declared on this type (ordered by declaration).
    pub fields: Vec<FieldId>,
    /// Instance method IDs declared on this type.
    pub methods: Vec<MethodId>,
    /// Static method IDs declared on this type.
    pub static_methods: Vec<MethodId>,
    /// Interfaces this type extends (for interfaces) or empty.
    pub extends: Vec<TypeDefId>,
    /// Type parameter names (e.g. T, K, V).
    pub type_params: Vec<NameId>,
    /// Interfaces implemented by this type.
    pub implements: Vec<VirImplementation>,
    /// Whether this type is an annotation type.
    pub is_annotation: bool,
}

// ---------------------------------------------------------------------------
// Field definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a field definition.
///
/// Contains the field name, type, and slot index — everything codegen
/// needs for field access without reaching back into sema.
#[derive(Debug, Clone)]
pub struct VirFieldDef {
    /// The sema entity ID for this field.
    pub id: FieldId,
    /// The field name.
    pub name_id: NameId,
    /// Fully qualified field name (e.g. `Point::x`).
    pub full_name_id: NameId,
    /// The type that owns this field.
    pub defining_type: TypeDefId,
    /// The field's VIR type.
    pub vir_ty: VirTypeId,
    /// The field's slot index in the type's storage layout.
    pub slot: usize,
}

// ---------------------------------------------------------------------------
// Method definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a method definition.
///
/// Contains method name, signature info, and dispatch metadata for
/// codegen without reaching back into sema.
#[derive(Debug, Clone)]
pub struct VirMethodDef {
    /// The sema entity ID for this method.
    pub id: MethodId,
    /// The method's short name (e.g. `next`).
    pub name_id: NameId,
    /// Fully qualified method name (e.g. `Iterator::next`).
    pub full_name_id: NameId,
    /// The type that defines this method.
    pub defining_type: TypeDefId,
    /// Whether this method has a default implementation.
    pub has_default: bool,
    /// Whether this is a static method.
    pub is_static: bool,
    /// Number of required parameters (without defaults).
    pub required_params: usize,
    /// Parameter names in declaration order (excluding `self`).
    pub param_names: Vec<String>,
}

// ---------------------------------------------------------------------------
// Implementation metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for an interface implementation.
///
/// Records which interface a type implements and its method bindings.
#[derive(Debug, Clone)]
pub struct VirImplementation {
    /// The interface being implemented.
    pub interface: TypeDefId,
    /// Method bindings for this implementation.
    pub method_bindings: Vec<VirMethodBinding>,
}

/// A single method binding in an implementation block.
#[derive(Debug, Clone)]
pub struct VirMethodBinding {
    /// The method name.
    pub method_name: NameId,
    /// Whether this is a builtin method.
    pub is_builtin: bool,
}

// ---------------------------------------------------------------------------
// VirEntityMetadata — the top-level container
// ---------------------------------------------------------------------------

/// Complete entity metadata for a VIR program.
///
/// Replaces `EntityView` as the codegen-accessible source of type, field,
/// and method metadata.  Populated once during VIR lowering from sema's
/// `EntityRegistry`.
#[derive(Debug, Clone, Default)]
pub struct VirEntityMetadata {
    /// Type definitions keyed by `TypeDefId`.
    type_defs: FxHashMap<TypeDefId, VirTypeDef>,
    /// Field definitions keyed by `FieldId`.
    field_defs: FxHashMap<FieldId, VirFieldDef>,
    /// Method definitions keyed by `MethodId`.
    method_defs: FxHashMap<MethodId, VirMethodDef>,
}

// ---------------------------------------------------------------------------
// Mutation (population during lowering)
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Create an empty metadata container.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a type definition.
    pub fn insert_type_def(&mut self, type_def: VirTypeDef) {
        self.type_defs.insert(type_def.id, type_def);
    }

    /// Register a field definition.
    pub fn insert_field_def(&mut self, field_def: VirFieldDef) {
        self.field_defs.insert(field_def.id, field_def);
    }

    /// Register a method definition.
    pub fn insert_method_def(&mut self, method_def: VirMethodDef) {
        self.method_defs.insert(method_def.id, method_def);
    }
}

// ---------------------------------------------------------------------------
// Type queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a type definition by ID.
    pub fn get_type_def(&self, id: TypeDefId) -> Option<&VirTypeDef> {
        self.type_defs.get(&id)
    }

    /// Return the kind of a type definition.
    pub fn type_def_kind(&self, id: TypeDefId) -> Option<VirTypeDefKind> {
        self.type_defs.get(&id).map(|td| td.kind)
    }

    /// Return field IDs declared on a type.
    pub fn fields_on_type(&self, id: TypeDefId) -> Option<&[FieldId]> {
        self.type_defs.get(&id).map(|td| td.fields.as_slice())
    }

    /// Return instance method IDs declared on a type.
    pub fn methods_on_type(&self, id: TypeDefId) -> Option<&[MethodId]> {
        self.type_defs.get(&id).map(|td| td.methods.as_slice())
    }

    /// Return static method IDs declared on a type.
    pub fn static_methods_on_type(&self, id: TypeDefId) -> Option<&[MethodId]> {
        self.type_defs
            .get(&id)
            .map(|td| td.static_methods.as_slice())
    }

    /// Return interfaces implemented by a type.
    pub fn implemented_interfaces(&self, id: TypeDefId) -> Vec<TypeDefId> {
        self.type_defs
            .get(&id)
            .map(|td| td.implements.iter().map(|i| i.interface).collect())
            .unwrap_or_default()
    }

    /// Return type parameter names for a type.
    pub fn type_params(&self, id: TypeDefId) -> Option<&[NameId]> {
        self.type_defs.get(&id).map(|td| td.type_params.as_slice())
    }

    /// Return the canonical name of a type.
    pub fn type_name_id(&self, id: TypeDefId) -> Option<NameId> {
        self.type_defs.get(&id).map(|td| td.name_id)
    }

    /// Return the extends list (parent interfaces) for a type.
    pub fn type_extends(&self, id: TypeDefId) -> Option<&[TypeDefId]> {
        self.type_defs.get(&id).map(|td| td.extends.as_slice())
    }

    /// Whether a type is an annotation type.
    pub fn is_annotation(&self, id: TypeDefId) -> bool {
        self.type_defs.get(&id).is_some_and(|td| td.is_annotation)
    }

    /// Return the number of registered type definitions.
    pub fn type_def_count(&self) -> usize {
        self.type_defs.len()
    }
}

// ---------------------------------------------------------------------------
// Field queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a field definition by ID.
    pub fn get_field_def(&self, id: FieldId) -> Option<&VirFieldDef> {
        self.field_defs.get(&id)
    }

    /// Return the VIR type of a field.
    pub fn field_vir_type(&self, id: FieldId) -> Option<VirTypeId> {
        self.field_defs.get(&id).map(|fd| fd.vir_ty)
    }

    /// Return the slot index of a field.
    pub fn field_slot(&self, id: FieldId) -> Option<usize> {
        self.field_defs.get(&id).map(|fd| fd.slot)
    }

    /// Return the name of a field.
    pub fn field_name_id(&self, id: FieldId) -> Option<NameId> {
        self.field_defs.get(&id).map(|fd| fd.name_id)
    }

    /// Return the defining type of a field.
    pub fn field_defining_type(&self, id: FieldId) -> Option<TypeDefId> {
        self.field_defs.get(&id).map(|fd| fd.defining_type)
    }

    /// Return the number of registered field definitions.
    pub fn field_def_count(&self) -> usize {
        self.field_defs.len()
    }
}

// ---------------------------------------------------------------------------
// Method queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a method definition by ID.
    pub fn get_method_def(&self, id: MethodId) -> Option<&VirMethodDef> {
        self.method_defs.get(&id)
    }

    /// Return the full name of a method.
    pub fn method_full_name_id(&self, id: MethodId) -> Option<NameId> {
        self.method_defs.get(&id).map(|md| md.full_name_id)
    }

    /// Return whether a method has a default implementation.
    pub fn method_has_default(&self, id: MethodId) -> Option<bool> {
        self.method_defs.get(&id).map(|md| md.has_default)
    }

    /// Return the defining type of a method.
    pub fn method_defining_type(&self, id: MethodId) -> Option<TypeDefId> {
        self.method_defs.get(&id).map(|md| md.defining_type)
    }

    /// Return the number of registered method definitions.
    pub fn method_def_count(&self) -> usize {
        self.method_defs.len()
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_type_def_id(n: u32) -> TypeDefId {
        TypeDefId::new(n)
    }

    fn make_field_id(n: u32) -> FieldId {
        FieldId::new(n)
    }

    fn make_method_id(n: u32) -> MethodId {
        MethodId::new(n)
    }

    fn make_name_id(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    #[test]
    fn empty_metadata() {
        let meta = VirEntityMetadata::new();
        assert_eq!(meta.type_def_count(), 0);
        assert_eq!(meta.field_def_count(), 0);
        assert_eq!(meta.method_def_count(), 0);
    }

    #[test]
    fn insert_and_query_type_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);
        let field_id = make_field_id(10);
        let method_id = make_method_id(20);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![field_id],
            methods: vec![method_id],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![make_name_id(200)],
            implements: vec![VirImplementation {
                interface: make_type_def_id(2),
                method_bindings: vec![],
            }],
            is_annotation: false,
        });

        assert_eq!(meta.type_def_count(), 1);

        let td = meta.get_type_def(id).expect("should find type def");
        assert_eq!(td.kind, VirTypeDefKind::Class);
        assert_eq!(td.fields, vec![field_id]);
        assert_eq!(td.methods, vec![method_id]);

        assert_eq!(meta.type_def_kind(id), Some(VirTypeDefKind::Class));
        assert_eq!(meta.fields_on_type(id), Some(&[field_id][..]));
        assert_eq!(meta.methods_on_type(id), Some(&[method_id][..]));
        assert_eq!(meta.type_name_id(id), Some(make_name_id(100)));
        assert_eq!(meta.type_params(id), Some(&[make_name_id(200)][..]));
        assert_eq!(meta.implemented_interfaces(id), vec![make_type_def_id(2)]);
        assert!(!meta.is_annotation(id));
    }

    #[test]
    fn insert_and_query_field_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_field_id(5);

        meta.insert_field_def(VirFieldDef {
            id,
            name_id: make_name_id(50),
            full_name_id: make_name_id(51),
            defining_type: make_type_def_id(1),
            vir_ty: VirTypeId::I64,
            slot: 3,
        });

        assert_eq!(meta.field_def_count(), 1);

        let fd = meta.get_field_def(id).expect("should find field def");
        assert_eq!(fd.slot, 3);
        assert_eq!(fd.vir_ty, VirTypeId::I64);

        assert_eq!(meta.field_vir_type(id), Some(VirTypeId::I64));
        assert_eq!(meta.field_slot(id), Some(3));
        assert_eq!(meta.field_name_id(id), Some(make_name_id(50)));
        assert_eq!(meta.field_defining_type(id), Some(make_type_def_id(1)));
    }

    #[test]
    fn insert_and_query_method_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_method_id(7);

        meta.insert_method_def(VirMethodDef {
            id,
            name_id: make_name_id(70),
            full_name_id: make_name_id(71),
            defining_type: make_type_def_id(2),
            has_default: true,
            is_static: false,
            required_params: 2,
            param_names: vec!["x".into(), "y".into()],
        });

        assert_eq!(meta.method_def_count(), 1);

        let md = meta.get_method_def(id).expect("should find method def");
        assert!(md.has_default);
        assert!(!md.is_static);
        assert_eq!(md.required_params, 2);
        assert_eq!(md.param_names, vec!["x", "y"]);

        assert_eq!(meta.method_full_name_id(id), Some(make_name_id(71)));
        assert_eq!(meta.method_has_default(id), Some(true));
        assert_eq!(meta.method_defining_type(id), Some(make_type_def_id(2)));
    }

    #[test]
    fn missing_lookups_return_none() {
        let meta = VirEntityMetadata::new();
        assert!(meta.get_type_def(make_type_def_id(99)).is_none());
        assert!(meta.get_field_def(make_field_id(99)).is_none());
        assert!(meta.get_method_def(make_method_id(99)).is_none());
        assert!(meta.type_def_kind(make_type_def_id(99)).is_none());
        assert!(meta.field_vir_type(make_field_id(99)).is_none());
        assert!(meta.method_full_name_id(make_method_id(99)).is_none());
        assert!(meta.implemented_interfaces(make_type_def_id(99)).is_empty());
    }

    #[test]
    fn type_def_kind_predicates() {
        assert!(VirTypeDefKind::Sentinel.is_sentinel());
        assert!(!VirTypeDefKind::Class.is_sentinel());

        assert!(VirTypeDefKind::Class.is_class_struct_or_sentinel());
        assert!(VirTypeDefKind::Struct.is_class_struct_or_sentinel());
        assert!(VirTypeDefKind::Sentinel.is_class_struct_or_sentinel());
        assert!(!VirTypeDefKind::Interface.is_class_struct_or_sentinel());

        assert!(VirTypeDefKind::Interface.is_interface());
        assert!(!VirTypeDefKind::Class.is_interface());
    }

    #[test]
    fn annotation_type() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(42);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(420),
            kind: VirTypeDefKind::Struct,
            fields: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: true,
        });

        assert!(meta.is_annotation(id));
    }

    #[test]
    fn interface_with_extends() {
        let mut meta = VirEntityMetadata::new();
        let parent = make_type_def_id(1);
        let child = make_type_def_id(2);

        meta.insert_type_def(VirTypeDef {
            id: child,
            name_id: make_name_id(200),
            kind: VirTypeDefKind::Interface,
            fields: vec![],
            methods: vec![make_method_id(30)],
            static_methods: vec![],
            extends: vec![parent],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
        });

        assert_eq!(meta.type_extends(child), Some(&[parent][..]));
    }

    #[test]
    fn overwrite_type_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![make_field_id(1)],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
        });

        // Overwrite with different data.
        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(101),
            kind: VirTypeDefKind::Struct,
            fields: vec![make_field_id(2), make_field_id(3)],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
        });

        assert_eq!(meta.type_def_count(), 1);
        let td = meta.get_type_def(id).unwrap();
        assert_eq!(td.kind, VirTypeDefKind::Struct);
        assert_eq!(td.fields.len(), 2);
        assert_eq!(td.name_id, make_name_id(101));
    }
}
