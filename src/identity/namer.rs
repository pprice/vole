use crate::frontend::{Interner, Symbol};
use crate::identity::{ModuleId, NameId, NameTable};

pub struct Namer<'a> {
    interner: &'a Interner,
    names: &'a mut NameTable,
}

pub struct NamerLookup<'a> {
    interner: &'a Interner,
    names: &'a NameTable,
}

impl<'a> Namer<'a> {
    pub fn new(names: &'a mut NameTable, interner: &'a Interner) -> Self {
        Self { interner, names }
    }

    pub fn intern_symbol(&mut self, module: ModuleId, name: Symbol) -> NameId {
        self.names.intern(module, &[name])
    }

    pub fn intern_raw(&mut self, module: ModuleId, segments: &[&str]) -> NameId {
        self.names.intern_raw(module, segments)
    }

    pub fn function(&mut self, module: ModuleId, name: Symbol) -> NameId {
        self.names.intern(module, &[name])
    }

    pub fn method(&mut self, name: Symbol) -> NameId {
        let module = self.names.builtin_module();
        let name_str = self.interner.resolve(name);
        self.names.intern_raw(module, &[name_str])
    }

    pub fn test(&mut self, index: usize) -> NameId {
        let module = self.names.builtin_module();
        self.names.intern_indexed_raw(module, "__test_", index)
    }

    pub fn lambda(&mut self, index: usize) -> NameId {
        let module = self.names.builtin_module();
        self.names.intern_indexed_raw(module, "__lambda_", index)
    }

    pub fn monomorph(&mut self, module: ModuleId, base: Symbol, id: u32) -> NameId {
        let base_name = self.interner.resolve(base);
        let mangled = format!("{}__mono_{}", base_name, id);
        self.names.intern_raw(module, &[mangled.as_str()])
    }
}

impl<'a> NamerLookup<'a> {
    pub fn new(names: &'a NameTable, interner: &'a Interner) -> Self {
        Self { interner, names }
    }

    pub fn function(&self, module: ModuleId, name: Symbol) -> Option<NameId> {
        self.names.name_id(module, &[name])
    }

    pub fn method(&self, name: Symbol) -> Option<NameId> {
        let module = self.names.builtin_module_id()?;
        let name_str = self.interner.resolve(name);
        self.names.name_id_raw(module, &[name_str])
    }
}
