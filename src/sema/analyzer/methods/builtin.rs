use super::super::*;
use crate::sema::PrimitiveType;
use crate::sema::types::LegacyType;

impl Analyzer {
    /// Check if a method call is a built-in method on a primitive type
    /// Returns Some(function_type) if handled, None if not a built-in
    pub(crate) fn check_builtin_method(
        &mut self,
        object_type: &LegacyType,
        method_name: &str,
        args: &[Expr],
        interner: &Interner,
    ) -> Option<FunctionType> {
        match (object_type, method_name) {
            // Array.length() -> i64
            (LegacyType::Array(_), "length") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                Some(FunctionType::from_ids(
                    &[],
                    self.ty_i64_id(),
                    false,
                    &self.type_arena.borrow(),
                ))
            }
            // Array.iter() -> Iterator<T>
            (LegacyType::Array(elem_ty), "iter") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                // Convert element type to TypeId for interface_type_id
                let elem_ty_id = self.type_arena.borrow_mut().from_type(elem_ty);
                let iter_type_id = self.interface_type_id("Iterator", &[elem_ty_id], interner)?;
                Some(FunctionType::from_ids(
                    &[],
                    iter_type_id,
                    false,
                    &self.type_arena.borrow(),
                ))
            }
            // Range.iter() -> Iterator<i64>
            (LegacyType::Range, "iter") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                let iter_type_id = self.interface_type_id("Iterator", &[self.ty_i64_id()], interner)?;
                Some(FunctionType::from_ids(
                    &[],
                    iter_type_id,
                    false,
                    &self.type_arena.borrow(),
                ))
            }
            // String.length() -> i64
            (LegacyType::Primitive(PrimitiveType::String), "length") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                Some(FunctionType::from_ids(
                    &[],
                    self.ty_i64_id(),
                    false,
                    &self.type_arena.borrow(),
                ))
            }
            // String.iter() -> Iterator<string>
            (LegacyType::Primitive(PrimitiveType::String), "iter") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                let iter_type_id = self.interface_type_id("Iterator", &[self.ty_string_id()], interner)?;
                Some(FunctionType::from_ids(
                    &[],
                    iter_type_id,
                    false,
                    &self.type_arena.borrow(),
                ))
            }
            _ => None,
        }
    }
}
