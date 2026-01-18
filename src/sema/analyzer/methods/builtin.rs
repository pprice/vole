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
                let iter_type =
                    self.interface_type("Iterator", vec![*elem_ty.clone()], interner)?;
                Some(FunctionType::new_with_arena(
                    Vec::<LegacyType>::new(),
                    iter_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                ))
            }
            // Range.iter() -> Iterator<i64>
            (LegacyType::Range, "iter") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                let i64_ty = self.type_arena.borrow().to_type(self.ty_i64_id());
                let iter_type = self.interface_type("Iterator", vec![i64_ty], interner)?;
                Some(FunctionType::new_with_arena(
                    Vec::<LegacyType>::new(),
                    iter_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
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
                let string_ty = self.type_arena.borrow().to_type(self.ty_string_id());
                let iter_type = self.interface_type("Iterator", vec![string_ty], interner)?;
                Some(FunctionType::new_with_arena(
                    Vec::<LegacyType>::new(),
                    iter_type,
                    false,
                    &mut self.type_arena.borrow_mut(),
                ))
            }
            _ => None,
        }
    }
}
