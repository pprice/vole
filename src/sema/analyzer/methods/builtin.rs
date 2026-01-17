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
        let method_type = |params: Vec<LegacyType>, return_type: LegacyType| FunctionType { params: params.into(), return_type: Box::new(return_type), is_closure: false, params_id: None, return_type_id: None };

        match (object_type, method_name) {
            // Array.length() -> i64
            (LegacyType::Array(_), "length") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                Some(method_type(vec![], self.ty_i64()))
            }
            // Array.iter() -> Iterator<T>
            (LegacyType::Array(elem_ty), "iter") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                let iter_type =
                    self.interface_type("Iterator", vec![*elem_ty.clone()], interner)?;
                Some(method_type(vec![], iter_type))
            }
            // Range.iter() -> Iterator<i64>
            (LegacyType::Range, "iter") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                let i64_ty = self.ty_i64();
                let iter_type = self.interface_type("Iterator", vec![i64_ty], interner)?;
                Some(method_type(vec![], iter_type))
            }
            // String.length() -> i64
            (LegacyType::Primitive(PrimitiveType::String), "length") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                Some(method_type(vec![], self.ty_i64()))
            }
            // String.iter() -> Iterator<string>
            (LegacyType::Primitive(PrimitiveType::String), "iter") => {
                if !args.is_empty() {
                    self.add_wrong_arg_count(0, args.len(), args[0].span);
                }
                let string_ty = self.ty_string();
                let iter_type = self.interface_type("Iterator", vec![string_ty], interner)?;
                Some(method_type(vec![], iter_type))
            }
            _ => None,
        }
    }
}
