use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::ast::CallArg;

impl Analyzer {
    /// Check if a method call is a built-in method on a primitive type (TypeId version)
    /// Returns Some(function_type) if handled, None if not a built-in
    pub(crate) fn check_builtin_method_id(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: &str,
        args: &[CallArg],
        interner: &Interner,
    ) -> Option<FunctionType> {
        // Check for array types - extract element type before borrowing again
        let array_elem = self.type_arena().unwrap_array(object_type_id);
        if let Some(elem_ty_id) = array_elem {
            return match method_name {
                // Array.length() -> i64
                "length" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].expr().span);
                    }
                    Some(FunctionType::nullary(self.ty_i64_id()))
                }
                // Array.iter() -> Iterator<T>
                "iter" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].expr().span);
                    }
                    let iter_type_id =
                        self.interface_type_id("Iterator", &[elem_ty_id], interner)?;
                    Some(FunctionType::nullary(iter_type_id))
                }
                _ => None,
            };
        }

        // Check for Range type
        if object_type_id == ArenaTypeId::RANGE {
            return match method_name {
                // Range.iter() -> Iterator<i64>
                "iter" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].expr().span);
                    }
                    let iter_type_id =
                        self.interface_type_id("Iterator", &[self.ty_i64_id()], interner)?;
                    Some(FunctionType::nullary(iter_type_id))
                }
                _ => None,
            };
        }

        // Check for String type
        if object_type_id == ArenaTypeId::STRING {
            return match method_name {
                // String.length() -> i64
                "length" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].expr().span);
                    }
                    Some(FunctionType::nullary(self.ty_i64_id()))
                }
                // String.iter() -> Iterator<string>
                "iter" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].expr().span);
                    }
                    let iter_type_id =
                        self.interface_type_id("Iterator", &[self.ty_string_id()], interner)?;
                    Some(FunctionType::nullary(iter_type_id))
                }
                _ => None,
            };
        }

        None
    }
}
