use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check if a method call is a built-in method on a primitive type (TypeId version)
    /// Returns Some(function_type) if handled, None if not a built-in
    pub(crate) fn check_builtin_method_id(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: &str,
        args: &[Expr],
        interner: &Interner,
    ) -> Option<FunctionType> {
        // Check for array types - extract element type before borrowing again
        let array_elem = self.type_arena.borrow().unwrap_array(object_type_id);
        if let Some(elem_ty_id) = array_elem {
            return match method_name {
                // Array.length() -> i64
                "length" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].span);
                    }
                    Some(FunctionType::from_ids(&[], self.ty_i64_id(), false))
                }
                // Array.iter() -> Iterator<T>
                "iter" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].span);
                    }
                    let iter_type_id =
                        self.interface_type_id("Iterator", &[elem_ty_id], interner)?;
                    Some(FunctionType::from_ids(&[], iter_type_id, false))
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
                        self.add_wrong_arg_count(0, args.len(), args[0].span);
                    }
                    let iter_type_id =
                        self.interface_type_id("Iterator", &[self.ty_i64_id()], interner)?;
                    Some(FunctionType::from_ids(&[], iter_type_id, false))
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
                        self.add_wrong_arg_count(0, args.len(), args[0].span);
                    }
                    Some(FunctionType::from_ids(&[], self.ty_i64_id(), false))
                }
                // String.iter() -> Iterator<string>
                "iter" => {
                    if !args.is_empty() {
                        self.add_wrong_arg_count(0, args.len(), args[0].span);
                    }
                    let iter_type_id =
                        self.interface_type_id("Iterator", &[self.ty_string_id()], interner)?;
                    Some(FunctionType::from_ids(&[], iter_type_id, false))
                }
                _ => None,
            };
        }

        None
    }
}
