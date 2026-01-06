use super::super::*;

#[allow(dead_code)]
impl Analyzer {
    pub(crate) fn types_compatible(&self, from: &Type, to: &Type, interner: &Interner) -> bool {
        // Use the core compatibility check for most cases
        if types_compatible_core(from, to) {
            return true;
        }

        // Function type is compatible with functional interface if signatures match
        if let Type::Function(fn_type) = from
            && let Type::Interface(iface) = to
            && let Some(iface_fn) = self.get_functional_interface_type(iface.name, interner)
            && function_compatible_with_interface(fn_type, &iface_fn)
        {
            return true;
        }

        false
    }

    /// Check if a method signature matches an interface requirement
    pub(crate) fn signatures_match(required: &InterfaceMethodDef, found: &FunctionType) -> bool {
        // Check parameter count
        if required.params.len() != found.params.len() {
            return false;
        }
        // Check parameter types
        for (req_param, found_param) in required.params.iter().zip(found.params.iter()) {
            if req_param != found_param {
                return false;
            }
        }
        // Check return type
        required.return_type == *found.return_type
    }

    /// Format a method signature for error messages
    pub(crate) fn format_method_signature(params: &[Type], return_type: &Type) -> String {
        let params_str: Vec<String> = params.iter().map(|t| t.to_string()).collect();
        format!("({}) -> {}", params_str.join(", "), return_type)
    }
}
