//! Query interface for analyzed programs.
//!
//! ProgramQuery provides a clean API for querying type information,
//! method resolutions, and other analysis results.

use crate::frontend::NodeId;
use crate::identity::TypeDefId;
use crate::sema::entity_registry::EntityRegistry;
use crate::sema::expression_data::ExpressionData;
use crate::sema::generic::MonomorphKey;
use crate::sema::resolution::ResolvedMethod;
use crate::sema::types::Type;
use crate::sema::entity_defs::{Implementation, TypeDef};

/// Information about a call site, bundling all call-related data.
#[derive(Debug, Clone)]
pub struct CallInfo<'a> {
    /// The type of the call expression
    pub result_type: Option<&'a Type>,
    /// Resolved method (for method calls)
    pub method: Option<&'a ResolvedMethod>,
    /// Monomorphization key (for generic function calls)
    pub monomorph: Option<&'a MonomorphKey>,
}

/// Query interface for accessing analyzed program data.
/// Provides a unified API for type queries, method resolution lookups,
/// and other analysis results.
pub struct ProgramQuery<'a> {
    registry: &'a EntityRegistry,
    expr_data: &'a ExpressionData,
}

impl<'a> ProgramQuery<'a> {
    /// Create a new query interface
    pub fn new(registry: &'a EntityRegistry, expr_data: &'a ExpressionData) -> Self {
        Self { registry, expr_data }
    }

    // ===== Expression queries =====

    /// Get the type of an expression by its NodeId
    pub fn type_of(&self, node: NodeId) -> Option<&'a Type> {
        self.expr_data.get_type(node)
    }

    /// Get the resolved method at a call site
    pub fn method_at(&self, node: NodeId) -> Option<&'a ResolvedMethod> {
        self.expr_data.get_method(node)
    }

    /// Get the monomorphization key for a generic call
    pub fn monomorph_for(&self, node: NodeId) -> Option<&'a MonomorphKey> {
        self.expr_data.get_generic(node)
    }

    /// Get bundled information about a call site
    pub fn info_for_call(&self, node: NodeId) -> CallInfo<'a> {
        CallInfo {
            result_type: self.type_of(node),
            method: self.method_at(node),
            monomorph: self.monomorph_for(node),
        }
    }

    // ===== Type queries =====

    /// Get a type definition by ID
    pub fn get_type(&self, type_id: TypeDefId) -> &'a TypeDef {
        self.registry.get_type(type_id)
    }

    /// Resolve a type alias to its underlying type.
    /// Returns None if the type is not an alias or has no aliased_type.
    pub fn resolve_alias(&self, type_id: TypeDefId) -> Option<&'a Type> {
        let type_def = self.registry.get_type(type_id);
        type_def.aliased_type.as_ref()
    }

    /// Get all interface implementations for a type
    pub fn implementations_of(&self, type_id: TypeDefId) -> &'a [Implementation] {
        &self.registry.get_type(type_id).implements
    }

    // ===== Registry access =====

    /// Get direct access to the entity registry for advanced queries
    pub fn registry(&self) -> &'a EntityRegistry {
        self.registry
    }

    /// Get direct access to expression data for advanced queries
    pub fn expr_data(&self) -> &'a ExpressionData {
        self.expr_data
    }
}
