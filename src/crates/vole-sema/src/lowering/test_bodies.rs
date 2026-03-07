// lowering/test_bodies.rs
//
// Lower test function bodies from AST to VIR.

use crate::LoweringEntityLookup;
use crate::vir_lower::{lower_stmts, lower_test_body};
use crate::{NodeMap, TypeArena};
use vole_frontend::{Decl, Interner, Program};
use vole_identity::{ModuleId, NameTable};
use vole_vir::VirTest;
use vole_vir::type_table::VirTypeTable;

/// Lower all test function bodies in the program to VIR.
///
/// Walks the program's `Decl::Tests` blocks (including nested ones) and
/// lowers each `TestCase.body` to a `VirBody`.  Returns a list of `VirTest`
/// entries for O(1) lookup during test compilation.
pub fn lower_test_bodies(
    program: &Program,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
) -> Vec<VirTest> {
    let mut tests = Vec::new();
    for decl in &program.declarations {
        if let Decl::Tests(tests_decl) = decl {
            lower_tests_decl_bodies(
                tests_decl, node_map, interner, type_arena, entities, names, &mut tests,
                type_table, module_id,
            );
        }
    }
    tests
}

/// Recursively lower test bodies from a single `TestsDecl`.
#[allow(clippy::too_many_arguments)]
fn lower_tests_decl_bodies(
    tests_decl: &vole_frontend::ast::TestsDecl,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    tests: &mut Vec<VirTest>,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
) {
    let scoped_let_stmts: Vec<vole_frontend::Stmt> = tests_decl
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Let(let_stmt) => Some(vole_frontend::Stmt::Let(let_stmt.clone())),
            Decl::LetTuple(let_tuple) => Some(vole_frontend::Stmt::LetTuple(let_tuple.clone())),
            _ => None,
        })
        .collect();
    let empty_xmod = crate::vir_lower::CrossModuleCtx::empty();
    let scoped_let_vir_stmts = if scoped_let_stmts.is_empty() {
        Vec::new()
    } else {
        let mut ctx = crate::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            module_id,
            generic: false,
            func_return_type: vole_identity::TypeId::VOID,
            captures: rustc_hash::FxHashSet::default(),
            cross_module: &empty_xmod,
        };
        lower_stmts(&scoped_let_stmts, &mut ctx).stmts
    };

    for test in &tests_decl.tests {
        let mut vir_body = lower_test_body(
            &test.body,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
            module_id,
            &empty_xmod,
        );
        if !scoped_let_vir_stmts.is_empty() {
            vir_body
                .stmts
                .splice(0..0, scoped_let_vir_stmts.iter().cloned());
        }
        tests.push(VirTest {
            name: test.name.clone(),
            body: vir_body,
            span: test.span,
        });
    }
    // Recurse into nested tests blocks
    for decl in &tests_decl.decls {
        if let Decl::Tests(nested) = decl {
            lower_tests_decl_bodies(
                nested, node_map, interner, type_arena, entities, names, tests, type_table,
                module_id,
            );
        }
    }
}
