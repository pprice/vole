//! Rule: inline assertions exercising string methods.
//!
//! Generates self-contained `assert(...)` blocks that test string methods
//! not otherwise well-covered by the generator: `contains`, `starts_with`,
//! `ends_with`, `replace`, `trim`, `substring`, and `split(...).collect()`.
//!
//! Six variants, each with 2-3 templates for variety:
//!
//! - Variant 0: `contains` -- positive and negative cases
//! - Variant 1: `starts_with` / `ends_with`
//! - Variant 2: `replace` -- replace a known substring
//! - Variant 3: `split(",").collect()` -- split, assert length and elements
//! - Variant 4: `trim` -- trim whitespace
//! - Variant 5: `substring(start, end)` -- extract known substring (end exclusive)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringMethodCall;

impl StmtRule for StringMethodCall {
    fn name(&self) -> &'static str {
        "string_method_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let indent = emit.indent_str();
        match emit.gen_range(0..6) {
            0 => emit_contains(emit, &indent),
            1 => emit_starts_ends_with(emit, &indent),
            2 => emit_replace(emit, &indent),
            3 => emit_split_collect(scope, emit, &indent),
            4 => emit_trim(emit, &indent),
            _ => emit_substring(emit, &indent),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- contains
// ---------------------------------------------------------------------------

struct ContainsTemplate {
    haystack: &'static str,
    positive: &'static str,
    negative: &'static str,
}

const CONTAINS_TEMPLATES: &[ContainsTemplate] = &[
    ContainsTemplate {
        haystack: "hello world",
        positive: "world",
        negative: "xyz",
    },
    ContainsTemplate {
        haystack: "the quick brown fox",
        positive: "quick",
        negative: "slow",
    },
    ContainsTemplate {
        haystack: "abcdef",
        positive: "cde",
        negative: "xyz",
    },
];

fn emit_contains(emit: &mut Emit, indent: &str) -> Option<String> {
    let t = &CONTAINS_TEMPLATES[emit.gen_range(0..CONTAINS_TEMPLATES.len())];
    Some(format!(
        "assert(\"{}\".contains(\"{}\"))\n\
         {}assert(!(\"{}\".contains(\"{}\")))",
        t.haystack, t.positive, indent, t.haystack, t.negative,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- starts_with / ends_with
// ---------------------------------------------------------------------------

struct StartsEndsTemplate {
    haystack: &'static str,
    prefix: &'static str,
    suffix: &'static str,
}

const STARTS_ENDS_TEMPLATES: &[StartsEndsTemplate] = &[
    StartsEndsTemplate {
        haystack: "hello world",
        prefix: "hello",
        suffix: "world",
    },
    StartsEndsTemplate {
        haystack: "foobar baz",
        prefix: "foo",
        suffix: "baz",
    },
    StartsEndsTemplate {
        haystack: "alpha beta gamma",
        prefix: "alpha",
        suffix: "gamma",
    },
];

fn emit_starts_ends_with(emit: &mut Emit, indent: &str) -> Option<String> {
    let t = &STARTS_ENDS_TEMPLATES[emit.gen_range(0..STARTS_ENDS_TEMPLATES.len())];
    Some(format!(
        "assert(\"{}\".starts_with(\"{}\"))\n\
         {}assert(\"{}\".ends_with(\"{}\"))",
        t.haystack, t.prefix, indent, t.haystack, t.suffix,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- replace
// ---------------------------------------------------------------------------

struct ReplaceTemplate {
    input: &'static str,
    from: &'static str,
    to: &'static str,
    expected: &'static str,
}

const REPLACE_TEMPLATES: &[ReplaceTemplate] = &[
    ReplaceTemplate {
        input: "hello world",
        from: "world",
        to: "vole",
        expected: "hello vole",
    },
    ReplaceTemplate {
        input: "aabbcc",
        from: "bb",
        to: "XX",
        expected: "aaXXcc",
    },
    ReplaceTemplate {
        input: "foo bar foo",
        from: "foo",
        to: "baz",
        expected: "baz bar baz",
    },
];

fn emit_replace(emit: &mut Emit, _indent: &str) -> Option<String> {
    let t = &REPLACE_TEMPLATES[emit.gen_range(0..REPLACE_TEMPLATES.len())];
    Some(format!(
        "assert(\"{}\".replace(\"{}\", \"{}\") == \"{}\")",
        t.input, t.from, t.to, t.expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 3 -- split(",").collect()
// ---------------------------------------------------------------------------

struct SplitTemplate {
    input: &'static str,
    delim: &'static str,
    count: usize,
    first: &'static str,
}

const SPLIT_TEMPLATES: &[SplitTemplate] = &[
    SplitTemplate {
        input: "a,b,c",
        delim: ",",
        count: 3,
        first: "a",
    },
    SplitTemplate {
        input: "one;two;three;four",
        delim: ";",
        count: 4,
        first: "one",
    },
    SplitTemplate {
        input: "x-y-z",
        delim: "-",
        count: 3,
        first: "x",
    },
];

fn emit_split_collect(scope: &mut Scope, emit: &mut Emit, indent: &str) -> Option<String> {
    let t = &SPLIT_TEMPLATES[emit.gen_range(0..SPLIT_TEMPLATES.len())];
    let name = scope.fresh_name();
    scope.add_local(
        name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );
    Some(format!(
        "let {} = \"{}\".split(\"{}\").collect()\n\
         {}assert({}.length() == {})\n\
         {}assert({}[0] == \"{}\")",
        name, t.input, t.delim, indent, name, t.count, indent, name, t.first,
    ))
}

// ---------------------------------------------------------------------------
// Variant 4 -- trim
// ---------------------------------------------------------------------------

struct TrimTemplate {
    input: &'static str,
    expected: &'static str,
}

const TRIM_TEMPLATES: &[TrimTemplate] = &[
    TrimTemplate {
        input: "  hello  ",
        expected: "hello",
    },
    TrimTemplate {
        input: "  vole lang  ",
        expected: "vole lang",
    },
    TrimTemplate {
        input: "   abc   ",
        expected: "abc",
    },
];

fn emit_trim(emit: &mut Emit, _indent: &str) -> Option<String> {
    let t = &TRIM_TEMPLATES[emit.gen_range(0..TRIM_TEMPLATES.len())];
    Some(format!(
        "assert(\"{}\".trim() == \"{}\")",
        t.input, t.expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 5 -- substring(start, end) where end is exclusive
// ---------------------------------------------------------------------------

struct SubstringTemplate {
    input: &'static str,
    start: usize,
    end: usize,
    expected: &'static str,
}

const SUBSTRING_TEMPLATES: &[SubstringTemplate] = &[
    SubstringTemplate {
        input: "hello",
        start: 1,
        end: 4,
        expected: "ell",
    },
    SubstringTemplate {
        input: "abcdef",
        start: 2,
        end: 5,
        expected: "cde",
    },
    SubstringTemplate {
        input: "vole lang",
        start: 0,
        end: 4,
        expected: "vole",
    },
];

fn emit_substring(emit: &mut Emit, _indent: &str) -> Option<String> {
    let t = &SUBSTRING_TEMPLATES[emit.gen_range(0..SUBSTRING_TEMPLATES.len())];
    Some(format!(
        "assert(\"{}\".substring({}, {}) == \"{}\")",
        t.input, t.start, t.end, t.expected,
    ))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(
            rng,
            EMPTY_STMT,
            EMPTY_EXPR,
            resolved,
            crate::symbols::SymbolTable::empty_ref(),
        )
    }

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StringMethodCall.name(), "string_method_call");
    }

    #[test]
    fn generates_contains_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = StringMethodCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".contains(") {
                    found = true;
                    assert!(text.contains("assert("), "got: {text}");
                    assert!(text.contains("!("), "expected negative case, got: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated contains variant in 100 seeds");
    }

    #[test]
    fn generates_starts_ends_with_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = StringMethodCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".starts_with(") {
                    found = true;
                    assert!(text.contains(".ends_with("), "got: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated starts_with variant in 100 seeds");
    }

    #[test]
    fn generates_replace_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = StringMethodCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".replace(") {
                    found = true;
                    assert!(text.contains("assert("), "got: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated replace variant in 100 seeds");
    }

    #[test]
    fn generates_split_collect_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = StringMethodCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".split(") && text.contains(".collect()") {
                    found = true;
                    assert!(text.contains(".length()"), "got: {text}");
                    assert!(!scope.locals.is_empty(), "split variant should add a local");
                    break;
                }
            }
        }
        assert!(found, "never generated split_collect variant in 100 seeds");
    }

    #[test]
    fn generates_trim_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = StringMethodCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".trim()") && text.contains("==") {
                    found = true;
                    assert!(text.contains("assert("), "got: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated trim variant in 100 seeds");
    }

    #[test]
    fn generates_substring_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = StringMethodCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".substring(") {
                    found = true;
                    assert!(text.contains("assert("), "got: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated substring variant in 100 seeds");
    }
}
