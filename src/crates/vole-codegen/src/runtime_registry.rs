//! Typed runtime callable registry for codegen.
//!
//! This module is the staged source of truth for runtime callables. It starts
//! as metadata-only and is wired into JIT import/symbol paths in later phases.

/// Typed key for a runtime callable exposed to codegen.
///
/// This avoids ad-hoc string literals in Rust call sites.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeKey {
    StringNew,
    StringConcat,
    StringEq,
    StringLen,
    PrintlnString,
    PrintlnI64,
    PrintlnF64,
    PrintlnBool,
    PrintString,
    PrintI64,
    PrintF64,
    PrintBool,
    PrintChar,
    I64ToString,
    I128ToString,
    I128Sdiv,
    I128Srem,
    F64ToString,
    F32ToString,
    BoolToString,
    NilToString,
    ArrayI64ToString,
    Flush,
    AssertFail,
    Panic,
    ArrayNew,
    ArrayPush,
    ArrayGetValue,
    ArrayLen,
    ArrayIter,
    ArrayIterNext,
    ArrayIterCollect,
    ArraySet,
    ArrayFilled,
    MapIter,
    MapIterNext,
    MapIterCollect,
    FilterIter,
    FilterIterNext,
    FilterIterCollect,
    TakeIter,
    TakeIterNext,
    TakeIterCollect,
    SkipIter,
    SkipIterNext,
    SkipIterCollect,
    IterCount,
    IterSum,
    IterForEach,
    IterReduce,
    IterReduceTagged,
    IterSetElemTag,
    IterSetProducesOwned,
    IterFirst,
    IterLast,
    IterNth,
    RangeIter,
    StringCharsIter,
    ClosureAlloc,
    ClosureSetCapture,
    ClosureSetCaptureKind,
    ClosureGetCapture,
    ClosureGetFunc,
    HeapAlloc,
    InstanceNew,
    InstanceGetField,
    InstanceSetField,
    SbNew,
    SbPushString,
    SbFinish,
    InterfaceIter,
    RcInc,
    RcDec,
}

/// Metadata for a runtime callable.
#[derive(Debug, Clone, Copy)]
pub struct RuntimeSymbol {
    pub key: RuntimeKey,
    pub c_name: &'static str,
    pub exposed_to_codegen: bool,
}

const RUNTIME_SYMBOLS: &[RuntimeSymbol] = &[
    RuntimeSymbol {
        key: RuntimeKey::StringNew,
        c_name: "vole_string_new",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::StringConcat,
        c_name: "vole_string_concat",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::StringEq,
        c_name: "vole_string_eq",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::StringLen,
        c_name: "vole_string_len",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintlnString,
        c_name: "vole_println_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintlnI64,
        c_name: "vole_println_i64",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintlnF64,
        c_name: "vole_println_f64",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintlnBool,
        c_name: "vole_println_bool",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintString,
        c_name: "vole_print_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintI64,
        c_name: "vole_print_i64",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintF64,
        c_name: "vole_print_f64",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintBool,
        c_name: "vole_print_bool",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::PrintChar,
        c_name: "vole_print_char",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::I64ToString,
        c_name: "vole_i64_to_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::I128ToString,
        c_name: "vole_i128_to_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::I128Sdiv,
        c_name: "vole_i128_sdiv",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::I128Srem,
        c_name: "vole_i128_srem",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::F64ToString,
        c_name: "vole_f64_to_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::F32ToString,
        c_name: "vole_f32_to_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::BoolToString,
        c_name: "vole_bool_to_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::NilToString,
        c_name: "vole_nil_to_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayI64ToString,
        c_name: "vole_array_i64_to_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::Flush,
        c_name: "vole_flush",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::AssertFail,
        c_name: "vole_assert_fail",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::Panic,
        c_name: "vole_panic",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayNew,
        c_name: "vole_array_new",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayPush,
        c_name: "vole_array_push",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayGetValue,
        c_name: "vole_array_get_value",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayLen,
        c_name: "vole_array_len",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayIter,
        c_name: "vole_array_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayIterNext,
        c_name: "vole_array_iter_next",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayIterCollect,
        c_name: "vole_array_iter_collect",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArraySet,
        c_name: "vole_array_set",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ArrayFilled,
        c_name: "vole_array_filled",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::MapIter,
        c_name: "vole_map_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::MapIterNext,
        c_name: "vole_map_iter_next",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::MapIterCollect,
        c_name: "vole_map_iter_collect",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::FilterIter,
        c_name: "vole_filter_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::FilterIterNext,
        c_name: "vole_filter_iter_next",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::FilterIterCollect,
        c_name: "vole_filter_iter_collect",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::TakeIter,
        c_name: "vole_take_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::TakeIterNext,
        c_name: "vole_take_iter_next",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::TakeIterCollect,
        c_name: "vole_take_iter_collect",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::SkipIter,
        c_name: "vole_skip_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::SkipIterNext,
        c_name: "vole_skip_iter_next",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::SkipIterCollect,
        c_name: "vole_skip_iter_collect",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterCount,
        c_name: "vole_iter_count",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterSum,
        c_name: "vole_iter_sum",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterForEach,
        c_name: "vole_iter_for_each",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterReduce,
        c_name: "vole_iter_reduce",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterReduceTagged,
        c_name: "vole_iter_reduce_tagged",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterSetElemTag,
        c_name: "vole_iter_set_elem_tag",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterSetProducesOwned,
        c_name: "vole_iter_set_produces_owned",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterFirst,
        c_name: "vole_iter_first",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterLast,
        c_name: "vole_iter_last",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::IterNth,
        c_name: "vole_iter_nth",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::RangeIter,
        c_name: "vole_range_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::StringCharsIter,
        c_name: "vole_string_chars_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ClosureAlloc,
        c_name: "vole_closure_alloc",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ClosureSetCapture,
        c_name: "vole_closure_set_capture",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ClosureSetCaptureKind,
        c_name: "vole_closure_set_capture_kind",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ClosureGetCapture,
        c_name: "vole_closure_get_capture",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::ClosureGetFunc,
        c_name: "vole_closure_get_func",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::HeapAlloc,
        c_name: "vole_heap_alloc",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::InstanceNew,
        c_name: "vole_instance_new",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::InstanceGetField,
        c_name: "vole_instance_get_field",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::InstanceSetField,
        c_name: "vole_instance_set_field",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::SbNew,
        c_name: "vole_sb_new",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::SbPushString,
        c_name: "vole_sb_push_string",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::SbFinish,
        c_name: "vole_sb_finish",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::InterfaceIter,
        c_name: "vole_interface_iter",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::RcInc,
        c_name: "rc_inc",
        exposed_to_codegen: true,
    },
    RuntimeSymbol {
        key: RuntimeKey::RcDec,
        c_name: "rc_dec",
        exposed_to_codegen: true,
    },
];

pub fn all_symbols() -> &'static [RuntimeSymbol] {
    RUNTIME_SYMBOLS
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_hash::FxHashSet;

    #[test]
    fn runtime_symbol_names_are_unique() {
        let mut seen = FxHashSet::default();
        for symbol in all_symbols() {
            assert!(
                seen.insert(symbol.c_name),
                "duplicate runtime symbol name in registry: {}",
                symbol.c_name
            );
        }
    }

    #[test]
    fn runtime_keys_are_unique() {
        let mut seen = FxHashSet::default();
        for symbol in all_symbols() {
            assert!(
                seen.insert(symbol.key),
                "duplicate runtime key in registry: {:?}",
                symbol.key
            );
        }
    }
}
