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

impl RuntimeKey {
    pub const ALL: &'static [RuntimeKey] = &[
        RuntimeKey::StringNew,
        RuntimeKey::StringConcat,
        RuntimeKey::StringEq,
        RuntimeKey::StringLen,
        RuntimeKey::PrintlnString,
        RuntimeKey::PrintlnI64,
        RuntimeKey::PrintlnF64,
        RuntimeKey::PrintlnBool,
        RuntimeKey::PrintString,
        RuntimeKey::PrintI64,
        RuntimeKey::PrintF64,
        RuntimeKey::PrintBool,
        RuntimeKey::PrintChar,
        RuntimeKey::I64ToString,
        RuntimeKey::I128ToString,
        RuntimeKey::I128Sdiv,
        RuntimeKey::I128Srem,
        RuntimeKey::F64ToString,
        RuntimeKey::F32ToString,
        RuntimeKey::BoolToString,
        RuntimeKey::NilToString,
        RuntimeKey::ArrayI64ToString,
        RuntimeKey::Flush,
        RuntimeKey::AssertFail,
        RuntimeKey::Panic,
        RuntimeKey::ArrayNew,
        RuntimeKey::ArrayPush,
        RuntimeKey::ArrayGetValue,
        RuntimeKey::ArrayLen,
        RuntimeKey::ArrayIter,
        RuntimeKey::ArrayIterNext,
        RuntimeKey::ArrayIterCollect,
        RuntimeKey::ArraySet,
        RuntimeKey::ArrayFilled,
        RuntimeKey::MapIter,
        RuntimeKey::MapIterNext,
        RuntimeKey::MapIterCollect,
        RuntimeKey::FilterIter,
        RuntimeKey::FilterIterNext,
        RuntimeKey::FilterIterCollect,
        RuntimeKey::TakeIter,
        RuntimeKey::TakeIterNext,
        RuntimeKey::TakeIterCollect,
        RuntimeKey::SkipIter,
        RuntimeKey::SkipIterNext,
        RuntimeKey::SkipIterCollect,
        RuntimeKey::IterCount,
        RuntimeKey::IterSum,
        RuntimeKey::IterForEach,
        RuntimeKey::IterReduce,
        RuntimeKey::IterReduceTagged,
        RuntimeKey::IterSetElemTag,
        RuntimeKey::IterSetProducesOwned,
        RuntimeKey::IterFirst,
        RuntimeKey::IterLast,
        RuntimeKey::IterNth,
        RuntimeKey::RangeIter,
        RuntimeKey::StringCharsIter,
        RuntimeKey::ClosureAlloc,
        RuntimeKey::ClosureSetCapture,
        RuntimeKey::ClosureSetCaptureKind,
        RuntimeKey::ClosureGetCapture,
        RuntimeKey::ClosureGetFunc,
        RuntimeKey::HeapAlloc,
        RuntimeKey::InstanceNew,
        RuntimeKey::InstanceGetField,
        RuntimeKey::InstanceSetField,
        RuntimeKey::SbNew,
        RuntimeKey::SbPushString,
        RuntimeKey::SbFinish,
        RuntimeKey::InterfaceIter,
        RuntimeKey::RcInc,
        RuntimeKey::RcDec,
    ];

    pub fn name(self) -> &'static str {
        for symbol in RUNTIME_SYMBOLS {
            if symbol.key == self {
                return symbol.c_name;
            }
        }
        panic!("missing runtime symbol name for key: {self:?}");
    }
}

/// Metadata for a runtime callable.
#[derive(Debug, Clone, Copy)]
pub struct RuntimeSymbol {
    pub key: RuntimeKey,
    pub c_name: &'static str,
    pub exposed_to_codegen: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbiTy {
    Ptr,
    I8,
    I32,
    I64,
    I128,
    F32,
    F64,
}

#[derive(Debug, Clone, Copy)]
pub struct SigSpec {
    pub params: &'static [AbiTy],
    pub ret: Option<AbiTy>,
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

pub fn codegen_symbols() -> impl Iterator<Item = &'static RuntimeSymbol> {
    RUNTIME_SYMBOLS
        .iter()
        .filter(|symbol| symbol.exposed_to_codegen)
}

pub fn signature_for(key: RuntimeKey) -> SigSpec {
    match key {
        RuntimeKey::StringNew => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::StringConcat => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::StringEq => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I8),
        },
        RuntimeKey::StringLen => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::PrintlnString => SigSpec {
            params: &[AbiTy::Ptr],
            ret: None,
        },
        RuntimeKey::PrintlnI64 => SigSpec {
            params: &[AbiTy::I64],
            ret: None,
        },
        RuntimeKey::PrintlnF64 => SigSpec {
            params: &[AbiTy::F64],
            ret: None,
        },
        RuntimeKey::PrintlnBool => SigSpec {
            params: &[AbiTy::I8],
            ret: None,
        },
        RuntimeKey::PrintString => SigSpec {
            params: &[AbiTy::Ptr],
            ret: None,
        },
        RuntimeKey::PrintI64 => SigSpec {
            params: &[AbiTy::I64],
            ret: None,
        },
        RuntimeKey::PrintF64 => SigSpec {
            params: &[AbiTy::F64],
            ret: None,
        },
        RuntimeKey::PrintBool => SigSpec {
            params: &[AbiTy::I8],
            ret: None,
        },
        RuntimeKey::PrintChar => SigSpec {
            params: &[AbiTy::I8],
            ret: None,
        },
        RuntimeKey::I64ToString => SigSpec {
            params: &[AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::I128ToString => SigSpec {
            params: &[AbiTy::I128],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::I128Sdiv => SigSpec {
            params: &[AbiTy::I128, AbiTy::I128],
            ret: Some(AbiTy::I128),
        },
        RuntimeKey::I128Srem => SigSpec {
            params: &[AbiTy::I128, AbiTy::I128],
            ret: Some(AbiTy::I128),
        },
        RuntimeKey::F64ToString => SigSpec {
            params: &[AbiTy::F64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::F32ToString => SigSpec {
            params: &[AbiTy::F32],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::BoolToString => SigSpec {
            params: &[AbiTy::I8],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::NilToString => SigSpec {
            params: &[],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::ArrayI64ToString => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::Flush => SigSpec {
            params: &[],
            ret: None,
        },
        RuntimeKey::AssertFail => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64, AbiTy::I32],
            ret: None,
        },
        RuntimeKey::Panic => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr, AbiTy::I64, AbiTy::I32],
            ret: None,
        },
        RuntimeKey::ArrayNew => SigSpec {
            params: &[],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::ArrayPush => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64, AbiTy::I64],
            ret: None,
        },
        RuntimeKey::ArrayGetValue => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::ArrayLen => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::ArrayIter => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::ArrayIterNext => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::ArrayIterCollect => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::ArraySet => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64, AbiTy::I64, AbiTy::I64],
            ret: None,
        },
        RuntimeKey::ArrayFilled => SigSpec {
            params: &[AbiTy::I64, AbiTy::I64, AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::MapIter => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::MapIterNext => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::MapIterCollect => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::FilterIter => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::FilterIterNext => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::FilterIterCollect => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::TakeIter => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::TakeIterNext => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::TakeIterCollect => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::SkipIter => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::SkipIterNext => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::SkipIterCollect => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::IterCount => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::IterSum => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::IterForEach => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: None,
        },
        RuntimeKey::IterReduce => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64, AbiTy::Ptr],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::IterReduceTagged => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64, AbiTy::Ptr, AbiTy::I64, AbiTy::I64],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::IterSetElemTag => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64],
            ret: None,
        },
        RuntimeKey::IterSetProducesOwned => SigSpec {
            params: &[AbiTy::Ptr],
            ret: None,
        },
        RuntimeKey::IterFirst => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::IterLast => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::IterNth => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::RangeIter => SigSpec {
            params: &[AbiTy::I64, AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::StringCharsIter => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::ClosureAlloc => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::ClosureSetCapture => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64, AbiTy::Ptr],
            ret: None,
        },
        RuntimeKey::ClosureSetCaptureKind => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64, AbiTy::I8],
            ret: None,
        },
        RuntimeKey::ClosureGetCapture => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::ClosureGetFunc => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::HeapAlloc => SigSpec {
            params: &[AbiTy::I64],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::InstanceNew => SigSpec {
            params: &[AbiTy::I32, AbiTy::I32, AbiTy::I32],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::InstanceGetField => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I32],
            ret: Some(AbiTy::I64),
        },
        RuntimeKey::InstanceSetField => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::I32, AbiTy::I64],
            ret: None,
        },
        RuntimeKey::SbNew => SigSpec {
            params: &[],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::SbPushString => SigSpec {
            params: &[AbiTy::Ptr, AbiTy::Ptr],
            ret: None,
        },
        RuntimeKey::SbFinish => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::InterfaceIter => SigSpec {
            params: &[AbiTy::Ptr],
            ret: Some(AbiTy::Ptr),
        },
        RuntimeKey::RcInc | RuntimeKey::RcDec => SigSpec {
            params: &[AbiTy::Ptr],
            ret: None,
        },
    }
}

/// Runtime symbols that can be linked into JIT modules.
#[derive(Clone, Copy)]
pub struct LinkableRuntimeSymbol {
    pub c_name: &'static str,
    pub ptr: *const u8,
}

const LINKABLE_RUNTIME_SYMBOLS: &[LinkableRuntimeSymbol] = &[
    LinkableRuntimeSymbol {
        c_name: "rc_inc",
        ptr: vole_runtime::value::rc_inc as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "rc_dec",
        ptr: vole_runtime::value::rc_dec as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_new",
        ptr: vole_runtime::string::vole_string_new as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_inc",
        ptr: vole_runtime::string::vole_string_inc as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_dec",
        ptr: vole_runtime::string::vole_string_dec as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_len",
        ptr: vole_runtime::string::vole_string_len as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_data",
        ptr: vole_runtime::string::vole_string_data as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_eq",
        ptr: vole_runtime::string::vole_string_eq as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_concat",
        ptr: vole_runtime::builtins::vole_string_concat as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_println_string",
        ptr: vole_runtime::builtins::vole_println_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_println_i64",
        ptr: vole_runtime::builtins::vole_println_i64 as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_println_f64",
        ptr: vole_runtime::builtins::vole_println_f64 as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_println_bool",
        ptr: vole_runtime::builtins::vole_println_bool as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_print_string",
        ptr: vole_runtime::builtins::vole_print_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_print_i64",
        ptr: vole_runtime::builtins::vole_print_i64 as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_print_f64",
        ptr: vole_runtime::builtins::vole_print_f64 as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_print_bool",
        ptr: vole_runtime::builtins::vole_print_bool as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_print_char",
        ptr: vole_runtime::builtins::vole_print_char as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_flush",
        ptr: vole_runtime::builtins::vole_flush as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_i64_to_string",
        ptr: vole_runtime::builtins::vole_i64_to_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_f64_to_string",
        ptr: vole_runtime::builtins::vole_f64_to_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_f32_to_string",
        ptr: vole_runtime::builtins::vole_f32_to_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_i128_to_string",
        ptr: vole_runtime::builtins::vole_i128_to_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_i128_sdiv",
        ptr: vole_runtime::builtins::vole_i128_sdiv as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_i128_srem",
        ptr: vole_runtime::builtins::vole_i128_srem as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_bool_to_string",
        ptr: vole_runtime::builtins::vole_bool_to_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_nil_to_string",
        ptr: vole_runtime::builtins::vole_nil_to_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_i64_to_string",
        ptr: vole_runtime::builtins::vole_array_i64_to_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_assert_fail",
        ptr: vole_runtime::assert::vole_assert_fail as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_panic",
        ptr: vole_runtime::builtins::vole_panic as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_new",
        ptr: vole_runtime::builtins::vole_array_new as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_push",
        ptr: vole_runtime::builtins::vole_array_push as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_get_value",
        ptr: vole_runtime::builtins::vole_array_get_value as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_len",
        ptr: vole_runtime::builtins::vole_array_len as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_iter",
        ptr: vole_runtime::iterator::vole_array_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_interface_iter",
        ptr: vole_runtime::iterator::vole_interface_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_iter_next",
        ptr: vole_runtime::iterator::vole_array_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_iter_collect",
        ptr: vole_runtime::iterator::vole_array_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_map_iter",
        ptr: vole_runtime::iterator::vole_map_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_map_iter_next",
        ptr: vole_runtime::iterator::vole_map_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_map_iter_collect",
        ptr: vole_runtime::iterator::vole_map_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_filter_iter",
        ptr: vole_runtime::iterator::vole_filter_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_filter_iter_next",
        ptr: vole_runtime::iterator::vole_filter_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_filter_iter_collect",
        ptr: vole_runtime::iterator::vole_filter_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_count",
        ptr: vole_runtime::iterator::vole_iter_count as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_sum",
        ptr: vole_runtime::iterator::vole_iter_sum as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_set_elem_tag",
        ptr: vole_runtime::iterator::vole_iter_set_elem_tag as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_set_produces_owned",
        ptr: vole_runtime::iterator::vole_iter_set_produces_owned as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_for_each",
        ptr: vole_runtime::iterator::vole_iter_for_each as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_reduce",
        ptr: vole_runtime::iterator::vole_iter_reduce as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_reduce_tagged",
        ptr: vole_runtime::iterator::vole_iter_reduce_tagged as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_first",
        ptr: vole_runtime::iterator::vole_iter_first as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_last",
        ptr: vole_runtime::iterator::vole_iter_last as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_iter_nth",
        ptr: vole_runtime::iterator::vole_iter_nth as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_take_iter",
        ptr: vole_runtime::iterator::vole_take_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_take_iter_next",
        ptr: vole_runtime::iterator::vole_take_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_take_iter_collect",
        ptr: vole_runtime::iterator::vole_take_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_skip_iter",
        ptr: vole_runtime::iterator::vole_skip_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_skip_iter_next",
        ptr: vole_runtime::iterator::vole_skip_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_skip_iter_collect",
        ptr: vole_runtime::iterator::vole_skip_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_chain_iter",
        ptr: vole_runtime::iterator::vole_chain_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_chain_iter_next",
        ptr: vole_runtime::iterator::vole_chain_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_chain_iter_collect",
        ptr: vole_runtime::iterator::vole_chain_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_flatten_iter",
        ptr: vole_runtime::iterator::vole_flatten_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_flatten_iter_next",
        ptr: vole_runtime::iterator::vole_flatten_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_flatten_iter_collect",
        ptr: vole_runtime::iterator::vole_flatten_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_flat_map_iter",
        ptr: vole_runtime::iterator::vole_flat_map_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_flat_map_iter_next",
        ptr: vole_runtime::iterator::vole_flat_map_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_flat_map_iter_collect",
        ptr: vole_runtime::iterator::vole_flat_map_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_reverse_iter",
        ptr: vole_runtime::iterator::vole_reverse_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_sorted_iter",
        ptr: vole_runtime::iterator::vole_sorted_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_unique_iter",
        ptr: vole_runtime::iterator::vole_unique_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_unique_iter_next",
        ptr: vole_runtime::iterator::vole_unique_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_chunks_iter",
        ptr: vole_runtime::iterator::vole_chunks_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_chunks_iter_next",
        ptr: vole_runtime::iterator::vole_chunks_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_chunks_iter_collect",
        ptr: vole_runtime::iterator::vole_chunks_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_windows_iter",
        ptr: vole_runtime::iterator::vole_windows_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_windows_iter_next",
        ptr: vole_runtime::iterator::vole_windows_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_windows_iter_collect",
        ptr: vole_runtime::iterator::vole_windows_iter_collect as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_repeat_iter",
        ptr: vole_runtime::iterator::vole_repeat_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_repeat_iter_next",
        ptr: vole_runtime::iterator::vole_repeat_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_once_iter",
        ptr: vole_runtime::iterator::vole_once_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_once_iter_next",
        ptr: vole_runtime::iterator::vole_once_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_empty_iter",
        ptr: vole_runtime::iterator::vole_empty_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_from_fn_iter",
        ptr: vole_runtime::iterator::vole_from_fn_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_from_fn_iter_next",
        ptr: vole_runtime::iterator::vole_from_fn_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_range_iter",
        ptr: vole_runtime::iterator::vole_range_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_range_iter_next",
        ptr: vole_runtime::iterator::vole_range_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_chars_iter",
        ptr: vole_runtime::iterator::vole_string_chars_iter as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_string_chars_iter_next",
        ptr: vole_runtime::iterator::vole_string_chars_iter_next as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_set",
        ptr: vole_runtime::builtins::vole_array_set as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_array_filled",
        ptr: vole_runtime::builtins::vole_array_filled as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_closure_alloc",
        ptr: vole_runtime::closure::vole_closure_alloc as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_closure_get_capture",
        ptr: vole_runtime::closure::vole_closure_get_capture as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_closure_set_capture",
        ptr: vole_runtime::closure::vole_closure_set_capture as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_closure_set_capture_kind",
        ptr: vole_runtime::closure::vole_closure_set_capture_kind as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_closure_get_func",
        ptr: vole_runtime::closure::vole_closure_get_func as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_heap_alloc",
        ptr: vole_runtime::closure::vole_heap_alloc as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_sb_new",
        ptr: vole_runtime::string_builder::vole_sb_new as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_sb_push_string",
        ptr: vole_runtime::string_builder::vole_sb_push_string as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_sb_finish",
        ptr: vole_runtime::string_builder::vole_sb_finish as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_instance_new",
        ptr: vole_runtime::instance::vole_instance_new as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_instance_inc",
        ptr: vole_runtime::instance::vole_instance_inc as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_instance_dec",
        ptr: vole_runtime::instance::vole_instance_dec as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_instance_get_field",
        ptr: vole_runtime::instance::vole_instance_get_field as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_instance_set_field",
        ptr: vole_runtime::instance::vole_instance_set_field as *const u8,
    },
];

pub fn all_linkable_symbols() -> &'static [LinkableRuntimeSymbol] {
    LINKABLE_RUNTIME_SYMBOLS
}

/// Linkable runtime symbols intentionally not exposed through `RuntimeKey` imports.
///
/// These are currently invoked via NativeRegistry external dispatch or runtime-internal
/// pathways rather than `RuntimeFn`-typed call sites.
#[cfg(test)]
const NON_CODEGEN_LINKABLE_SYMBOLS: &[&str] = &[
    "vole_string_inc",
    "vole_string_dec",
    "vole_string_data",
    "vole_chain_iter",
    "vole_chain_iter_next",
    "vole_chain_iter_collect",
    "vole_flatten_iter",
    "vole_flatten_iter_next",
    "vole_flatten_iter_collect",
    "vole_flat_map_iter",
    "vole_flat_map_iter_next",
    "vole_flat_map_iter_collect",
    "vole_reverse_iter",
    "vole_sorted_iter",
    "vole_unique_iter",
    "vole_unique_iter_next",
    "vole_chunks_iter",
    "vole_chunks_iter_next",
    "vole_chunks_iter_collect",
    "vole_windows_iter",
    "vole_windows_iter_next",
    "vole_windows_iter_collect",
    "vole_repeat_iter",
    "vole_repeat_iter_next",
    "vole_once_iter",
    "vole_once_iter_next",
    "vole_empty_iter",
    "vole_from_fn_iter",
    "vole_from_fn_iter_next",
    "vole_range_iter_next",
    "vole_string_chars_iter_next",
    "vole_instance_inc",
    "vole_instance_dec",
];

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_hash::FxHashSet;
    use std::fs;
    use std::path::Path;

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

    #[test]
    fn linkable_symbol_names_are_unique() {
        let mut seen = FxHashSet::default();
        for symbol in all_linkable_symbols() {
            assert!(
                seen.insert(symbol.c_name),
                "duplicate linkable runtime symbol name: {}",
                symbol.c_name
            );
        }
    }

    #[test]
    fn runtime_key_all_matches_codegen_symbols() {
        let expected: FxHashSet<_> = RuntimeKey::ALL.iter().copied().collect();
        let actual: FxHashSet<_> = codegen_symbols().map(|symbol| symbol.key).collect();

        assert_eq!(
            expected, actual,
            "RuntimeKey::ALL and codegen symbol exposure diverged"
        );
    }

    #[test]
    fn every_codegen_symbol_has_linkable_pointer() {
        let linkable_names: FxHashSet<_> = all_linkable_symbols()
            .iter()
            .map(|symbol| symbol.c_name)
            .collect();

        for symbol in codegen_symbols() {
            assert!(
                linkable_names.contains(symbol.c_name),
                "codegen symbol missing linkable pointer: {}",
                symbol.c_name
            );
        }
    }

    #[test]
    fn linkables_are_either_codegen_or_explicit_non_codegen() {
        let codegen_names: FxHashSet<_> = codegen_symbols().map(|symbol| symbol.c_name).collect();
        let allowed_non_codegen: FxHashSet<_> =
            NON_CODEGEN_LINKABLE_SYMBOLS.iter().copied().collect();

        for symbol in all_linkable_symbols() {
            assert!(
                codegen_names.contains(symbol.c_name)
                    || allowed_non_codegen.contains(symbol.c_name),
                "unclassified non-codegen linkable symbol: {}",
                symbol.c_name
            );
        }

        for &name in NON_CODEGEN_LINKABLE_SYMBOLS {
            assert!(
                all_linkable_symbols()
                    .iter()
                    .any(|symbol| symbol.c_name == name),
                "stale non-codegen linkable symbol entry: {name}"
            );
        }
    }

    #[test]
    fn signatures_exist_for_all_runtime_keys() {
        for key in RuntimeKey::ALL {
            let _ = signature_for(*key);
        }
    }

    #[test]
    fn runtime_symbol_string_literals_only_live_in_registry() {
        let crate_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut rs_files = Vec::new();
        collect_rs_files(&crate_root, &mut rs_files);

        for file in rs_files {
            let rel = file
                .strip_prefix(&crate_root)
                .expect("INTERNAL: file must live under codegen/src");
            if rel == Path::new("runtime_registry.rs") {
                continue;
            }

            let content =
                fs::read_to_string(&file).expect("INTERNAL: failed to read codegen source file");
            assert!(
                !contains_runtime_symbol_literal(&content),
                "runtime symbol string literal found outside registry: {}",
                rel.display()
            );
        }
    }

    fn collect_rs_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        let entries = fs::read_dir(dir).expect("INTERNAL: failed to read directory");
        for entry in entries {
            let entry = entry.expect("INTERNAL: failed to read directory entry");
            let path = entry.path();
            if path.is_dir() {
                collect_rs_files(&path, out);
                continue;
            }
            if path.extension().is_some_and(|ext| ext == "rs") {
                out.push(path);
            }
        }
    }

    fn contains_runtime_symbol_literal(src: &str) -> bool {
        let runtime_literals: FxHashSet<&'static str> = all_symbols()
            .iter()
            .map(|symbol| symbol.c_name)
            .chain(all_linkable_symbols().iter().map(|symbol| symbol.c_name))
            .collect();

        for literal in string_literals(src) {
            if runtime_literals.contains(literal.as_str()) {
                return true;
            }
        }
        false
    }

    fn string_literals(src: &str) -> Vec<String> {
        let bytes = src.as_bytes();
        let mut out = Vec::new();
        let mut i = 0usize;

        while i < bytes.len() {
            // Skip line comments.
            if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                i += 2;
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                continue;
            }

            // Skip block comments (supports nesting).
            if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
                i += 2;
                let mut depth = 1usize;
                while i + 1 < bytes.len() && depth > 0 {
                    if bytes[i] == b'/' && bytes[i + 1] == b'*' {
                        depth += 1;
                        i += 2;
                    } else if bytes[i] == b'*' && bytes[i + 1] == b'/' {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                continue;
            }

            // Parse normal string literal.
            if bytes[i] == b'"' {
                i += 1;
                let mut lit = String::new();
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        if i + 1 < bytes.len() {
                            lit.push(bytes[i + 1] as char);
                            i += 2;
                            continue;
                        }
                        break;
                    }
                    if bytes[i] == b'"' {
                        i += 1;
                        break;
                    }
                    lit.push(bytes[i] as char);
                    i += 1;
                }
                out.push(lit);
                continue;
            }

            // Parse raw string literal r#"..."# (and multi-# forms).
            if bytes[i] == b'r'
                && i + 1 < bytes.len()
                && (bytes[i + 1] == b'"' || bytes[i + 1] == b'#')
            {
                let mut j = i + 1;
                let mut hashes = 0usize;
                while j < bytes.len() && bytes[j] == b'#' {
                    hashes += 1;
                    j += 1;
                }
                if j < bytes.len() && bytes[j] == b'"' {
                    j += 1;
                    let content_start = j;
                    let mut content_end = None;
                    while j < bytes.len() {
                        if bytes[j] == b'"' {
                            let mut k = j + 1;
                            let mut seen_hashes = 0usize;
                            while k < bytes.len() && seen_hashes < hashes && bytes[k] == b'#' {
                                seen_hashes += 1;
                                k += 1;
                            }
                            if seen_hashes == hashes {
                                content_end = Some(j);
                                i = k;
                                break;
                            }
                        }
                        j += 1;
                    }
                    if let Some(end) = content_end {
                        let lit = String::from_utf8_lossy(&bytes[content_start..end]).to_string();
                        out.push(lit);
                        continue;
                    }
                }
            }

            i += 1;
        }

        out
    }
}
