//! Typed runtime callable registry for codegen.
//!
//! This module is the staged source of truth for runtime callables. It starts
//! as metadata-only and is wired into JIT import/symbol paths in later phases.

/// Metadata for a runtime callable.
#[derive(Debug, Clone, Copy)]
pub struct RuntimeSymbol {
    pub key: RuntimeKey,
    pub c_name: &'static str,
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

/// Maps a type token (`Ptr`, `I8`, etc.) to `AbiTy`. `Void` is not a real
/// AbiTy -- it is handled by the return-type position in `sig_ret!`.
macro_rules! abi_ty {
    (Ptr) => {
        AbiTy::Ptr
    };
    (I8) => {
        AbiTy::I8
    };
    (I32) => {
        AbiTy::I32
    };
    (I64) => {
        AbiTy::I64
    };
    (I128) => {
        AbiTy::I128
    };
    (F32) => {
        AbiTy::F32
    };
    (F64) => {
        AbiTy::F64
    };
}

/// Maps a return-type token to `Option<AbiTy>`. `Void` yields `None`.
macro_rules! sig_ret {
    (Void) => {
        None
    };
    ($ty:ident) => {
        Some(abi_ty!($ty))
    };
}

/// Generates the `RuntimeKey` enum, `RuntimeKey::ALL`, `RuntimeKey::name()`,
/// `RUNTIME_SYMBOLS`, and `signature_for()` from a single declaration table.
///
/// Each entry has the form:
///     Variant => "c_name" : (Param, ...) -> Ret
///
/// where `Ret` is either a type token or `Void` (no return value).
macro_rules! runtime_keys {
    ( $( $variant:ident => $c_name:literal : ( $($param:ident),* ) -> $ret:ident ),+ $(,)? ) => {
        /// Typed key for a runtime callable exposed to codegen.
        ///
        /// This avoids ad-hoc string literals in Rust call sites.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum RuntimeKey {
            $( $variant, )+
        }

        impl RuntimeKey {
            pub const ALL: &'static [RuntimeKey] = &[
                $( RuntimeKey::$variant, )+
            ];

            pub fn name(self) -> &'static str {
                match self {
                    $( RuntimeKey::$variant => $c_name, )+
                }
            }
        }

        const RUNTIME_SYMBOLS: &[RuntimeSymbol] = &[
            $( RuntimeSymbol { key: RuntimeKey::$variant, c_name: $c_name }, )+
        ];

        pub fn signature_for(key: RuntimeKey) -> SigSpec {
            match key {
                $( RuntimeKey::$variant => SigSpec {
                    params: &[ $( abi_ty!($param) ),* ],
                    ret: sig_ret!($ret),
                }, )+
            }
        }
    };
}

runtime_keys! {
    // ── Strings ──────────────────────────────────────────────────────
    StringNew              => "vole_string_new"              : (Ptr, Ptr) -> Ptr,
    StringConcat           => "vole_string_concat"           : (Ptr, Ptr) -> Ptr,
    StringEq               => "vole_string_eq"               : (Ptr, Ptr) -> I8,
    StringLen              => "vole_string_len"              : (Ptr) -> I64,

    // ── Printing ─────────────────────────────────────────────────────
    PrintlnString          => "vole_println_string"          : (Ptr) -> Void,
    PrintlnI64             => "vole_println_i64"             : (I64) -> Void,
    PrintlnF64             => "vole_println_f64"             : (F64) -> Void,
    PrintlnBool            => "vole_println_bool"            : (I8) -> Void,
    PrintString            => "vole_print_string"            : (Ptr) -> Void,
    PrintI64               => "vole_print_i64"               : (I64) -> Void,
    PrintF64               => "vole_print_f64"               : (F64) -> Void,
    PrintBool              => "vole_print_bool"              : (I8) -> Void,
    PrintChar              => "vole_print_char"              : (I8) -> Void,

    // ── Conversions ──────────────────────────────────────────────────
    I64ToString            => "vole_i64_to_string"           : (I64) -> Ptr,
    I128ToString           => "vole_i128_to_string"          : (I128) -> Ptr,
    I128Sdiv               => "vole_i128_sdiv"               : (I128, I128) -> I128,
    I128Srem               => "vole_i128_srem"               : (I128, I128) -> I128,
    F64ToString            => "vole_f64_to_string"           : (F64) -> Ptr,
    F32ToString            => "vole_f32_to_string"           : (F32) -> Ptr,
    BoolToString           => "vole_bool_to_string"          : (I8) -> Ptr,
    NilToString            => "vole_nil_to_string"           : () -> Ptr,
    ArrayI64ToString       => "vole_array_i64_to_string"     : (Ptr) -> Ptr,

    // ── IO ───────────────────────────────────────────────────────────
    Flush                  => "vole_flush"                   : () -> Void,

    // ── Diagnostics ──────────────────────────────────────────────────
    AssertFail             => "vole_assert_fail"             : (Ptr, I64, I32) -> Void,
    Panic                  => "vole_panic"                   : (Ptr, Ptr, I64, I32) -> Void,

    // ── Arrays ───────────────────────────────────────────────────────
    ArrayNew               => "vole_array_new"               : () -> Ptr,
    ArrayPush              => "vole_array_push"              : (Ptr, I64, I64) -> Void,
    ArrayGetTag            => "vole_array_get_tag"           : (Ptr, I64) -> I64,
    ArrayGetValue          => "vole_array_get_value"         : (Ptr, I64) -> I64,
    ArrayLen               => "vole_array_len"               : (Ptr) -> I64,
    ArrayIter              => "vole_array_iter"              : (Ptr) -> Ptr,
    ArrayIterNext          => "vole_array_iter_next"         : (Ptr, Ptr) -> I64,
    ArrayIterCollect       => "vole_array_iter_collect"      : (Ptr) -> Ptr,
    ArraySet               => "vole_array_set"               : (Ptr, I64, I64, I64) -> Void,
    ArrayFilled            => "vole_array_filled"            : (I64, I64, I64) -> Ptr,

    // ── Map iterator ─────────────────────────────────────────────────
    MapIter                => "vole_map_iter"                : (Ptr, Ptr) -> Ptr,
    MapIterNext            => "vole_map_iter_next"           : (Ptr, Ptr) -> I64,
    MapIterCollect         => "vole_map_iter_collect"        : (Ptr) -> Ptr,

    // ── Filter iterator ──────────────────────────────────────────────
    FilterIter             => "vole_filter_iter"             : (Ptr, Ptr) -> Ptr,
    FilterIterNext         => "vole_filter_iter_next"        : (Ptr, Ptr) -> I64,
    FilterIterCollect      => "vole_filter_iter_collect"     : (Ptr) -> Ptr,

    // ── Take iterator ────────────────────────────────────────────────
    TakeIter               => "vole_take_iter"               : (Ptr, I64) -> Ptr,
    TakeIterNext           => "vole_take_iter_next"          : (Ptr, Ptr) -> I64,
    TakeIterCollect        => "vole_take_iter_collect"       : (Ptr) -> Ptr,

    // ── Skip iterator ────────────────────────────────────────────────
    SkipIter               => "vole_skip_iter"               : (Ptr, I64) -> Ptr,
    SkipIterNext           => "vole_skip_iter_next"          : (Ptr, Ptr) -> I64,
    SkipIterCollect        => "vole_skip_iter_collect"       : (Ptr) -> Ptr,

    // ── Iterator consumers ───────────────────────────────────────────
    IterCount              => "vole_iter_count"              : (Ptr) -> I64,
    IterSum                => "vole_iter_sum"                : (Ptr) -> I64,
    IterForEach            => "vole_iter_for_each"           : (Ptr, Ptr) -> Void,
    IterReduce             => "vole_iter_reduce"             : (Ptr, I64, Ptr) -> I64,
    IterReduceTagged       => "vole_iter_reduce_tagged"      : (Ptr, I64, Ptr, I64, I64) -> I64,
    IterSetElemTag         => "vole_iter_set_elem_tag"       : (Ptr, I64) -> Void,
    IterSetProducesOwned   => "vole_iter_set_produces_owned" : (Ptr) -> Void,
    IterFirst              => "vole_iter_first"              : (Ptr) -> Ptr,
    IterLast               => "vole_iter_last"               : (Ptr) -> Ptr,
    IterNth                => "vole_iter_nth"                : (Ptr, I64) -> Ptr,

    // ── Range / string char iterators ────────────────────────────────
    RangeIter              => "vole_range_iter"              : (I64, I64) -> Ptr,
    StringCharsIter        => "vole_string_chars_iter"       : (Ptr) -> Ptr,

    // ── Closures ─────────────────────────────────────────────────────
    ClosureAlloc           => "vole_closure_alloc"           : (Ptr, I64) -> Ptr,
    ClosureSetCapture      => "vole_closure_set_capture"     : (Ptr, I64, Ptr) -> Void,
    ClosureSetCaptureKind  => "vole_closure_set_capture_kind": (Ptr, I64, I8) -> Void,
    ClosureSetCaptureSize  => "vole_closure_set_capture_size": (Ptr, I64, I32) -> Void,
    ClosureGetCapture      => "vole_closure_get_capture"     : (Ptr, I64) -> Ptr,
    ClosureGetFunc         => "vole_closure_get_func"        : (Ptr) -> Ptr,

    // ── Heap ─────────────────────────────────────────────────────────
    HeapAlloc              => "vole_heap_alloc"              : (I64) -> Ptr,

    // ── Instances ────────────────────────────────────────────────────
    InstanceNew            => "vole_instance_new"            : (I32, I32, I32) -> Ptr,
    InstanceGetField       => "vole_instance_get_field"      : (Ptr, I32) -> I64,
    InstanceSetField       => "vole_instance_set_field"      : (Ptr, I32, I64) -> Void,

    // ── String builder ───────────────────────────────────────────────
    SbNew                  => "vole_sb_new"                  : () -> Ptr,
    SbPushString           => "vole_sb_push_string"          : (Ptr, Ptr) -> Void,
    SbFinish               => "vole_sb_finish"               : (Ptr) -> Ptr,

    // ── Interface ────────────────────────────────────────────────────
    InterfaceIter          => "vole_interface_iter"          : (Ptr) -> Ptr,

    // ── Generator coroutines ────────────────────────────────────────────
    GeneratorNew           => "vole_generator_new"           : (Ptr, Ptr, I64) -> Ptr,
    GeneratorYield         => "vole_generator_yield"         : (Ptr, I64) -> Void,

    // ── Reference counting ───────────────────────────────────────────
    RcInc                  => "rc_inc"                       : (Ptr) -> Void,
    RcDec                  => "rc_dec"                       : (Ptr) -> Void,

    // ── Task scheduler ─────────────────────────────────────────────────
    TaskSpawn              => "vole_task_spawn"              : (Ptr, Ptr) -> I64,
    TaskYield              => "vole_task_yield"              : () -> Void,
    TaskBlock              => "vole_task_block"              : () -> I64,
    TaskUnblock            => "vole_task_unblock"            : (I64) -> Void,
    TaskJoin               => "vole_task_join"               : (I64) -> I64,
    TaskCancel             => "vole_task_cancel"             : (I64) -> Void,
    TaskIsDone             => "vole_task_is_done"            : (I64) -> I64,
    SchedulerRun           => "vole_scheduler_run"           : () -> Void,

    // ── Task spawn tag ──────────────────────────────────────────────────
    TaskSetSpawnTag        => "vole_task_set_spawn_tag"      : (I64) -> Void,

    // ── Task handles (RcTask) ───────────────────────────────────────────
    RcTaskRun              => "vole_rctask_run"              : (Ptr, Ptr, I64) -> Ptr,
    RcTaskJoin             => "vole_rctask_join"             : (Ptr) -> I64,
    RcTaskCancel           => "vole_rctask_cancel"           : (Ptr) -> Void,
    RcTaskIsDone           => "vole_rctask_is_done"          : (Ptr) -> I64,

    // ── Channels ──────────────────────────────────────────────────────
    ChannelNew             => "vole_channel_new"             : (I64) -> Ptr,
    ChannelSend            => "vole_channel_send"            : (Ptr, I64, I64) -> I64,
    ChannelRecv            => "vole_channel_recv"            : (Ptr, Ptr) -> I64,
    ChannelClose           => "vole_channel_close"           : (Ptr) -> Void,
    ChannelIsClosed        => "vole_channel_is_closed"       : (Ptr) -> I8,
}

pub fn all_symbols() -> &'static [RuntimeSymbol] {
    RUNTIME_SYMBOLS
}

pub fn codegen_symbols() -> impl Iterator<Item = &'static RuntimeSymbol> {
    RUNTIME_SYMBOLS.iter()
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
        c_name: "vole_array_get_tag",
        ptr: vole_runtime::builtins::vole_array_get_tag as *const u8,
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
        c_name: "vole_closure_set_capture_size",
        ptr: vole_runtime::closure::vole_closure_set_capture_size as *const u8,
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
        c_name: "vole_generator_new",
        ptr: vole_runtime::coroutine::vole_generator_new as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_generator_yield",
        ptr: vole_runtime::coroutine::vole_generator_yield as *const u8,
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
    // ── Task scheduler ─────────────────────────────────────────────────
    LinkableRuntimeSymbol {
        c_name: "vole_task_spawn",
        ptr: vole_runtime::scheduler::vole_task_spawn as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_task_yield",
        ptr: vole_runtime::scheduler::vole_task_yield as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_task_block",
        ptr: vole_runtime::scheduler::vole_task_block as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_task_unblock",
        ptr: vole_runtime::scheduler::vole_task_unblock as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_task_join",
        ptr: vole_runtime::scheduler::vole_task_join as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_task_cancel",
        ptr: vole_runtime::scheduler::vole_task_cancel as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_task_is_done",
        ptr: vole_runtime::scheduler::vole_task_is_done as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_scheduler_run",
        ptr: vole_runtime::scheduler::vole_scheduler_run as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_task_set_spawn_tag",
        ptr: vole_runtime::scheduler::vole_task_set_spawn_tag as *const u8,
    },
    // ── Task handles (RcTask) ───────────────────────────────────────────
    LinkableRuntimeSymbol {
        c_name: "vole_rctask_run",
        ptr: vole_runtime::task::vole_rctask_run as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_rctask_join",
        ptr: vole_runtime::task::vole_rctask_join as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_rctask_cancel",
        ptr: vole_runtime::task::vole_rctask_cancel as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_rctask_is_done",
        ptr: vole_runtime::task::vole_rctask_is_done as *const u8,
    },
    // ── Channels ──────────────────────────────────────────────────────
    LinkableRuntimeSymbol {
        c_name: "vole_channel_new",
        ptr: vole_runtime::channel::vole_channel_new as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_channel_send",
        ptr: vole_runtime::channel::vole_channel_send as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_channel_recv",
        ptr: vole_runtime::channel::vole_channel_recv as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_channel_close",
        ptr: vole_runtime::channel::vole_channel_close as *const u8,
    },
    LinkableRuntimeSymbol {
        c_name: "vole_channel_is_closed",
        ptr: vole_runtime::channel::vole_channel_is_closed as *const u8,
    },
];

pub fn all_linkable_symbols() -> &'static [LinkableRuntimeSymbol] {
    LINKABLE_RUNTIME_SYMBOLS
}

/// Linkable runtime symbols intentionally not exposed through `RuntimeKey` imports.
///
/// These are currently invoked via NativeRegistry external dispatch or runtime-internal
/// pathways rather than `RuntimeKey`-typed call sites.
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
