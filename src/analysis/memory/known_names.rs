// This file is adapted from MIRAI (https://github.com/facebookexperimental/MIRAI)
// Original author: Herman Venter <hermanv@fb.com>
// Original copyright header:

// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use rustc_hir::def_id::DefId;
use rustc_hir::definitions::{DefPathData, DisambiguatedDefPathData};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::iter::Iterator;

/// Well known definitions (language provided items) that are treated in special ways.
#[derive(Clone, Copy, Debug, Eq, PartialOrd, PartialEq, Hash, Ord)]
pub enum KnownNames {
    /// This is not a known name
    None,
    CheckerVerify,
    RustAlloc,
    RustAllocZeroed,
    RustDealloc,
    RustRealloc,
    StdMemSizeOf,
    StdMemForget,
    StdMemManuallyDropNew,
    StdPanickingBeginPanic,
    StdPanickingBeginPanicFmt,

    StdIntoVec,
    CoreOpsIndex,
    CoreOpsDeref,
    StdFrom,
    StdAsMutPtr,
    StdAsPtr,

    VecFromRawParts,
    StdPtrSwap,
    StdPtrSwapNonOverlapping,
    StdPtrReplace,
    StdPtrRead,
    StdPtrReadVolatile,
    StdPtrReadUnAligned,
    StdPtrWrite,
    StdPtrConstPtrRead,
    StdPtrMutPtrRead,
    StdPtrWriteBytes,
    StdPtrWriteVolatile,
    StdPtrWriteUnAligned,
    StdPtrDropInPlace,
    StdPtrConstPtrCast,
    StdPtrConstPtrAdd,
    StdPtrConstPtrSub,
    StdPtrConstPtrOffset,
    StdPtrConstPtrByteAdd,
    StdPtrConstPtrByteSub,
    StdPtrConstPtrByteOffset,
    StdPtrConstPtrWrappingAdd,
    StdPtrConstPtrWrappingSub,
    StdPtrConstPtrWrappingOffset,
    StdPtrConstPtrWrappingByteAdd,
    StdPtrConstPtrWrappingByteSub,
    StdPtrConstPtrWrappingByteOffset,
    StdPtrMutPtrCast,
    StdPtrMutPtrAdd,
    StdPtrMutPtrSub,
    StdPtrMutPtrOffset,
    StdPtrMutPtrByteAdd,
    StdPtrMutPtrByteSub,
    StdPtrMutPtrByteOffset,
    StdPtrMutPtrWrappingAdd,
    StdPtrMutPtrWrappingSub,
    StdPtrMutPtrWrappingOffset,
    StdPtrMutPtrWrappingByteAdd,
    StdPtrMutPtrWrappingByteSub,
    StdPtrMutPtrWrappingByteOffset,

    StdPtrConstPtrOffsetFrom,
    StdPtrMutPtrOffsetFrom,
    StdPtrConstPtrByteOffsetFrom,
    StdPtrMutPtrByteOffsetFrom,

    StdSliceIndexGetUnchecked,
    StdSliceIndexGetUncheckedMut,

    CoreStrConvertsFromUtf8Unchecked,
    StdIntrinsicsCopy,
    StdIntrinsicsCopyNonOverlapping,

    StdBoxIntoRaw,
    StdBoxLeak,
    StdBoxFromRaw,  // 新增

    /// std::mem::uninitialized (deprecated but still needs modeling)
    StdMemUninitialized,

    /// Vec::with_capacity
    VecWithCapacity,

    /// Vec::reserve
    VecReserve,

    /// Vec::set_len
    VecSetLen,

    /// mem::MaybeUninit::uninit
    StdMemMaybeUninitUninit,

    /// core::slice::from_raw_parts
    StdSliceFromRawParts,
}

/// An analysis lifetime cache that contains a map from def ids to known names.
pub struct KnownNamesCache {
    name_cache: HashMap<DefId, KnownNames>,
}

type Iter<'a> = std::slice::Iter<'a, rustc_hir::definitions::DisambiguatedDefPathData>;

impl KnownNamesCache {
    /// Create an empty known names cache.
    /// This cache is re-used by every successive MIR visitor instance.
    pub fn create_cache_from_language_items() -> KnownNamesCache {
        let name_cache = HashMap::new();
        KnownNamesCache { name_cache }
    }

    /// Get the well known name for the given def id and cache the association.
    /// I.e. the first call for an unknown def id will be somewhat costly but
    /// subsequent calls will be cheap. If the def_id does not have an actual well
    /// known name, this returns KnownNames::None.
    pub fn get(&mut self, tcx: TyCtxt<'_>, def_id: DefId) -> KnownNames {
        *self
            .name_cache
            .entry(def_id)
            .or_insert_with(|| Self::get_known_name_for(tcx, def_id))
    }

    /// Uses information obtained from tcx to figure out which well known name (if any)
    /// this def id corresponds to.
    fn get_known_name_for(tcx: TyCtxt<'_>, def_id: DefId) -> KnownNames {
        use DefPathData::*;

        // E.g. DefPath { data: [DisambiguatedDefPathData { data: TypeNs("mem"), disambiguator: 0 }, DisambiguatedDefPathData { data: ValueNs("size_of"), disambiguator: 0 }], krate: crate2 }
        let def_path = &tcx.def_path(def_id);
        debug!("TEST: {:?}", def_path);

        // 【新增】特判：直接检查最后一个元素是否是 as_ptr 或 as_mut_ptr
        if let Some(last_elem) = def_path.data.last() {
            if let TypeNs(name) | ValueNs(name) = last_elem.data {
                match name.as_str() {
                    "as_ptr" => return KnownNames::StdAsPtr,
                    "as_mut_ptr" => return KnownNames::StdAsMutPtr,
                    _ => {}
                }
            }
        }

        let def_path_data_iter = def_path.data.iter();

        // helper to get next elem from def path and return its name, if it has one
        let get_path_data_elem_name =
            |def_path_data_elem: Option<&rustc_hir::definitions::DisambiguatedDefPathData>| {
                def_path_data_elem.and_then(|ref elem| {
                    let DisambiguatedDefPathData { data, .. } = elem;
                    // Get only something in the type/value namespace, and ignore others
                    match &data {
                        TypeNs(name) | ValueNs(name) => Some(*name),
                        _ => None,
                    }
                })
            };

        let get_known_name_for_alloc_namespace =
            |mut def_path_data_iter: Iter<'_>| match get_path_data_elem_name(
                def_path_data_iter.next(),
            ) {
                Some(n) if n.as_str() == "" => get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str() {
                        "__rust_alloc" => KnownNames::RustAlloc,
                        "__rust_alloc_zeroed" => KnownNames::RustAllocZeroed,
                        "__rust_dealloc" => KnownNames::RustDealloc,
                        "__rust_realloc" => KnownNames::RustRealloc,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None),
                _ => KnownNames::None,
            };

        let get_known_name_for_manually_drop_namespace = |mut def_path_data_iter: Iter<'_>| {
            def_path_data_iter.next();
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "new" => KnownNames::StdMemManuallyDropNew,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_maybe_uninit_namespace =
            |mut def_path_data_iter: Iter<'_>| {
                get_path_data_elem_name(def_path_data_iter.next())
                    .map(|n| match n.as_str() {
                        "uninit" => KnownNames::StdMemMaybeUninitUninit,
                        _ => KnownNames::None,
                    })
                    .unwrap_or(KnownNames::None)
            };

        let get_known_name_for_mem_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "size_of" => KnownNames::StdMemSizeOf,
                    "forget" => KnownNames::StdMemForget,
                    "uninitialized" => KnownNames::StdMemUninitialized,
                    "manually_drop" => {
                        get_known_name_for_manually_drop_namespace(def_path_data_iter)
                    }
                    "MaybeUninit" => {
                        get_known_name_for_maybe_uninit_namespace(def_path_data_iter)
                    }
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_ops_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "index" | "index_mut" => KnownNames::CoreOpsIndex,
                    "deref" => KnownNames::CoreOpsDeref,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_panicking_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "begin_panic" | "panic" => KnownNames::StdPanickingBeginPanic,
                    "begin_panic_fmt" | "panic_fmt" => KnownNames::StdPanickingBeginPanicFmt,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_slice_namespace = |mut def_path_data_iter: Iter<'_>| {
            def_path_data_iter.next();
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "into_vec" => KnownNames::StdIntoVec,
                    "get_unchecked_mut" => KnownNames::StdSliceIndexGetUncheckedMut,
                    "get_unchecked" => KnownNames::StdSliceIndexGetUnchecked,
                    "from_raw_parts" => KnownNames::StdSliceFromRawParts,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_convert_namespace = |mut def_path_data_iter: Iter<'_>| {
            def_path_data_iter.next();
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "from" => KnownNames::StdFrom,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_vec_namespace = |mut def_path_data_iter: Iter<'_>| {
            // 路径可能是 alloc::vec::Vec::set_len 或 alloc::vec::{{impl}}::set_len
            // 下一个元素可能是 "Vec" (TypeNs) 或者 "{impl}" (Impl)
            // get_path_data_elem_name 对于 Impl 会返回 None
            
            let maybe_vec_or_impl = def_path_data_iter.next();
            
            // 如果有名字，可能是 "Vec"；如果是 None (Impl)，则继续
            if let Some(name) = get_path_data_elem_name(maybe_vec_or_impl) {
                // 允许 "Vec" 或跳过（如果是 impl 块）
                if name.as_str() != "Vec" {
                    // 如果不是 "Vec"，可能是其他类型，继续检查下一个元素
                    debug!("Vec namespace: found non-Vec type name: {}", name.as_str());
                }
            } else {
                debug!("Vec namespace: found impl block (no name)");
            }

            // 检查方法名
            let method_name = def_path_data_iter.next();
            let result = get_path_data_elem_name(method_name)
                .map(|n| {
                    debug!("Vec namespace: checking method name: {}", n.as_str());
                    match n.as_str() {
                        // "as_ptr" => KnownNames::StdAsPtr,
                        // "as_mut_ptr" => KnownNames::StdAsMutPtr,
                        "from_raw_parts" => KnownNames::VecFromRawParts,
                        "with_capacity" => KnownNames::VecWithCapacity,
                        "reserve" => {
                            debug!("Vec namespace: recognized Vec::reserve");
                            KnownNames::VecReserve
                        }
                        "set_len" => {
                            debug!("Vec namespace: recognized Vec::set_len");
                            KnownNames::VecSetLen
                        }
                        _ => KnownNames::None,
                    }
                })
                .unwrap_or_else(|| {
                    debug!("Vec namespace: method name not found or is impl");
                    KnownNames::None
                });
            result
        };

        let get_known_name_for_ptr_mut_ptr_namespace = |mut def_path_data_iter: Iter<'_>| {
            def_path_data_iter.next();
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "read" => KnownNames::StdPtrMutPtrRead,
                    // "write_bytes" => KnownNames::StdIntrinsicsWriteBytes,
                    "offset_from" => KnownNames::StdPtrConstPtrOffsetFrom,
                    "byte_offset_from" => KnownNames::StdPtrMutPtrByteOffsetFrom,
                    "cast" => KnownNames::StdPtrMutPtrCast,
                    "add" => KnownNames::StdPtrMutPtrAdd,
                    "sub" => KnownNames::StdPtrMutPtrSub,
                    "offset" => KnownNames::StdPtrMutPtrOffset,
                    "byte_add" => KnownNames::StdPtrMutPtrByteAdd,
                    "byte_sub" => KnownNames::StdPtrMutPtrByteSub,
                    "byte_offset" => KnownNames::StdPtrMutPtrByteOffset,
                    "wrapping_add" => KnownNames::StdPtrMutPtrWrappingAdd,
                    "wrapping_sub" => KnownNames::StdPtrMutPtrWrappingSub,
                    "wrapping_offset" => KnownNames::StdPtrMutPtrWrappingOffset,
                    "wrapping_byte_add" => KnownNames::StdPtrMutPtrWrappingByteAdd,
                    "wrapping_byte_sub" => KnownNames::StdPtrMutPtrWrappingByteSub,
                    "wrapping_byte_offset" => KnownNames::StdPtrMutPtrWrappingByteOffset,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_boxed_namespace = |mut def_path_data_iter: Iter<'_>| {
            // 路径通常是 alloc::boxed::{impl}::leak 或 alloc::boxed::Box::leak
            // 下一个元素可能是 "Box" (TypeNs) 或者 "{impl}" (Impl)
            // get_path_data_elem_name 对于 Impl 会返回 None
            
            let maybe_box_or_impl = def_path_data_iter.next();
            
            // 如果有名字，必须是 "Box"；如果是 None (Impl)，则继续
            if let Some(name) = get_path_data_elem_name(maybe_box_or_impl) {
                if name.as_str() != "Box" {
                    return KnownNames::None;
                }
            }

            // 检查方法名
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "into_raw" => KnownNames::StdBoxIntoRaw,
                    "leak" => KnownNames::StdBoxLeak,
                    "from_raw" => KnownNames::StdBoxFromRaw,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_ptr_const_ptr_namespace = |mut def_path_data_iter: Iter<'_>| {
            def_path_data_iter.next();
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    // "write_bytes" => KnownNames::StdIntrinsicsWriteBytes,
                    "read" => KnownNames::StdPtrConstPtrRead,
                    "offset_from" => KnownNames::StdPtrConstPtrOffsetFrom,
                    "byte_offset_from" => KnownNames::StdPtrMutPtrByteOffsetFrom,
                    "cast" => KnownNames::StdPtrConstPtrCast,
                    "add" => KnownNames::StdPtrConstPtrAdd,
                    "sub" => KnownNames::StdPtrConstPtrSub,
                    "offset" => KnownNames::StdPtrConstPtrOffset,
                    "byte_add" => KnownNames::StdPtrConstPtrByteAdd,
                    "byte_sub" => KnownNames::StdPtrConstPtrByteSub,
                    "byte_offset" => KnownNames::StdPtrConstPtrByteOffset,
                    "wrapping_add" => KnownNames::StdPtrConstPtrWrappingAdd,
                    "wrapping_sub" => KnownNames::StdPtrConstPtrWrappingSub,
                    "wrapping_offset" => KnownNames::StdPtrConstPtrWrappingOffset,
                    "wrapping_byte_add" => KnownNames::StdPtrConstPtrWrappingByteAdd,
                    "wrapping_byte_sub" => KnownNames::StdPtrConstPtrWrappingByteSub,
                    "wrapping_byte_offset" => KnownNames::StdPtrConstPtrWrappingByteOffset,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_ptr_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "mut_ptr" => get_known_name_for_ptr_mut_ptr_namespace(def_path_data_iter),
                    "const_ptr" => get_known_name_for_ptr_const_ptr_namespace(def_path_data_iter),
                    "read" => KnownNames::StdPtrRead,
                    "read_unaligned" => KnownNames::StdPtrReadUnAligned,
                    "read_volatile" => KnownNames::StdPtrReadVolatile,
                    "drop_in_place" => KnownNames::StdPtrDropInPlace,
                    "replace" => KnownNames::StdPtrReplace,
                    "write" => KnownNames::StdPtrWrite,
                    "write_bytes" => KnownNames::StdPtrWriteBytes,
                    "write_unaligned" => KnownNames::StdPtrWriteUnAligned,
                    "write_volatile" => KnownNames::StdPtrWriteVolatile,
                    "swap" => KnownNames::StdPtrSwap,
                    "swap_nonoverlapping" => KnownNames::StdPtrSwapNonOverlapping,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_converts_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "from_utf8_unchecked" => KnownNames::CoreStrConvertsFromUtf8Unchecked,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_str_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "converts" => get_known_name_for_converts_namespace(def_path_data_iter),
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_intrinsics_namespace = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "copy" => KnownNames::StdIntrinsicsCopy,
                    "copy_nonoverlapping" => KnownNames::StdIntrinsicsCopyNonOverlapping,
                    _ => KnownNames::None,
                })
                .unwrap_or(KnownNames::None)
        };

        let get_known_name_for_known_crate = |mut def_path_data_iter: Iter<'_>| {
            get_path_data_elem_name(def_path_data_iter.next())
                .map(|n| match n.as_str() {
                    "alloc" => get_known_name_for_alloc_namespace(def_path_data_iter),
                    "mem" => get_known_name_for_mem_namespace(def_path_data_iter),
                    "boxed" => get_known_name_for_boxed_namespace(def_path_data_iter), // 注册 boxed 命名空间
                    "ops" => get_known_name_for_ops_namespace(def_path_data_iter),
                    "slice" => get_known_name_for_slice_namespace(def_path_data_iter),
                    "panicking" => get_known_name_for_panicking_namespace(def_path_data_iter),
                    "convert" => get_known_name_for_convert_namespace(def_path_data_iter),
                    "vec" => get_known_name_for_vec_namespace(def_path_data_iter),
                    "ptr" => get_known_name_for_ptr_namespace(def_path_data_iter),
                    "str" => get_known_name_for_str_namespace(def_path_data_iter),
                    "mir_checker_verify" => KnownNames::CheckerVerify,
                    "intrinsics" => get_known_name_for_intrinsics_namespace(def_path_data_iter),
                    _ => {
                        debug!("Normal function: {:?}", n.as_str());
                        KnownNames::None
                    }
                })
                .unwrap_or(KnownNames::None)
        };

        let crate_name = tcx.crate_name(def_id.krate);
        match crate_name.as_str() {
            // Only recognize known functions from the following crates
            "alloc" | "core" | "macros" | "std" => {
                get_known_name_for_known_crate(def_path_data_iter)
            }
            _ => KnownNames::None,
        }
    }
}
