use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Terminator, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use std::collections::HashSet;

/// Copied from Miri
/// Returns the "default sysroot" if no `--sysroot` flag is set.
/// Should be a compile-time constant.
pub fn compile_time_sysroot() -> Option<String> {
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc.
        return None;
    }
    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default.  The sysroot computation in librustc would
    // end up somewhere in the build dir.
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build Miri without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

pub fn find_sysroot() -> String {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{home}/toolchains/{toolchain}"),
        _ => match option_env!("RUST_SYSROOT") {
            None => {
                panic!(
                    "Could not find sysroot. Specify the RUST_SYSROOT environment variable, \
                 or use rustup to set the compiler to use for Mirai",
                )
            }
            Some(sys_root) => sys_root.to_owned(),
        },
    }
}

// 获取指定函数中所有被调用的函数的 DefId
pub fn get_called_functions<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> HashSet<DefId> {
    let mut called_functions = HashSet::new();

    // 获取函数的 MIR body
    let body = tcx.optimized_mir(def_id);

    // 遍历所有基本块
    for bb_data in body.basic_blocks.iter() {
        // 检查终结符 (terminator)
        if let Some(terminator) = &bb_data.terminator {
            extract_calls_from_terminator(terminator, &mut called_functions);
        }

        // 检查语句中的调用（某些情况下调用可能在语句中）
        for _ in &bb_data.statements {
            // 这里可以根据需要处理语句中的调用
            // 通常函数调用在 terminator 中
        }
    }

    called_functions
}

/// 从终结符中提取函数调用的 DefId
fn extract_calls_from_terminator(terminator: &Terminator, called_functions: &mut HashSet<DefId>) {
    match &terminator.kind {
        TerminatorKind::Call { func, .. } => {
            // 从 Operand 中获取函数的 DefId
            if let Some(def_id) = extract_def_id_from_operand(func) {
                called_functions.insert(def_id);
            }
        }
        // 其他类型的终结符不包含函数调用
        _ => {}
    }
}

/// 从 Operand 中提取 DefId
fn extract_def_id_from_operand(operand: &rustc_middle::mir::Operand) -> Option<DefId> {
    use rustc_middle::mir::Operand;
    use rustc_middle::ty::TyKind;

    match operand {
        Operand::Constant(box constant) => {
            // 从常量中获取类型
            match constant.ty().kind() {
                TyKind::FnDef(def_id, _) => Some(*def_id),
                _ => None,
            }
        }
        _ => None,
    }
}

/// 获取指定 DefId 的起始 span
pub fn get_def_span<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Span> {
    // 尝试获取 HIR 节点的 span
    if let Some(_) = def_id.as_local() {
        // 对于本地定义的项，可以从 TyCtxt 直接获取 span
        Some(tcx.def_span(def_id))
    } else {
        // 对于外部 crate 的项，尝试从 metadata 中获取 span
        tcx.def_span(def_id).into()
    }
}

/// 获取多个 DefId 的 span 信息
pub fn get_multiple_def_spans<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_ids: &HashSet<DefId>,
) -> Vec<(DefId, Option<Span>)> {
    def_ids
        .iter()
        .map(|&def_id| (def_id, get_def_span(tcx, def_id)))
        .collect()
}

/// 获取函数调用链的 span 信息（包含调用者和被调用者的 span）
pub fn get_call_chain_spans<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
) -> Vec<(DefId, Option<Span>)> {
    let called_functions = get_called_functions(tcx, caller_def_id);
    let mut spans = vec![(caller_def_id, get_def_span(tcx, caller_def_id))];

    for called_def_id in called_functions {
        spans.push((called_def_id, get_def_span(tcx, called_def_id)));
    }

    spans
}
