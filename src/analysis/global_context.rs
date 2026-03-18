use crate::analysis::contain_unsafe::contains_unsafe;
use crate::analysis::diagnostics::DiagnosticsForDefId;
use crate::analysis::memory::symbolic_value::SymbolicValue;
use crate::analysis::option::Options;
use crate::analysis::wto::Wto;
use log::{debug, info};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc; // 添加这个导入

/// Cache the wto so we do not need to recompute them when analyzing a function multiple times
pub struct WtoCache<'tcx> {
    value: HashMap<DefId, Wto<'tcx>>,
}

impl<'tcx> WtoCache<'tcx> {
    pub fn get(&self, def_id: DefId) -> Option<&Wto<'tcx>> {
        self.value.get(&def_id)
    }

    pub fn insert(&mut self, def_id: DefId, wto: Wto<'tcx>) {
        self.value.insert(def_id, wto);
    }
}

impl<'tcx> Default for WtoCache<'tcx> {
    fn default() -> Self {
        Self {
            value: HashMap::new(),
        }
    }
}

/// Stores the global information of the analysis
pub struct GlobalContext<'tcx, 'compilation> {
    /// The central data structure of the compiler
    pub tcx: TyCtxt<'tcx>,

    /// Represents the data associated with a compilation session for a single crate
    pub session: &'compilation Session,

    /// The entry functions of the analysis
    pub entry_points: Vec<DefId>,

    /// The current entry function to analyze
    pub entry_point: DefId,

    /// Stores the DefIds that have been already checked, to avoid redundant check
    pub checked_def_ids: HashSet<DefId>,

    /// Cache for the Weak Topological Ordering
    pub wto_cache: WtoCache<'tcx>,

    /// Stores the Heaps that have been already dropped, to detect double-free, use-after-free, etc.
    pub dropped_heaps: HashSet<Rc<SymbolicValue>>,

    /// Cache for the name of each DefId
    pub function_name_cache: HashMap<DefId, Rc<String>>,

    /// Customized options that may change the behavior of the analysis
    pub analysis_options: Options,

    /// Generated diagnostic messages for each DefId
    pub diagnostics_for: DiagnosticsForDefId<'compilation>,
}

impl<'tcx, 'compilation> fmt::Debug for GlobalContext<'tcx, 'compilation> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GlobalContext")
    }
}

impl<'tcx, 'compilation> GlobalContext<'tcx, 'compilation> {
    pub fn new(
        session: &'compilation Session,
        tcx: TyCtxt<'tcx>,
        analysis_options: Options,
    ) -> Option<Self> {
        info!("Initializing GlobalContext");

        // 存储所有入口点
        let mut entry_points = Vec::new();

        // 如果指定了只分析 unsafe 代码
        if analysis_options.unsafe_only {
            let mut unsafe_functions = Vec::new();

            // 遍历所有函数
            for def_id in tcx.hir_body_owners() {
                if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                    let def_id = def_id.to_def_id();

                    // 使用 contains_unsafe 函数检查函数
                    if contains_unsafe(tcx, def_id) {
                        // 收集符合条件的函数
                        let name = tcx.item_name(def_id);
                        unsafe_functions.push((def_id, name.to_string()));

                        // 将 unsafe 函数添加到入口点列表
                        entry_points.push(def_id);

                        // 输出找到的unsafe函数信息
                        info!("Found unsafe function: {} (DefId: {:?})", name, def_id);
                    }
                }
            }

            // 输出所有找到的unsafe函数列表
            if !unsafe_functions.is_empty() {
                info!("Found {} unsafe functions:", unsafe_functions.len());
                for (def_id, name) in &unsafe_functions {
                    info!("  {} (DefId[{:?}])", name, def_id.index.as_u32());
                }
            } else {
                info!("No unsafe functions found in the codebase.");
            }

            // 如果没有找到 unsafe 函数，则返回 None
            if entry_points.is_empty() {
                return None;
            }
        } else if analysis_options.show_entries {
            // 只显示条目名称，不进行分析
            let mut names = HashSet::new();
            for def_id in tcx.hir_body_owners() {
                if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                    let name = tcx.item_name(def_id.to_def_id());
                    if !names.contains(&name) {
                        names.insert(name);
                        println!("{}", name);
                    }
                }
            }
            return None;
        } else if analysis_options.show_entries_index {
            // 只显示条目索引，不进行分析
            for def_id in tcx.hir_body_owners() {
                if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                    println!("{}", def_id.to_def_id().index.as_u32());
                }
            }
            return None;
        } else {
            // 默认情况：查找指定的入口函数
            let mut entry_func = None;

            // 遍历所有函数
            for def_id in tcx.hir_body_owners() {
                let def_kind = tcx.def_kind(def_id);
                // 查找入口点，入口点必须是函数
                if def_kind == DefKind::Fn || def_kind == DefKind::AssocFn {
                    // 如果提供了 entry_def_id_index 标志，则根据索引查找入口点
                    if let Some(entry_def_id_index) = analysis_options.entry_def_id_index {
                        let item_name = tcx.item_name(def_id.to_def_id());
                        if def_id.to_def_id().index.as_u32() == entry_def_id_index {
                            entry_func = Some(def_id);
                            debug!("Entry Point: {:?}, DefId: {:?}", item_name, def_id);
                        } else {
                            debug!(
                                "Name: {:?}, DefId: {:?}, DefKind: {:?}",
                                tcx.item_name(def_id.to_def_id()),
                                def_id,
                                def_kind
                            );
                        }
                    }
                    // 如果没有提供索引，则根据函数名称查找入口点
                    else {
                        let entry_point = analysis_options.entry_point.clone();
                        let item_name = tcx.item_name(def_id.to_def_id());
                        if item_name.to_string() == *entry_point {
                            entry_func = Some(def_id);
                            debug!("Entry Point: {:?}, DefId: {:?}", item_name, def_id);
                        } else {
                            debug!(
                                "Name: {:?}, DefId: {:?}, DefKind: {:?}",
                                tcx.item_name(def_id.to_def_id()),
                                def_id,
                                def_kind
                            );
                        }
                    }
                }
            }

            // 将找到的入口函数添加到入口点列表
            if let Some(entry) = entry_func {
                entry_points.push(entry.to_def_id());
            } else {
                error!("Entry point not found");
                return None;
            }
        }
        debug_assert!(entry_points.len() != 0);
        let entry_point = entry_points[0].clone();
        // 创建并返回 GlobalContext 实例
        Some(Self {
            tcx,
            session,
            function_name_cache: HashMap::new(),
            entry_points, // 使用新的 entry_points 字段
            entry_point: entry_point,
            checked_def_ids: HashSet::new(),
            dropped_heaps: HashSet::new(),
            wto_cache: WtoCache::default(),
            analysis_options,
            diagnostics_for: DiagnosticsForDefId::default(),
        })
    }

    pub fn get_wto(&mut self, def_id: DefId) -> Wto<'tcx> {
        let mir = self.tcx.optimized_mir(def_id);
        let wto;
        // First see whether the wto has been already computed
        if let Some(cached_wto) = self.wto_cache.get(def_id) {
            debug!("Using cached w.t.o for {}", self.tcx.item_name(def_id));
            wto = cached_wto.clone();
        } else {
            // If not, compute the wto
            wto = Wto::new(mir);
            debug!(
                "Compute the new w.t.o for {}: {:?}",
                self.tcx.item_name(def_id),
                wto
            );
            // Cache the wto
            self.wto_cache.insert(def_id, wto.clone());
        }
        wto
    }
}
