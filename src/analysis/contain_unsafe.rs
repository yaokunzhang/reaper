use log::debug;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{
    self as hir,
    intravisit::{self, Visitor},
};
use rustc_hir::{Block, BlockCheckMode, Expr, ExprKind, QPath, UnOp};
use rustc_middle::ty::TyCtxt;

struct ContainUnsafe<'tcx> {
    tcx: TyCtxt<'tcx>,
    has_unsafe: bool,
}

impl<'tcx> ContainUnsafe<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            has_unsafe: false,
        }
    }

    pub fn check_def_id(&mut self, def_id: DefId) -> bool {
        self.has_unsafe = false;

        let fn_sig = self.tcx.fn_sig(def_id);
        if fn_sig.skip_binder().safety().is_unsafe() {
            return true;
        }

        if let Some(local_def_id) = def_id.as_local() {
            self.check_function(local_def_id);
        }

        self.has_unsafe
    }

    fn check_function(&mut self, def_id: LocalDefId) -> bool {
        if let Some(body_id) = self.tcx.hir_node_by_def_id(def_id).body_id() {
            let body = self.tcx.hir_body(body_id);
            self.visit_body(body);
        }
        self.has_unsafe
    }
}

impl<'tcx> Visitor<'tcx> for ContainUnsafe<'tcx> {
    // type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        match block.rules {
            BlockCheckMode::UnsafeBlock(..) => {
                self.has_unsafe = true;
            }
            _ => {}
        }
        intravisit::walk_block(self, block);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call(func, _) => {
                if let ExprKind::Path(QPath::Resolved(_, path)) = &func.kind {
                    if let hir::def::Res::Def(hir::def::DefKind::Fn, def_id) = path.res {
                        if self.is_unsafe_function(def_id) {
                            self.has_unsafe = true;
                        }
                    }
                }
            }
            ExprKind::MethodCall(..) => {
                let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                if let Some(def_id) = typeck.type_dependent_def_id(expr.hir_id) {
                    if self.is_unsafe_function(def_id) {
                        self.has_unsafe = true;
                    }
                }
            }

            ExprKind::Unary(UnOp::Deref, operand) => {
                let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                let operand_ty: rustc_middle::ty::Ty<'_> = typeck.expr_ty(operand);
                if operand_ty.is_raw_ptr() {
                    self.has_unsafe = true;
                }
            }

            ExprKind::Field(base, _) => {
                let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                let base_ty = typeck.expr_ty(base);
                if let rustc_middle::ty::TyKind::Adt(adt_def, _) = base_ty.kind() {
                    if adt_def.is_union() {
                        self.has_unsafe = true;
                    }
                }
            }

            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

impl<'tcx> ContainUnsafe<'tcx> {
    fn is_unsafe_function(&self, def_id: DefId) -> bool {
        let fn_sig = self.tcx.fn_sig(def_id);
        if fn_sig.skip_binder().safety().is_unsafe() {
            debug!(
                "Function {} is marked as unsafe",
                self.tcx.item_name(def_id)
            );
            return true;
        }
        return false;
    }
}

pub fn contains_unsafe<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let mut checker = ContainUnsafe::new(tcx);
    checker.check_def_id(def_id)
}
