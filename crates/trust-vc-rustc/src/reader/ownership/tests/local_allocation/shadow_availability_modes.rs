// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Completed same-context mode facts select exact source occurrences.
use super::*;
use crate::reader::attrs::ItemAttrs;
use crate::reader::declaration_modes::DeclarationModes;
use crate::reader::modes::{
    self, AccessKind, ModeCheck, ModeContext, ReborrowDisposition, ReborrowPhase, ReborrowUse,
    VarErasure,
};
use crate::verus_items::VerusItem;
use rustc_hir::intravisit::{self, Visitor};
use trust_vc_vcir::Mode;

struct Context<'tcx>(DeclarationModes<'tcx>);
impl<'tcx> ModeContext<'tcx> for Context<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.0.tcx()
    }
    fn function_mode(&self, definition: DefId) -> Option<Mode> {
        self.0.function_mode(definition)
    }
    fn body_owner(&self, definition: LocalDefId) -> Option<LocalDefId> {
        self.0.body_owner(definition)
    }
    fn declaration_attrs(&self, definition: LocalDefId) -> ItemAttrs {
        self.0.declaration_attrs(definition)
    }
    fn verus_item(&self, definition: DefId) -> Option<VerusItem> {
        self.0.verus_item(definition)
    }
    fn new_mut_ref(&self) -> bool {
        true
    }
    fn constant_proxy(&self, definition: LocalDefId) -> Option<LocalDefId> {
        self.0.constant_proxy(definition)
    }
    fn constant_mode(&self, definition: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        self.0.constant_mode(definition)
    }
    fn friendly_fn_path(&self, definition: DefId) -> String {
        self.0.friendly_fn_path(definition)
    }
    fn read_adt_field_modes(&self) -> bool {
        true
    }
    fn permits_adt_fields(&self, definition: DefId) -> bool {
        definition.is_local()
    }
}
pub(super) struct Plan {
    pub reads: Vec<hir::HirId>,
    pub erases: Vec<hir::HirId>,
    pub borrows: Vec<hir::HirId>,
    pub assigns: Vec<hir::HirId>,
    pub reborrows: HashMap<hir::HirId, ReborrowUse>,
    pub adjusted_borrows: Vec<hir::HirId>,
}

fn mode_failure<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, result: ModeCheck<'tcx>) -> ! {
    struct Adjustments<'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        rows: Vec<String>,
    }
    impl<'tcx> Visitor<'tcx> for Adjustments<'tcx> {
        fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
            let typeck = self.tcx.typeck(self.owner);
            let adjustments = typeck.expr_adjustments(expression);
            if !adjustments.is_empty() {
                self.rows.push(format!(
                    "{:?} {:?}: source={:?}, type={:?}, adjusted={:?}, adjustments={adjustments:?}",
                    expression.hir_id,
                    expression.span,
                    self.tcx.sess.source_map().span_to_snippet(expression.span),
                    typeck.expr_ty(expression),
                    typeck.expr_ty_adjusted(expression),
                ));
            }
            intravisit::walk_expr(self, expression);
        }
    }
    let mut observed = Adjustments {
        tcx,
        owner,
        rows: Vec::new(),
    };
    observed.visit_body(tcx.hir_body_owned_by(owner));
    panic!(
        "actual source mode check failed: {result:?}; adjustments={:#?}",
        observed.rows
    );
}
pub(super) fn plan(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    map: &HashMap<hir::HirId, hooks::Shadow>,
) -> Plan {
    let context = Context(DeclarationModes::new(tcx));
    let checked = match modes::check_with_context(&context, owner) {
        ModeCheck::Clean(checked) => checked,
        result => mode_failure(tcx, owner, result),
    };
    let facts = checked
        .availability
        .checked(tcx, owner, owner)
        .expect("same-context original body facts");
    let synthetic = map
        .values()
        .map(|shadow| shadow.binding)
        .collect::<HashSet<_>>();
    let seeds = map
        .values()
        .map(|shadow| shadow.initializer)
        .collect::<HashSet<_>>();
    let expression = |id| {
        let hir::Node::Expr(expression) = tcx.hir_node(id) else {
            panic!("actual source expression");
        };
        expression
    };
    let mut plan = Plan {
        reads: Vec::new(),
        erases: Vec::new(),
        borrows: Vec::new(),
        assigns: Vec::new(),
        reborrows: HashMap::new(),
        adjusted_borrows: Vec::new(),
    };
    for row in facts.uses() {
        if synthetic.contains(&row.binding)
            || seeds.contains(&row.place)
            || seeds.contains(&row.local_use)
        {
            continue;
        }
        if row.access == AccessKind::Read && row.erasure == VarErasure::Shadow {
            assert!(row.shadow_check && row.mode == Mode::Spec && row.binding_mode != Mode::Spec);
            assert_eq!(
                facts
                    .use_for(expression(row.place), AccessKind::Read)
                    .unwrap(),
                row
            );
            if !map.contains_key(&row.binding) {
                tcx.dcx()
                    .fatal("a required shadow read has no published shadow map");
            }
            plan.reads.push(row.place);
        } else if row.access == AccessKind::Read && row.erasure == VarErasure::Erase {
            assert_eq!(
                facts
                    .use_for(expression(row.place), AccessKind::Read)
                    .unwrap(),
                row
            );
            plan.erases.push(row.place);
        }
    }
    for row in facts.operations() {
        let access = facts
            .use_for(expression(row.place), row.kind)
            .expect("whole-place access mode");
        if synthetic.contains(&access.binding) || seeds.contains(&row.expression) {
            continue;
        }
        assert_eq!(
            facts.operation_for(expression(row.expression)).unwrap(),
            row
        );
        if access.erasure != VarErasure::Keep {
            tcx.dcx()
                .fatal("this component requires kept source mutation operations");
        }
        if !map.contains_key(&access.binding) {
            tcx.dcx()
                .fatal("a required mutation has no published shadow map");
        }
        match row.kind {
            AccessKind::MutBorrow => plan.borrows.push(row.expression),
            AccessKind::Assign => plan.assigns.push(row.expression),
            AccessKind::Read => panic!("a read is not a mutation operation"),
        }
    }
    for row in facts.adjustments() {
        let Some(detail) = row.reborrow else {
            continue;
        };
        assert_eq!(
            facts.adjustment_for(expression(row.expression)).unwrap(),
            row
        );
        assert_eq!((detail.deref_index, detail.borrow_index), (0, 1));
        assert!(plan.reborrows.insert(row.expression, detail).is_none());
        if detail.disposition != ReborrowDisposition::KeptPlace {
            continue;
        }
        let access = facts
            .use_for(expression(row.expression), AccessKind::MutBorrow)
            .expect("the actual carrier access of a kept implicit reborrow");
        if synthetic.contains(&access.binding) || seeds.contains(&row.expression) {
            continue;
        }
        assert_eq!(detail.phase, ReborrowPhase::Immediate);
        assert_eq!(access.place_mode, detail.carrier_mode);
        assert_eq!(access.mode, detail.carrier_mode);
        assert_eq!(detail.pointee_mode, Some(Mode::Exec));
        assert_eq!(access.erasure, VarErasure::Keep);
        if !map.contains_key(&access.binding) {
            tcx.dcx()
                .fatal("a required implicit borrow has no published shadow map");
        }
        plan.adjusted_borrows.push(row.expression);
    }
    plan
}
