// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Physical roles are authenticated on the immutable canonical graph once.
use super::*;
use crate::reader::modes::{ReborrowPhase, ReborrowUse};
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use rustc_middle::ty::adjustment::{
    Adjust, AllowTwoPhase, AutoBorrow, AutoBorrowMutability, DerefAdjustKind,
};
use thir::{ExprId, ExprKind, Thir};

#[derive(Clone, Copy)]
pub(super) struct Site {
    pub adjusted: ExprId,
    pub source: ExprId,
}
pub(super) type Sites = HashMap<hir::HirId, Site>;

fn without_scopes(body: &Thir<'_>, mut id: ExprId) -> ExprId {
    let mut seen = HashSet::new();
    while let ExprKind::Scope { value, .. } = body[id].kind {
        assert!(seen.insert(id), "a canonical scope cycle");
        id = value;
    }
    id
}

fn reborrow_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &Thir<'tcx>,
    id: hir::HirId,
    adjusted: ExprId,
    detail: ReborrowUse,
) -> ExprId {
    let hir::Node::Expr(expression) = tcx.hir_node(id) else {
        panic!("source expression");
    };
    let typeck = tcx.typeck(owner);
    let adjustments = typeck.expr_adjustments(expression);
    assert_eq!(
        (detail.deref_index, detail.borrow_index, adjustments.len()),
        (0, 1, 2)
    );
    assert!(matches!(
        adjustments[0].kind,
        Adjust::Deref(DerefAdjustKind::Builtin)
    ));
    let Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Mut {
        allow_two_phase_borrow,
    })) = adjustments[1].kind
    else {
        panic!("the recorded mutable reborrow adjustment");
    };
    assert_eq!(
        detail.phase,
        match allow_two_phase_borrow {
            AllowTwoPhase::No => ReborrowPhase::Immediate,
            AllowTwoPhase::Yes => ReborrowPhase::TwoPhase,
        }
    );
    let ExprKind::Borrow {
        borrow_kind: BorrowKind::Mut { kind },
        arg: deref,
    } = body[adjusted].kind
    else {
        panic!("the physical adjusted borrow");
    };
    assert_eq!(
        kind,
        match detail.phase {
            ReborrowPhase::Immediate => MutBorrowKind::Default,
            ReborrowPhase::TwoPhase => MutBorrowKind::TwoPhaseBorrow,
        }
    );
    let ExprKind::Deref { arg: source } = body[deref].kind else {
        panic!("the physical adjustment dereference");
    };
    assert_eq!(body[adjusted].ty, typeck.expr_ty_adjusted(expression));
    assert_eq!(body[deref].ty, adjustments[0].target);
    assert_eq!(body[source].ty, typeck.expr_ty(expression));
    assert_eq!(body[adjusted].ty, adjustments[1].target);
    source
}

pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &Thir<'tcx>,
    map: &HashMap<hir::HirId, hooks::Shadow>,
    plan: &modes::Plan,
) -> Sites {
    let mut required = map
        .values()
        .map(|shadow| shadow.initializer)
        .collect::<HashSet<_>>();
    required.extend(plan.reborrows.keys().copied());
    for ids in [
        &plan.reads,
        &plan.erases,
        &plan.borrows,
        &plan.assigns,
        &plan.adjusted_borrows,
    ] {
        required.extend(ids.iter().copied());
    }
    let mut scopes = HashMap::new();
    for (_, expression) in body.exprs.iter_enumerated() {
        if let ExprKind::Scope { hir_id, value, .. } = expression.kind {
            if required.contains(&hir_id) {
                assert!(
                    scopes.insert(hir_id, value).is_none(),
                    "ambiguous canonical source scope"
                );
            }
        }
    }
    let mut sites = HashMap::new();
    for id in required {
        let adjusted = without_scopes(body, scopes[&id]);
        let source = if let Some(detail) = plan.reborrows.get(&id) {
            reborrow_source(tcx, owner, body, id, adjusted, *detail)
        } else {
            adjusted
        };
        assert!(sites.insert(id, Site { adjusted, source }).is_none());
    }
    sites
}
