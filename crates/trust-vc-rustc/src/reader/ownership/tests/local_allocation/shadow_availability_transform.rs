// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact source scopes connect real mode facts to the cloned THIR graph.
use super::*;
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use thir::{ExprId, ExprKind, Thir};

pub(super) fn apply<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &mut Thir<'tcx>,
    root: ExprId,
    map: &HashMap<hir::HirId, hooks::Shadow>,
    helpers: Helpers,
    plan: modes::Plan,
    sites: sites::Sites,
    case: Case,
) -> Counts {
    let metadata = (body[root].ty, body[root].span, body[root].temp_scope_id);
    let mut counts = Counts::default();
    for shadow in map.values() {
        let mut lets = body.stmts.iter().filter_map(|statement| {
            let thir::StmtKind::Let {
                hir_id,
                pattern,
                initializer: Some(initializer),
                ..
            } = &statement.kind
            else {
                return None;
            };
            let thir::PatKind::Binding { var, ty, .. } = &pattern.kind else {
                return None;
            };
            (*hir_id == shadow.local && var.0 == shadow.binding).then_some((
                *initializer,
                *ty,
                pattern.ty,
            ))
        });
        let (initializer, binding_type, pattern_type) =
            lets.next().expect("registered real shadow Let");
        assert!(lets.next().is_none());
        let id = sites[&shadow.initializer].adjusted;
        let meta = body[id].clone();
        let expected = tcx.typeck(owner).node_type(shadow.binding);
        assert_eq!(
            (body[initializer].ty, binding_type, pattern_type, meta.ty),
            (expected, expected, expected, expected)
        );
        let unit = expressions::tuple(tcx, body, &meta, Vec::new());
        let kind = expressions::call_kind(
            tcx,
            body,
            &meta,
            helpers.erased,
            [tcx.types.unit, expected],
            vec![unit],
            false,
        );
        body.exprs[id].kind = kind;
        counts.seeds += 1;
    }
    if case != Case::FullKeep {
        for source in plan.erases {
            let site = sites[&source];
            let id = site.adjusted;
            let meta = body[id].clone();
            if !expressions::pure_place(body, site.source) {
                tcx.dcx().fatal("unsupported effectful erased read");
            }
            let unit = expressions::tuple(tcx, body, &meta, Vec::new());
            body.exprs[id].kind = expressions::call_kind(
                tcx,
                body,
                &meta,
                helpers.erased,
                [tcx.types.unit, meta.ty],
                vec![unit],
                false,
            );
            counts.erased_reads += 1;
        }
        for source in plan.reads {
            let site = sites[&source];
            let id = site.adjusted;
            let meta = body[id].clone();
            let mirrored = expressions::mirror(tcx, owner, body, site.source, map);
            counts.projected_reads +=
                usize::from(projections::fields(body, site.source, mirrored) > 0);
            let borrowed = expressions::borrow(tcx, body, &meta, mirrored, false);
            let tuple = expressions::tuple(tcx, body, &meta, vec![borrowed]);
            let argument = body[tuple].ty;
            body.exprs[id].kind = expressions::call_kind(
                tcx,
                body,
                &meta,
                helpers.shadow,
                [argument, meta.ty],
                vec![tuple],
                false,
            );
            counts.reads += 1;
        }
    }
    for (source, adjusted) in plan
        .borrows
        .into_iter()
        .map(|id| (id, false))
        .chain(plan.adjusted_borrows.into_iter().map(|id| (id, true)))
    {
        let site = sites[&source];
        let id = if adjusted { site.adjusted } else { site.source };
        let meta = body[id].clone();
        let ExprKind::Borrow {
            borrow_kind:
                BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                },
            arg,
        } = meta.kind
        else {
            tcx.dcx().fatal("unsupported kept borrow kind");
        };
        let original = body.exprs.push(meta.clone());
        let mirrored = expressions::mirror(tcx, owner, body, arg, map);
        counts.projected_ties += usize::from(projections::fields(body, arg, mirrored) > 0);
        let shadow = expressions::borrow(tcx, body, &meta, mirrored, true);
        let first = body[arg].ty;
        let second = body[mirrored].ty;
        let kind = expressions::call_kind(
            tcx,
            body,
            &meta,
            helpers.tie,
            [first, second],
            vec![original, shadow],
            true,
        );
        body.exprs[id].kind = kind;
        counts.ties += 1;
        if adjusted {
            counts.adjusted_ties += 1;
            let detail = plan.reborrows[&source];
            if detail.carrier_mode == trust_vc_vcir::Mode::Proof {
                assert_eq!(detail.pointee_mode, Some(trust_vc_vcir::Mode::Exec));
                assert_eq!(detail.result_mode, trust_vc_vcir::Mode::Proof);
                counts.proof_reborrows += 1;
            }
        }
    }
    for source in plan.assigns {
        let id = sites[&source].source;
        let meta = body[id].clone();
        let ExprKind::Assign { lhs, .. } = meta.kind else {
            tcx.dcx().fatal("unsupported mutation needs a shadow reset");
        };
        // Clone only AFTER child transformations. The cloned assignment keeps
        // its original RHS and normal evaluation order, without a self cycle.
        let original = body.exprs.push(meta.clone());
        let shadow = expressions::mirror(tcx, owner, body, lhs, map);
        counts.projected_resets += usize::from(projections::fields(body, lhs, shadow) > 0);
        counts.aggregate_resets +=
            usize::from(matches!(body[lhs].ty.kind(), ty::Tuple(_) | ty::Adt(..)));
        let shadow_type = body[shadow].ty;
        let erased = expressions::erased(tcx, body, &meta, helpers.erased, shadow_type);
        let reset = expressions::push(
            body,
            &meta,
            tcx.types.unit,
            ExprKind::Assign {
                lhs: shadow,
                rhs: erased,
            },
        );
        let pair = expressions::tuple(tcx, body, &meta, vec![original, reset]);
        let argument = body[pair].ty;
        assert_eq!(meta.ty, tcx.types.unit);
        body.exprs[id].kind = expressions::call_kind(
            tcx,
            body,
            &meta,
            helpers.erased,
            [argument, tcx.types.unit],
            vec![pair],
            false,
        );
        counts.resets += 1;
    }
    assert_eq!(
        (body[root].ty, body[root].span, body[root].temp_scope_id),
        metadata
    );
    counts
}
