// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Required occurrences are queried by original allocation, never by span.

use super::*;

fn expression<'tcx>(tcx: TyCtxt<'tcx>, id: hir::HirId) -> &'tcx hir::Expr<'tcx> {
    let hir::Node::Expr(expression) = tcx.hir_node(id) else {
        panic!("an availability record must name an original expression");
    };
    expression
}

pub(super) fn check(tcx: TyCtxt<'_>, facts: &AvailabilityFacts<'_>) {
    assert!(facts.new_mut_ref());
    let live = usage(tcx, facts, "record.live", AccessKind::Read);
    let original = expression(tcx, live.place);
    assert_eq!(facts.use_for(original, AccessKind::Read).unwrap(), live);
    assert!(facts.use_for(original, AccessKind::Assign).is_err());
    assert!(facts.operation_for(original).is_err());
    assert!(facts.adjustment_for(original).is_err());

    let arguments = facts
        .arguments()
        .iter()
        .filter(|row| text(tcx, row.call) == "Sink(value, value)")
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 2);
    let call = expression(tcx, arguments[0].call);
    assert_eq!(facts.argument_for(call, 0).unwrap(), arguments[0]);
    assert_eq!(facts.argument_for(call, 1).unwrap(), arguments[1]);
    assert!(facts.argument_for(call, 2).is_err());
    let original = expression(tcx, arguments[0].argument);
    assert!(facts.use_for(original, AccessKind::Read).is_ok());
    let hir::ExprKind::Path(hir::QPath::Resolved(qself, path)) = original.kind else {
        panic!("this source argument is its actual native local path");
    };
    let copied = hir::Expr {
        hir_id: original.hir_id,
        kind: hir::ExprKind::Path(hir::QPath::Resolved(qself, path)),
        span: original.span,
    };
    assert_eq!(copied.hir_id, original.hir_id);
    assert!(!std::ptr::eq(&copied, original));
    assert!(
        facts.use_for(&copied, AccessKind::Read).is_err(),
        "copying an ID and expression cannot replace the original native allocation"
    );

    let operation = facts
        .operations()
        .iter()
        .find(|row| {
            row.kind == AccessKind::MutBorrow && text(tcx, row.expression) == "&mut record.live"
        })
        .unwrap();
    assert_eq!(
        facts
            .operation_for(expression(tcx, operation.expression))
            .unwrap(),
        operation
    );
    let adjustment = facts
        .adjustments()
        .iter()
        .find(|row| {
            text(tcx, row.expression) == "reference"
                && row.kinds == vec![AdjustmentKind::BuiltinDeref, AdjustmentKind::SharedBorrow]
        })
        .unwrap();
    assert_eq!(
        facts
            .adjustment_for(expression(tcx, adjustment.expression))
            .unwrap(),
        adjustment
    );
}
