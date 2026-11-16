// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Isolated loop queries reconstruct the function's distinct entry values.

use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::{CheckKind, FnVcs, InvariantAt, QueryGroup};

fn invariant() -> Expr {
    let entry = Expr::new(Ty::Bool, span(), ExprKind::Old(Place::local(LocalId(1))));
    Expr::binary(BinOp::Eq, parameter(), not(entry), Ty::Bool, span())
}

fn source(negate_callee_condition: bool) -> VcCrate {
    let mut caller = function(1);
    caller.unwind = Some(UnwindSpec::NoUnwindWhen(parameter()));
    let mut callee = function(2);
    callee.unwind = Some(UnwindSpec::NoUnwindWhen(if negate_callee_condition {
        not(parameter())
    } else {
        parameter()
    }));
    let lp = Loop {
        id: LoopId(0),
        isolation: true,
        allow_complex_invariants: false,
        cond: None,
        invariants: vec![LoopInvariant {
            kind: InvariantKind::Always,
            expr: invariant(),
            span: span(),
        }],
        decreases: vec![],
        body: Block::new(vec![
            statement(StmtKind::Call {
                callee: callee.id,
                type_args: vec![],
                args: vec![parameter()],
                dest: None,
                site: SiteId(3),
            }),
            statement(StmtKind::Assert {
                expr: invariant(),
                site: SiteId(4),
                attrs: ClauseAttrs::default(),
            }),
            statement(StmtKind::Break {
                target: LoopId(0),
                site: SiteId(13),
            }),
        ]),
        sites: LoopSites {
            entry: SiteId(10),
            end: SiteId(11),
            exit: SiteId(12),
        },
    };
    caller.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Assign {
            place: Place::local(LocalId(1)),
            value: not(parameter()),
        }),
        statement(StmtKind::Loop(Box::new(lp))),
        statement(StmtKind::Return {
            value: None,
            site: SiteId(9),
        }),
    ]));
    let mut source = VcCrate::new("isolated-loop unwind entry snapshot");
    source.fns = vec![caller, callee];
    source
}

fn require(negate_callee_condition: bool, unwind_proved: bool) {
    let source = source(negate_callee_condition);
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    let generated = vcgen::generate(&source);
    for function in &source.fns {
        assert!(
            matches!(generated.get(function.id), Some(FnVcs::Checks(_))),
            "{generated:?}"
        );
    }
    let Some(FnVcs::Checks(checks)) = generated.get(id(1)) else {
        unreachable!()
    };
    assert_eq!(checks.len(), 4, "{checks:?}");
    let loop_group = QueryGroup::Loop {
        index: 0,
        span: span(),
    };
    let mut unwind = 0;
    let mut entry = 0;
    let mut exit = 0;
    let mut assertions = 0;
    for check in checks {
        assert!(!check.approximate && !check.order_unknown);
        let expected = match &check.kind {
            CheckKind::Unwind { call, callee } => {
                assert_eq!((check.site, *call, *callee), (SiteId(3), span(), id(2)));
                assert_eq!(check.group, loop_group);
                unwind += 1;
                unwind_proved
            }
            CheckKind::Assert { .. } => {
                assert_eq!((check.site, check.group), (SiteId(4), loop_group));
                assertions += 1;
                true
            }
            CheckKind::LoopInvariant {
                at: InvariantAt::Entry,
                kind,
                invariant,
            } => {
                assert_eq!(*kind, InvariantKind::Always);
                assert_eq!(*invariant, span());
                assert_eq!((check.site, check.group), (SiteId(10), QueryGroup::Body));
                entry += 1;
                true
            }
            CheckKind::LoopInvariant {
                at: InvariantAt::Break(at),
                kind,
                invariant,
            } => {
                assert_eq!(
                    (*at, *kind, *invariant),
                    (span(), InvariantKind::Always, span())
                );
                assert_eq!((check.site, check.group), (SiteId(13), loop_group));
                exit += 1;
                true
            }
            other => panic!("unexpected isolated-loop check: {other:?}"),
        };
        let answer = check_detailed(
            &check.query,
            "isolated loop unwind entry-state implication",
            &Limits::default(),
        );
        assert!(
            if expected {
                matches!(answer.verdict, Verdict::Proved { .. })
            } else {
                matches!(answer.verdict, Verdict::Refuted { .. })
            },
            "expected proved={expected}: {answer:?}; check={check:?}"
        );
    }
    assert_eq!((unwind, entry, exit, assertions), (1, 1, 1, 1));
}

#[test]
fn isolated_loop_unwind_uses_the_entry_value_reconstructed_from_its_invariant() {
    require(true, true);
}

#[test]
fn isolated_loop_unwind_does_not_replace_entry_with_the_mutated_parameter() {
    require(false, false);
}
