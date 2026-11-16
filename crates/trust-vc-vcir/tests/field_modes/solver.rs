// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{self, CheckKind, FnVcs, QueryGroup};

fn check(expected: i128, proved: bool) {
    let mut caller = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let destination = add(&mut caller, scalar(), Mode::Proof, LocalKind::Let);
    caller.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Ghost(Block::new(vec![
            statement(StmtKind::Let {
                local: destination,
                init: None,
            }),
            statement(StmtKind::Call {
                callee: id(2),
                type_args: vec![],
                args: vec![],
                dest: Some(Place::local(destination)),
                site: SiteId(1),
            }),
            statement(StmtKind::Assert {
                expr: equality(read(destination, scalar()), integer(expected)),
                site: SiteId(0),
                attrs: ClauseAttrs::default(),
            }),
        ]))),
        returned(None),
    ]));
    let mut krate = source(caller);
    krate.fns.push(proof_seven());
    clean(&krate);
    let result = vcgen::generate(&krate);
    for function in &krate.fns {
        assert!(
            matches!(result.get(function.id), Some(FnVcs::Checks(_))),
            "{result:?}"
        );
        assert_eq!(function.role, FnRole::Item);
        assert!(!function.attrs.external_body && function.attrs.instance.is_none());
    }
    let Some(FnVcs::Checks(callee)) = result.get(id(2)) else {
        panic!("{result:?}");
    };
    assert_eq!(callee.len(), 1);
    assert_eq!(
        callee[0].kind,
        CheckKind::Postcondition {
            exit: span(),
            clause: 0
        }
    );
    assert!(matches!(
        check_detailed(
            &callee[0].query,
            "actual proof producer",
            &Limits::default()
        )
        .verdict,
        Verdict::Proved { .. }
    ));
    let Some(FnVcs::Checks(caller)) = result.get(id(1)) else {
        panic!("{result:?}");
    };
    assert_eq!(caller.len(), 1);
    let obligation = &caller[0];
    assert_eq!(obligation.site, SiteId(0));
    assert_eq!(obligation.group, QueryGroup::Body);
    assert_eq!(
        obligation.kind,
        CheckKind::Assert {
            span: span(),
            attrs: ClauseAttrs::default()
        }
    );
    assert!(!obligation.approximate && !obligation.order_unknown);
    assert!(!matches!(obligation.query.goal, Term::Bool(_)));
    let answer = check_detailed(
        &obligation.query,
        "tracked call destination",
        &Limits::default(),
    );
    assert!(
        if proved {
            matches!(answer.verdict, Verdict::Proved { .. })
        } else {
            matches!(answer.verdict, Verdict::Refuted { .. })
        },
        "{answer:?}"
    );
}

#[test]
fn a_real_proof_call_initializes_owned_proof_storage() {
    check(7, true);
}

#[test]
fn proof_call_destination_does_not_prove_a_false_value() {
    check(8, false);
}

fn proof_borrow_value(expected: i128, proved: bool) {
    let krate = borrowed_from_proof(false, expected);
    clean(&krate);
    let result = vcgen::generate(&krate);
    let Some(FnVcs::Checks(checks)) = result.get(id(1)) else {
        panic!("{result:?}");
    };
    assert_eq!(checks.len(), 1);
    assert_eq!(checks[0].site, SiteId(0));
    assert_eq!(checks[0].group, QueryGroup::Body);
    assert_eq!(
        checks[0].kind,
        CheckKind::Assert {
            span: span(),
            attrs: ClauseAttrs::default()
        }
    );
    assert!(!checks[0].approximate && !checks[0].order_unknown);
    assert!(!matches!(checks[0].query.goal, Term::Bool(_)));
    let answer = check_detailed(
        &checks[0].query,
        "Proof carrier current value",
        &Limits::default(),
    );
    assert!(
        if proved {
            matches!(answer.verdict, Verdict::Proved { .. })
        } else {
            matches!(answer.verdict, Verdict::Refuted { .. })
        },
        "{answer:?}"
    );
}

#[test]
fn proof_borrow_reads_the_real_current_exec_value() {
    proof_borrow_value(7, true);
}

#[test]
fn proof_borrow_does_not_prove_a_false_current_value() {
    proof_borrow_value(8, false);
}
