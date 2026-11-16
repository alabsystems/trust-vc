// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ordinary AY queries distinguish entry contracts from the live call state.

use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::{CheckKind, FnVcs};

fn source(
    caller_contract: UnwindSpec,
    callee_contract: UnwindSpec,
    mutate: bool,
    negate_argument: bool,
    assert_parameter: bool,
) -> VcCrate {
    let mut caller = function(1);
    caller.unwind = Some(caller_contract);
    let mut callee = function(2);
    callee.unwind = Some(callee_contract);
    let mut statements = Vec::new();
    if mutate {
        statements.push(statement(StmtKind::Assign {
            place: Place::local(LocalId(1)),
            value: not(parameter()),
        }));
    }
    statements.push(statement(StmtKind::Call {
        callee: callee.id,
        type_args: vec![],
        args: vec![if negate_argument {
            not(parameter())
        } else {
            parameter()
        }],
        dest: None,
        site: SiteId(3),
    }));
    let assertion = if assert_parameter {
        parameter()
    } else {
        Expr::binary(BinOp::Eq, parameter(), parameter(), Ty::Bool, span())
    };
    statements.push(statement(StmtKind::Assert {
        expr: assertion,
        site: SiteId(4),
        attrs: ClauseAttrs::default(),
    }));
    statements.push(statement(StmtKind::Return {
        value: None,
        site: SiteId(9),
    }));
    caller.body = Body::Stmts(Block::new(statements));
    let mut source = VcCrate::new("unwind contract implications");
    source.fns = vec![caller, callee];
    source
}

fn require(source: &VcCrate, unwind: Option<bool>, assertion: bool) {
    let errors = check_crate(source);
    assert!(errors.is_empty(), "{errors:?}");
    let generated = vcgen::generate(source);
    for function in &source.fns {
        assert!(
            matches!(generated.get(function.id), Some(FnVcs::Checks(_))),
            "{generated:?}"
        );
    }
    let Some(FnVcs::Checks(checks)) = generated.get(id(1)) else {
        unreachable!()
    };
    assert_eq!(
        checks.len(),
        1 + usize::from(unwind.is_some()),
        "{checks:?}"
    );
    let mut seen_unwind = 0;
    let mut seen_assertion = 0;
    for check in checks {
        assert!(!check.approximate && !check.order_unknown);
        let expected = match &check.kind {
            CheckKind::Unwind { call, callee } => {
                assert_eq!((check.site, *call, *callee), (SiteId(3), span(), id(2)));
                seen_unwind += 1;
                unwind.expect("this callee requires an unwind implication")
            }
            CheckKind::Assert { .. } => {
                assert_eq!(check.site, SiteId(4));
                seen_assertion += 1;
                assertion
            }
            other => panic!("an unexpected contract check: {other:?}"),
        };
        let answer = check_detailed(
            &check.query,
            "actual unwind contract implication",
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
    assert_eq!(seen_unwind, usize::from(unwind.is_some()));
    assert_eq!(seen_assertion, 1);
}

#[test]
fn an_unconditional_no_unwind_caller_rejects_a_may_unwind_callee() {
    require(
        &source(
            UnwindSpec::NoUnwind,
            UnwindSpec::MayUnwind,
            false,
            false,
            false,
        ),
        Some(false),
        true,
    );
}

#[test]
fn an_unconditional_no_unwind_callee_needs_no_call_obligation() {
    require(
        &source(
            UnwindSpec::NoUnwind,
            UnwindSpec::NoUnwind,
            false,
            false,
            false,
        ),
        None,
        true,
    );
}

#[test]
fn a_conditional_caller_proves_the_matching_callee_condition() {
    require(
        &source(
            UnwindSpec::NoUnwindWhen(parameter()),
            UnwindSpec::NoUnwindWhen(parameter()),
            false,
            false,
            false,
        ),
        Some(true),
        true,
    );
}

#[test]
fn a_conditional_caller_rejects_the_opposite_callee_condition() {
    require(
        &source(
            UnwindSpec::NoUnwindWhen(parameter()),
            UnwindSpec::NoUnwindWhen(not(parameter())),
            false,
            false,
            false,
        ),
        Some(false),
        true,
    );
}

#[test]
fn a_mutated_parameter_does_not_replace_the_caller_entry_condition() {
    require(
        &source(
            UnwindSpec::NoUnwindWhen(parameter()),
            UnwindSpec::NoUnwindWhen(parameter()),
            true,
            true,
            false,
        ),
        Some(true),
        true,
    );
}

#[test]
fn the_live_call_argument_cannot_supply_an_entry_condition() {
    require(
        &source(
            UnwindSpec::NoUnwindWhen(parameter()),
            UnwindSpec::NoUnwindWhen(parameter()),
            true,
            false,
            false,
        ),
        Some(false),
        true,
    );
}

#[test]
fn a_caller_unwind_condition_is_not_assumed_on_the_normal_path() {
    require(
        &source(
            UnwindSpec::NoUnwindWhen(parameter()),
            UnwindSpec::NoUnwindWhen(parameter()),
            false,
            false,
            true,
        ),
        Some(true),
        false,
    );
}
