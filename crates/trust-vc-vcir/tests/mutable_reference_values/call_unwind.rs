// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real solver controls for the normal and unwinding successors of a call.
use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::CheckKind;

#[derive(Clone, Copy, Debug)]
enum Scenario {
    NoCall,
    BeforeAssertion,
    AfterAssertion,
    Destination,
}

fn source(scenario: Scenario) -> VcCrate {
    let inner_ty = reference(Ty::uint(64));
    let mut caller = function(Ty::Unit);
    let x = add(
        &mut caller,
        reference(inner_ty.clone()),
        Mode::Exec,
        LocalKind::Param,
    );
    let y = add(&mut caller, inner_ty.clone(), Mode::Exec, LocalKind::Param);

    // Even a simple body retains the default MayUnwind call contract.
    // The destination case uses the ordinary identity fn(y: &mut T) -> &mut T.
    let callee_id = FnId(DefHash::new(133, 2));
    let mut callee = function(if matches!(scenario, Scenario::Destination) {
        inner_ty.clone()
    } else {
        Ty::Unit
    });
    callee.id = callee_id;
    callee.name = "call_might_unwind".into();
    let mut arguments = Vec::new();
    let returned = if matches!(scenario, Scenario::Destination) {
        let parameter = add(&mut callee, inner_ty.clone(), Mode::Exec, LocalKind::Param);
        arguments.push(read(y, inner_ty.clone()));
        Some(read(parameter, inner_ty.clone()))
    } else {
        None
    };
    callee.body = Body::Stmts(Block::new(vec![ret(returned)]));
    let destination = if matches!(scenario, Scenario::Destination) {
        Some(Place::deref(x))
    } else {
        None
    };
    let invocation = stmt(StmtKind::Call {
        callee: callee_id,
        type_args: vec![],
        args: arguments,
        dest: destination,
        site: SiteId(1),
    });

    let nested = Expr::read(Place::deref(x), inner_ty.clone(), span());
    let resolved = Expr::new(Ty::Bool, span(), ExprKind::HasResolved(Box::new(nested)));
    let assertion = assertion(resolved, 0);
    let mut statements = match scenario {
        Scenario::NoCall => vec![assertion],
        Scenario::BeforeAssertion => vec![invocation, assertion],
        Scenario::AfterAssertion | Scenario::Destination => vec![assertion, invocation],
    };
    if !matches!(scenario, Scenario::Destination) {
        statements.push(stmt(StmtKind::Assign {
            place: Place::deref(x),
            value: read(y, inner_ty),
        }));
    }
    statements.push(ret(None));
    caller.body = Body::Stmts(Block::new(statements));

    let mut source = krate(caller);
    source.fns.push(callee);
    source
}

fn require_verdict(scenario: Scenario, proved: bool) {
    let source = source(scenario);
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{scenario:?}: {errors:?}");
    let generated = vcgen::generate(&source);
    for function in &source.fns {
        assert!(
            matches!(generated.get(function.id), Some(FnVcs::Checks(_))),
            "{scenario:?}: every fixture function must generate supported checks: {generated:?}"
        );
    }
    let Some(FnVcs::Checks(checks)) = generated.get(id()) else {
        panic!("{scenario:?}: {generated:?}")
    };
    assert_eq!(checks.len(), 1, "{scenario:?}");
    let check = &checks[0];
    assert_eq!(check.site, SiteId(0));
    assert!(matches!(check.kind, CheckKind::Assert { .. }));
    assert!(!check.approximate && !check.order_unknown);
    let result = check_detailed(
        &check.query,
        "owned reference call unwind control",
        &Limits::default(),
    );
    let correct = if proved {
        matches!(result.verdict, Verdict::Proved { .. })
    } else {
        matches!(result.verdict, Verdict::Refuted { .. })
    };
    assert!(
        correct,
        "{scenario:?}: expected {}, got {result:?}; generated goal: {:?}",
        if proved { "Proved" } else { "Refuted" },
        check.query.goal,
    );
}

#[test]
fn may_unwind_blocks_early_nested_reference_resolution() {
    require_verdict(Scenario::AfterAssertion, false);
}

#[test]
fn an_unconditional_later_overwrite_resolves_the_old_nested_reference() {
    require_verdict(Scenario::NoCall, true);
}

#[test]
fn resolution_after_a_may_unwind_call_uses_only_the_normal_continuation() {
    require_verdict(Scenario::BeforeAssertion, true);
}

#[test]
fn an_unwinding_call_does_not_overwrite_its_destination() {
    require_verdict(Scenario::Destination, false);
}

#[test]
fn an_explicit_no_unwind_call_preserves_normal_overwrite_resolution() {
    for scenario in [Scenario::AfterAssertion, Scenario::Destination] {
        let mut source = source(scenario);
        source.fns[1].unwind = Some(UnwindSpec::NoUnwind);
        let errors = check_crate(&source);
        assert!(errors.is_empty(), "{scenario:?}: {errors:?}");
        let generated = vcgen::generate(&source);
        for function in &source.fns {
            assert!(
                matches!(generated.get(function.id), Some(FnVcs::Checks(_))),
                "{scenario:?}: {generated:?}"
            );
        }
        let Some(FnVcs::Checks(checks)) = generated.get(id()) else {
            unreachable!()
        };
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].site, SiteId(0));
        assert!(matches!(checks[0].kind, CheckKind::Assert { .. }));
        assert!(!checks[0].approximate && !checks[0].order_unknown);
        let answer = check_detailed(
            &checks[0].query,
            "explicit no-unwind owned reference resolution",
            &Limits::default(),
        );
        assert!(
            matches!(answer.verdict, Verdict::Proved { .. }),
            "{scenario:?}: {answer:?}"
        );
    }
}
