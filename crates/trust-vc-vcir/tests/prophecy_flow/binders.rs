//! Prophecy-flow regression cases. Root wrappers preserve the test roster.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) fn quantifier_triggers_do_not_taint_values_but_quantifier_bodies_do() {
    let mut trigger = function(2, Mode::Spec, Ty::Bool);
    trigger.attrs.prophetic = true;
    let param = add(
        &mut trigger,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    trigger.body = Body::Spec(read(param, Ty::Bool));
    let mut caller = function(3, Mode::Spec, Ty::Bool);
    let bound = add(
        &mut caller,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Bound,
        DeclProphecy::Default,
    );
    caller.body = Body::Spec(Expr::new(
        Ty::Bool,
        span(),
        ExprKind::Quant {
            kind: QuantKind::Forall,
            vars: vec![(bound, Ty::Bool)],
            triggers: vec![vec![call(2, Ty::Bool, vec![read(bound, Ty::Bool)])]],
            body: Box::new(boolean(true)),
        },
    ));
    let mut krate = source(vec![trigger, caller]);
    accepted(&krate);
    let Body::Spec(Expr {
        kind: ExprKind::Quant { body, .. },
        ..
    }) = &mut krate.fns[2].body
    else {
        panic!()
    };
    **body = call(1, Ty::Bool, vec![]);
    rejected(&krate, 3, "body of non-prophetic spec function");
}

pub(super) fn choose_joins_condition_and_result_with_nonprophetic_bound_variables() {
    let mut predicate = function(2, Mode::Spec, Ty::Bool);
    let param = add(
        &mut predicate,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    predicate.body = Body::Spec(read(param, Ty::Bool));
    let mut caller = function(3, Mode::Spec, Ty::Bool);
    let bound = add(
        &mut caller,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Bound,
        DeclProphecy::Default,
    );
    caller.body = Body::Spec(Expr::new(
        Ty::Bool,
        span(),
        ExprKind::Choose {
            vars: vec![(bound, Ty::Bool)],
            triggers: vec![vec![call(2, Ty::Bool, vec![read(bound, Ty::Bool)])]],
            cond: Box::new(boolean(true)),
            result: Box::new(read(bound, Ty::Bool)),
        },
    ));
    let mut krate = source(vec![predicate, caller]);
    accepted(&krate);
    let Body::Spec(Expr {
        kind: ExprKind::Choose { cond, .. },
        ..
    }) = &mut krate.fns[2].body
    else {
        panic!()
    };
    **cond = call(1, Ty::Bool, vec![]);
    rejected(&krate, 3, "body of non-prophetic spec function");
}

pub(super) fn diagnostic_binders_keep_prophecy_errors_and_other_function_diagnostics() {
    let mut caller = function(2, Mode::Spec, Ty::Bool);
    let bound = add(
        &mut caller,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Bound,
        DeclProphecy::Default,
    );
    caller.body = Body::Spec(Expr::new(
        Ty::Bool,
        span(),
        ExprKind::UntriggeredQuant {
            kind: QuantKind::Forall,
            vars: vec![(bound, Ty::Bool)],
            trigger_candidates: vec![read(bound, Ty::Bool)],
            body: Box::new(call(1, Ty::Bool, vec![])),
        },
    ));
    let mut other = function(3, Mode::Spec, Ty::Bool);
    other.body = Body::Spec(boolean(true));
    other.requires.push(Clause {
        expr: boolean(true),
        span: span(),
        attrs: ClauseAttrs {
            proof_notes: vec!["first".into(), "second".into()],
            custom_errs: vec![],
        },
    });
    let diagnostics = check_crate_for_diagnostics(&source(vec![caller, other]));
    assert_eq!(diagnostics.incomplete_binders, [(id(2), span())]);
    assert!(diagnostics
        .errors
        .iter()
        .any(|e| e.function == Some(id(2)) && e.message.contains("non-prophetic spec function")));
    assert!(diagnostics
        .errors
        .iter()
        .any(|e| e.function == Some(id(3)) && e.message == wf::MSG_DUPLICATE_NOTE));
}

pub(super) fn short_circuit_control_reaches_embedded_proof_blocks() {
    let mut lemma = function(2, Mode::Proof, Ty::Unit);
    add(
        &mut lemma,
        Ty::Bool,
        Mode::Proof,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    let mut caller = function(3, Mode::Spec, Ty::Bool);
    caller.attrs.prophetic = true;
    caller.decreases.push(integer(0));
    let temp = add(
        &mut caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Bound,
        DeclProphecy::Default,
    );
    let rhs = Expr::new(
        Ty::Bool,
        span(),
        ExprKind::Let {
            local: temp,
            value: Box::new(Expr::new(
                Ty::Unit,
                span(),
                ExprKind::ProofInSpec(Block::new(vec![invoke(2, vec![boolean(true)], None, 1)])),
            )),
            body: Box::new(boolean(true)),
        },
    );
    for op in [BinOp::And, BinOp::Or, BinOp::Implies] {
        caller.body = Body::Spec(Expr::binary(
            op,
            boolean(false),
            rhs.clone(),
            Ty::Bool,
            span(),
        ));
        accepted(&source(vec![lemma.clone(), caller.clone()]));
        caller.body = Body::Spec(Expr::binary(
            op,
            call(1, Ty::Bool, vec![]),
            rhs.clone(),
            Ty::Bool,
            span(),
        ));
        rejected(&source(vec![lemma.clone(), caller.clone()]), 3,
            "call to proof-mode function with tracked parameters cannot occur in prophecy-conditional context");
    }
}
