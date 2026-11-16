//! Prophecy-flow regression cases. Root wrappers preserve the test roster.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) fn annotated_constant_calls_taint_bodies_and_both_generation_entries_refuse() {
    let mut caller = function(2, Mode::Spec, Ty::Bool);
    caller.body = Body::Spec(call(1, Ty::Bool, vec![]));
    let mut good = function(3, Mode::Spec, Ty::Bool);
    good.body = Body::Spec(boolean(true));
    let mut krate = source(vec![caller, good]);
    let before = krate.clone();
    rejected(&krate, 2, "body of non-prophetic spec function");
    assert!(check_crate_for_diagnostics(&krate)
        .errors
        .iter()
        .all(|e| e.function == Some(id(2))));
    let generated = vcgen::generate(&krate);
    assert!(krate
        .fns
        .iter()
        .all(|f| matches!(generated.get(f.id), Some(FnVcs::Refused(_)))));
    assert!(vcgen::Recommendations::new(&krate).is_err());
    assert_eq!(
        krate, before,
        "effect checking must not rewrite source classifications"
    );
    krate.fns[1].attrs.prophetic = true;
    accepted(&krate);
    assert_eq!(vcgen::generate(&krate).get(id(2)), Some(&FnVcs::Spec));
}

pub(super) fn pure_spec_parameters_start_nonprophetic_and_calls_join_actual_arguments() {
    let mut identity = function(2, Mode::Spec, Ty::Bool);
    let param = add(
        &mut identity,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    identity.body = Body::Spec(read(param, Ty::Bool));
    let mut caller = function(3, Mode::Spec, Ty::Bool);
    caller.body = Body::Spec(call(2, Ty::Bool, vec![boolean(false)]));
    let mut krate = source(vec![identity, caller]);
    accepted(&krate);
    krate.fns[2].body = Body::Spec(call(2, Ty::Bool, vec![call(1, Ty::Bool, vec![])]));
    rejected(&krate, 3, "body of non-prophetic spec function");
    krate.fns[2].attrs.prophetic = true;
    accepted(&krate);
}

pub(super) fn expression_let_discards_unused_initializer_but_propagates_bound_reads() {
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
        ExprKind::Let {
            local: bound,
            value: Box::new(call(1, Ty::Bool, vec![])),
            body: Box::new(boolean(false)),
        },
    ));
    let mut krate = source(vec![caller]);
    accepted(&krate);
    let Body::Spec(Expr {
        kind: ExprKind::Let { body, .. },
        ..
    }) = &mut krate.fns[1].body
    else {
        panic!()
    };
    **body = read(bound, Ty::Bool);
    rejected(&krate, 2, "body of non-prophetic spec function");
}

pub(super) fn constant_if_arms_still_depend_on_the_prophetic_condition() {
    let mut caller = function(2, Mode::Spec, Ty::Bool);
    caller.body = Body::Spec(Expr::new(
        Ty::Bool,
        span(),
        ExprKind::If {
            cond: Box::new(call(1, Ty::Bool, vec![])),
            then_expr: Box::new(boolean(false)),
            else_expr: Box::new(boolean(false)),
        },
    ));
    rejected(
        &source(vec![caller]),
        2,
        "body of non-prophetic spec function",
    );
}

pub(super) fn inference_is_fixed_at_declaration_and_explicit_prophetic_constants_stay_prophetic() {
    let mut proof = function(2, Mode::Proof, Ty::Unit);
    let target = add(
        &mut proof,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::Default,
    );
    proof.body = Body::Stmts(Block::new(vec![
        let_stmt(target, Some(boolean(false))),
        assign(target, call(1, Ty::Bool, vec![])),
    ]));
    let mut krate = source(vec![proof]);
    rejected(&krate, 2, "assignment to non-prophetic location");
    krate.fns[1].locals[target.index()].prophecy = DeclProphecy::Prophetic;
    accepted(&krate);
    krate.fns[1].body = Body::Stmts(Block::new(vec![
        let_stmt(target, Some(boolean(false))),
        stmt(StmtKind::Return {
            value: Some(read(target, Ty::Bool)),
            site: SiteId(1),
        }),
    ]));
    krate.fns[1].locals[0].ty = Ty::Bool;
    rejected(&krate, 2, "return value");
}

pub(super) fn default_no_initializer_is_fixed_but_delayed_inference_uses_first_assignment() {
    let mut proof = function(2, Mode::Proof, Ty::Unit);
    let target = add(
        &mut proof,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::Default,
    );
    proof.body = Body::Stmts(Block::new(vec![
        let_stmt(target, None),
        assign(target, call(1, Ty::Bool, vec![])),
    ]));
    let mut krate = source(vec![proof]);
    rejected(&krate, 2, "assignment to non-prophetic location");
    krate.fns[1].locals[target.index()].prophecy = DeclProphecy::DelayedInfer;
    accepted(&krate);
    krate.fns[1].body = Body::Stmts(Block::new(vec![
        let_stmt(target, None),
        assign(target, boolean(false)),
        assign(target, call(1, Ty::Bool, vec![])),
    ]));
    rejected(&krate, 2, "assignment to non-prophetic location");
}

pub(super) fn delayed_inference_does_not_join_outer_control_on_first_assignment() {
    let mut proof = function(2, Mode::Proof, Ty::Unit);
    let target = add(
        &mut proof,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::DelayedInfer,
    );
    proof.body = Body::Stmts(Block::new(vec![
        let_stmt(target, None),
        branch(
            call(1, Ty::Bool, vec![]),
            vec![assign(target, boolean(false))],
        ),
    ]));
    rejected(
        &source(vec![proof]),
        2,
        "assignment to non-prophetic location cannot occur in prophecy-conditional context",
    );
}

pub(super) fn inferred_initializers_and_conditional_declarations_are_prophetic() {
    let mut proof = function(2, Mode::Proof, Ty::Unit);
    let target = add(
        &mut proof,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::Default,
    );
    proof.body = Body::Stmts(Block::new(vec![
        let_stmt(target, Some(call(1, Ty::Bool, vec![]))),
        branch(
            call(1, Ty::Bool, vec![]),
            vec![assign(target, boolean(false))],
        ),
        assume(read(target, Ty::Bool)),
    ]));
    let mut krate = source(vec![proof]);
    accepted(&krate);
    krate.fns[1].body = Body::Stmts(Block::new(vec![branch(
        call(1, Ty::Bool, vec![]),
        vec![
            let_stmt(target, Some(boolean(false))),
            assign(target, call(1, Ty::Bool, vec![])),
        ],
    )]));
    accepted(&krate);
}
