//! Unit values are normalized at upstream mode-consuming boundaries, while
//! raw expressions can still contribute prophecy to a non-unit expression.
//!
//! In particular, `check_expr_has_mode` and `check_place_has_mode` clear Unit
//! effects in pinned `vir/src/modes.rs`; Binary Eq checks its operands raw.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::*;

#[path = "unit_prophecy_effects/support.rs"]
mod support;
use support::*;

#[test]
fn unit_spec_body_normalizes_a_prophetic_call_result() {
    let mut caller = function(10, Mode::Spec, Ty::Unit);
    caller.body = Body::Spec(call(2, Ty::Unit, vec![]));
    accepted(&source(vec![caller]));
}

#[test]
fn boolean_equality_keeps_the_raw_effect_of_a_prophetic_unit_spec_call() {
    let mut caller = function(10, Mode::Spec, Ty::Bool);
    caller.body = Body::Spec(equal(call(2, Ty::Unit, vec![]), unit()));
    rejected(
        &source(vec![caller]),
        10,
        "body of non-prophetic spec function",
    );
}

#[test]
fn explicit_unit_return_normalizes_its_value_effect() {
    let mut caller = function(10, Mode::Proof, Ty::Unit);
    caller.body = Body::Stmts(Block::new(vec![stmt(StmtKind::Return {
        value: Some(call(2, Ty::Unit, vec![])),
        site: SiteId(1),
    })]));
    accepted(&source(vec![caller]));
}

#[test]
fn ordinary_unit_arguments_do_not_taint_the_boolean_call_result() {
    let mut equality = function(10, Mode::Spec, Ty::Bool);
    let argument = add(
        &mut equality,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    equality.body = Body::Spec(equal(read(argument, Ty::Unit), unit()));
    let mut caller = function(11, Mode::Spec, Ty::Bool);
    caller.body = Body::Spec(call(10, Ty::Bool, vec![call(2, Ty::Unit, vec![])]));
    accepted(&source(vec![equality, caller]));
}

#[test]
fn tracked_function_argument_checks_normalize_unit_values() {
    let mut consumer = function(10, Mode::Proof, Ty::Unit);
    add(
        &mut consumer,
        Ty::Unit,
        Mode::Proof,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    let mut caller = function(11, Mode::Proof, Ty::Unit);
    caller.body = Body::Stmts(Block::new(vec![invoke(
        10,
        vec![call(2, Ty::Unit, vec![])],
        None,
    )]));
    accepted(&source(vec![consumer, caller]));
}

#[test]
fn authored_unit_binding_inference_normalizes_initializers_but_respects_explicit_markers() {
    let mut caller = function(10, Mode::Spec, Ty::Bool);
    let binding = add(
        &mut caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Bound,
        DeclProphecy::Default,
    );
    caller.body = Body::Spec(Expr::new(
        Ty::Bool,
        at(),
        ExprKind::Let {
            local: binding,
            value: Box::new(call(2, Ty::Unit, vec![])),
            body: Box::new(equal(read(binding, Ty::Unit), unit())),
        },
    ));
    accepted(&source(vec![caller.clone()]));
    caller.locals[binding.index()].prophecy = DeclProphecy::Prophetic;
    rejected(
        &source(vec![caller]),
        10,
        "body of non-prophetic spec function",
    );
}

#[test]
fn authored_unit_assignment_and_delayed_inference_normalize_the_rhs() {
    for prophecy in [DeclProphecy::Default, DeclProphecy::DelayedInfer] {
        let mut caller = function(10, Mode::Proof, Ty::Unit);
        let binding = add(&mut caller, Ty::Unit, Mode::Spec, LocalKind::Let, prophecy);
        caller.body = Body::Stmts(Block::new(vec![
            declare(binding, None),
            assign(binding, call(2, Ty::Unit, vec![])),
        ]));
        accepted(&source(vec![caller]));
    }
}

#[test]
fn projected_unit_assignment_normalizes_the_projected_rhs_type() {
    let mut caller = function(10, Mode::Proof, Ty::Unit);
    let pair_ty = Ty::Tuple(vec![Ty::Unit, Ty::Bool]);
    let pair = add(
        &mut caller,
        pair_ty.clone(),
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::Default,
    );
    caller.body = Body::Stmts(Block::new(vec![
        declare(
            pair,
            Some(Expr::new(
                pair_ty,
                at(),
                ExprKind::Tuple(vec![unit(), boolean(false)]),
            )),
        ),
        stmt(StmtKind::Assign {
            place: Place {
                local: pair,
                projections: vec![Projection::TupleField(0)],
            },
            value: call(2, Ty::Unit, vec![]),
        }),
    ]));
    accepted(&source(vec![caller]));
}

#[test]
fn proof_call_result_tail_reaches_boolean_equality_before_unit_normalization() {
    let mut caller = with_proof_body(10, Ty::Bool);
    let result = add(
        &mut caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Temp,
        DeclProphecy::DelayedInfer,
    );
    let proof = proof_tail(
        vec![
            declare(result, None),
            invoke(3, vec![call(1, Ty::Bool, vec![])], Some(result)),
        ],
        read(result, Ty::Unit),
    );
    caller.body = Body::Spec(equal(proof, unit()));
    rejected(
        &source(vec![caller.clone()]),
        10,
        "body of non-prophetic spec function",
    );
    caller.attrs.prophetic = true;
    accepted(&source(vec![caller]));
}

#[test]
fn proof_statement_semicolon_discards_the_unit_call_result_effect() {
    let mut caller = with_proof_body(10, Ty::Bool);
    let proof = Expr::new(
        Ty::Unit,
        at(),
        ExprKind::ProofInSpec(Block::new(vec![invoke(
            3,
            vec![call(1, Ty::Bool, vec![])],
            None,
        )])),
    );
    caller.body = Body::Spec(equal(proof, unit()));
    accepted(&source(vec![caller]));
}

#[test]
fn pure_unit_if_is_normalized_as_a_body_but_taints_a_boolean_equality() {
    let choice = Expr::new(
        Ty::Unit,
        at(),
        ExprKind::If {
            cond: Box::new(call(1, Ty::Bool, vec![])),
            then_expr: Box::new(unit()),
            else_expr: Box::new(unit()),
        },
    );
    let mut caller = function(10, Mode::Spec, Ty::Unit);
    caller.body = Body::Spec(choice.clone());
    accepted(&source(vec![caller]));
    let mut caller = function(11, Mode::Spec, Ty::Bool);
    caller.body = Body::Spec(equal(choice, unit()));
    rejected(
        &source(vec![caller]),
        11,
        "body of non-prophetic spec function",
    );
}

#[test]
fn generated_unit_branch_results_keep_raw_control_effects() {
    let mut caller = with_proof_body(10, Ty::Bool);
    let result = add(
        &mut caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Temp,
        DeclProphecy::DelayedInfer,
    );
    let proof = proof_tail(
        vec![
            declare(result, None),
            conditional(
                call(1, Ty::Bool, vec![]),
                vec![assign(result, unit())],
                vec![assign(result, unit())],
            ),
        ],
        read(result, Ty::Unit),
    );
    caller.body = Body::Spec(equal(proof.clone(), unit()));
    rejected(
        &source(vec![caller]),
        10,
        "body of non-prophetic spec function",
    );
    let mut unit_caller = with_proof_body(11, Ty::Unit);
    let result = add(
        &mut unit_caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Temp,
        DeclProphecy::DelayedInfer,
    );
    unit_caller.body = Body::Spec(proof_tail(
        vec![
            declare(result, None),
            conditional(
                call(1, Ty::Bool, vec![]),
                vec![assign(result, unit())],
                vec![assign(result, unit())],
            ),
        ],
        read(result, Ty::Unit),
    ));
    accepted(&source(vec![unit_caller]));
}

#[test]
fn compiler_operand_save_temporaries_preserve_raw_unit_effects() {
    let mut caller = with_proof_body(10, Ty::Bool);
    let saved = add(
        &mut caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Temp,
        DeclProphecy::Default,
    );
    caller.body = Body::Spec(equal(
        proof_tail(
            vec![declare(saved, Some(call(2, Ty::Unit, vec![])))],
            read(saved, Ty::Unit),
        ),
        unit(),
    ));
    rejected(
        &source(vec![caller]),
        10,
        "body of non-prophetic spec function",
    );
}

#[test]
fn unit_result_normalization_does_not_skip_inner_tracked_effect_checks() {
    let mut caller = with_proof_body(10, Ty::Unit);
    caller.body = Body::Spec(proof_tail(
        vec![conditional(
            call(1, Ty::Bool, vec![]),
            vec![invoke(4, vec![boolean(false)], None)],
            vec![],
        )],
        unit(),
    ));
    rejected(
        &source(vec![caller]),
        10,
        "call to proof-mode function with tracked parameters cannot occur",
    );
}

#[test]
fn unit_assignment_still_rejects_prophecy_conditional_control() {
    let mut caller = function(10, Mode::Proof, Ty::Unit);
    let binding = add(
        &mut caller,
        Ty::Unit,
        Mode::Spec,
        LocalKind::Let,
        DeclProphecy::Default,
    );
    caller.body = Body::Stmts(Block::new(vec![
        declare(binding, Some(unit())),
        conditional(
            call(1, Ty::Bool, vec![]),
            vec![assign(binding, unit())],
            vec![],
        ),
    ]));
    rejected(
        &source(vec![caller]),
        10,
        "assignment to non-prophetic location cannot occur",
    );
}
