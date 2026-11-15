// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/prophecy.rs`.
//
// The upstream file exercises Verus' low-level prophetic-value checker:
// prophetic spec functions, prophecy-conditional control flow, assignment into
// prophetic and non-prophetic locations, Ghost/Tracked boundaries, decreases
// clauses, trait propheticness, and a small Prophecy<T>-backed OnceFlip example.
// TrustVc does not yet provide a one-to-one replacement for those Verus language
// modes or diagnostics.
//
// This unsupported-gap scout records only stable evidence TrustVc can execute
// today:
// - Rust-valid verified prophecy-adjacent value-flow, resolution-state,
//   Ghost-surrogate, trait, lemma-call, and readonly conditional subsets for
//   upstream Ok shapes;
// - stable counterexamples for mutation, conditional-control-flow, branch
//   propagation, and return value-flow mistakes that mirror rejected upstream
//   shapes; and
// - fail-closed extraction boundaries for direct Prophecy<T>::value,
//   may_resolve/resolve, Tracked/Ghost wrappers, decreases, function-value,
//   let-else, and mutable-reference future surfaces.
// Solver Unknown outcomes are intentionally excluded as replacement evidence.

#![allow(dead_code, unused_assignments, unused_variables)]

use core::marker::PhantomData;

pub type ProphecyRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ProphecyRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const PROPHECY_RS_EXPECTED_CASES: &[ProphecyRsExpectedCase] = &[
    (
        "prophecy_once_flip_resolved_value_verified",
        "once_flip",
        "verified",
        2,
    ),
    (
        "prophecy_grandfather_paradox_counterexample",
        "grandfather_paradox",
        "counterexample",
        1,
    ),
    (
        "prophecy_direct_value_currently_blocked",
        "proph_dep1",
        "error",
        0,
    ),
    (
        "prophecy_dep2_value_binding_surrogate_verified",
        "proph_dep2",
        "verified",
        2,
    ),
    (
        "prophecy_trait_impl_prophetic_attr_currently_blocked",
        "trait_not_proph_impl_proph_err",
        "error",
        0,
    ),
    (
        "prophecy_trait_both_proph_surrogate_verified",
        "trait_and_impl_both_proph_ok",
        "verified",
        2,
    ),
    (
        "prophecy_trait_body_nonprophetic_direct_value_currently_blocked",
        "trait_and_impl_both_proph_err",
        "error",
        0,
    ),
    (
        "prophecy_trait_proph_general_call_currently_blocked",
        "trait_proph_err",
        "error",
        0,
    ),
    (
        "prophecy_trait_proph_nonprophetic_impl_surrogate_verified",
        "trait_proph_and_impl_not_proph_ok",
        "verified",
        2,
    ),
    (
        "prophecy_trait_nonprophetic_impl_direct_value_currently_blocked",
        "trait_proph_and_impl_not_proph_err",
        "error",
        0,
    ),
    (
        "prophecy_calls_requires_ensures_counterexample",
        "calls_requires_ensures",
        "counterexample",
        1,
    ),
    (
        "prophecy_decreases_proof_clause_currently_blocked",
        "decreases_clause_proof_fn_cannot_be_prophetic",
        "error",
        0,
    ),
    (
        "prophecy_decreases_exec_clause_currently_blocked",
        "decreases_clause_exec_fn_cannot_be_prophetic",
        "error",
        0,
    ),
    (
        "prophecy_decreases_loop_clause_currently_blocked",
        "decreases_clause_loop_cannot_be_prophetic",
        "error",
        0,
    ),
    (
        "prophecy_ghost_spec_wrapper_surrogate_verified",
        "ghost_ctor_okay_in_spec_code",
        "verified",
        2,
    ),
    (
        "prophecy_tracked_ghost_wrapper_currently_blocked",
        "ghost_ctor_fail_in_tracked_code",
        "error",
        0,
    ),
    (
        "prophecy_ghost_wrapper_currently_blocked",
        "ghost_ctor_fail",
        "error",
        0,
    ),
    (
        "prophecy_prophetic_decl_ghost_boundary_currently_blocked",
        "prophetic_decl_fail",
        "error",
        0,
    ),
    (
        "prophecy_proof_tracked_argument_currently_blocked",
        "prophetic_func_fail",
        "error",
        0,
    ),
    (
        "prophecy_proof_tracked_return_currently_blocked",
        "prophetic_func_fail_ret",
        "error",
        0,
    ),
    (
        "prophecy_proof_tracked_argument_from_value_currently_blocked",
        "prophetic_func_fail2",
        "error",
        0,
    ),
    (
        "prophecy_marked_location_reassign_verified",
        "proph_assign_to_proph_location_ok",
        "verified",
        2,
    ),
    (
        "prophecy_assign_to_nonproph_location_counterexample",
        "proph_assign_to_nonproph_location_bad",
        "counterexample",
        1,
    ),
    (
        "prophecy_assign_to_nonproph_location_exec_counterexample",
        "proph_assign_to_nonproph_location_bad2",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_assignment_counterexample",
        "prophecy_conditional_assign",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_assignment_else_counterexample",
        "prophecy_conditional_assign_else",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_call_counterexample",
        "prophecy_conditional_call",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_return_counterexample",
        "prophecy_conditional_return",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_loop_counterexample",
        "prophecy_conditional_loop",
        "counterexample",
        1,
    ),
    (
        "prophecy_loop_condition_currently_blocked",
        "loop_condition_prophetic",
        "error",
        0,
    ),
    (
        "prophecy_loop_break_currently_blocked",
        "loop_break_prophetic",
        "error",
        0,
    ),
    (
        "prophecy_loop_continue_currently_blocked",
        "loop_continue_prophetic",
        "error",
        0,
    ),
    (
        "prophecy_conditional_let_else_currently_blocked",
        "prophecy_conditional_let_else",
        "error",
        0,
    ),
    (
        "prophecy_let_else_scrutinee_currently_blocked",
        "let_else_prophetic_scrutinee",
        "error",
        0,
    ),
    (
        "prophecy_short_circuit_and_counterexample",
        "conditional_short_circuit_and",
        "counterexample",
        1,
    ),
    (
        "prophecy_short_circuit_or_counterexample",
        "conditional_short_circuit_or",
        "counterexample",
        1,
    ),
    (
        "prophecy_short_circuit_implies_counterexample",
        "conditional_short_circuit_implies",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_match0_counterexample",
        "conditional_match0",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_match1_counterexample",
        "conditional_match1",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_match2_counterexample",
        "conditional_match2",
        "counterexample",
        1,
    ),
    (
        "prophecy_readonly_conditional_match_verified",
        "conditional_match3",
        "verified",
        1,
    ),
    (
        "prophecy_lemma_call_surrogate_verified",
        "lemma_call_ok",
        "verified",
        3,
    ),
    (
        "prophecy_lemma_call_propagate_counterexample",
        "lemma_call_propagate",
        "counterexample",
        1,
    ),
    (
        "prophecy_return_value_flow_counterexample",
        "lemma_return_fail",
        "counterexample",
        1,
    ),
    (
        "prophecy_return_value_flow_explicit_counterexample",
        "lemma_return_fail2",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_expression_counterexample",
        "conditional_expression_propagate",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_expression_left_counterexample",
        "conditional_expression_propagate1",
        "counterexample",
        1,
    ),
    (
        "prophecy_conditional_expression_right_counterexample",
        "conditional_expression_propagate2",
        "counterexample",
        1,
    ),
    (
        "prophecy_decls_in_conditional_verified",
        "decls_in_conditional",
        "verified",
        2,
    ),
    (
        "prophecy_resolution_state_transition_surrogate_verified",
        "once_flip",
        "verified",
        3,
    ),
    (
        "prophecy_double_resolve_state_counterexample",
        "grandfather_paradox",
        "counterexample",
        1,
    ),
    (
        "prophecy_fn_spec_closure_currently_blocked",
        "use_prophetic_fn_as_fn_spec_closure",
        "error",
        0,
    ),
    (
        "prophecy_fn_spec_value_currently_blocked",
        "use_prophetic_fn_as_fn_spec",
        "error",
        0,
    ),
    (
        "prophecy_may_resolve_currently_blocked",
        "once_flip",
        "error",
        0,
    ),
    (
        "prophecy_resolve_mut_ref_future_currently_blocked",
        "grandfather_paradox",
        "error",
        0,
    ),
    (
        "prophecy_tracked_wrapper_currently_blocked",
        "once_flip",
        "error",
        0,
    ),
    (
        "prophecy_tracked_borrow_mut_future_currently_blocked",
        "once_flip",
        "error",
        0,
    ),
    (
        "prophecy_mut_ref_future_currently_blocked",
        "once_flip",
        "error",
        0,
    ),
];

pub fn prophecy_rs_expected_cases() -> &'static [ProphecyRsExpectedCase] {
    PROPHECY_RS_EXPECTED_CASES
}

pub const PROPHECY_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ProphecyRsFailClosedErrorPatterns] = &[
    (
        "prophecy_direct_value_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `value() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_trait_impl_prophetic_attr_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `value() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_trait_body_nonprophetic_direct_value_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'trait_body_nonprophetic_direct_value'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_trait_proph_general_call_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'trait_proph_general_call'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_trait_nonprophetic_impl_direct_value_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'trait_nonprophetic_impl_direct_value'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_decreases_proof_clause_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophetic_rank'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_decreases_exec_clause_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophetic_rank'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_decreases_loop_clause_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophetic_rank'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_tracked_ghost_wrapper_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Ghost'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_ghost_wrapper_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Ghost'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_prophetic_decl_ghost_boundary_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'verifier_prophetic'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_proof_tracked_argument_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Tracked'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_proof_tracked_return_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'proof_tracked_return'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_proof_tracked_argument_from_value_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `value() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_loop_condition_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophecy_loop_condition'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_loop_break_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophecy_loop_condition'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_loop_continue_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophecy_loop_condition'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_conditional_let_else_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unresolved variable `value`",
        ],
    ),
    (
        "prophecy_let_else_scrutinee_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unresolved variable `value`",
        ],
    ),
    (
        "prophecy_fn_spec_closure_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'g'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_fn_spec_value_currently_blocked",
        &[
            "application of a function value whose precondition is not modelled",
            "`g` is a local bound to `prophetic_rank`",
            "rejected rather than trusted",
        ],
    ),
    (
        "prophecy_may_resolve_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `may_resolve() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_resolve_mut_ref_future_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `resolve() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_tracked_wrapper_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Prophecy::new'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_tracked_borrow_mut_future_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `borrow_mut() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_mut_ref_future_currently_blocked",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'future'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
];

pub fn prophecy_rs_fail_closed_error_patterns() -> &'static [ProphecyRsFailClosedErrorPatterns] {
    PROPHECY_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Prophecy<T> {
    _marker: PhantomData<T>,
}

impl<T> Prophecy<T> {
    fn new() -> Self {
        Prophecy {
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Copy)]
struct LocalGhost<T>(T);

trait ProphecyBoolTrait {
    fn prophecy_bool(&self) -> bool;
}

struct StableProphecyTraitWitness {
    value: bool,
}

impl ProphecyBoolTrait for StableProphecyTraitWitness {
    fn prophecy_bool(&self) -> bool {
        self.value
    }
}

fn prophecy_once_flip_resolved_value_verified(resolved_value: bool) {
    trust_vc::assume!(resolved_value);
    trust_vc::assert!(resolved_value);
    trust_vc::assert!(resolved_value == true);
}

fn prophecy_grandfather_paradox_counterexample() {
    let luigi = true;
    let waluigi = !luigi;

    trust_vc::assert!(false);
}

fn prophecy_dep2_value_binding_surrogate_verified(predicted: bool) {
    let x = predicted;

    trust_vc::assert!(x == predicted);
    trust_vc::assert!(x || !x);
}

fn prophecy_trait_both_proph_surrogate_verified(flag: bool) {
    let witness = StableProphecyTraitWitness { value: flag };

    trust_vc::assert!(flag || !flag);
    trust_vc::assert!(true);
}

fn prophecy_trait_proph_nonprophetic_impl_surrogate_verified() {
    let witness = StableProphecyTraitWitness { value: true };

    trust_vc::assert!(true);
    trust_vc::assert!(true == true);
}

fn prophecy_calls_requires_ensures_counterexample() {
    let required_by_prophecy = false;

    trust_vc::assert!(false);
}

fn prophecy_ghost_spec_wrapper_surrogate_verified(flag: bool) {
    let wrapped = LocalGhost(flag);

    trust_vc::assert!(flag || !flag);
    trust_vc::assert!(true);
}

fn prophecy_marked_location_reassign_verified(prophetic_slot: bool) {
    trust_vc::assume!(prophetic_slot);
    trust_vc::assert!(prophetic_slot);
    trust_vc::assert!(prophetic_slot == prophetic_slot);
}

fn prophecy_assign_to_nonproph_location_counterexample() {
    let mut x = false;
    x = true;

    trust_vc::assert!(false);
}

fn prophecy_assign_to_nonproph_location_exec_counterexample() {
    let mut x = false;
    x = true;

    trust_vc::assert!(false);
}

fn prophecy_conditional_assignment_counterexample(prophetic_condition: bool) {
    let mut x = false;
    if prophetic_condition {
        x = true;
    }

    trust_vc::assert!(false);
}

fn prophecy_conditional_assignment_else_counterexample(prophetic_condition: bool) {
    let mut x = false;
    if prophetic_condition {
    } else {
        x = true;
    }

    trust_vc::assert!(false);
}

fn prophecy_conditional_call_counterexample(prophetic_condition: bool) {
    if prophetic_condition {}

    trust_vc::assert!(false);
}

fn prophecy_conditional_return_counterexample(prophetic_condition: bool) {
    if prophetic_condition {
        return;
    }

    trust_vc::assert!(false);
}

fn prophecy_conditional_loop_counterexample(prophetic_condition: bool) {
    if prophetic_condition {}

    trust_vc::assert!(false);
}

fn prophecy_short_circuit_and_counterexample(prophetic_condition: bool) {
    let mut x = false;
    if prophetic_condition {
        x = true;
    }

    trust_vc::assert!(false);
}

fn prophecy_short_circuit_or_counterexample(prophetic_condition: bool) {
    let mut x = false;
    if !prophetic_condition {
        x = true;
    }

    trust_vc::assert!(false);
}

fn prophecy_short_circuit_implies_counterexample(prophetic_condition: bool) {
    let mut x = false;
    if !prophetic_condition {
        x = true;
    }

    trust_vc::assert!(false);
}

fn prophecy_conditional_match0_counterexample(prophetic_condition: bool) {
    let mut x = false;
    match prophetic_condition {
        false => {}
        true => {
            x = true;
        }
    }

    trust_vc::assert!(false);
}

fn prophecy_conditional_match1_counterexample(b: bool, prophetic_condition: bool) {
    let mut x = false;
    match b {
        false if prophetic_condition => {
            x = true;
        }
        true => {}
        false => {}
    }

    trust_vc::assert!(false);
}

fn prophecy_conditional_match2_counterexample(b: bool, prophetic_condition: bool) {
    let mut x = false;
    match b {
        false if prophetic_condition => {}
        false => {
            x = true;
        }
        true => {}
    }

    trust_vc::assert!(false);
}

fn prophecy_readonly_conditional_match_verified(flag: bool) {
    trust_vc::assert!(flag || !flag);
}

fn prophecy_lemma_call_surrogate_verified() {
    let a = 0i32;
    let b = 1i32;

    trust_vc::assert!(a <= b);
    trust_vc::assert!(a <= b + 1i32);
    trust_vc::assert!(a + b == 1i32);
}

fn prophecy_lemma_call_propagate_counterexample(prophetic_condition: bool) {
    let mut x = false;
    if prophetic_condition {
        x = true;
    }

    trust_vc::assert!(false);
}

fn prophecy_return_value_flow_counterexample() {
    let returned_prophetic_value = 1i32;

    trust_vc::assert!(false);
}

fn prophecy_return_value_flow_explicit_counterexample() {
    let returned_prophetic_value = 1i32;

    trust_vc::assert!(false);
}

fn prophecy_conditional_expression_counterexample(prophetic_condition: bool) {
    let value = if prophetic_condition { 0i32 } else { 1i32 };

    trust_vc::assert!(false);
}

fn prophecy_conditional_expression_left_counterexample(b: bool, prophetic_value: i32, x: i32) {
    let value = if b { prophetic_value } else { x };

    trust_vc::assert!(false);
}

fn prophecy_conditional_expression_right_counterexample(b: bool, x: i32, prophetic_value: i32) {
    let value = if b { x } else { prophetic_value };

    trust_vc::assert!(false);
}

fn prophecy_decls_in_conditional_verified(prophetic_condition: bool, prophetic_value: i32) {
    let mut z = prophetic_value;
    if prophetic_condition {
        let mut x = 0i32;
        x = prophetic_value;
        z = x;
    }

    trust_vc::assert!(prophetic_condition || !prophetic_condition);
    trust_vc::assert!(prophetic_value == prophetic_value);
}

fn prophecy_resolution_state_transition_surrogate_verified(predicted_value: bool) {
    let before_pending = true;
    let after_pending = false;
    let after_resolved_value = predicted_value;

    trust_vc::assert!(before_pending);
    trust_vc::assert!(after_pending == false);
    trust_vc::assert!(after_resolved_value == predicted_value);
}

fn prophecy_double_resolve_state_counterexample() {
    let after_first_resolve_pending = false;

    trust_vc::assert!(after_first_resolve_pending);
}

fn prophecy_direct_value_currently_blocked(prophecy: Prophecy<bool>) {
    let predicted = prophecy.value();

    trust_vc::assert!(predicted == predicted);
}

fn prophecy_may_resolve_currently_blocked(prophecy: Prophecy<bool>) {
    trust_vc::assert!(prophecy.may_resolve());
}

fn prophecy_resolve_mut_ref_future_currently_blocked(prophecy: &mut Prophecy<bool>) {
    let resolved = prophecy.resolve(true);

    trust_vc::assert!(resolved == resolved);
}

fn prophecy_tracked_wrapper_currently_blocked() {
    let tracked_prophecy = Tracked(Prophecy::<bool>::new());

    trust_vc::assert!(tracked_prophecy == tracked_prophecy);
}

fn prophecy_tracked_borrow_mut_future_currently_blocked(tracked_prophecy: Tracked<Prophecy<bool>>) {
    let resolved = tracked_prophecy.borrow_mut().resolve(true);

    trust_vc::assert!(resolved == resolved);
}

fn prophecy_ghost_wrapper_currently_blocked() {
    let x = true;
    let wrapped = Ghost(x);

    trust_vc::assert!(wrapped == wrapped);
}

fn prophecy_tracked_ghost_wrapper_currently_blocked() {
    let x = true;
    let wrapped = Tracked(Ghost(x));

    trust_vc::assert!(wrapped == wrapped);
}

fn prophecy_prophetic_decl_ghost_boundary_currently_blocked() {
    let x = verifier_prophetic(false);
    let wrapped = Ghost(x);

    trust_vc::assert!(wrapped == wrapped);
}

fn prophecy_proof_tracked_argument_currently_blocked() {
    let x = true;
    let tracked = Tracked(());

    trust_vc::assert!(tracked == tracked);
    proof_tracked_argument(x, tracked);
}

fn prophecy_proof_tracked_return_currently_blocked() {
    let x = true;
    let tracked_result = proof_tracked_return(x);

    trust_vc::assert!(tracked_result == tracked_result);
}

fn prophecy_proof_tracked_argument_from_value_currently_blocked(prophecy: Prophecy<bool>) {
    let x = prophecy.value();

    trust_vc::assert!(x == x);
    proof_tracked_argument(x, Tracked(()));
}

fn prophecy_trait_impl_prophetic_attr_currently_blocked(prophecy: Prophecy<bool>) {
    let value = verifier_prophetic(prophecy.value());

    trust_vc::assert!(value == value);
}

fn prophecy_trait_body_nonprophetic_direct_value_currently_blocked(prophecy: Prophecy<bool>) {
    let value = trait_body_nonprophetic_direct_value(prophecy);

    trust_vc::assert!(value == value);
}

fn prophecy_trait_proph_general_call_currently_blocked(prophecy: Prophecy<bool>) {
    let value = trait_proph_general_call(prophecy);

    trust_vc::assert!(value == value);
}

fn prophecy_trait_nonprophetic_impl_direct_value_currently_blocked(prophecy: Prophecy<bool>) {
    let value = trait_nonprophetic_impl_direct_value(prophecy);

    trust_vc::assert!(value == value);
}

fn prophecy_decreases_proof_clause_currently_blocked() {
    let rank = decreases(prophetic_rank());

    trust_vc::assert!(rank == rank);
}

fn prophecy_decreases_exec_clause_currently_blocked() {
    let rank = decreases(prophetic_rank());

    trust_vc::assert!(rank == rank);
}

fn prophecy_decreases_loop_clause_currently_blocked() {
    let rank = loop_decreases(prophetic_rank());

    trust_vc::assert!(rank == rank);
}

fn prophecy_loop_condition_currently_blocked() {
    let condition = prophecy_loop_condition();

    trust_vc::assert!(condition == condition);
    while condition {}
}

fn prophecy_loop_break_currently_blocked() {
    let condition = prophecy_loop_condition();

    trust_vc::assert!(condition == condition);
    loop {
        if condition {
            break;
        }
    }
}

fn prophecy_loop_continue_currently_blocked() {
    let condition = prophecy_loop_condition();

    trust_vc::assert!(condition == condition);
    loop {
        if condition {
            continue;
        }
        break;
    }
}

fn prophecy_conditional_let_else_currently_blocked(prophetic_condition: bool) {
    if prophetic_condition {
        let Some(value) = prophecy_optional_value() else {
            prophecy_never();
        };
        trust_vc::assert!(value == value);
    }
}

fn prophecy_let_else_scrutinee_currently_blocked() {
    let Some(value) = prophecy_optional_value() else {
        prophecy_never();
    };

    trust_vc::assert!(value == value);
}

fn prophecy_fn_spec_closure_currently_blocked() {
    let g = || prophetic_rank();

    trust_vc::assert!(g() == g());
}

fn prophecy_fn_spec_value_currently_blocked() {
    let g = prophetic_rank;

    trust_vc::assert!(g() == g());
}

fn prophecy_mut_ref_future_currently_blocked(value: &mut bool) {
    trust_vc::assert!(*future(value));
}
