// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Capability + soundness suite for H6: an APPLICATION of a closure or other
// quality-audit: allow-file allow-rust-size — one liar/twin matrix per application shape
//! function VALUE must PROVE the callee's precondition at the call site, or fail
//! closed at EXTRACTION time. A lowering-time failure never counts, because an
//! unused result (`let _t = f(..)`, a unit statement, a discarded tail, a
//! reflexive `t == t`) is never lowered.
//!
//! MEASURED BEFORE THE FIX (cache-off, file lane): every liar
//! below returned `Verified` — the let-bound n-ary / nullary `closure!` lane
//! (the call-site seam was unary-only), the directly applied `closure!` literal
//! lane (unary included), the `F: Fn(..)` parameter lane (the requires was
//! folded into an ASSUMED implication and never proven), and every value callee
//! the seams did not recognize (FnMut / FnOnce / `impl Fn` / generic `Fn(T)`
//! params, aliases, block initializers, tuple fields, `if`-selected callees,
//! returned closures, function-item aliases of a contracted helper). In a
//! non-test build `closure!` expands `requires` to a runtime `assert!`, so each
//! of those programs panics.
//!
//! THE RULE (`body_extract.rs::record_closure_application_obligations`):
//! * a registered `closure!` binding at ANY arity proves `requires` and assumes
//!   the def-side-checked `ensures` through the helper-contract emitter; an arity
//!   mismatch is an extraction error;
//! * an Fn-bound `SpecFn` parameter proves `f.requires((args,))` (Verus/vstd
//!   semantics) and assumes `f.ensures((args,), result)` under it;
//! * every other value callee (anything but a function item by name, a bare
//!   exec closure local, or a ghost spec-fn parameter) fails closed with a
//!   "function value" diagnostic; a function-item alias keeps its treatment
//!   only when it resolves to a sibling function WITHOUT a `requires`;
//! * R5 — a closure model never outlives its binding: a destructuring or valued
//!   `let` hides an outer registered contract / bare body of the same name, a
//!   local whose value binding was havocked is not mistaken for a function
//!   item, and a `mut` binding ascribed a fn-pointer type (which can later hold
//!   other code) is never modelled;
//! * R6 — a call through a `const` / `static` item applies a function value and
//!   fails closed;
//! * R7 — a `mut` `F: Fn(..)` parameter (which can be reassigned or swapped) is
//!   not modelled, so its application fails closed.
//!
//! Verdict classes: CXreq = a Counterexample on the call's
//! `__call_requires_pp*_<callee>_*` obligation; CXassert = a Counterexample on an
//! `assertion_*` obligation; FC = an extraction `Err` / `VerifyResult::Error`
//! whose message names the "function value".
//!
//! CACHE DISCIPLINE: every verdict is recomputed cache-off
//! (`TRUST_VC_DISABLE_VC_CACHE=1`) so a stale `Verified` can never mask a
//! false-verify.

use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn repro_path() -> String {
    format!(
        "{}/tests/data/closure_application_requires_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&repro_path(), func)
    })
}

fn verdict(func: &str) -> VerifyResult {
    verify(func).unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should VERIFY; got {v:?}"
    );
}

/// The repeated-callable refusal: the call-site requires held, and the
/// `Verified` answer for a function that evaluates a callable parameter twice
/// is refused (a stateful `Fn` closure returns two values).
fn assert_repeat_refused(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(&v, VerifyResult::Error { message } if message.starts_with("bodiless call repeated")),
        "`{func}` should be REFUSED as a repeated callable parameter; got {v:?}"
    );
}

/// A `while let` over `it.next()` is refused before its binding is read: the
/// condition may change `it` and the loop frame is built from the body only.
const WHILE_CONDITION_REFUSAL: &str = "the condition of this `while` loop may change";

/// Refused, either for the shadowed binding (`needle`) or, for a `while let`
/// whose condition changes its scrutinee, by the loop-condition refusal that
/// fires first.
fn assert_while_let_refused(func: &str, needle: &str) {
    let message = match verify(func) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => panic!("`{func}` must be refused; got {other:?}"),
    };
    assert!(
        message.contains(WHILE_CONDITION_REFUSAL)
            || (message.contains("unresolved variable") && message.contains(needle)),
        "`{func}` was refused for an unexpected reason: {message}"
    );
}

fn assert_not_verified(func: &str) {
    if let Ok(VerifyResult::Verified) = verify(func) {
        panic!("CLOSURE-APPLICATION FALSE-VERIFY: `{func}` must not verify")
    }
}

/// A Counterexample on the call-site prove-requires obligation of `callee`.
fn assert_cx_requires(func: &str, callee: &str) {
    let v = verdict(func);
    match &v {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.starts_with("__call_requires_pp")
            && obligation_name.contains(&format!("_{callee}_")) => {}
        _ => panic!(
            "`{func}` should COUNTEREXAMPLE on the `__call_requires_pp*_{callee}_*` \
             prove-requires obligation; got {v:?}"
        ),
    }
}

/// A Counterexample on a body assertion (not on a call-site requires).
fn assert_cx_assertion(func: &str) {
    let v = verdict(func);
    match &v {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.starts_with("assertion_") => {}
        _ => panic!("`{func}` should COUNTEREXAMPLE on an `assertion_*` obligation; got {v:?}"),
    }
}

/// An extraction-time fail-closed refusal naming the function value.
fn assert_fail_closed(func: &str) {
    let message = match verify(func) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => panic!(
            "`{func}` should FAIL CLOSED at extraction with a \"function value\" \
             diagnostic; got {other:?}"
        ),
    };
    assert!(
        message.contains("function value"),
        "`{func}` failed closed, but not with the \"function value\" application \
         diagnostic: {message}"
    );
}

/// A Counterexample on an arithmetic-safety obligation reporting a division by
/// zero (the invoked bare-closure body's own obligation, which current main
/// also instruments at the closure's DEFINITION site).
fn assert_cx_div_zero(func: &str) {
    let v = verdict(func);
    match &v {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.contains("division by zero") => {}
        _ => panic!(
            "`{func}` should COUNTEREXAMPLE on a division-by-zero arithmetic \
             obligation; got {v:?}"
        ),
    }
}

/// Extraction-only obligation count (cache-independent).
fn obligation_count(func: &str) -> usize {
    let source = std::fs::read_to_string(repro_path()).expect("repro fixture should be readable");
    let file = syn::parse_file(&source).expect("repro fixture should parse");
    let item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == func => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| panic!("`{func}` should exist in the repro fixture"));
    extract_verification_conditions_with_file_context(&file, item)
        .unwrap_or_else(|e| panic!("`{func}` should extract: {e:?}"))
        .obligations()
        .len()
}

// ---------------------------------------------------------------------------
// Unary controls (correct before the fix; must stay).
// ---------------------------------------------------------------------------

#[test]
fn l0a_unary_bad_requires_cx() {
    assert_cx_requires("l0a_unary_bad_requires_cx", "f");
}

#[test]
fn l0b_unary_good_requires_verified() {
    assert_verified("l0b_unary_good_requires_verified");
}

// ---------------------------------------------------------------------------
// R1 liars — let-bound n-ary / nullary closure!. BEFORE: all Verified.
// ---------------------------------------------------------------------------

#[test]
fn l1a_nary_bad_requires_unused_cx() {
    // BEFORE: Verified with 1 obligation (the `ensures(true)` alone). The
    // prove-requires must be EMITTED, not vacuously skipped.
    assert!(
        obligation_count("l1a_nary_bad_requires_unused") >= 2,
        "the n-ary application must emit its prove-requires obligation"
    );
    assert_cx_requires("l1a_nary_bad_requires_unused", "f");
}

#[test]
fn l1b_nary_param_div_cx() {
    assert_cx_requires("l1b_nary_param_div", "f");
}

#[test]
fn l1c_nary_unit_stmt_cx() {
    assert_cx_requires("l1c_nary_unit_stmt", "f");
}

#[test]
fn l1d_nary3_bad_requires_cx() {
    assert_cx_requires("l1d_nary3_bad_requires", "f");
}

#[test]
fn l1e_nullary_requires_false_cx() {
    assert_cx_requires("l1e_nullary_requires_false", "f");
}

#[test]
fn l1f_nary_tail_bad_requires_cx() {
    assert_cx_requires("l1f_nary_tail_bad_requires", "f");
}

#[test]
fn l1g_nary_in_assert_reflexive_cx() {
    assert_cx_requires("l1g_nary_in_assert_reflexive", "f");
}

#[test]
fn l1h_nary_in_loop_cx() {
    // The requires is never dropped inside a loop body (only the ensures-assume is).
    assert_cx_requires("l1h_nary_in_loop", "f");
}

#[test]
fn l1i_nary_branch_unguarded_cx() {
    assert_cx_requires("l1i_nary_branch_unguarded", "f");
}

#[test]
fn l1u_nary_method_chain_cx() {
    assert_cx_requires("l1u_nary_method_chain", "f");
}

#[test]
fn l1v_nary_match_scrutinee_cx() {
    assert_cx_requires("l1v_nary_match_scrutinee", "f");
}

#[test]
fn l1w_nary_div_zero_body_refused() {
    // The applied divisor is the CONSTANT 0, so the requires-guarded ensures
    // assumption `z == 3 / 0` is rejected by the encoder's constant-divisor check
    // before the solver runs — a fail-closed Error (measured). Either that refusal
    // or the prove-requires Counterexample is acceptable; Verified and Unknown
    // are not. `l1b_nary_param_div` pins the symbolic-divisor CXreq.
    match verdict("l1w_nary_div_zero_body") {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.starts_with("__call_requires_pp")
            && obligation_name.contains("_f_") => {}
        VerifyResult::Error { message } if message.contains("Division by zero") => {}
        other => panic!(
            "`l1w_nary_div_zero_body` should be refused (CXreq or the constant \
             division-by-zero encoding Error); got {other:?}"
        ),
    }
}

#[test]
fn l1x_nary_overflow_body_cx() {
    assert_cx_requires("l1x_nary_overflow_body", "f");
}

// ---------------------------------------------------------------------------
// R1 controls.
// ---------------------------------------------------------------------------

#[test]
fn l1y_nary_false_tail_after_bad_call_not_vacuous() {
    // Non-vacuity: the bad call does not make the rest of the body vacuous.
    assert_not_verified("l1y_nary_false_tail_after_bad_call");
    assert!(matches!(
        verdict("l1y_nary_false_tail_after_bad_call"),
        VerifyResult::Counterexample { .. }
    ));
}

#[test]
fn l1j_nary_branch_guarded_ok_verified() {
    assert_verified("l1j_nary_branch_guarded_ok");
}

#[test]
fn l1k_nary_ensures_used_ok_verified() {
    // BEFORE: CXassert (the n-ary ensures was not assumed). Flips because the
    // def-side-checked ensures is now assumed after the requires is proven.
    assert_verified("l1k_nary_ensures_used_ok");
}

#[test]
fn l1l_nary_ensures_used_liar_cx() {
    assert_cx_assertion("l1l_nary_ensures_used_liar");
}

#[test]
fn l1m_nary_lying_closure_not_verified() {
    // The def-side check poisons the parent regardless of the call-site assume.
    assert_not_verified("l1m_nary_lying_closure");
}

#[test]
fn l1n_nullary_ok_verified() {
    // BEFORE: CXassert.
    assert_verified("l1n_nullary_ok");
}

#[test]
fn l1o_nullary_liar_cx() {
    assert_cx_assertion("l1o_nullary_liar");
}

#[test]
fn l1z_nary_good_requires_verified() {
    // BEFORE: CXassert.
    assert_verified("l1z_nary_good_requires_verified");
}

// ---------------------------------------------------------------------------
// R1b — unregistered closure! bindings. BEFORE: all Verified.
// ---------------------------------------------------------------------------

#[test]
fn l1p_unregistered_no_ret_ty_fail_closed() {
    assert_fail_closed("l1p_unregistered_no_ret_ty");
}

#[test]
fn l1q_unregistered_shadows_registered_fail_closed() {
    assert_fail_closed("l1q_unregistered_shadows_registered");
}

#[test]
fn l1r_unregistered_shadows_bare_fail_closed() {
    assert_fail_closed("l1r_unregistered_shadows_bare");
}

#[test]
fn l1s_paren_pattern_binding_cx() {
    // `let (f) = closure!(..)` registers like `let f = closure!(..)`.
    assert_cx_requires("l1s_paren_pattern_binding", "f");
}

#[test]
fn l1t_typed_pattern_binding_cx() {
    assert_cx_requires("l1t_typed_pattern_binding_cx", "f");
}

// ---------------------------------------------------------------------------
// Lane 2 — directly applied closure! literals. BEFORE: Verified (l2a-l2d).
// ---------------------------------------------------------------------------

#[test]
fn l2a_literal_unary_bad_fail_closed() {
    assert_fail_closed("l2a_literal_unary_bad");
}

#[test]
fn l2b_literal_unary_param_div_fail_closed() {
    assert_fail_closed("l2b_literal_unary_param_div");
}

#[test]
fn l2c_literal_nary_bad_fail_closed() {
    assert_fail_closed("l2c_literal_nary_bad");
}

#[test]
fn l2d_paren_literal_fail_closed() {
    assert_fail_closed("l2d_paren_literal");
}

#[test]
fn l2e_literal_true_claim_fail_closed() {
    // Documented incompleteness (BEFORE: a lowering Error on the used value).
    assert_fail_closed("l2e_literal_true_claim");
}

#[test]
fn l2f_ctrl_bare_iife_div0_not_verified() {
    // BEFORE: Error "Division by zero" — the bare-closure body lane is unchanged.
    assert_not_verified("l2f_ctrl_bare_iife_div0");
}

// ---------------------------------------------------------------------------
// R3 — Fn-bound parameters. BEFORE: liars Verified.
// ---------------------------------------------------------------------------

#[test]
fn l3a_fnbound_unary_no_requires_cx() {
    assert_cx_requires("l3a_fnbound_unary_no_requires", "f");
}

#[test]
fn l3b_fnbound_nary_no_requires_cx() {
    assert_cx_requires("l3b_fnbound_nary_no_requires", "f");
}

#[test]
fn l3c_fnbound_nullary_no_requires_cx() {
    assert_cx_requires("l3c_fnbound_nullary_no_requires", "f");
}

#[test]
fn l3d_fnbound_requires_other_arg_cx() {
    assert_cx_requires("l3d_fnbound_requires_other_arg", "f");
}

#[test]
fn l3g_fnbound_determinism_no_requires_cx() {
    // Requires-free determinism is a whole-program false verify: re-keyed with a
    // requires clause in the fn-bound suites.
    assert_cx_requires("l3g_fnbound_determinism_no_requires", "f");
}

#[test]
fn l3e_fnbound_requires_same_arg_verified() {
    // BEFORE: Error "nothing to prove" (no obligation was emitted at all).
    assert_verified("l3e_fnbound_requires_same_arg_verified");
}

#[test]
fn l3f_fnbound_determinism_refused() {
    assert_repeat_refused("l3f_fnbound_determinism_refused");
}

#[test]
fn l3h_fnbound_nary_determinism_refused() {
    assert_repeat_refused("l3h_fnbound_nary_determinism_refused");
}

#[test]
fn l3i_fnbound_nullary_determinism_refused() {
    assert_repeat_refused("l3i_fnbound_nullary_determinism_refused");
}

#[test]
fn l3j_fnbound_distinct_args_cx() {
    assert_cx_assertion("l3j_fnbound_distinct_args_cx");
}

#[test]
fn l3k_apply1u_req_verified() {
    assert_verified("l3k_apply1u_req");
}

#[test]
fn l3l_caller_passes_div_closure_cx() {
    assert_cx_requires("l3l_caller_passes_div_closure", "l3k_apply1u_req");
}

#[test]
fn l3m_caller_passes_good_closure_verified() {
    assert_verified("l3m_caller_passes_good_closure");
}

#[test]
fn l3n_apply2u_no_requires_cx() {
    assert_cx_requires("l3n_apply2u_no_requires", "f");
}

// ---------------------------------------------------------------------------
// R4 — unmodelled value callees. BEFORE: all Verified except the fn-pointer /
// dyn params (solver Unknown on an unencodable variable type).
// ---------------------------------------------------------------------------

#[test]
fn l4a_fnmut_param_fail_closed() {
    assert_fail_closed("l4a_fnmut_param");
}

#[test]
fn l4b_fnonce_param_fail_closed() {
    assert_fail_closed("l4b_fnonce_param");
}

#[test]
fn l4c_impl_fn_param_cx() {
    // `impl Fn(u64) -> u64` desugars to an anonymous `Fn`-bound type parameter
    // (`impl_trait_desugar`), so it takes the R3 lane: the requires is PROVEN
    // (measured: CXreq on `__call_requires_pp0_f_0_0`), exactly like `l3a`.
    assert_cx_requires("l4c_impl_fn_param", "f");
}

#[test]
fn l4d_where_fnmut_param_fail_closed() {
    assert_fail_closed("l4d_where_fnmut_param");
}

#[test]
fn l4e_generic_fn_param_fail_closed() {
    assert_fail_closed("l4e_generic_fn_param");
}

#[test]
fn l4f_alias_registered_fail_closed() {
    assert_fail_closed("l4f_alias_registered");
}

#[test]
fn l4g_block_init_fail_closed() {
    assert_fail_closed("l4g_block_init");
}

#[test]
fn l4h_tuple_field_fail_closed() {
    assert_fail_closed("l4h_tuple_field");
}

#[test]
fn l4i_if_else_callee_fail_closed() {
    assert_fail_closed("l4i_if_else_callee");
}

#[test]
fn l4j_alias_bare_div0_fail_closed() {
    assert_fail_closed("l4j_alias_bare_div0");
}

#[test]
fn l4k_returned_closure_fail_closed() {
    assert_fail_closed("l4k_returned_closure");
}

#[test]
fn l4l_fn_item_alias_bad_requires_fail_closed() {
    assert_fail_closed("l4l_fn_item_alias_bad_requires");
}

#[test]
fn l4o_fn_pointer_param_not_verified() {
    assert_not_verified("l4o_fn_pointer_param");
}

#[test]
fn l4p_dyn_fn_param_not_verified() {
    assert_not_verified("l4p_dyn_fn_param");
}

#[test]
fn l4m_plain_fn_item_alias_verified() {
    // A requires-free function-item alias keeps verifying.
    assert_verified("l4m_plain_fn_item_alias_verified");
}

#[test]
fn l4q_direct_contracted_helper_bad_requires_cx() {
    assert_cx_requires("l4q_direct_contracted_helper_bad_requires_cx", "l4_llama");
}

#[test]
fn l4r_match_bound_callee_fail_closed() {
    assert_fail_closed("l4r_match_bound_callee");
}

#[test]
fn l4s_if_let_bound_callee_fail_closed() {
    assert_fail_closed("l4s_if_let_bound_callee");
}

#[test]
fn l4t_for_bound_callee_fail_closed() {
    assert_fail_closed("l4t_for_bound_callee");
}

#[test]
fn l4u_struct_field_callee_fail_closed() {
    assert_fail_closed("l4u_struct_field_callee");
}

#[test]
fn l4v_reference_callee_fail_closed() {
    assert_fail_closed("l4v_reference_callee");
}

#[test]
fn l4w_qualified_fn_item_alias_bad_requires_fail_closed() {
    assert_fail_closed("l4w_qualified_fn_item_alias_bad_requires");
}

#[test]
fn l4x_qualified_plain_fn_item_alias_verified() {
    assert_verified("l4x_qualified_plain_fn_item_alias_verified");
}

// ---------------------------------------------------------------------------
// R5 — stale closure models after the binding changes. MEASURED with R1-R4 and
// before R5: Verified, except `l5e` (already fail-closed).
// ---------------------------------------------------------------------------

#[test]
fn l5a_destructure_shadows_registered_fail_closed() {
    assert_fail_closed("l5a_destructure_shadows_registered");
}

#[test]
fn l5b_valued_let_shadows_registered_fail_closed() {
    assert_fail_closed("l5b_valued_let_shadows_registered");
}

#[test]
fn l5c_fn_item_let_shadows_registered_fail_closed() {
    assert_fail_closed("l5c_fn_item_let_shadows_registered");
}

#[test]
fn l5d_if_value_let_shadows_registered_fail_closed() {
    assert_fail_closed("l5d_if_value_let_shadows_registered");
}

#[test]
fn l5e_match_arm_shadows_registered_fail_closed() {
    assert_fail_closed("l5e_match_arm_shadows_registered");
}

#[test]
fn l5f_fn_ptr_closure_reassigned_fail_closed() {
    assert_fail_closed("l5f_fn_ptr_closure_reassigned");
}

#[test]
fn l5g_fn_ptr_closure_deref_written_fail_closed() {
    assert_fail_closed("l5g_fn_ptr_closure_deref_written");
}

#[test]
fn l5h_fn_ptr_closure_mem_replaced_fail_closed() {
    assert_fail_closed("l5h_fn_ptr_closure_mem_replaced");
}

#[test]
fn l5i_fn_ptr_closure_block_assigned_fail_closed() {
    assert_fail_closed("l5i_fn_ptr_closure_block_assigned");
}

#[test]
fn l5j_bare_fn_ptr_deref_written_div0_fail_closed() {
    assert_fail_closed("l5j_bare_fn_ptr_deref_written_div0");
}

#[test]
fn l5k_bare_fn_ptr_mem_replaced_div0_fail_closed() {
    assert_fail_closed("l5k_bare_fn_ptr_mem_replaced_div0");
}

#[test]
fn l5l_bare_fn_ptr_block_assigned_div0_fail_closed() {
    assert_fail_closed("l5l_bare_fn_ptr_block_assigned_div0");
}

#[test]
fn l5m_bare_fn_ptr_branch_assigned_div0_fail_closed() {
    assert_fail_closed("l5m_bare_fn_ptr_branch_assigned_div0");
}

#[test]
fn l5n_inner_shadow_restores_verified() {
    assert_verified("l5n_inner_shadow_restores_verified");
}

#[test]
fn l5o_inner_shadow_restores_liar_cx() {
    assert_cx_assertion("l5o_inner_shadow_restores_liar");
}

#[test]
fn l5p_mut_unascribed_closure_verified() {
    assert_verified("l5p_mut_unascribed_closure_verified");
}

#[test]
fn l5q_mut_unascribed_closure_liar_cx() {
    assert_cx_assertion("l5q_mut_unascribed_closure_liar");
}

// ---------------------------------------------------------------------------
// R6 — `const` / `static` function values. MEASURED before R6: all Verified.
// ---------------------------------------------------------------------------

#[test]
fn l6a_const_fn_ptr_callee_fail_closed() {
    assert_fail_closed("l6a_const_fn_ptr_callee");
}

#[test]
fn l6b_static_fn_ptr_callee_fail_closed() {
    assert_fail_closed("l6b_static_fn_ptr_callee");
}

#[test]
fn l6c_module_const_fn_ptr_callee_fail_closed() {
    assert_fail_closed("l6c_module_const_fn_ptr_callee");
}

#[test]
fn l6d_assoc_const_fn_ptr_callee_fail_closed() {
    assert_fail_closed("l6d_assoc_const_fn_ptr_callee");
}

#[test]
fn l6e_qself_const_fn_ptr_callee_fail_closed() {
    assert_fail_closed("l6e_qself_const_fn_ptr_callee");
}

// ---------------------------------------------------------------------------
// R7 — `mut` Fn-bound parameters are not modelled.
// ---------------------------------------------------------------------------

#[test]
fn l7a_mut_param_branch_reassigned_fail_closed() {
    assert_fail_closed("l7a_mut_param_branch_reassigned");
}

#[test]
fn l7b_mut_param_mem_swapped_fail_closed() {
    assert_fail_closed("l7b_mut_param_mem_swapped");
}

#[test]
fn l7c_mut_param_loop_assigned_fail_closed() {
    assert_fail_closed("l7c_mut_param_loop_assigned");
}

// ---------------------------------------------------------------------------
// R8 — applications inside MACRO TOKENS (blocker 1): every
// rendered call is classified (`format_call_expr`), every call of an `assert!` /
// `assume!` condition — quantifier bodies included — is classified, and a
// MODELLED application in a condition that proves no call-site requires
// (`invariant!`, `loop_ensures!`, `assert_by!` conditions, `calc!`, `vec!`, …)
// fails closed. MEASURED before the fix: every liar below Verified, except `l8l`
// (a lowering Error there) — each red on that engine.
// ---------------------------------------------------------------------------

#[test]
fn l8a_unregistered_shadow_in_assert_fail_closed() {
    assert_fail_closed("l8a_unregistered_shadow_in_assert");
}

#[test]
fn l8b_item_alias_shadow_in_assert_fail_closed() {
    assert_fail_closed("l8b_item_alias_shadow_in_assert");
}

#[test]
fn l8c_fnbound_shadowed_by_unregistered_in_assert_fail_closed() {
    assert_fail_closed("l8c_fnbound_shadowed_by_unregistered_in_assert");
}

#[test]
fn l8d_destructure_shadow_in_assert_fail_closed() {
    assert_fail_closed("l8d_destructure_shadow_in_assert");
}

#[test]
fn l8e_match_arm_shadow_in_assert_fail_closed() {
    assert_fail_closed("l8e_match_arm_shadow_in_assert");
}

#[test]
fn l8f_inner_block_unregistered_in_assert_fail_closed() {
    assert_fail_closed("l8f_inner_block_unregistered_in_assert");
}

#[test]
fn l8g_unregistered_shadow_in_invariant_fail_closed() {
    assert_fail_closed("l8g_unregistered_shadow_in_invariant");
}

#[test]
fn l8h_fnbound_shadowed_by_item_in_assert_fail_closed() {
    assert_fail_closed("l8h_fnbound_shadowed_by_item_in_assert");
}

#[test]
fn l8i_fnbound_shadowed_by_alias_in_assert_fail_closed() {
    // The whole-program witness: the callee is where the unproven application
    // is, so the callee must be refused (the caller's own obligations hold).
    assert_fail_closed("l8i_fnbound_shadowed_by_alias_in_assert");
}

#[test]
fn l8j_fnbound_shadowed_if_let_in_assert_fail_closed() {
    assert_fail_closed("l8j_fnbound_shadowed_if_let_in_assert");
}

#[test]
fn l8k_unregistered_shadow_in_assert_nonreflexive_fail_closed() {
    assert_fail_closed("l8k_unregistered_shadow_in_assert_nonreflexive");
}

#[test]
fn l8l_unregistered_shadow_in_assert_forall_fail_closed() {
    assert_fail_closed("l8l_unregistered_shadow_in_assert_forall");
}

#[test]
fn l8m_registered_in_invariant_fail_closed() {
    assert_fail_closed("l8m_registered_in_invariant");
}

#[test]
fn l8n_registered_in_vec_fail_closed() {
    assert_fail_closed("l8n_registered_in_vec");
}

#[test]
fn l8o_registered_in_assert_verified() {
    assert_verified("l8o_registered_in_assert_verified");
}

#[test]
fn l8p_registered_in_assert_liar_cx() {
    assert_cx_assertion("l8p_registered_in_assert_liar");
}

#[test]
fn l8q_fnbound_in_assert_refused() {
    assert_repeat_refused("l8q_fnbound_in_assert_refused");
}

#[test]
fn l8r_fnbound_in_assert_liar_cx() {
    assert_cx_requires("l8r_fnbound_in_assert_liar", "f");
}

#[test]
fn l8s_vec_plain_items_verified() {
    assert_verified("l8s_vec_plain_items_verified");
}

#[test]
fn l8s_vec_plain_items_liar_cx() {
    assert_cx_assertion("l8s_vec_plain_items_liar");
}

#[test]
fn l8t_assert_by_blocks_second_application_liar_cx() {
    assert_cx_requires("l8t_assert_by_blocks_second_application_liar", "f");
}

#[test]
fn l8u_assert_by_blocks_both_applications_verified() {
    assert_verified("l8u_assert_by_blocks_both_applications_verified");
}

// ---------------------------------------------------------------------------
// R9 — a bare closure's parameter named like an outer declared variable
// (blocker 2). The parameter is bound to a fresh, never-declared
// symbol, so a body obligation that reads it is refused exactly as when nothing
// collides (an unresolved variable at lowering). MEASURED before the fix: every
// liar below (`l9a`-`l9h`) Verified.
// ---------------------------------------------------------------------------

/// Refused (never Verified, never a Counterexample over the OUTER variable)
/// because the body obligation reads the closure parameter, which the
/// diagnostic reports as a new binding the model does not know (`needle`).
fn assert_refused_reading_closure_param(func: &str, needle: &str) {
    let message = match verify(func) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => panic!(
            "`{func}` reads a closure parameter the model does not bind and must be \
             refused; got {other:?}"
        ),
    };
    assert!(
        message.contains("unresolved variable") && message.contains(needle),
        "`{func}` was refused, but not for the unbound closure parameter `{needle}`: {message}"
    );
}

#[test]
fn l9a_closure_param_shadows_outer_nary_refused() {
    assert_refused_reading_closure_param(
        "l9a_closure_param_shadows_outer_nary",
        "binds this name again",
    );
}

#[test]
fn l9b_closure_param_shadows_outer_unary_refused() {
    assert_refused_reading_closure_param(
        "l9b_closure_param_shadows_outer_unary",
        "binds this name again",
    );
}

#[test]
fn l9c_fnbound_closure_param_shadow_refused() {
    assert_refused_reading_closure_param(
        "l9c_fnbound_closure_param_shadow",
        "binds this name again",
    );
}

#[test]
fn l9d_fnbound_in_map_closure_refused() {
    assert_refused_reading_closure_param("l9d_fnbound_in_map_closure", "binds this name again");
}

#[test]
fn l9e_registered_in_map_closure_refused() {
    assert_refused_reading_closure_param("l9e_registered_in_map_closure", "binds this name again");
}

#[test]
fn l9f_helper_closure_param_shadow_refused() {
    assert_refused_reading_closure_param(
        "l9f_helper_closure_param_shadow",
        "binds this name again",
    );
}

#[test]
fn l9g_fnbound_callee_refused() {
    assert_refused_reading_closure_param("l9g_fnbound_callee", "binds this name again");
}

#[test]
fn l9h_closure_body_assert_param_collision_refused() {
    assert_refused_reading_closure_param(
        "l9h_closure_body_assert_param_collision",
        "binds this name again",
    );
}

#[test]
fn l9i_helper_closure_param_no_collision_refused_identically() {
    assert_refused_reading_closure_param("l9i_helper_closure_param_no_collision", "`x`");
}

#[test]
fn l9j_closure_param_collision_unused_verified() {
    assert_verified("l9j_closure_param_collision_unused_verified");
}

#[test]
fn l9k_closure_param_collision_unused_liar_cx() {
    assert_cx_requires("l9k_closure_param_collision_unused_liar", "l9_need4");
}

// ---------------------------------------------------------------------------
// R10 — result binder named like a parameter (major): the
// requires is substituted parameters-last. MEASURED before the fix:
// every liar below Verified.
// ---------------------------------------------------------------------------

#[test]
fn l10a_result_named_like_param_unary_cx() {
    assert_cx_requires("l10a_result_named_like_param_unary", "f");
}

#[test]
fn l10b_result_named_like_param_nary_cx() {
    assert_cx_requires("l10b_result_named_like_param_nary", "f");
}

#[test]
fn l10c_result_named_like_param_underflow_cx() {
    assert_cx_requires("l10c_result_named_like_param_underflow", "f");
}

#[test]
fn l10d_result_named_like_param_underflow_nary_cx() {
    assert_cx_requires("l10d_result_named_like_param_underflow_nary", "f");
}

#[test]
fn l10e_result_named_like_param_verified() {
    assert_verified("l10e_result_named_like_param_verified");
}

#[test]
fn l10f_result_named_like_param_liar_cx() {
    assert_cx_assertion("l10f_result_named_like_param_liar");
}

// ---------------------------------------------------------------------------
// R11 — a pattern binding named like an outer declared variable: `while let`
// (bound to nothing before), and `if let` / `match` arms over an opaque
// scrutinee (identity shadows). Same binder as R9 (`shadow_names`).
// MEASURED before the fix: every liar below (`l11a`-`l11f`) Verified.
// ---------------------------------------------------------------------------

#[test]
fn l11a_while_let_shadow_helper_refused() {
    assert_while_let_refused("l11a_while_let_shadow_helper", "binds this name again");
}

#[test]
fn l11b_while_let_shadow_closure_app_refused() {
    assert_while_let_refused("l11b_while_let_shadow_closure_app", "binds this name again");
}

#[test]
fn l11c_while_let_shadow_assert_refused() {
    assert_while_let_refused("l11c_while_let_shadow_assert", "binds this name again");
}

#[test]
fn l11d_if_let_opaque_scrutinee_shadow_refused() {
    assert_refused_reading_closure_param(
        "l11d_if_let_opaque_scrutinee_shadow",
        "binds this name again",
    );
}

#[test]
fn l11e_match_opaque_scrutinee_shadow_refused() {
    assert_refused_reading_closure_param(
        "l11e_match_opaque_scrutinee_shadow",
        "binds this name again",
    );
}

#[test]
fn l11f_while_let_tuple_shadow_refused() {
    assert_while_let_refused("l11f_while_let_tuple_shadow", "binds this name again");
}

#[test]
fn l11g_while_let_no_collision_refused_identically() {
    assert_while_let_refused("l11g_while_let_no_collision", "`x`");
}

#[test]
fn l11h_while_let_collision_unused_refused() {
    // The loop-condition refusal fires before the body is read, so this
    // true control cannot verify on the `while let` spelling; it stays a
    // fail-closed pin.
    assert_while_let_refused("l11h_while_let_collision_unused_verified", "`x`");
}

#[test]
fn l11i_while_let_collision_unused_liar_refused() {
    assert_while_let_refused("l11i_while_let_collision_unused_liar", "`x`");
}

#[test]
fn l11j_if_let_datatype_shadow_cx() {
    assert_cx_requires("l11j_if_let_datatype_shadow_cx", "l9_need4");
}

// ---------------------------------------------------------------------------
// R12 — the `Fn` / `FnMut` / `FnOnce` ABI SPELLING of an application (blocker).
// `f.call((a, b))`, `f.call_once((a,))`, `Fn::call(&f,
// (a,))` ARE the application `f(a, b)` — `dispatch/methods.rs` lowers the unary
// `.call` form to the very same `spec_fn_apply` UF — but every seam
// (`record_closure_application_obligations`,
// `emit_fn_bound_param_application_obligations`, `reject_unmodelled_value_callee`,
// `collect_expr_calls`, and `referenced_helper_calls`) was keyed on
// `syn::ExprCall`, so an `ExprMethodCall` (or a UFCS trait-path call) reached
// none of them. With the result UNUSED nothing is lowered either, so the whole
// fragment R1/R3/R8 close leaked back out through this one spelling.
// MEASURED Verified before the fix: every liar
// below. `l12b` is the ORIGINAL hole repro
// `h6_nary_bad_requires_via_call_method` verbatim, which the H6 hole record's
// own confirmation also lists as Verified at main.
// ---------------------------------------------------------------------------

/// KNOWN OVER-REJECTION (minor), pinned so it cannot be lost
/// silently: a `mut`-ascribed binding is never modelled BECAUSE `l5j`-`l5m`
/// reassign one and divide by zero, so a binding that is never reassigned is
/// refused too. Sound (fail-closed), and a capability residual — not a rule to
/// relax without the reassignment analysis that would make it safe.
#[test]
fn l5n_bare_fn_ptr_never_reassigned_refused() {
    assert_fail_closed("l5n_bare_fn_ptr_never_reassigned_refused");
}

#[test]
fn l12a_call_unary_bad_requires_cx() {
    // BEFORE: Verified with 1 obligation (the `ensures(true)` alone).
    assert!(
        obligation_count("l12a_call_unary_bad_requires") >= 2,
        "the `.call` application must emit its prove-requires obligation"
    );
    assert_cx_requires("l12a_call_unary_bad_requires", "f");
}

#[test]
fn l12b_call_nary_bad_requires_cx() {
    assert_cx_requires("l12b_call_nary_bad_requires", "f");
}

#[test]
fn l12c_call_unary_div_zero_cx() {
    assert_cx_requires("l12c_call_unary_div_zero", "f");
}

#[test]
fn l12d_call_once_bad_requires_cx() {
    assert_cx_requires("l12d_call_once_bad_requires", "f");
}

#[test]
fn l12e_call_mut_bad_requires_cx() {
    assert_cx_requires("l12e_call_mut_bad_requires", "f");
}

#[test]
fn l12f_call_ufcs_bad_requires_cx() {
    assert_cx_requires("l12f_call_ufcs_bad_requires", "f");
}

#[test]
fn l12g_call_ufcs_once_bad_requires_cx() {
    assert_cx_requires("l12g_call_ufcs_once_bad_requires", "f");
}

#[test]
fn l12h_call_fnbound_unary_cx() {
    assert_cx_requires("l12h_call_fnbound_unary", "f");
}

#[test]
fn l12i_call_fnbound_nary_cx() {
    assert_cx_requires("l12i_call_fnbound_nary", "f");
}

#[test]
fn l12j_call_bare_closure_div_zero_cx() {
    // The invoked bare exec closure's BODY arithmetic is instrumented at the
    // `.call` site exactly as at `f(0u64)`.
    //
    // The closure's body is ALSO checked at its DEFINITION site, over fresh
    // declared parameters (`b__closureparam_*`), so the program comes back
    // REFUTED with a model (`b__closureparam_0 = 0`) rather than merely
    // refused. A Counterexample is a strictly STRONGER outcome than a
    // fail-closed `Error` — the liar is still caught, and now with a witness —
    // so the assertion demands the refutation.
    assert_cx_div_zero("l12j_call_bare_closure_div_zero");
}

#[test]
fn l12k_call_in_assert_cx() {
    assert_cx_requires("l12k_call_in_assert", "f");
}

#[test]
fn l12l_call_helper_item_cx() {
    assert_cx_requires("l12l_call_helper_item", "l9_need4");
}

#[test]
fn l12m_call_helper_item_ufcs_cx() {
    assert_cx_requires("l12m_call_helper_item_ufcs", "l9_need4");
}

#[test]
fn l12n_call_mut_fnmut_param_fail_closed() {
    assert_fail_closed("l12n_call_mut_fnmut_param");
}

#[test]
fn l12o_call_alias_of_closure_fail_closed() {
    assert_fail_closed("l12o_call_alias_of_closure");
}

#[test]
fn l12p_call_through_deref_fail_closed() {
    assert_fail_closed("l12p_call_through_deref");
}

// Controls — the identical spellings with a SATISFIED precondition still verify
// (no over-rejection), so each refusal above is the precondition and not the
// spelling.

#[test]
fn l12q_call_nary_good_requires_verified() {
    assert_verified("l12q_call_nary_good_requires_verified");
}

#[test]
fn l12r_call_ufcs_good_requires_verified() {
    assert_verified("l12r_call_ufcs_good_requires_verified");
}

#[test]
fn l12s_call_fnbound_good_requires_verified() {
    assert_verified("l12s_call_fnbound_good_requires_verified");
}

#[test]
fn l12t_call_helper_item_good_verified() {
    assert_verified("l12t_call_helper_item_good_verified");
}

#[test]
fn l12u_spec_fn_call_surface_verified() {
    // The GHOST `SpecFn::call(x)` spec surface takes a BARE argument, never the
    // `Fn`-ABI tuple, so the desugaring does not touch it.
    assert_verified("l12u_spec_fn_call_surface_verified");
}

#[test]
fn l12v_spec_fn_call_surface_liar_cx() {
    assert_cx_assertion("l12v_spec_fn_call_surface_liar");
}
