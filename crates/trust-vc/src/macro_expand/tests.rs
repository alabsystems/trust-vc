// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use quote::quote;

#[test]
fn test_expand_ghost_requires_routes_to_trust_mc_assume() {
    let expanded = expand_ghost_requires(quote!(value > 0)).to_string();
    assert!(
        expanded.contains("cfg (trust_mc)"),
        "ghost_requires should still have trust_mc path: {expanded}"
    );
    assert!(
        expanded.contains(":: trust_mc :: assume !"),
        "ghost_requires trust_mc path should use assume: {expanded}"
    );
}

#[test]
fn test_expand_ghost_requires_has_trust_vc_test_path() {
    let expanded = expand_ghost_requires(quote!(value > 0)).to_string();
    assert!(
        expanded.contains("cfg (all (test , not (trust_mc)))"),
        "ghost_requires must have trust_vc test path (#2525): {expanded}"
    );
    assert!(
        expanded.contains("ObligationKind :: Assume"),
        "ghost_requires trust_vc path must collect Assume obligation (#2525): {expanded}"
    );
}

#[test]
fn test_expand_assert_forall_by_does_not_require_default_binders() {
    let parsed = trust_vc_core::parse_assert_forall_by(quote! {
        |x: NoCtor| true,
        { trust_vc::assume!(true); }
    })
    .expect("typed assert_forall_by input should parse");
    let expanded = expand_assert_forall_by(parsed).to_string();

    assert!(
        !expanded.contains("core :: default :: Default"),
        "assert_forall_by binders are ghost variables and must not require Default: {expanded}"
    );
    assert!(
        expanded.contains("ObligationKind :: Assume"),
        "direct proof-block assume! should still collect a scoped obligation: {expanded}"
    );
    assert!(
        expanded.contains("| x : NoCtor |"),
        "expansion should keep a non-executed type-checking closure for binder syntax: {expanded}"
    );
}

#[test]
fn test_expand_assert_forall_by_preserves_trigger_patterns() {
    let parsed = trust_vc_core::parse_assert_forall_by(quote! {
        |k: u32| #[trigger] f(k) && k == k,
        {}
    })
    .expect("trigger-bearing assert_forall_by input should parse");
    let expanded = expand_assert_forall_by(parsed).to_string();

    assert!(
        expanded.contains("end_assert_forall_by_scope_expr_with_triggers"),
        "typed assert_forall_by path should pass trigger patterns: {expanded}"
    );
    assert!(
        expanded.contains("f (k)") && expanded.contains("__trust_vc_trigger_patterns"),
        "expansion should materialize the explicit trigger pattern: {expanded}"
    );
    assert!(
        !expanded.contains("let _ = | k : u32 | { # [trigger]"),
        "non-test typecheck closure must not re-emit unstable expression attrs: {expanded}"
    );
}

#[test]
fn test_expand_assert_seqs_equal_uses_ext_eq_collection() {
    let parsed =
        trust_vc_core::parse_assert_seqs_equal(quote!(s1 == Seq::<i32>::empty().push(1i32)))
            .expect("assert_seqs_equal binary syntax should parse");
    let expanded = expand_assert_seqs_equal(&parsed).to_string();

    assert!(
        expanded.contains("collect_ext_eq_obligation"),
        "assert_seqs_equal should delegate to extensional equality collection: {expanded}"
    );
    assert!(
        expanded.contains("ObligationKind :: Assert"),
        "assert_seqs_equal should collect an assert obligation: {expanded}"
    );
    assert!(
        expanded.contains("true"),
        "assert_seqs_equal should pass is_eq=true to ext_eq collection: {expanded}"
    );
}

#[test]
fn test_expand_ghost_ensures_routes_to_trust_mc_assert() {
    let expanded = expand_ghost_ensures(quote!(result > 0)).to_string();
    assert!(
        expanded.contains("cfg (trust_mc)"),
        "ghost_ensures should still have trust_mc path: {expanded}"
    );
    assert!(
        expanded.contains(":: trust_mc :: assert !"),
        "ghost_ensures trust_mc path should use assert: {expanded}"
    );
}

#[test]
fn test_expand_ghost_ensures_has_trust_vc_test_path() {
    let expanded = expand_ghost_ensures(quote!(result > 0)).to_string();
    assert!(
        expanded.contains("cfg (all (test , not (trust_mc)))"),
        "ghost_ensures must have trust_vc test path (#2525): {expanded}"
    );
    assert!(
        expanded.contains("ObligationKind :: Ensures"),
        "ghost_ensures trust_vc path must collect Ensures obligation (#2525): {expanded}"
    );
}

#[test]
fn test_expand_assume_by_with_block_contains_scope_and_assumption() {
    let expanded = expand_assume_by_with_block(
        quote!(x > 0),
        quote!({
            trust_vc::assert!(x > 0);
        }),
    )
    .to_string();

    // Verify structural elements of the expansion
    assert!(
        expanded.contains("begin_assert_by_scope"),
        "assume_by expansion should open a scope"
    );
    assert!(
        expanded.contains("end_assert_by_scope"),
        "assume_by expansion should close the scope"
    );
    assert!(
        expanded.contains("ObligationKind :: Assume"),
        "assume_by expansion should inject an Assume obligation, got: {}",
        expanded
    );
}

#[test]
fn test_expand_calc_two_step_chain_emits_transitive_conclusion() {
    let expanded = expand_calc(quote! {
        a;
        == {}
        b;
        == {}
        c;
    })
    .to_string();

    assert_eq!(
        expanded.matches("begin_assert_by_scope_with_label").count(),
        3,
        "two-step calc chain should emit two step obligations plus one transitive conclusion: {expanded}"
    );
    assert!(
        expanded.contains("a == c"),
        "calc expansion should include transitive conclusion over the first and last expressions: {expanded}"
    );
}

#[test]
fn test_expand_open_local_invariant_contains_symbolic_lowering() {
    let expanded = expand_open_local_invariant(quote! {
        &inv => inner => {
            trust_vc::assert!(*inner == *inner);
            *inner = *inner;
        }
    })
    .to_string();

    assert!(
        expanded.contains("begin_invariant_open"),
        "open_local_invariant expansion should open an invariant scope: {expanded}"
    );
    assert!(
        expanded.contains("end_invariant_open"),
        "open_local_invariant expansion should close an invariant scope: {expanded}"
    );
    assert!(
        expanded.contains("register_invariant_predicate_helper"),
        "expansion should register the symbolic predicate helper: {expanded}"
    );
    assert!(
        expanded.contains("collect_let_binding"),
        "expansion should rewrite assignments into symbolic let-bindings: {expanded}"
    );
    assert!(
        expanded.contains("invariant_predicate"),
        "expansion should emit symbolic open/close predicate obligations: {expanded}"
    );
}

#[test]
fn test_expand_open_local_invariant_bad_syntax_produces_error() {
    let expanded = expand_open_local_invariant(quote! {
        not_valid_syntax
    })
    .to_string();

    assert!(
        expanded.contains("compile_error"),
        "bad syntax should produce a compile error: {expanded}"
    );
}

#[test]
fn test_expand_track_let_symbolic_initializer_collects_let_binding() {
    let expanded = expand_track_let(quote! {
        let y: u64 = x + 1u64;
        trust_vc::assert!(y > x);
    })
    .to_string();

    assert!(
        expanded.contains("collect_variable") && expanded.contains("\"u64\""),
        "typed track_let binding should register the local type: {expanded}"
    );
    assert!(
        expanded.contains("collect_let_binding"),
        "encodable track_let initializer should use symbolic let-binding collection: {expanded}"
    );
    assert!(
        !expanded.contains("collect_let_binding_runtime_value_from_ref"),
        "encodable track_let initializer should not use runtime value capture: {expanded}"
    );
}

#[test]
fn test_expand_track_let_exec_call_initializer_collects_runtime_value() {
    let expanded = expand_track_let(quote! {
        let y = helper(x);
        trust_vc::assert!(y == 5u64);
    })
    .to_string();

    assert!(
        expanded.contains("collect_variable_runtime"),
        "untyped track_let binding should infer the local type at runtime: {expanded}"
    );
    assert!(
        expanded.contains("collect_let_binding_runtime_value_from_ref"),
        "opaque track_let initializer should capture the call result through the macro surface: {expanded}"
    );
    assert!(
        expanded.contains("trust_vc :: assert !"),
        "track_let should preserve following statements in the scoped block: {expanded}"
    );
}

const PRECONDITION_CHECK: &str = "\"trust_vc precondition failed: {}\"";
const POSTCONDITION_CHECK: &str = "\"trust_vc postcondition failed: {}\"";
const ASSERTION_CHECK: &str = "\"trust_vc assertion failed: {}\"";
const INVARIANT_CHECK: &str = "\"trust_vc loop invariant failed\"";

#[track_caller]
fn assert_only_type_checked(expanded: &str, check: &str, what: &str) {
    assert!(
        !expanded.contains(check) && expanded.contains("if false"),
        "{what} should only be type-checked at run time: {expanded}"
    );
}

#[test]
fn test_a_clause_that_can_call_a_ghost_function_is_not_checked_at_run_time() {
    for clause in [
        quote!(inc(x) > 5u64),
        quote!(s.view() == s.a),
        quote!(v[i] == 0u64),
    ] {
        let requires = expand_requires(clause.clone()).to_string();
        assert_only_type_checked(
            &requires,
            PRECONDITION_CHECK,
            &format!("requires({clause})"),
        );
        let ensures = expand_ensures(clause.clone()).to_string();
        assert_only_type_checked(&ensures, POSTCONDITION_CHECK, &format!("ensures({clause})"));
        let parsed: syn::Expr = syn::parse2(clause.clone()).expect("clause should parse");
        let assertion = expand_assert(clause.clone(), &parsed).to_string();
        assert_only_type_checked(&assertion, ASSERTION_CHECK, &format!("assert!({clause})"));
        let invariant = crate::macro_expand_ext::expand_invariant(clause.clone()).to_string();
        assert_only_type_checked(
            &invariant,
            INVARIANT_CHECK,
            &format!("invariant!({clause})"),
        );
    }
}

#[test]
fn test_a_clause_that_calls_nothing_keeps_its_run_time_check() {
    let requires = expand_requires(quote!(x < 100u64)).to_string();
    assert!(
        requires.contains(PRECONDITION_CHECK),
        "requires(x < 100u64) should keep its run-time check: {requires}"
    );
    let ensures = expand_ensures(quote!(r == x + 1u64)).to_string();
    assert!(
        ensures.contains(POSTCONDITION_CHECK),
        "ensures(r == x + 1u64) should keep its run-time check: {ensures}"
    );
    let clause = quote!(x + 1u64 > x);
    let parsed: syn::Expr = syn::parse2(clause.clone()).expect("clause should parse");
    let assertion = expand_assert(clause, &parsed).to_string();
    assert!(
        assertion.contains(ASSERTION_CHECK),
        "assert!(x + 1u64 > x) should keep its run-time check: {assertion}"
    );
    let invariant = crate::macro_expand_ext::expand_invariant(quote!(i <= n)).to_string();
    assert!(
        invariant.contains(INVARIANT_CHECK),
        "invariant!(i <= n) should keep its run-time check: {invariant}"
    );
}

#[test]
fn test_a_precondition_read_over_the_integers_is_not_checked_at_run_time() {
    for clause in [quote!(z + 1u32 > z), quote!(-x < 0i64), quote!(a * b >= a)] {
        let requires = expand_requires(clause.clone()).to_string();
        assert_only_type_checked(
            &requires,
            PRECONDITION_CHECK,
            &format!("requires({clause})"),
        );
    }
    let measure = crate::macro_expand_ext::expand_loop_decreases(quote!(n - i)).to_string();
    assert!(
        measure.contains("if false"),
        "loop_decreases!(n - i) should not be evaluated at run time: {measure}"
    );
    let plain = crate::macro_expand_ext::expand_loop_decreases(quote!(n)).to_string();
    assert!(
        !plain.contains("if false"),
        "loop_decreases!(n) should still be evaluated: {plain}"
    );
}

#[test]
fn test_recommends_is_never_checked_at_run_time() {
    let recommends = expand_recommends(quote!(x > 0u64)).to_string();
    assert_only_type_checked(&recommends, "debug_assert !", "recommends(x > 0u64)");
}
