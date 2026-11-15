// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `canonicalize_impl_method_ensures` — the registration-time rewrite that moves
//! a trait-impl method's own `ensures` out of the IMPL's parameter scope onto the
//! positional placeholders its captured conformance body uses.
//!
//! The end-to-end verdicts (liars, controls, conformance) live in
//! `tests/impl_ensures_positional_binding_capability.rs`; this file pins the
//! rewrite itself: the exact placeholder each identifier becomes, the positions
//! it must NOT touch, and every shape on which it must decline. Declining is
//! all-or-nothing per method, and it is the conservative direction — nothing is
//! registered, so nothing is published to callers.

use super::*;

fn method(src: &str) -> syn::ImplItemFn {
    syn::parse_str(src).unwrap_or_else(|err| panic!("fixture method should parse: {err}"))
}

fn canon(method_src: &str, clauses: &[&str]) -> Option<Vec<String>> {
    let clauses: Vec<String> = clauses.iter().map(|c| (*c).to_string()).collect();
    canonicalize_impl_method_ensures(&method(method_src), &clauses)
}

/// Token-normalized spelling, so expectations are written as ordinary Rust.
fn tokens(expr: &str) -> String {
    syn::parse_str::<Expr>(expr)
        .unwrap_or_else(|err| panic!("expectation should parse: {err}"))
        .to_token_stream()
        .to_string()
}

/// A decline pin is only meaningful for a clause that PARSES; otherwise it would
/// pass through the unparsable-clause rule and test nothing about its own.
fn declines_parsable(method_src: &str, clause: &str) {
    assert!(
        syn::parse_str::<Expr>(clause).is_ok(),
        "decline fixture must parse: {clause}"
    );
    assert_eq!(canon(method_src, &[clause]), None, "must decline: {clause}");
}

const SWAPPED: &str = "fn f(&self, b: u64, a: u64) -> u64 { a }";

#[test]
fn swapped_params_rename_by_position_not_by_name() {
    assert_eq!(
        canon(SWAPPED, &["result == a", "b <= result || b > result"]),
        Some(vec![
            tokens("result == __trust_vc_conf_arg_1"),
            tokens("__trust_vc_conf_arg_0 <= result || __trust_vc_conf_arg_0 > result"),
        ])
    );
}

#[test]
fn associated_function_numbers_from_the_first_param() {
    assert_eq!(
        canon("fn g(a: u64, b: u64) -> u64 { b }", &["result == b"]),
        Some(vec![tokens("result == __trust_vc_conf_arg_1")])
    );
}

#[test]
fn member_and_method_names_are_not_parameters() {
    // `self.a` is a FIELD and `.a()` a METHOD even though `a` is also a
    // parameter; only the free occurrences rename.
    assert_eq!(
        canon(
            SWAPPED,
            &["result == self.a + a", "result == a.wrapping_add(b).a()"]
        ),
        Some(vec![
            tokens("result == self.a + __trust_vc_conf_arg_1"),
            tokens("result == __trust_vc_conf_arg_1.wrapping_add(__trust_vc_conf_arg_0).a()"),
        ])
    );
}

#[test]
fn range_operands_are_free_positions() {
    // `..` ends in a lone `.`, which must not be mistaken for member access.
    assert_eq!(
        canon(
            SWAPPED,
            &["(b..a).contains(&result)", "(b..=a).contains(&result)"]
        ),
        Some(vec![
            tokens("(__trust_vc_conf_arg_0..__trust_vc_conf_arg_1).contains(&result)"),
            tokens("(__trust_vc_conf_arg_0..=__trust_vc_conf_arg_1).contains(&result)"),
        ])
    );
}

#[test]
fn a_binder_named_after_no_impl_param_is_left_alone() {
    // `x` is not an impl parameter (it may be a TRAIT parameter's name); the
    // closure binder must survive untouched and no free identifier changes.
    assert_eq!(
        canon(SWAPPED, &["result == a && forall(|x: u64| x == x)"]),
        Some(vec![tokens(
            "result == __trust_vc_conf_arg_1 && forall(|x: u64| x == x)"
        )])
    );
}

#[test]
fn a_binder_shadowing_an_impl_param_declines() {
    for clause in [
        "result == a && forall(|a: u64| a == a)",
        "{ let b = 1u64; result == b }",
        "match result { a => a == a }",
    ] {
        declines_parsable(SWAPPED, clause);
    }
}

#[test]
fn a_param_surviving_inside_a_macro_token_stream_declines() {
    declines_parsable(SWAPPED, "result == my_spec!(a)");
    // A macro that does not mention a parameter is harmless.
    assert_eq!(
        canon(SWAPPED, &["result == a && my_spec!(1u64)"]),
        Some(vec![tokens(
            "result == __trust_vc_conf_arg_1 && my_spec!(1u64)"
        )])
    );
}

#[test]
fn struct_shorthand_and_multi_segment_paths_decline() {
    // Shorthand `P { a }` prints its member, not the renamed expression.
    declines_parsable(SWAPPED, "result == P { a }.a");
    declines_parsable(SWAPPED, "result == a::LIMIT");
}

#[test]
fn reserved_and_result_names_decline() {
    assert_eq!(
        canon(
            "fn k(&self, result: u64, a: u64) -> u64 { a }",
            &["result == 1u64"]
        ),
        None
    );
    assert_eq!(
        canon(
            "fn k(&self, __trust_vc_conf_arg_1: u64, a: u64) -> u64 { a }",
            &["result == a"]
        ),
        None
    );
    assert_eq!(
        canon(SWAPPED, &["result == __trust_vc_conf_arg_0"]),
        None,
        "a clause already spelling a placeholder could be captured by the rename"
    );
}

#[test]
fn non_ident_param_patterns_and_unparsable_clauses_decline() {
    assert_eq!(
        canon(
            "fn p(&self, (x, y): (u64, u64)) -> u64 { x }",
            &["result == 1u64"]
        ),
        None
    );
    assert_eq!(canon(SWAPPED, &["result ==> a"]), None);
    assert_eq!(canon(SWAPPED, &["result == a, result > b"]), None);
}

#[test]
fn declining_is_all_or_nothing_per_method() {
    assert_eq!(
        canon(SWAPPED, &["result == a", "forall(|b: u64| b == b)"]),
        None,
        "one declining clause must drop the whole method, not publish the rest"
    );
}
