// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `#[verifier::rlimit(N)]` / `#[verifier::rlimit(infinity)]` attribute
//! wiring (upstream basic.rs `test_rlimit_20` / `test_rlimit_inf`).
//!
//! Upstream semantics: `rlimit(N)` grants roughly N seconds of reference
//! solver work (`verifier.rs::set_rlimit`, `RLIMIT_PER_SECOND`); `infinity`
//! (and `0`, which Z3 reads as unlimited) disables the budget; a malformed
//! argument is rejected with "expected number, or `infinity` for rlimit"
//! (`attributes.rs::get_rlimit_arg`). These tests prove the attribute is
//! actually APPLIED — the extracted `VerificationContext` carries the mapped
//! `rlimit_ms` nominal solver budget that the encoder's watchdog/timeout
//! plumbing (#2489/#2577) consumes — not merely parsed and dropped.

use crate::mode_attrs::RLIMIT_INFINITY_MS;

fn extract(source: &str) -> crate::TrustVcResult<crate::vc::VerificationContext> {
    let file: syn::File = syn::parse_str(source).expect("test source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) => Some(func),
            _ => None,
        })
        .expect("test source should contain a function");
    super::super::extract_verification_conditions_with_file_context(&file, func)
}

#[test]
fn rlimit_path_form_sets_context_budget() {
    let ctx = extract(
        "#[verifier::rlimit(20)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("upstream test_rlimit_20 shape should extract");
    assert_eq!(
        ctx.rlimit_ms,
        Some(20_000),
        "rlimit(20) = 20 upstream rlimit units ≈ 20s of nominal solver budget"
    );
}

#[test]
fn rlimit_infinity_sets_unlimited_budget() {
    let ctx = extract(
        "#[verifier::rlimit(infinity)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("upstream test_rlimit_inf shape should extract");
    assert_eq!(ctx.rlimit_ms, Some(RLIMIT_INFINITY_MS));
}

#[test]
fn rlimit_list_form_sets_context_budget() {
    let ctx = extract(
        "#[verifier(rlimit(20))]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("#[verifier(rlimit(20))] list form should extract");
    assert_eq!(ctx.rlimit_ms, Some(20_000));
}

#[test]
fn rlimit_trust_vc_prefixed_path_form_sets_context_budget() {
    let ctx = extract(
        "#[trust_vc::verifier::rlimit(3)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("trust_vc::verifier::rlimit path form should extract");
    assert_eq!(ctx.rlimit_ms, Some(3_000));
}

#[test]
fn rlimit_float_argument_maps_to_milliseconds() {
    // Upstream parses the argument as f32 (Float | Integer literals).
    let ctx = extract(
        "#[verifier::rlimit(2.5)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("float rlimit should extract");
    assert_eq!(ctx.rlimit_ms, Some(2_500));
}

#[test]
fn rlimit_zero_is_unlimited_like_upstream_z3() {
    // Upstream forwards 0 to Z3, which interprets a zero rlimit as infinity.
    let ctx = extract(
        "#[verifier::rlimit(0)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("rlimit(0) should extract");
    assert_eq!(ctx.rlimit_ms, Some(RLIMIT_INFINITY_MS));
}

#[test]
fn duplicate_rlimit_last_wins_like_upstream() {
    // Upstream `parse_attrs` overwrites `vs.rlimit` per attribute in order.
    let ctx = extract(
        "#[verifier::rlimit(20)]\n\
         #[verifier::rlimit(5)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("duplicate rlimit attributes should extract");
    assert_eq!(ctx.rlimit_ms, Some(5_000));
}

#[test]
fn no_rlimit_attribute_leaves_default_budget() {
    let ctx = extract(
        "#[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("plain function should extract");
    assert_eq!(ctx.rlimit_ms, None);
}

#[test]
fn legacy_trust_vc_rlimit_ms_attribute_is_not_reinterpreted() {
    // `#[trust_vc::rlimit(N)]` is the LEGACY proc-macro-path attribute whose N
    // is already in milliseconds (spec_expand.rs, #2489); the Verus-unit
    // mapping must not touch it. (It is applied by the generated runtime code,
    // not by this extraction path.)
    let ctx = extract(
        "#[trust_vc::rlimit(5000)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("legacy rlimit attribute should extract");
    assert_eq!(ctx.rlimit_ms, None);
}

#[test]
fn malformed_rlimit_ident_fails_closed_with_upstream_message() {
    let err = extract(
        "#[verifier::rlimit(frobnitz)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect_err("malformed rlimit must be rejected");
    assert!(
        err.to_string()
            .contains("expected number, or `infinity` for rlimit"),
        "unexpected error: {err}"
    );
}

#[test]
fn malformed_rlimit_extra_tokens_fail_closed() {
    let err = extract(
        "#[verifier::rlimit(20, 30)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect_err("multi-argument rlimit must be rejected");
    assert!(
        err.to_string()
            .contains("expected number, or `infinity` for rlimit"),
        "unexpected error: {err}"
    );
}

#[test]
fn malformed_rlimit_empty_args_fail_closed() {
    let err = extract(
        "#[verifier::rlimit()]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect_err("empty rlimit must be rejected");
    assert!(
        err.to_string()
            .contains("expected number, or `infinity` for rlimit"),
        "unexpected error: {err}"
    );
}

#[test]
fn malformed_rlimit_in_list_form_fails_closed() {
    let err = extract(
        "#[verifier(rlimit(frobnitz))]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect_err("malformed list-form rlimit must be rejected");
    assert!(
        err.to_string()
            .contains("expected number, or `infinity` for rlimit"),
        "unexpected error: {err}"
    );
}

#[test]
fn unknown_function_style_verifier_option_still_fails_closed() {
    // Before this slice, `#[verifier(anything(...))]` failed the
    // `Punctuated<Path>` parse outright; the rlimit carve-out must not
    // silently accept other function-style options.
    let err = extract(
        "#[verifier(frobnitz(20))]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect_err("unknown function-style verifier option must be rejected");
    assert!(
        err.to_string().contains("unsupported verifier option"),
        "unexpected error: {err}"
    );
}

#[test]
fn rlimit_combines_with_solver_mode_in_one_list() {
    let ctx = extract(
        "#[verifier(nonlinear, rlimit(20))]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("solver mode + rlimit in one verifier list should extract");
    assert_eq!(ctx.rlimit_ms, Some(20_000));
}

#[test]
fn rlimit_huge_value_saturates_to_infinity_sentinel() {
    let ctx = extract(
        "#[verifier::rlimit(99999999999)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("huge rlimit should extract");
    assert_eq!(ctx.rlimit_ms, Some(RLIMIT_INFINITY_MS));
}
