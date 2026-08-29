// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `#[verifier::rlimit(N)]` / `#[verifier::rlimit(infinity)]` attribute
//! wiring (upstream basic.rs `test_rlimit_20` / `test_rlimit_inf`).
//!
//! Upstream semantics: `rlimit(N)` grants `N × RLIMIT_PER_SECOND` Z3 RESOURCE
//! UNITS — a DETERMINISTIC work budget (`verifier.rs::set_rlimit`);
//! `infinity` (and `0`, which Z3 reads as unlimited) disables the budget; a
//! malformed argument is rejected with "expected number, or `infinity` for
//! rlimit" (`attributes.rs::get_rlimit_arg`).
//!
//! THE UNIT MOVED, AND THAT IS THE POINT OF THIS FILE. These assertions used
//! to read `ctx.rlimit_ms == Some(N * 1000)`: the attribute bought
//! MILLISECONDS OF WALL CLOCK, so the same annotation granted less work on a
//! loaded machine and the verdict moved with the load. It now buys SAT
//! CONFLICTS — machine-independent work — and keeps a wall FLOOR only so that
//! raising `N` can never shrink the envelope on either axis. The tests below
//! pin both halves, because pinning only the conflict budget would let the
//! wall floor silently regress into a tighter bound than the default.
//!
//! `infinity`/`0` map to `ConflictBudget::AyDefault` — decline to install a
//! trust-vc budget, leaving ay's own calibrated ground allowance in force —
//! NOT to `:rlimit 0`. See `ConflictBudget::AyDefault` for why that
//! distinction is a liveness property and not a style choice.

use crate::mode_attrs::RLIMIT_INFINITY_WALL_MS;
use crate::solver_budget::{ConflictBudget, RLIMIT_UNIT_CONFLICTS};

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

fn bounded(conflicts: u64) -> Option<ConflictBudget> {
    Some(ConflictBudget::bounded(conflicts))
}

#[test]
fn rlimit_path_form_sets_deterministic_conflict_budget() {
    let ctx = extract(
        "#[verifier::rlimit(20)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("upstream test_rlimit_20 shape should extract");
    assert_eq!(
        ctx.rlimit_conflicts,
        bounded(20 * RLIMIT_UNIT_CONFLICTS),
        "rlimit(20) must grant 20 units of DETERMINISTIC work, not 20s of wall clock"
    );
    assert_eq!(
        ctx.rlimit_ms, None,
        "a 20s wall floor is BELOW the default backstop, so it must not be \
         installed — the attribute may only widen the envelope, never tighten it"
    );
}

#[test]
fn rlimit_is_a_monotone_multiplier_on_work() {
    // The property that actually survives the unit change from Z3 resource
    // units to ay conflicts: `rlimit(2N)` grants exactly twice the work of
    // `rlimit(N)`, on every machine and under every load.
    let small = extract(
        "#[verifier::rlimit(3)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("rlimit(3) should extract");
    let large = extract(
        "#[verifier::rlimit(6)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("rlimit(6) should extract");
    let small = small
        .rlimit_conflicts
        .and_then(ConflictBudget::conflicts)
        .expect("rlimit(3) is a bounded budget");
    let large = large
        .rlimit_conflicts
        .and_then(ConflictBudget::conflicts)
        .expect("rlimit(6) is a bounded budget");
    assert_eq!(large, small * 2, "doubling N must double the work grant");
}

#[test]
fn rlimit_infinity_declines_a_trust_vc_budget_and_raises_the_wall() {
    let ctx = extract(
        "#[verifier::rlimit(infinity)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("upstream test_rlimit_inf shape should extract");
    assert_eq!(
        ctx.rlimit_conflicts,
        Some(ConflictBudget::AyDefault),
        "infinity must decline to install a trust-vc budget. It must NOT map \
         to `:rlimit 0`: that also switches off ay's own default ground \
         allowance, and combined with the ~1-year wall floor infinity installs \
         it would leave the function with no termination bound at all"
    );
    assert_eq!(ctx.rlimit_ms, Some(RLIMIT_INFINITY_WALL_MS));
}

#[test]
fn rlimit_list_form_sets_deterministic_conflict_budget() {
    let ctx = extract(
        "#[verifier(rlimit(20))]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("#[verifier(rlimit(20))] list form should extract");
    assert_eq!(ctx.rlimit_conflicts, bounded(20 * RLIMIT_UNIT_CONFLICTS));
}

#[test]
fn rlimit_trust_vc_prefixed_path_form_sets_deterministic_conflict_budget() {
    let ctx = extract(
        "#[trust_vc::verifier::rlimit(3)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("trust_vc::verifier::rlimit path form should extract");
    assert_eq!(ctx.rlimit_conflicts, bounded(3 * RLIMIT_UNIT_CONFLICTS));
}

#[test]
fn rlimit_float_argument_scales_the_conflict_budget() {
    // Upstream parses the argument as f32 (Float | Integer literals).
    let ctx = extract(
        "#[verifier::rlimit(2.5)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("float rlimit should extract");
    assert_eq!(ctx.rlimit_conflicts, bounded(100_000));
}

#[test]
fn tiny_rlimit_floors_at_one_conflict_and_never_becomes_the_default() {
    // The trap this pins: a fractional grant that rounds to zero must NOT
    // silently widen into "no trust-vc budget" — the opposite of the tiny
    // budget the user asked for.
    let ctx = extract(
        "#[verifier::rlimit(0.000001)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("tiny rlimit should extract");
    assert_eq!(
        ctx.rlimit_conflicts,
        bounded(1),
        "a rounded-to-zero grant must saturate UP to 1 conflict"
    );
    assert_ne!(ctx.rlimit_conflicts, Some(ConflictBudget::AyDefault));
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
    assert_eq!(ctx.rlimit_conflicts, Some(ConflictBudget::AyDefault));
    assert_eq!(ctx.rlimit_ms, Some(RLIMIT_INFINITY_WALL_MS));
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
    assert_eq!(ctx.rlimit_conflicts, bounded(5 * RLIMIT_UNIT_CONFLICTS));
}

#[test]
fn no_rlimit_attribute_leaves_default_budget() {
    let ctx = extract(
        "#[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("plain function should extract");
    assert_eq!(ctx.rlimit_ms, None);
    assert_eq!(
        ctx.rlimit_conflicts, None,
        "None means 'resolve to the calibrated default' — it must NOT be \
         spelled AyDefault, which is the DECLINE-to-install spelling"
    );
}

#[test]
fn legacy_trust_vc_rlimit_ms_attribute_is_not_reinterpreted() {
    // `#[trust_vc::rlimit(N)]` is the LEGACY proc-macro-path attribute whose N
    // is already in MILLISECONDS (spec_expand.rs, #2489), and it stays that
    // way: it names the wall backstop, not the work budget. Reinterpreting an
    // existing millisecond argument as a conflict count would change every
    // existing use of it by a factor of RLIMIT_UNIT_CONFLICTS with no
    // diagnostic. (It is applied by the generated runtime code, not by this
    // extraction path.)
    let ctx = extract(
        "#[trust_vc::rlimit(5000)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("legacy rlimit attribute should extract");
    assert_eq!(ctx.rlimit_ms, None);
    assert_eq!(ctx.rlimit_conflicts, None);
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
    assert_eq!(ctx.rlimit_conflicts, bounded(20 * RLIMIT_UNIT_CONFLICTS));
}

#[test]
fn rlimit_huge_value_saturates_upward_on_both_axes() {
    let ctx = extract(
        "#[verifier::rlimit(99999999999)]\n\
         #[trust_vc::ensures(true)]\n\
         fn f() { trust_vc::assert!(true); }",
    )
    .expect("huge rlimit should extract");
    // Saturation must go UP, never wrap into a small budget.
    let conflicts = ctx
        .rlimit_conflicts
        .and_then(ConflictBudget::conflicts)
        .expect("still representable as a bounded budget");
    assert!(
        conflicts > 1_000_000_000_000,
        "huge rlimit must grant a huge budget, got {conflicts}"
    );
    assert_eq!(ctx.rlimit_ms, Some(RLIMIT_INFINITY_WALL_MS));
}
