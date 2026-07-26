// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream opaque_reveal.rs.
//
// This file covers the Rust-valid source-extraction slice TrustVc supports
// today: opaque spec-function bodies are hidden until reveal, non-opaque spec
// bodies remain visible, reveal can make concrete and simple generic opaque
// spec calls provable, exact reveal names do not reveal sibling functions, and
// unsupported reveal/hide syntax fails closed. It intentionally does not claim
// full upstream parity for hide, reveal_with_fuel, trait/inherent paths,
// trailing-comma reveal syntax, qualified module path resolution, closed/open
// visibility, cross-crate fuel, or diagnostic text.

#![allow(dead_code)]

pub const UPSTREAM_OPAQUE_REVEAL_RS_PINNED_CASES: &[&str] = &[
    "trait_fn_free_fn_nogeneric",
    "trait_fn_inherent_fn_nogeneric",
    "trait_fn_inherent_fn_self_nogeneric",
    "trait_fn_trait_fn_nogeneric",
    "trait_fn_free_fn_generic_1",
    "trait_fn_free_fn_generic_2",
    "trait_fn_inherent_fn_generic",
    "trait_fn_inherent_fn_self_generic",
    "trait_fn_trait_fn_generic",
    "trait_fn_free_fn_expanded_invalid_1",
    "struct_fn_free_fn_1",
    "struct_fn_free_fn_2",
    "struct_fn_free_fn_3_incorrect_type",
    "mod_invalid_1",
    "struct_fn_free_fn_4_not_found",
    "across_modules_and_use",
    "across_crates",
    "trailing_commas",
    "regression_704_impl_arg",
    "regression_907_reveal_u64_1",
    "regression_907_reveal_u64_2",
    "regression_925_reveal_loop_1",
    "regression_925_reveal_loop_2",
    "no_broadcast_use_as_reveal_1",
    "no_broadcast_use_as_reveal_2",
    "reveal_closed_error",
    "reveal_closed_not_error",
    "reveal_function_that_isnt_recursive_but_has_decreases_issue644",
];

pub fn upstream_opaque_reveal_rs_pinned_cases() -> &'static [&'static str] {
    UPSTREAM_OPAQUE_REVEAL_RS_PINNED_CASES
}

pub type OpaqueRevealExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type OpaqueRevealFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const OPAQUE_REVEAL_RS_EXPECTED_CASES: &[OpaqueRevealExpectedCase] = &[
    (
        "test_opaque_reveal_makes_body_visible",
        "trait_fn_trait_fn_nogeneric direct opaque reveal body visibility",
        "verified",
        1,
    ),
    (
        "test_opaque_reveal_bool_predicate_visible",
        "trait_fn_trait_fn_nogeneric opaque bool predicate reveal",
        "verified",
        1,
    ),
    (
        "test_non_opaque_spec_body_visible_without_reveal",
        "non-opaque spec function baseline",
        "verified",
        1,
    ),
    (
        "test_reveal_non_opaque_spec_is_harmless",
        "reveal non-opaque spec function baseline",
        "verified",
        1,
    ),
    (
        "test_opaque_generic_reveal_makes_body_visible",
        "trait_fn_free_fn_generic_1 generic reveal target",
        "verified",
        1,
    ),
    (
        "test_unqualified_opaque_identity_reveal_makes_body_visible",
        "struct_fn_free_fn_2 unqualified reveal target",
        "verified",
        1,
    ),
    (
        "test_opaque_without_reveal_hides_body",
        "opaque spec function without reveal",
        "blocked",
        1,
    ),
    (
        "test_opaque_generic_without_reveal_hides_body",
        "generic opaque spec function without reveal",
        "blocked",
        1,
    ),
    (
        "test_opaque_without_reveal_reflexive_false_counterexample",
        "opaque spec function without reveal stable false reflexivity witness",
        "counterexample",
        1,
    ),
    (
        "test_opaque_generic_without_reveal_reflexive_false_counterexample",
        "generic opaque spec function without reveal stable false reflexivity witness",
        "counterexample",
        1,
    ),
    (
        "test_opaque_reveal_wrong_value_currently_unknown",
        "revealed opaque spec function false assertion",
        "blocked",
        1,
    ),
    (
        "test_opaque_bool_revealed_wrong_claim_counterexample",
        "revealed opaque bool predicate false assertion",
        "counterexample",
        1,
    ),
    (
        "test_reveal_exact_target_does_not_reveal_sibling",
        "partial reveal exact-target boundary",
        "blocked",
        1,
    ),
    (
        "test_qualified_opaque_identity_reveal_target_fails_closed",
        "across_modules_and_use qualified reveal target boundary",
        "error",
        0,
    ),
    (
        "test_inherent_opaque_reveal_target_fails_closed",
        "struct_fn_free_fn_1/2 inherent reveal target boundary",
        "error",
        0,
    ),
    (
        "test_trait_opaque_reveal_target_fails_closed",
        "trait_fn_free_fn_nogeneric trait reveal target boundary",
        "error",
        0,
    ),
    (
        // Legacy name (retained for pin stability): hide! is now supported
        // (#2785), so this is a faithful Counterexample — hide!(opaque_successor)
        // re-opaques the (already opaque) fn, and with no reveal the assert
        // `opaque_successor(4) == 5` is provable only via the hidden body, so it
        // fails. Matches upstream Verus (assertion failure on an unrevealed
        // opaque/hidden fn).
        "test_hide_macro_currently_fails_closed",
        "trailing_commas hide syntax boundary",
        "counterexample",
        1,
    ),
    (
        "test_reveal_with_fuel_currently_fails_closed",
        "across_crates/reveal_function_that_isnt_recursive_but_has_decreases_issue644 fuel boundary",
        "error",
        0,
    ),
    (
        "test_reveal_target_trailing_comma_currently_fails_closed",
        "trailing_commas reveal syntax boundary",
        "error",
        0,
    ),
    (
        "test_reveal_unknown_target_fails_closed",
        "struct_fn_free_fn_4_not_found missing reveal target boundary",
        "error",
        0,
    ),
];

pub fn opaque_reveal_rs_expected_cases() -> &'static [OpaqueRevealExpectedCase] {
    OPAQUE_REVEAL_RS_EXPECTED_CASES
}

pub const OPAQUE_REVEAL_RS_FAIL_CLOSED_ERROR_PATTERNS: &[OpaqueRevealFailClosedErrorPatterns] = &[
    (
        "test_qualified_opaque_identity_reveal_target_fails_closed",
        &[
            "supports only unqualified function names",
            "opaque_reveal_qualified_target :: opaque_identity",
        ],
    ),
    (
        "test_inherent_opaque_reveal_target_fails_closed",
        &[
            "supports only unqualified function names",
            "OpaqueRevealWitness :: always",
        ],
    ),
    (
        "test_trait_opaque_reveal_target_fails_closed",
        &["Failed to parse reveal!() target"],
    ),
    // test_hide_macro_currently_fails_closed is no longer a fail-closed error
    // case (hide! is supported, #2785) — it is a Counterexample, so it carries
    // no error patterns and is absent from this table.
    (
        "test_reveal_with_fuel_currently_fails_closed",
        &[
            "Unsupported reveal_with_fuel!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "test_reveal_target_trailing_comma_currently_fails_closed",
        &["Failed to parse reveal!() target"],
    ),
    (
        "test_reveal_unknown_target_fails_closed",
        &[
            "reveal!(opaque_missing_successor) references unknown function",
            "Available functions",
        ],
    ),
];

pub fn opaque_reveal_rs_fail_closed_error_patterns(
) -> &'static [OpaqueRevealFailClosedErrorPatterns] {
    OPAQUE_REVEAL_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_successor(x: u64) -> u64 {
    x + 1
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_sibling_successor(x: u64) -> u64 {
    x + 1
}

#[trust_vc::spec]
fn visible_successor(x: u64) -> u64 {
    x + 1
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_truth() -> bool {
    true
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_tagged_successor<T>(_tag: T, x: u64) -> u64 {
    x + 1
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn opaque_identity(x: u64) -> u64 {
    x
}

mod opaque_reveal_qualified_target {
    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn opaque_identity(x: u64) -> u64 {
        x
    }
}

struct OpaqueRevealWitness;

trait OpaqueRevealTrait {
    fn trait_always() -> bool;
}

impl OpaqueRevealWitness {
    #[trust_vc::spec]
    #[trust_vc::opaque]
    fn always() -> bool {
        true
    }
}

impl OpaqueRevealTrait for OpaqueRevealWitness {
    fn trait_always() -> bool {
        true
    }
}

#[trust_vc::ensures(true)]
fn test_opaque_reveal_makes_body_visible() {
    let _ = opaque_successor(0u64);
    trust_vc::reveal!(opaque_successor);
    trust_vc::assert!(opaque_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_opaque_reveal_bool_predicate_visible() {
    let _ = opaque_truth();
    trust_vc::reveal!(opaque_truth);
    trust_vc::assert!(opaque_truth());
}

#[trust_vc::ensures(true)]
fn test_opaque_without_reveal_hides_body() {
    let _ = opaque_successor(0u64);
    trust_vc::assert!(opaque_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_opaque_without_reveal_reflexive_false_counterexample() {
    let _ = opaque_successor(0u64);
    trust_vc::assert!(opaque_successor(4u64) != opaque_successor(4u64));
}

#[trust_vc::ensures(true)]
fn test_non_opaque_spec_body_visible_without_reveal() {
    let _ = visible_successor(0u64);
    trust_vc::assert!(visible_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_reveal_non_opaque_spec_is_harmless() {
    let _ = visible_successor(0u64);
    trust_vc::reveal!(visible_successor);
    trust_vc::assert!(visible_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_opaque_generic_reveal_makes_body_visible() {
    let _ = opaque_tagged_successor::<bool>(true, 0u64);
    trust_vc::reveal!(opaque_tagged_successor::<bool>);
    trust_vc::assert!(opaque_tagged_successor::<bool>(true, 4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_opaque_generic_without_reveal_hides_body() {
    let _ = opaque_tagged_successor::<bool>(true, 0u64);
    trust_vc::assert!(opaque_tagged_successor::<bool>(true, 4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_opaque_generic_without_reveal_reflexive_false_counterexample() {
    let _ = opaque_tagged_successor::<bool>(true, 0u64);
    trust_vc::assert!(
        opaque_tagged_successor::<bool>(true, 4u64) != opaque_tagged_successor::<bool>(true, 4u64)
    );
}

#[trust_vc::ensures(true)]
fn test_unqualified_opaque_identity_reveal_makes_body_visible() {
    let _ = opaque_identity(0u64);
    trust_vc::reveal!(opaque_identity);
    trust_vc::assert!(opaque_identity(4u64) == 4u64);
}

#[trust_vc::ensures(true)]
fn test_opaque_reveal_wrong_value_currently_unknown() {
    let _ = opaque_successor(0u64);
    trust_vc::reveal!(opaque_successor);
    trust_vc::assert!(opaque_successor(4u64) == 6u64);
}

#[trust_vc::ensures(true)]
fn test_opaque_bool_revealed_wrong_claim_counterexample() {
    let _ = opaque_truth();
    trust_vc::reveal!(opaque_truth);
    trust_vc::assert!(!opaque_truth());
}

#[trust_vc::ensures(true)]
fn test_reveal_exact_target_does_not_reveal_sibling() {
    let _ = opaque_successor(0u64);
    let _ = opaque_sibling_successor(0u64);
    trust_vc::reveal!(opaque_successor);
    trust_vc::assert!(opaque_sibling_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_qualified_opaque_identity_reveal_target_fails_closed() {
    let _ = opaque_identity(0u64);
    trust_vc::reveal!(opaque_reveal_qualified_target::opaque_identity);
    trust_vc::assert!(opaque_identity(4u64) == 4u64);
}

#[trust_vc::ensures(true)]
fn test_inherent_opaque_reveal_target_fails_closed() {
    let _ = OpaqueRevealWitness::always();
    trust_vc::reveal!(OpaqueRevealWitness::always);
    trust_vc::assert!(OpaqueRevealWitness::always());
}

#[trust_vc::ensures(true)]
fn test_trait_opaque_reveal_target_fails_closed() {
    trust_vc::reveal!(<OpaqueRevealWitness as OpaqueRevealTrait>::trait_always);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
// Legacy name (kept for pin stability). hide! is supported (#2785): hiding the
// (opaque) fn with no reveal leaves `opaque_successor(4) == 5` provable only via
// the hidden body → Counterexample, matching upstream Verus.
fn test_hide_macro_currently_fails_closed() {
    let _ = opaque_successor(0u64);
    trust_vc::hide!(opaque_successor);
    trust_vc::assert!(opaque_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_reveal_with_fuel_currently_fails_closed() {
    let _ = opaque_successor(0u64);
    trust_vc::reveal_with_fuel!(opaque_successor, 2);
    trust_vc::assert!(opaque_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_reveal_target_trailing_comma_currently_fails_closed() {
    let _ = opaque_successor(0u64);
    trust_vc::reveal!(opaque_successor,);
    trust_vc::assert!(opaque_successor(4u64) == 5u64);
}

#[trust_vc::ensures(true)]
fn test_reveal_unknown_target_fails_closed() {
    let _ = opaque_successor(0u64);
    trust_vc::reveal!(opaque_missing_successor);
    trust_vc::assert!(opaque_successor(4u64) == 5u64);
}
