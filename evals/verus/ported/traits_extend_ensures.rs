// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/traits_extend_ensures.rs`.
//
// The upstream file checks that impl methods can extend trait method
// postconditions and that callers can use both sides of that contract. This
// scout slice keeps the manifest classification as unsupported-gap and covers
// only Rust-valid TrustVc evidence:
// - A trait method postcondition plus an additional impl postcondition both
//   verify for a concrete implementation.
// - A separate numeric trait/impl postcondition extension witness verifies
//   without relying on `returns` sugar.
// - An implementation for a trait method with no declaration-side
//   postcondition violates only the added impl postcondition and is rejected.
// - A concrete caller USING the combined extension surface via a no-`self` UFCS
//   associated call now verifies both the trait-inherited and impl-extended
//   postconditions (`caller_uses_..._verified`), and an assertion outside the
//   extended postcondition is soundly rejected with a counterexample
//   (`caller_outside_..._counterexample`).
// - Verus-style named return extension via returns binders remains a
//   fail-closed boundary when both the trait method and impl method declare
//   `returns`.
//
// Full upstream parity is not claimed. Tuple return-pattern binders, proof/spec
// mode variants, argument/result renaming, generic tuple payloads, and
// Compare-style spec predicates remain unsupported, unrepresented, or
// fail-closed here.

#![allow(dead_code)]

pub const TRAITS_EXTEND_ENSURES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "trait_and_impl_postconditions_extend_verified",
        "test_basic",
        "verified",
        1,
    ),
    (
        "trait_and_impl_postconditions_extended_u8",
        "test_basic",
        "verified",
        1,
    ),
    (
        "caller_uses_inherited_and_extended_postconditions_verified",
        "test_basic",
        "verified",
        1,
    ),
    (
        "trait_impl_extended_postcondition_counterexample",
        "test_basic2",
        "counterexample",
        1,
    ),
    (
        "caller_outside_extended_postcondition_counterexample",
        "test_basic",
        "counterexample",
        1,
    ),
    (
        "trait_and_impl_returns_clause_extension_currently_blocked",
        "test_basic",
        "error",
        0,
    ),
];

pub const TRAITS_EXTEND_ENSURES_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "trait_and_impl_returns_clause_extension_currently_blocked",
        &["a `returns` clause cannot be declared on both a trait method impl and its declaration"],
    ),
];

pub fn traits_extend_ensures_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    TRAITS_EXTEND_ENSURES_RS_EXPECTED_CASES
}

pub fn traits_extend_ensures_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    TRAITS_EXTEND_ENSURES_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::trait_spec]
trait TraitDeclReturnsTrue {
    #[trust_vc::ensures(result)]
    fn trait_and_impl_postconditions_extend_verified() -> bool;
}

#[trust_vc::trait_impl]
impl TraitDeclReturnsTrue for bool {
    #[trust_vc::returns(true)]
    fn trait_and_impl_postconditions_extend_verified() -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait TraitDeclResultAtLeastTen {
    #[trust_vc::ensures(result >= 10u8)]
    fn trait_and_impl_postconditions_extended_u8() -> u8;
}

#[trust_vc::trait_impl]
impl TraitDeclResultAtLeastTen for bool {
    #[trust_vc::ensures(result <= 20u8)]
    fn trait_and_impl_postconditions_extended_u8() -> u8 {
        15u8
    }
}

// Caller-side USE of the inherited (trait) + extended (impl) postconditions
// through a no-`self` UFCS associated call now RESOLVES: the impl body axiom
// `result == 15u8` is registered for `<bool as ...>::extended_u8()`, so both the
// trait-inherited `>= 10` and the impl-extended `<= 20` follow at the call site.
#[trust_vc::ensures(true)]
fn caller_uses_inherited_and_extended_postconditions_verified() {
    let value: u8 =
        <bool as TraitDeclResultAtLeastTen>::trait_and_impl_postconditions_extended_u8();
    trust_vc::assert!(value >= 10u8);
    trust_vc::assert!(value <= 20u8);
}

// The same call site with an assertion OUTSIDE the extended postcondition
// (`value > 20`, but the body is `15u8`) is soundly rejected with a
// counterexample — the body axiom fixes `value == 15`.
#[trust_vc::ensures(true)]
fn caller_outside_extended_postcondition_counterexample() {
    let value: u8 =
        <bool as TraitDeclResultAtLeastTen>::trait_and_impl_postconditions_extended_u8();
    trust_vc::assert!(value > 20u8);
}

#[trust_vc::trait_spec]
trait TraitDeclNoPostconditionForBadImpl {
    fn trait_impl_extended_postcondition_counterexample() -> bool;
}

#[trust_vc::trait_impl]
impl TraitDeclNoPostconditionForBadImpl for bool {
    #[trust_vc::returns(true)]
    fn trait_impl_extended_postcondition_counterexample() -> bool {
        false
    }
}

#[trust_vc::trait_spec]
trait TraitReturnsBinderExtensionBoundary {
    #[trust_vc::contract(ensures(result >= 10u8), returns(result))]
    fn trait_and_impl_returns_clause_extension_currently_blocked() -> u8;
}

#[trust_vc::trait_impl]
impl TraitReturnsBinderExtensionBoundary for bool {
    #[trust_vc::contract(ensures(result <= 20u8), returns(result))]
    fn trait_and_impl_returns_clause_extension_currently_blocked() -> u8 {
        15u8
    }
}
