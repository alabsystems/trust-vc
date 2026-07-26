// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/traits.rs`.
//
// This file intentionally covers only the trait surfaces that can be expressed
// through the current Rust-valid TrustVc syntax:
// - A default trait method with a return contract.
// - A concrete impl inheriting a trait method contract.
// - A generic trait-bound caller using the inherited method postcondition.
//
// The upstream file remains an unsupported gap. Broader Verus trait surfaces
// such as associated types, specialization, cyclic trait requirements,
// no_method_body diagnostics, const generics, and full trait dispatch parity are
// not claimed here.

pub const TRAITS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("default_returns_input", "test_supported_9", "verified", 1),
    (
        "trait_impl_inherits_returns_contract_verified",
        "trait_impl_inherits_returns_contract",
        "verified",
        1,
    ),
    (
        "generic_trait_bound_uses_trait_method_contract_verified",
        "test_ok_where_clause",
        "verified",
        1,
    ),
    (
        "default_trait_method_false_assert_counterexample",
        "test_supported_9",
        "counterexample",
        1,
    ),
    (
        "trait_impl_conflicting_returns_clause_currently_blocked",
        "trait_impl_conflicting_returns_clause",
        "error",
        0,
    ),
];

pub fn traits_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    TRAITS_RS_EXPECTED_CASES
}

pub const TRAITS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "trait_impl_conflicting_returns_clause_currently_blocked",
    &["a `returns` clause cannot be declared on both a trait method impl and its declaration"],
)];

pub fn traits_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    TRAITS_RS_EXPECTED_ERROR_PATTERNS
}

struct TraitsGood;
struct TraitsBad;

#[trust_vc::trait_spec]
trait TraitsDefaultReturnsInput {
    #[trust_vc::contract(
        ensures(result == input),
        returns(result),
    )]
    fn default_returns_input(input: u8) -> u8 {
        input
    }
}

#[trust_vc::trait_impl]
impl TraitsDefaultReturnsInput for TraitsGood {}

#[trust_vc::trait_spec]
trait TraitsInheritedReturnsTrue {
    #[trust_vc::returns(true)]
    fn trait_impl_inherits_returns_contract_verified() -> bool;
}

#[trust_vc::trait_impl]
impl TraitsInheritedReturnsTrue for TraitsGood {
    fn trait_impl_inherits_returns_contract_verified() -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait TraitsDefaultAssertFalse {
    #[trust_vc::ensures(true)]
    fn default_trait_method_false_assert_counterexample() {
        trust_vc::assert!(false);
    }
}

#[trust_vc::trait_spec]
trait TraitsGenericBoundDefault: Sized {
    #[trust_vc::returns(true)]
    fn default_trait_bound_returns_true(self) -> bool {
        true
    }
}

#[trust_vc::trait_impl]
impl TraitsGenericBoundDefault for bool {}

#[trust_vc::trait_spec]
trait TraitsConflictingReturns {
    #[trust_vc::returns(true)]
    fn trait_impl_conflicting_returns_clause_currently_blocked() -> bool;
}

#[trust_vc::trait_impl]
impl TraitsConflictingReturns for TraitsBad {
    #[trust_vc::returns(false)]
    fn trait_impl_conflicting_returns_clause_currently_blocked() -> bool {
        false
    }
}

#[trust_vc::ensures(true)]
fn generic_trait_bound_uses_trait_method_contract_verified<T: TraitsGenericBoundDefault>(
    value: T,
) {
    let returned = value.default_trait_bound_returns_true();
    trust_vc::assert!(returned);
}
