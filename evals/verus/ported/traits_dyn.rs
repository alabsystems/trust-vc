// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/traits_dyn.rs`.
//
// This file intentionally keeps the upstream manifest entry as an
// unsupported-gap. The upstream file exercises Verus dyn trait objects,
// object-safe spec/proof methods, ToDyn coercions, boxed trait objects,
// object-safety diagnostics, cycles, and dyn unsupported diagnostics.
//
// This scout slice pins only Rust-valid TrustVc evidence:
// - A trait method contract can be used through a generic static-dispatch
//   boundary.
// - A wrong assertion against that inherited method contract is rejected.
// - A direct `&dyn Trait` dynamic-dispatch boundary fails closed instead of
//   being accepted as replacement evidence.
// - A boxed `Box<dyn Trait>` dynamic-dispatch boundary also fails closed.
// - A `Self: Sized` method contract verifies through static dispatch but fails
//   closed through a dyn receiver rather than being accepted as dyn support.
// - A generic-method trait-object boundary fails closed while object-safety and
//   dyn method lowering remain unsupported.

#![allow(dead_code)]

pub type TraitsDynRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type TraitsDynRsExpectedErrorPatterns = (&'static str, &'static [&'static str]);

pub const TRAITS_DYN_RS_EXPECTED_CASES: &[TraitsDynRsExpectedCase] = &[
    (
        "traits_dyn_trait_bound_static_dispatch_verified",
        "test_dyn_generic",
        "verified",
        1,
    ),
    (
        "traits_dyn_sized_only_static_dispatch_verified",
        "test_dyn_generic",
        "verified",
        1,
    ),
    (
        "traits_dyn_sized_default_false_assert_counterexample",
        "dyn_proof_must_be_inhabited_sized",
        "counterexample",
        1,
    ),
    (
        "traits_dyn_trait_object_dispatch_currently_blocked",
        "test_dyn",
        "error",
        0,
    ),
    (
        "traits_dyn_boxed_trait_object_dispatch_currently_blocked",
        "test_dyn2",
        "error",
        0,
    ),
    (
        "traits_dyn_sized_only_trait_object_dispatch_currently_blocked",
        "test_dyn_generic",
        "error",
        0,
    ),
    (
        "traits_dyn_generic_method_trait_object_not_object_safe_currently_blocked",
        "test_dyn_generic",
        "error",
        0,
    ),
];

pub const TRAITS_DYN_RS_EXPECTED_ERROR_PATTERNS: &[TraitsDynRsExpectedErrorPatterns] = &[
    (
        "traits_dyn_trait_object_dispatch_currently_blocked",
        &["dyn"],
    ),
    (
        "traits_dyn_boxed_trait_object_dispatch_currently_blocked",
        &["dyn"],
    ),
    (
        "traits_dyn_sized_only_trait_object_dispatch_currently_blocked",
        &["unsupported method"],
    ),
    (
        "traits_dyn_generic_method_trait_object_not_object_safe_currently_blocked",
        &["unsupported method"],
    ),
];

pub fn traits_dyn_rs_expected_cases() -> &'static [TraitsDynRsExpectedCase] {
    TRAITS_DYN_RS_EXPECTED_CASES
}

pub fn traits_dyn_rs_expected_error_patterns() -> &'static [TraitsDynRsExpectedErrorPatterns] {
    TRAITS_DYN_RS_EXPECTED_ERROR_PATTERNS
}

struct TraitsDynGood;

struct TraitsDynSizedOnlyGood;

#[trust_vc::trait_spec]
trait TraitsDynReturnsTrue {
    #[trust_vc::returns(true)]
    fn traits_dyn_contract_value(&self) -> bool;
}

#[trust_vc::trait_impl]
impl TraitsDynReturnsTrue for TraitsDynGood {
    fn traits_dyn_contract_value(&self) -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait TraitsDynSizedFalseAssert {
    #[trust_vc::ensures(true)]
    fn traits_dyn_sized_default_false_assert_counterexample()
    where
        Self: Sized,
    {
        trust_vc::assert!(false);
    }
}

#[trust_vc::trait_spec]
trait TraitsDynSizedOnlyReturnsSeven {
    #[trust_vc::returns(7u32)]
    fn traits_dyn_sized_only_value(&self) -> u32
    where
        Self: Sized;
}

#[trust_vc::trait_impl]
impl TraitsDynSizedOnlyReturnsSeven for TraitsDynSizedOnlyGood {
    fn traits_dyn_sized_only_value(&self) -> u32 {
        7u32
    }
}

trait TraitsDynGenericMethodNotObjectSafe {
    fn traits_dyn_generic_method<T>(&self, value: T) -> bool;
}

#[trust_vc::ensures(true)]
fn traits_dyn_trait_bound_static_dispatch_verified<T: TraitsDynReturnsTrue>(value: T) {
    let returned = value.traits_dyn_contract_value();
    trust_vc::assert!(returned);
}

#[trust_vc::ensures(true)]
fn traits_dyn_sized_only_static_dispatch_verified<T: TraitsDynSizedOnlyReturnsSeven>(value: T) {
    let returned = value.traits_dyn_sized_only_value();
    trust_vc::assert!(returned == 7u32);
}

#[trust_vc::ensures(true)]
fn traits_dyn_trait_object_dispatch_currently_blocked(value: &dyn TraitsDynReturnsTrue) {
    let returned = value.traits_dyn_contract_value();
    trust_vc::assert!(returned);
}

#[trust_vc::ensures(true)]
fn traits_dyn_boxed_trait_object_dispatch_currently_blocked(value: Box<dyn TraitsDynReturnsTrue>) {
    let returned = value.traits_dyn_contract_value();
    trust_vc::assert!(returned);
}

#[trust_vc::ensures(true)]
fn traits_dyn_sized_only_trait_object_dispatch_currently_blocked(
    value: &dyn TraitsDynSizedOnlyReturnsSeven,
) {
    let returned = value.traits_dyn_sized_only_value();
    trust_vc::assert!(returned == 7u32);
}

#[trust_vc::ensures(true)]
fn traits_dyn_generic_method_trait_object_not_object_safe_currently_blocked(
    value: &dyn TraitsDynGenericMethodNotObjectSafe,
) {
    let returned = value.traits_dyn_generic_method(0u8);
    trust_vc::assert!(returned);
}
