// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/safe_api.rs`.
//
// Upstream safe_api.rs is mostly a `-V check-api-safety` diagnostic suite:
// public safe functions with nontrivial requires clauses, trait method
// postconditions, unwind/invariant clauses, unsafe/private exemptions, and
// higher-order function smuggling boundaries. TrustVc does not currently expose
// an equivalent whole-API safety checker or Verus diagnostic surface.
//
// This scout slice pins the executable contract behavior TrustVc can express
// today:
// - Rust-valid public, private, and unsafe function contract witnesses;
// - satisfied call-site precondition obligations;
// - trait inherited pre/postcondition witnesses on implementations and callers;
// - stable counterexamples for false public and trait implementation assertions;
// - fail-closed boundaries for TrustVc gaps around check-api-safety diagnostics,
//   impl-side trait preconditions, direct closures, and fn pointers.
//
// The manifest entry remains `unsupported-gap`.

#![allow(dead_code)]

pub type SafeApiExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type SafeApiFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const SAFE_API_RS_EXPECTED_CASES: &[SafeApiExpectedCase] = &[
    (
        "safe_api_normal_fn_ensures_verified",
        "normal_fn_ensures_is_ok",
        "verified",
        1,
    ),
    (
        "safe_api_public_requires_contract_verified",
        "",
        "verified",
        1,
    ),
    (
        "safe_api_private_requires_contract_verified",
        "normal_fn_private_is_ok",
        "verified",
        1,
    ),
    (
        "safe_api_public_unsafe_requires_contract_verified",
        "normal_fn_unsafe_is_ok",
        "verified",
        1,
    ),
    (
        "safe_api_requires_satisfied_call_verified",
        "",
        "verified",
        1,
    ),
    (
        "safe_api_trait_requires_impl_verified",
        "",
        "verified",
        1,
    ),
    (
        "safe_api_trait_requires_satisfied_call_verified",
        "",
        "verified",
        1,
    ),
    (
        "safe_api_trait_ensures_impl_verified",
        "",
        "verified",
        1,
    ),
    (
        "safe_api_public_false_assert_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "safe_api_trait_impl_false_assert_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "safe_api_trait_impl_side_requires_currently_blocked",
        "trait_fn_impl_requires_fail",
        "error",
        0,
    ),
    (
        "safe_api_closure_application_verified",
        "opaque_closure_type_returned",
        "verified",
        3,
    ),
    (
        "safe_api_closure_application_liar_counterexample",
        "opaque_closure_type_returned",
        "counterexample",
        3,
    ),
    (
        "safe_api_fn_pointer_return_boundary_fails_closed",
        "fnsig_type_returned",
        "error",
        0,
    ),
];

pub const SAFE_API_RS_FAIL_CLOSED_ERROR_PATTERNS: &[SafeApiFailClosedErrorPatterns] = &[
    (
        "safe_api_trait_impl_side_requires_currently_blocked",
        &["trait method implementation cannot declare requires"],
    ),
    (
        "safe_api_fn_pointer_return_boundary_fails_closed",
        &[
            "Failed to lower obligation 'return_value'",
            "unresolved variable `safe_api_fn_pointer_private_target`",
        ],
    ),
];

pub fn safe_api_rs_expected_cases() -> &'static [SafeApiExpectedCase] {
    SAFE_API_RS_EXPECTED_CASES
}

pub fn safe_api_rs_fail_closed_error_patterns() -> &'static [SafeApiFailClosedErrorPatterns] {
    SAFE_API_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(result > 0u8)]
pub fn safe_api_normal_fn_ensures_verified(_x: u8) -> u8 {
    20u8
}

#[trust_vc::requires(flag)]
#[trust_vc::ensures(result == flag)]
pub fn safe_api_public_requires_contract_verified(flag: bool) -> bool {
    flag
}

#[trust_vc::ensures(true)]
pub fn safe_api_public_false_assert_counterexample() {
    trust_vc::assert!(false);
}

#[trust_vc::requires(x > 0u8)]
#[trust_vc::ensures(result == x)]
fn safe_api_private_requires_contract_verified(x: u8) -> u8 {
    x
}

#[trust_vc::requires(x > 0u8)]
#[trust_vc::ensures(result == x)]
pub unsafe fn safe_api_public_unsafe_requires_contract_verified(x: u8) -> u8 {
    x
}

#[trust_vc::ensures(true)]
fn safe_api_requires_satisfied_call_verified() {
    let observed = safe_api_public_requires_contract_verified(true);
    trust_vc::assert!(observed);
}

#[trust_vc::trait_spec]
trait SafeApiTraitRequiresBoundary {
    #[trust_vc::requires(flag)]
    #[trust_vc::ensures(result == 8u8)]
    #[trust_vc::returns(result)]
    fn safe_api_trait_requires_impl_verified(flag: bool) -> u8;
}

struct SafeApiTraitRequiresGood;
struct SafeApiTraitRequiresCallGood;

#[trust_vc::trait_impl]
impl SafeApiTraitRequiresBoundary for SafeApiTraitRequiresGood {
    fn safe_api_trait_requires_impl_verified(flag: bool) -> u8 {
        trust_vc::assert!(flag);
        8u8
    }
}

#[trust_vc::trait_spec]
trait SafeApiTraitRequiresCallBoundary {
    #[trust_vc::requires(flag)]
    #[trust_vc::ensures(result == 8u8)]
    #[trust_vc::returns(result)]
    fn safe_api_trait_requires_call(&self, flag: bool) -> u8;
}

#[trust_vc::trait_impl]
impl SafeApiTraitRequiresCallBoundary for SafeApiTraitRequiresCallGood {
    fn safe_api_trait_requires_call(&self, flag: bool) -> u8 {
        trust_vc::assert!(flag);
        8u8
    }
}

#[trust_vc::ensures(true)]
fn safe_api_trait_requires_satisfied_call_verified<T: SafeApiTraitRequiresCallBoundary>(value: &T) {
    let observed = value.safe_api_trait_requires_call(true);
    trust_vc::assert!(observed == 8u8);
}

#[trust_vc::trait_spec]
trait SafeApiTraitPostconditionBoundary {
    #[trust_vc::ensures(true)]
    fn safe_api_trait_impl_false_assert_counterexample();
}

#[trust_vc::trait_spec]
trait SafeApiTraitPostconditionOkBoundary {
    #[trust_vc::returns(true)]
    fn safe_api_trait_ensures_impl_verified() -> bool;
}

struct SafeApiTraitBadImpl;
struct SafeApiTraitGoodImpl;

#[trust_vc::trait_impl]
impl SafeApiTraitPostconditionBoundary for SafeApiTraitBadImpl {
    fn safe_api_trait_impl_false_assert_counterexample() {
        trust_vc::assert!(false);
    }
}

#[trust_vc::trait_impl]
impl SafeApiTraitPostconditionOkBoundary for SafeApiTraitGoodImpl {
    fn safe_api_trait_ensures_impl_verified() -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait SafeApiTraitImplRequiresBoundary {
    #[trust_vc::returns(1u8)]
    fn safe_api_trait_impl_side_requires_currently_blocked(flag: bool) -> u8;
}

struct SafeApiTraitImplRequiresBlocked;

#[trust_vc::trait_impl]
impl SafeApiTraitImplRequiresBoundary for SafeApiTraitImplRequiresBlocked {
    #[trust_vc::requires(flag)]
    fn safe_api_trait_impl_side_requires_currently_blocked(flag: bool) -> u8 {
        trust_vc::assert!(flag);
        1u8
    }
}

#[trust_vc::ensures(true)]
fn safe_api_closure_application_verified() {
    let f = |y: u32| y + 1u32;
    let observed = f(1u32);
    trust_vc::assert!(observed == 2u32);
}

// Liar twin (2026-09-11): the local closure adds one.
#[trust_vc::ensures(true)]
fn safe_api_closure_application_liar_counterexample() {
    let f = |y: u32| y + 1u32;
    let observed = f(1u32);
    trust_vc::assert!(observed == 3u32);
}

#[trust_vc::requires(y > 0u32)]
fn safe_api_fn_pointer_private_target(_y: u32) {}

#[trust_vc::ensures(true)]
pub fn safe_api_fn_pointer_return_boundary_fails_closed() -> fn(u32) {
    safe_api_fn_pointer_private_target
}
