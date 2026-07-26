// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/opaque_types.rs`.
//
// The upstream file is centered on Verus return-position opaque types
// (`impl Trait`), associated-type projections through opaque boundaries,
// external assume_specification signatures, and diagnostics. TrustVc does not
// currently model Rust return-position `impl Trait` as a supported existential
// proof type, so this is scout coverage only and the upstream manifest entry
// remains an unsupported gap.
//
// This Rust-valid subset records the boundary TrustVc can express today:
// - a trait method contract can be used through a generic type-bound boundary;
// - a trait method contract can flow through an associated `Output = int`
//   projection argument on a generic bound;
// - bad trait-method claims are rejected; and
// - direct return-position `impl Trait` boundaries fail closed, including an
//   associated-type-constrained opaque boundary.

#![allow(dead_code)]

use trust_vc_types::int;

pub type OpaqueTypesExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type OpaqueTypesBlockedCase = (&'static str, &'static str, &'static str, usize);

pub const OPAQUE_TYPES_RS_EXPECTED_CASES: &[OpaqueTypesExpectedCase] = &[
    (
        "opaque_types_trait_method_contract_verified",
        "test_return_opaque_type_allows_trait_functions",
        "verified",
        1,
    ),
    (
        "opaque_types_associated_output_projection_verified",
        "test_return_opaque_type_reveal_real_type",
        "verified",
        1,
    ),
    (
        "opaque_types_trait_impl_wrong_return_counterexample",
        "test_return_opaque_type_allows_trait_functions",
        "counterexample",
        1,
    ),
    (
        "opaque_types_associated_output_wrong_return_counterexample",
        "test_return_opaque_type_reveal_real_type",
        "counterexample",
        1,
    ),
];

pub const OPAQUE_TYPES_RS_BLOCKED_CASES: &[OpaqueTypesBlockedCase] = &[
    (
        "opaque_types_return_impl_trait_fails_closed",
        "test_return_opaque_type",
        "blocked",
        0,
    ),
    (
        "opaque_types_return_impl_trait_with_assoc_fails_closed",
        "test_return_opaque_type_reveal_real_type",
        "blocked",
        0,
    ),
];

pub fn opaque_types_rs_expected_cases() -> &'static [OpaqueTypesExpectedCase] {
    OPAQUE_TYPES_RS_EXPECTED_CASES
}

pub fn opaque_types_rs_blocked_cases() -> &'static [OpaqueTypesBlockedCase] {
    OPAQUE_TYPES_RS_BLOCKED_CASES
}

#[trust_vc::trait_spec]
trait OpaqueTypesDummyTrait {
    #[trust_vc::returns(false)]
    fn opaque_types_trait_flag(&self) -> bool;
}

#[trust_vc::trait_impl]
impl OpaqueTypesDummyTrait for bool {
    fn opaque_types_trait_flag(&self) -> bool {
        false
    }
}

#[trust_vc::trait_spec]
trait OpaqueTypesBadTrait {
    #[trust_vc::returns(true)]
    fn opaque_types_trait_impl_wrong_return_counterexample() -> bool;
}

#[trust_vc::trait_impl]
impl OpaqueTypesBadTrait for bool {
    fn opaque_types_trait_impl_wrong_return_counterexample() -> bool {
        false
    }
}

#[trust_vc::trait_spec]
trait OpaqueTypesAssociatedOutputTrait {
    type Output;

    #[trust_vc::returns(false)]
    fn opaque_types_associated_output(&self, output: Self::Output) -> bool;
}

#[trust_vc::trait_impl]
impl OpaqueTypesAssociatedOutputTrait for bool {
    type Output = int;

    fn opaque_types_associated_output(&self, output: int) -> bool {
        let _ = output;
        false
    }
}

#[trust_vc::trait_spec]
trait OpaqueTypesAssociatedBadTrait {
    type Output;

    #[trust_vc::returns(true)]
    fn opaque_types_associated_output_wrong_return_counterexample(output: Self::Output) -> bool;
}

#[trust_vc::trait_impl]
impl OpaqueTypesAssociatedBadTrait for bool {
    type Output = int;

    fn opaque_types_associated_output_wrong_return_counterexample(output: int) -> bool {
        let _ = output;
        false
    }
}

#[trust_vc::ensures(true)]
fn opaque_types_trait_method_contract_verified<T: OpaqueTypesDummyTrait>(value: T) {
    let returned = value.opaque_types_trait_flag();
    trust_vc::assert!(returned == false);
}

#[trust_vc::ensures(true)]
fn opaque_types_associated_output_projection_verified<
    T: OpaqueTypesAssociatedOutputTrait<Output = int>,
>(
    value: T,
    witness: int,
) {
    let returned = value.opaque_types_associated_output(witness);
    trust_vc::assert!(returned == false);
}

#[trust_vc::ensures(true)]
fn opaque_types_return_impl_trait_fails_closed() -> impl OpaqueTypesDummyTrait {
    true
}

#[trust_vc::ensures(true)]
fn opaque_types_return_impl_trait_with_assoc_fails_closed(
) -> impl OpaqueTypesAssociatedOutputTrait<Output = int> {
    true
}
