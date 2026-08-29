// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/external_traits.rs`.
//
// TrustVc does not currently expose a Verus-style
// `external_trait_specification` attribute. This file instead pins the
// smallest Rust-valid surface available today:
// - An impl marked `external` can still participate in local `trait_spec`
//   contract inheritance when it is also marked `trait_impl`.
// - Local trait pre/postcondition obligations are inherited by external impls.
// - Trait-bound callers can use inherited postconditions when inherited
//   preconditions hold.
// - A bad external-annotated trait impl body is rejected by assertion checking.
// - A bad external-annotated trait impl return value currently fails closed
//   instead of being accepted as satisfying an inherited postcondition.
// - A simple associated-type declaration on an external-annotated impl can
//   coexist with a concrete method contract.
// - Impl-side contract extensions on external-annotated trait impls fail closed.
// - Duplicate matching trait impl methods fail closed as ambiguous contract
//   inheritance instead of selecting an arbitrary trait spec.
//
// Broader upstream external_traits.rs coverage, including external trait
// specification declarations, associated type method return mirrors such as
// `Self::X`, rich associated type projection reasoning, trait extension specs,
// blanket import behavior, and duplicate assume_specification diagnostics, is
// not claimed here.

pub const EXTERNAL_TRAITS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "external_trait_impl_contract_verified",
        "test_trait_ok / external trait impl method specification",
        "verified",
        1,
    ),
    (
        "external_trait_requires_contract_verified",
        "test_trait3 / impl satisfies inherited requires and returns",
        "verified",
        1,
    ),
    (
        "external_trait_bound_caller_uses_inherited_ensures_verified",
        "test_trait1 / trait-bound caller uses inherited postcondition",
        "verified",
        1,
    ),
    (
        "external_trait_associated_type_declaration_verified",
        "test_trait5 / associated-type declaration coexists with concrete impl contract",
        "verified",
        1,
    ),
    (
        "external_trait_impl_false_assert_counterexample",
        "test_trait3 bad impl body in external trait implementation",
        "counterexample",
        1,
    ),
    (
        "external_trait_impl_side_requires_currently_blocked",
        "test_trait_extension / impl-side external trait contract extension boundary",
        "error",
        0,
    ),
    (
        "external_trait_duplicate_spec_currently_fails_closed",
        "test_trait_dupe / duplicate external trait specification",
        "error",
        0,
    ),
];

pub fn external_traits_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    EXTERNAL_TRAITS_RS_EXPECTED_CASES
}

pub const EXTERNAL_TRAITS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "external_trait_impl_side_requires_currently_blocked",
        &["trait method implementation cannot declare requires"],
    ),
    // Two `#[trait_impl]` blocks define this name for the same concrete type, so
    // the bare name denotes two bodies. That is now caught at function RESOLUTION
    // (`resolve_function_in_file`), one layer above the contract-inheritance check
    // that used to report it — strictly stronger, since it cannot be reached past
    // and does not depend on the impls carrying matching contract attributes.
    (
        "external_trait_duplicate_spec_currently_fails_closed",
        &["is ambiguous in", "2 definitions share that name"],
    ),
];

pub fn external_traits_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    EXTERNAL_TRAITS_RS_EXPECTED_ERROR_PATTERNS
}

struct ExternalTraitsGood;
struct ExternalTraitsRequiresGood;
struct ExternalTraitsCallerGood;
struct ExternalTraitsBad;
struct ExternalTraitsWrongPostcondition;
struct ExternalTraitsAssociatedTypeGood;
struct ExternalTraitsImplRequiresBlocked;
struct ExternalTraitsAmbiguous;

#[trust_vc::trait_spec]
trait ExternalTraitsResultAboveSeven {
    #[trust_vc::ensures(result > 7u8)]
    #[trust_vc::returns(result)]
    fn external_trait_impl_contract_verified() -> u8;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsResultAboveSeven for ExternalTraitsGood {
    fn external_trait_impl_contract_verified() -> u8 {
        8u8
    }
}

#[trust_vc::trait_spec]
trait ExternalTraitsRequiresExactEight {
    #[trust_vc::requires(flag)]
    #[trust_vc::returns(8u8)]
    fn external_trait_requires_contract_verified(flag: bool) -> u8;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsRequiresExactEight for ExternalTraitsRequiresGood {
    fn external_trait_requires_contract_verified(flag: bool) -> u8 {
        trust_vc::assert!(flag);
        8u8
    }
}

#[trust_vc::trait_spec]
trait ExternalTraitsBoundCallerContract {
    #[trust_vc::requires(flag)]
    #[trust_vc::ensures(result > 7u8)]
    #[trust_vc::returns(result)]
    fn external_trait_bound_call(&self, flag: bool) -> u8;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsBoundCallerContract for ExternalTraitsCallerGood {
    fn external_trait_bound_call(&self, flag: bool) -> u8 {
        trust_vc::assert!(flag);
        9u8
    }
}

#[trust_vc::ensures(true)]
fn external_trait_bound_caller_uses_inherited_ensures_verified<
    T: ExternalTraitsBoundCallerContract,
>(
    value: &T,
) {
    let returned = value.external_trait_bound_call(true);
    trust_vc::assert!(returned > 7u8);
}

#[trust_vc::trait_spec]
trait ExternalTraitsRejectsBadBody {
    #[trust_vc::ensures(true)]
    fn external_trait_impl_false_assert_counterexample();
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsRejectsBadBody for ExternalTraitsBad {
    fn external_trait_impl_false_assert_counterexample() {
        trust_vc::assert!(false);
    }
}

#[trust_vc::trait_spec]
trait ExternalTraitsPostconditionBoundary {
    #[trust_vc::returns(8u8)]
    fn external_trait_impl_wrong_postcondition_currently_unknown() -> u8;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsPostconditionBoundary for ExternalTraitsWrongPostcondition {
    fn external_trait_impl_wrong_postcondition_currently_unknown() -> u8 {
        6u8
    }
}

#[trust_vc::trait_spec]
trait ExternalTraitsAssociatedTypeDeclaration {
    type Value;

    #[trust_vc::ensures(result == 8u8)]
    #[trust_vc::returns(result)]
    fn external_trait_associated_type_declaration_verified() -> u8;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsAssociatedTypeDeclaration for ExternalTraitsAssociatedTypeGood {
    type Value = u8;

    fn external_trait_associated_type_declaration_verified() -> u8 {
        8u8
    }
}

#[trust_vc::trait_spec]
trait ExternalTraitsImplRequiresBoundary {
    #[trust_vc::returns(1u8)]
    fn external_trait_impl_side_requires_currently_blocked(flag: bool) -> u8;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsImplRequiresBoundary for ExternalTraitsImplRequiresBlocked {
    #[trust_vc::requires(flag)]
    fn external_trait_impl_side_requires_currently_blocked(flag: bool) -> u8 {
        trust_vc::assert!(flag);
        1u8
    }
}

#[trust_vc::trait_spec]
trait ExternalTraitsDuplicateA {
    #[trust_vc::returns(true)]
    fn external_trait_duplicate_spec_currently_fails_closed() -> bool;
}

#[trust_vc::trait_spec]
trait ExternalTraitsDuplicateB {
    #[trust_vc::returns(true)]
    fn external_trait_duplicate_spec_currently_fails_closed() -> bool;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsDuplicateA for ExternalTraitsAmbiguous {
    fn external_trait_duplicate_spec_currently_fails_closed() -> bool {
        true
    }
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl ExternalTraitsDuplicateB for ExternalTraitsAmbiguous {
    fn external_trait_duplicate_spec_currently_fails_closed() -> bool {
        true
    }
}
