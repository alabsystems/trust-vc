// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/assoc_type_impls.rs`.
//
// This slice covers Rust-valid impl-associated-type witnesses through
// `trust_vc_types::View`, a generic associated-output method constrained by an
// associated type equality, concrete associated-type projection normalization
// in both local (`let y: <S as Tr>::X`) and PARAMETER (`x: <S as Tr>::X`)
// position, a trait default-body false assertion rejection, and direct/non-
// direct view dispatch fail-closed guards. Full upstream parity is not claimed.
// Bare-generic `<T as Trait>::Assoc` projection reasoning (self is a type
// parameter), associated type equality over external traits, lifetimes,
// overlap/dispatch, and Verus diagnostic parity remain unsupported or
// fail-closed here.

#![allow(dead_code, unused_imports, unused_variables)]

use std::borrow::Cow;

use trust_vc_types::{int, View};

pub type AssocTypeImplsRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type AssocTypeImplsRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const ASSOC_TYPE_IMPLS_RS_EXPECTED_CASES: &[AssocTypeImplsRsExpectedCase] = &[
    (
        "impl_associated_view_type_via_cow_verified",
        "trait_poly",
        "verified",
        1,
    ),
    (
        "associated_type_equality_output_method_verified",
        "trait_typ_equality1",
        "verified",
        1,
    ),
    (
        "associated_type_local_projection_normalizes_to_u8_verified",
        "assoc_normalize",
        "verified",
        1,
    ),
    (
        "associated_type_trait_default_false_assert_counterexample",
        "assoc_poly_different",
        "counterexample",
        1,
    ),
    (
        "associated_type_local_projection_too_strong_bound_counterexample",
        "assoc_normalize",
        "counterexample",
        1,
    ),
    (
        "impl_associated_view_type_cow_variable_currently_errors",
        "trait_poly",
        "error",
        1,
    ),
    (
        "impl_associated_view_type_direct_currently_errors",
        "trait_poly",
        "error",
        1,
    ),
    (
        "associated_type_parameter_projection_normalizes_to_u8_verified",
        "assoc_normalize",
        "verified",
        1,
    ),
    (
        "associated_type_returning_method_client_consumes_ensures_verified",
        "ensures_projection_poly",
        "verified",
        1,
    ),
    (
        "associated_type_returning_method_client_wrong_value_counterexample",
        "ensures_projection_poly",
        "counterexample",
        1,
    ),
];

pub const ASSOC_TYPE_IMPLS_RS_FAIL_CLOSED_ERROR_PATTERNS:
    &[AssocTypeImplsRsFailClosedErrorPatterns] = &[
    (
        "impl_associated_view_type_cow_variable_currently_errors",
        &["direct Cow::Owned"],
    ),
    (
        "impl_associated_view_type_direct_currently_errors",
        &["collection operation 'view' requires a collection receiver"],
    ),
];

pub fn assoc_type_impls_rs_expected_cases() -> &'static [AssocTypeImplsRsExpectedCase] {
    ASSOC_TYPE_IMPLS_RS_EXPECTED_CASES
}

pub fn assoc_type_impls_rs_fail_closed_error_patterns(
) -> &'static [AssocTypeImplsRsFailClosedErrorPatterns] {
    ASSOC_TYPE_IMPLS_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[derive(Clone)]
struct AssocViewNum {
    x: u64,
}

impl View for AssocViewNum {
    type ViewTy = u64;

    fn view(&self) -> u64 {
        self.x
    }
}

#[trust_vc::trait_spec]
trait AssocTypeDefaultBody {
    type Value;

    fn associated_type_trait_default_false_assert_counterexample() {
        trust_vc::assert!(false);
    }
}

#[trust_vc::trait_spec]
trait AssocTypeOutputPredicate {
    type Output;

    #[trust_vc::returns(true)]
    fn associated_type_output_accepts(&self, output: Self::Output) -> bool;
}

#[trust_vc::trait_impl]
impl AssocTypeOutputPredicate for AssocViewNum {
    type Output = int;

    fn associated_type_output_accepts(&self, output: int) -> bool {
        let _ = self;
        let _ = output;
        true
    }
}

#[trust_vc::trait_spec]
trait AssocTypeNormalizeTrait {
    type X;
}

struct AssocTypeNormalizeStruct;

#[trust_vc::trait_impl]
impl AssocTypeNormalizeTrait for AssocTypeNormalizeStruct {
    type X = u8;
}

fn impl_associated_view_type_direct_currently_errors(x: u64) {
    trust_vc::assert!(AssocViewNum { x }.view() == x);
}

fn impl_associated_view_type_via_cow_verified(x: u64) {
    trust_vc::assert!(Cow::Owned(AssocViewNum { x }).view() == x);
}

fn associated_type_equality_output_method_verified<T: AssocTypeOutputPredicate<Output = int>>(
    receiver: T,
    output: int,
) {
    let accepted = receiver.associated_type_output_accepts(output);
    trust_vc::assert!(accepted == true);
}

fn associated_type_local_projection_normalizes_to_u8_verified(x: u8) {
    let y: <AssocTypeNormalizeStruct as AssocTypeNormalizeTrait>::X = x;
    trust_vc::assert!(y <= 255u8);
}

fn associated_type_local_projection_too_strong_bound_counterexample() {
    let y: <AssocTypeNormalizeStruct as AssocTypeNormalizeTrait>::X = 255u8;
    trust_vc::assert!(y < 255u8);
}

fn associated_type_parameter_projection_normalizes_to_u8_verified(
    x: <AssocTypeNormalizeStruct as AssocTypeNormalizeTrait>::X,
) {
    trust_vc::assert!(x <= 255u8);
}

fn impl_associated_view_type_cow_variable_currently_errors(c: Cow<'static, AssocViewNum>) {
    trust_vc::assert!(c.view() == c.view());
}

// Phase A3 client seam (upstream `ensures_projection_poly` family): a trait
// method whose RETURN type is the associated type `Self::V` carries an
// `ensures`, and a concrete-receiver client consumes that ensures. Before A3
// the shared per-trait method UF's return slot for a `Self::V`-typed method was
// the erased Poly/Int sort, so `result == 7` could not encode and the
// postcondition was silently dropped; A3 emits the trait ensures on the PER-IMPL
// CONCRETE fn with `Self::V` resolved to `u64` (BV64). SOUND ONLY because the
// per-impl conformance obligation proves `body ⊨ ensures(result == 7)` at these
// resolved sorts — a non-conforming body (e.g. `3u64`) is refuted on its own
// conformance obligation, so the file cannot verify on a forged axiom.
#[trust_vc::trait_spec]
trait AssocReturningEnsures {
    type V;

    #[trust_vc::ensures(result == 7u64)]
    fn produce(&self) -> Self::V;
}

struct AssocProducer;

#[trust_vc::trait_impl]
impl AssocReturningEnsures for AssocProducer {
    type V = u64;

    fn produce(&self) -> u64 {
        7u64
    }
}

fn associated_type_returning_method_client_consumes_ensures_verified(p: AssocProducer) {
    let r = p.produce();
    trust_vc::assert!(r == 7u64);
}

fn associated_type_returning_method_client_wrong_value_counterexample(p: AssocProducer) {
    let r = p.produce();
    trust_vc::assert!(r == 8u64);
}
