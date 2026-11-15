// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream adts_generics.rs.
//
// The upstream file mixes Rust-valid generic ADT code with Verus-only proof,
// opaque, trigger, and field-erasure syntax. This first slice keeps the
// extractable behavior small: generic struct field substitution/projection,
// generic spec identity over projected fields, and generic enum construction.

pub type AdtsGenericsRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type AdtsGenericsRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const ADTS_GENERICS_RS_EXPECTED_CASES: &[AdtsGenericsRsExpectedCase] = &[
    (
        "generic_struct_projection_preserves_equal_payloads",
        "test_generic_adt_eq",
        "verified",
        2,
    ),
    (
        "generic_struct_u8_field_nonnegative",
        "test_box_unbox_struct",
        "verified",
        2,
    ),
    (
        "generic_spec_identity_preserves_projected_field",
        "test_refinements1",
        "verified",
        3,
    ),
    (
        "generic_enum_constructor_smoke",
        "test_box_enum",
        "verified",
        2,
    ),
    (
        "generic_enum_match_extracts_payload_verified",
        "test_box_enum",
        "verified",
        2,
    ),
    (
        "generic_struct_projection_wrong_value_compute_counterexample",
        "test_generic_adt_eq",
        "counterexample",
        2,
    ),
    (
        "generic_tuple_struct_destructure_currently_error",
        "test_erase1",
        "verified",
        3,
    ),
    // Upstream `test_generic_adt_eq` / `test_generic_adt_u8` verbatim: the
    // engine refutes each with a model (re-pinned 2026-09-13; the former
    // `*_currently_unknown` twins below are the same refutations).
    (
        "test_generic_adt_eq_counterexample",
        "test_generic_adt_eq",
        "counterexample",
        3,
    ),
    (
        "test_generic_adt_u8_counterexample",
        "test_generic_adt_u8",
        "counterexample",
        2,
    ),
];

// The generic tuple-struct destructure gap has since closed (monomorphized
// tuple-field selector support): `let TupleThing(first, second) = value;` now
// binds each pattern variable to the constructor's field, so the true field
// claims verify soundly. No case fails closed on an error message any more.
pub const ADTS_GENERICS_RS_FAIL_CLOSED_ERROR_PATTERNS: &[AdtsGenericsRsFailClosedErrorPatterns] =
    &[];

pub fn adts_generics_rs_expected_cases() -> &'static [AdtsGenericsRsExpectedCase] {
    ADTS_GENERICS_RS_EXPECTED_CASES
}

pub fn adts_generics_rs_fail_closed_error_patterns(
) -> &'static [AdtsGenericsRsFailClosedErrorPatterns] {
    ADTS_GENERICS_RS_FAIL_CLOSED_ERROR_PATTERNS
}

struct Thing<A> {
    a: A,
}

struct Pair<A, B> {
    a: A,
    b: B,
}

struct OutOfOrderXY {
    tz: OutOfOrderTZ,
}

struct OutOfOrderTZ {
    p: (u64, u64),
}

enum Choice<A> {
    First(A),
    Empty,
}

struct TupleThing<A, B>(A, B);

#[trust_vc::spec]
fn generic_id<A>(value: A) -> A {
    value
}

#[trust_vc::ensures(result == value)]
fn generic_exec_id<A>(value: A) -> A {
    value
}

#[trust_vc::ensures(true)]
fn generic_struct_projection_preserves_equal_payloads(value: u64) {
    let t1 = Thing::<u64> { a: value };
    let t2 = Thing::<u64> { a: value };
    let a1: u64 = t1.a;
    let a2: u64 = t2.a;

    trust_vc::assert!(a1 == a2);
}

#[trust_vc::ensures(true)]
fn generic_struct_projection_wrong_inequality_counterexample(value: u64) {
    let t1 = Thing::<u64> { a: value };
    let t2 = Thing::<u64> { a: value };
    let a1: u64 = t1.a;
    let a2: u64 = t2.a;

    trust_vc::assert!(a1 != a2);
}

// Upstream `test_generic_adt_eq::one`, verbatim on the native surface: the
// equal-payload assertion holds and the inequality on the same projections is
// the single upstream failure (`assert(a1 != a2); // FAILS`).
#[trust_vc::ensures(true)]
fn test_generic_adt_eq_counterexample(v: u64) {
    let t1 = Thing::<u64> { a: v };
    let t2 = Thing::<u64> { a: v };
    let a1: u64 = t1.a;
    let a2: u64 = t2.a;
    trust_vc::assert!(a1 == a2);
    trust_vc::assert!(a1 != a2); // FAILS
}

// Upstream `test_generic_adt_u8::two`, verbatim: a `Thing<u8>` payload has no
// lower bound of 1 (`assert(v.a >= 1); // FAILS`).
#[trust_vc::ensures(true)]
fn test_generic_adt_u8_counterexample(v: Thing<u8>) {
    trust_vc::assert!(v.a >= 1u8); // FAILS
}

#[trust_vc::ensures(true)]
fn generic_struct_u8_field_nonnegative(value: Thing<u8>) {
    trust_vc::assert!(value.a >= 0u8);
}

#[trust_vc::ensures(true)]
fn generic_struct_u8_field_at_least_one_counterexample(value: Thing<u8>) {
    trust_vc::assert!(value.a >= 1u8);
}

#[trust_vc::ensures(true)]
fn generic_spec_identity_preserves_projected_field() {
    let value = Thing::<u64> { a: 3u64 };

    trust_vc::assert!(generic_id::<u64>(value.a) >= 0u64);
    trust_vc::assert!(value.a >= 0u64);
}

#[trust_vc::ensures(true)]
fn generic_exec_identity_struct_field_currently_error() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_exec_id::<Pair<u64, u8>>(value);

    trust_vc::assert!(projected.a == 9u64);
    trust_vc::assert!(projected.b == 2u8);
}

#[trust_vc::ensures(true)]
fn generic_spec_identity_struct_field_currently_error() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_id::<Pair<u64, u8>>(value);

    trust_vc::assert!(projected.a == 9u64);
    trust_vc::assert!(projected.b == 2u8);
}

#[trust_vc::ensures(true)]
fn generic_spec_identity_wrong_struct_field_currently_rejected() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_id::<Pair<u64, u8>>(value);

    trust_vc::assert!(projected.a == 10u64);
}

#[trust_vc::ensures(true)]
fn generic_struct_projection_wrong_value_compute_counterexample() {
    trust_vc::assert_by_compute!(
        Thing::<u64> { a: 7u64 }.a == 8u64;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn generic_enum_constructor_smoke(payload: u64) {
    let _choice = Choice::<u64>::First(payload);

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn generic_tuple_struct_field_projection_currently_unknown() {
    let value = TupleThing::<bool, bool>(true, false);

    trust_vc::assert!(value.0);
    trust_vc::assert!(!value.1);
}

#[trust_vc::ensures(true)]
fn generic_named_struct_field_projection_verified() {
    let value = Pair::<bool, bool> { a: true, b: false };

    trust_vc::assert!(value.a);
    trust_vc::assert!(!value.b);
}

#[trust_vc::ensures(true)]
fn generic_named_struct_numeric_field_projection_verified() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };

    trust_vc::assert!(value.a == 9u64);
    trust_vc::assert!(value.b == 2u8);
}

#[trust_vc::ensures(true)]
fn generic_named_struct_destructure_currently_error() {
    let value = Pair::<bool, bool> { a: true, b: false };
    let Pair {
        a: first,
        b: second,
    } = value;

    trust_vc::assert!(first);
    trust_vc::assert!(!second);
}

#[trust_vc::ensures(true)]
fn out_of_order_nested_struct_construction_smoke() {
    let _value = OutOfOrderXY {
        tz: OutOfOrderTZ { p: (3u64, 4u64) },
    };

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn out_of_order_nested_tuple_projection_currently_error() {
    let value = OutOfOrderXY {
        tz: OutOfOrderTZ { p: (3u64, 4u64) },
    };

    trust_vc::assert!(value.tz.p.0 == 3u64);
    trust_vc::assert!(value.tz.p.1 == 4u64);
}

#[trust_vc::ensures(result)]
fn generic_enum_match_extracts_payload_verified() -> bool {
    match Choice::<u64>::First(11u64) {
        Choice::First(payload) => payload == 11u64,
        Choice::Empty => false,
    }
}

#[trust_vc::ensures(true)]
fn generic_enum_variant_helpers_currently_error(value: Choice<u64>) {
    trust_vc::assert!(value.is_First());
}

#[trust_vc::ensures(true)]
fn generic_tuple_struct_destructure_currently_error() {
    let value = TupleThing::<bool, bool>(true, false);
    let TupleThing(first, second) = value;

    trust_vc::assert!(first);
    trust_vc::assert!(!second);
}
