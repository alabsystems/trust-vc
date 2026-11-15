//! Genuine native enum values and preservation of datatype/mode rejections.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn pair(name: &str, source: &str, claim: &str, false_claim: &str) {
    assert_eq!(source.matches(claim).count(), 1);
    for (suffix, program, outcome) in [
        ("true", source.to_owned(), "checked"),
        (
            "false",
            source.replace(claim, false_claim),
            "verification-failed",
        ),
    ] {
        let run = common::run(&format!("enum_{name}_{suffix}"), &program, &[]);
        assert_eq!(run.outcome(), outcome, "{run:?}");
        assert!(run.raw.is_empty(), "{run:?}");
        if outcome == "verification-failed" {
            let errors = run.errors();
            assert_eq!(errors.len(), 1, "{run:?}");
            assert_eq!(errors[0].message, "assertion failed");
        }
    }
}

#[test]
fn tuple_variants_keep_payloads_and_unit_variants_distinct() {
    pair(
        "values",
        r#"verus! {
enum Choice<T> { Empty, Full(T), Other(T) }
proof fn test() {
    assert(Choice::<u8>::Empty != Choice::Full(3u8));
    assert(Choice::Full(3u8) != Choice::Other(3u8));
    assert(Choice::Full(3u8) == Choice::Full(3u8));
}
}"#,
        "Choice::Full(3u8) == Choice::Full(3u8)",
        "Choice::Full(3u8) == Choice::Full(5u8)",
    );
}

#[test]
fn generic_spec_functions_keep_the_actual_enum_value() {
    pair(
        "generic",
        r#"verus! {
pub enum Choice<T> { Empty, Full(T) }
pub open spec fn wrap<T>(value: T) -> Choice<T> { Choice::Full(value) }
proof fn test() { assert(wrap::<u8>(3u8) == Choice::Full(3u8)); }
}"#,
        "wrap::<u8>(3u8) == Choice::Full(3u8)",
        "wrap::<u8>(3u8) == Choice::Full(5u8)",
    );
}

#[test]
fn same_variant_spelling_keeps_native_datatype_identity() {
    pair(
        "origins",
        r#"
mod left { use super::*; verus! {
    pub enum Choice<T> { Empty, Full(T) }
    pub open spec fn value() -> Choice<u8> { Choice::Full(3u8) }
} }
mod right { use super::*; verus! {
    pub enum Choice<T> { Empty, Full(T) }
    pub open spec fn value() -> Choice<u8> { Choice::Full(5u8) }
} }
verus! { proof fn test() {
    assert(left::value() == left::Choice::Full(3u8));
    assert(right::value() == right::Choice::Full(5u8));
} }
"#,
        "right::value() == right::Choice::Full(5u8)",
        "right::value() == right::Choice::Full(3u8)",
    );
}

#[test]
fn enum_support_preserves_recursive_base_case_rejection() {
    let run = common::run(
        "enum_no_base",
        r#"verus! {
enum Cycle<'a> { Loop(&'a Cycle<'a>) }
proof fn test() { }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(
        errors[0].message,
        "datatype must have at least one non-recursive variant"
    );
}

#[test]
fn a_spec_payload_does_not_become_an_exec_constructor_value() {
    let run = common::run(
        "enum_spec_to_exec",
        r#"verus! {
enum Choice { Empty, Full(u8) }
fn leak(#[verifier::spec] value: u8) -> Choice { Choice::Full(value) }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(!run.errors().is_empty(), "{run:?}");
}

#[test]
fn a_single_variant_enum_pattern_remains_an_explicit_refusal() {
    let run = common::run(
        "enum_pattern_frontier",
        r#"verus! {
enum One { Payload(u8) }
proof fn test() {
    let One::Payload(value) = One::Payload(3u8);
    assert(value == 3);
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "refused", "{run:?}");
}

#[test]
fn generated_field_helpers_keep_instantiated_payload_values() {
    pair(
        "fields",
        r#"verus! {
pub enum Choice<T> { Empty, Full(T) }
proof fn test() {
    assert(Choice::Full(3u8).arrow_Full_0() == 3u8);
    assert(Choice::Full(true).arrow_0());
}
}"#,
        "Choice::Full(3u8).arrow_Full_0() == 3u8",
        "Choice::Full(3u8).arrow_Full_0() == 5u8",
    );
}

#[test]
fn native_variant_tests_keep_the_actual_generic_enum_and_variant() {
    pair(
        "recognition",
        r#"verus! {
enum Choice<T> { Empty, Full(T) }
proof fn test() {
    assert(Choice::Full(true) is Full);
    assert(Choice::Full(3u8) is Full);
}
}"#,
        "Choice::Full(3u8) is Full",
        "Choice::Full(3u8) is Empty",
    );
}

#[test]
fn wrong_variant_selector_does_not_make_the_context_inconsistent() {
    let run = common::run(
        "enum_wrong_variant",
        r#"verus! {
enum Choice<T> { Empty, Full(T) }
proof fn test() {
    let ghost value = Choice::<u8>::Empty.arrow_Full_0();
    assert(value == value);
    assert(false);
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(errors[0].message, "assertion failed");
}

#[test]
fn ambiguous_generated_getter_has_the_actual_upstream_call_diagnostic() {
    let run = common::run(
        "enum_ambiguous_field",
        r#"verus! {
enum Choice { Left(u8), Right(u8) }
proof fn test() { let ghost value = Choice::Left(3u8).arrow_0(); }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(
        errors[0].message,
        "this field is present in multiple variants, cannot use -> syntax"
    );
}

#[test]
fn field_intrinsic_cannot_invent_another_instantiated_result_type() {
    let run = common::run(
        "enum_wrong_field_type",
        r#"verus! {
enum Choice { Full(u8) }
proof fn test() {
    let ghost value = verus_builtin::get_variant_field::<Choice, bool>(Choice::Full(3u8), "Full", "0");
    assert(value);
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "refused", "{run:?}");
}

#[test]
fn an_authored_external_marker_cannot_become_a_generated_enum_diagnostic() {
    let run = common::run(
        "enum_forged_diagnostic",
        r#"verus! {
enum Choice { Left(u8), Right(u8) }
impl Choice {
    #[verus::internal(get_field_many_variants)]
    #[verifier::external]
    spec fn forged(self) -> u8 { unimplemented!() }
}
proof fn test() { assert(true); }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "refused", "{run:?}");
}
