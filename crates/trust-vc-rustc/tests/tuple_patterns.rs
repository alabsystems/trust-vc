//! Tuple bindings through the real compiler and AY, with one-line false twins.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn check_pair(name: &str, program: &str, assertion: &str, false_assertion: &str) {
    check_pair_message(
        name,
        program,
        assertion,
        false_assertion,
        "assertion failed",
    );
}

fn check_pair_message(
    name: &str,
    program: &str,
    assertion: &str,
    false_assertion: &str,
    message: &str,
) {
    assert_eq!(program.matches(assertion).count(), 1);
    let twin = program.replace(assertion, false_assertion);
    assert_eq!(
        program
            .lines()
            .zip(twin.lines())
            .filter(|(a, b)| a != b)
            .count(),
        1
    );
    for (suffix, source, outcome) in [
        ("", program, "checked"),
        ("_twin", twin.as_str(), "verification-failed"),
    ] {
        let run = common::run(&format!("{name}{suffix}"), source, &[]);
        assert_eq!(run.outcome(), outcome, "{name}{suffix}: {run:?}");
        assert!(run.raw.is_empty(), "{name}{suffix}: {:?}", run.raw);
        let checked = run.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .find(|function| function["def_path"] == "test")
            .expect("actual checked function");
        if outcome == "checked" {
            assert_eq!(run.exit, 0);
            assert!(run.errors().is_empty());
            assert_eq!(checked["verdict"], "verified", "{run:?}");
            assert!(checked["sites_proved"].as_u64().unwrap() > 0, "{run:?}");
            assert_eq!(checked["sites_failed"], 0, "{run:?}");
        } else {
            assert_eq!(run.exit, 1);
            let errors = run.errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert_eq!(errors[0].message, message);
            assert_eq!(checked["verdict"], "failed", "{run:?}");
            assert_eq!(checked["sites_failed"], 1, "{run:?}");
        }
    }
}

#[test]
fn singleton_tuple_values_and_nested_projection_have_false_twins() {
    check_pair(
        "singleton_tuple_value",
        r#"verus! {
proof fn test() {
    let value = ((7u8,),);
    assert(value.0.0 == 7);
}
}"#,
        "assert(value.0.0 == 7);",
        "assert(value.0.0 == 8);",
    );
}

#[test]
fn singleton_tuple_binding_keeps_its_initializer_once() {
    check_pair(
        "singleton_tuple_once",
        r#"verus! {
fn test() {
    let mut count: u32 = 0;
    let (mut value,) = { count = count + 1; (count,) };
    value = value + 1;
    assert(count == 1 && value == 2);
}
}"#,
        "assert(count == 1 && value == 2);",
        "assert(count == 2 && value == 2);",
    );
}

#[test]
fn singleton_tuple_generic_value_preserves_its_whole_product() {
    check_pair(
        "singleton_tuple_generic",
        r#"verus! {
spec fn identity<A>(value: A) -> A { value }
proof fn test() {
    let value = identity::<(u8,)>((7u8,));
    let unit = identity::<((),)>(((),));
    assert(value.0 == 7 && unit == ((),));
}
}"#,
        "assert(value.0 == 7 && unit == ((),));",
        "assert(value.0 == 8 && unit == ((),));",
    );
}

#[test]
fn singleton_tuple_bv_value_has_its_actual_ordered_element() {
    check_pair_message(
        "singleton_tuple_bv",
        r#"verus! {
proof fn test(x: u8) {
    assert((((x,),).0.0 ^ x) == 0) by(bit_vector);
}
}"#,
        "assert((((x,),).0.0 ^ x) == 0) by(bit_vector);",
        "assert((((x,),).0.0 ^ x) == 1) by(bit_vector);",
        "bitvector assertion not satisfied",
    );
}

#[test]
fn tuple_choice_keeps_both_witnesses() {
    check_pair(
        "tuple_choice",
        r#"verus! {
spec fn eligible(i: int, j: int) -> bool { i >= 5 && j >= 5 }
proof fn test() {
    assert(eligible(7, 8));
    let (i, j) = choose|i: int, j: int| eligible(i, j);
    assert(i >= 5 && j >= 5);
}
}"#,
        "assert(i >= 5 && j >= 5);",
        "assert(i < 5 && j >= 5);",
    );
}

#[test]
fn nested_rest_pattern_evaluates_its_initializer_once() {
    check_pair(
        "tuple_once",
        r#"verus! {
fn test() {
    let mut count: u32 = 0;
    let (a, (_, b), .., c) = {
        count = count + 1;
        (count, (2u32, 3u32), 4u32, 5u32)
    };
    assert(count == 1 && a == 1 && b == 3 && c == 5);
}
}"#,
        "assert(count == 1 && a == 1 && b == 3 && c == 5);",
        "assert(count == 2 && a == 1 && b == 3 && c == 5);",
    );
}

#[test]
fn tuple_bindings_shadow_only_after_initialization() {
    check_pair(
        "tuple_shadow",
        r#"verus! {
fn test() {
    let a: u32 = 7;
    let (mut a, b) = (2u32, a);
    a = a + 1;
    assert(a == 3 && b == 7);
}
}"#,
        "assert(a == 3 && b == 7);",
        "assert(a == 3 && b == 2);",
    );
}

#[test]
fn uninitialized_tuple_bindings_are_independent() {
    check_pair(
        "tuple_uninitialized",
        r#"verus! {
fn test() {
    let (a, b): (u32, u32);
    a = 1;
    b = 2;
    assert(a + b == 3);
}
}"#,
        "assert(a + b == 3);",
        "assert(a + b == 4);",
    );
}

#[test]
fn tuple_fields_keep_their_evaluation_order() {
    check_pair(
        "tuple_field_order",
        r#"verus! {
fn test() {
    let mut count: u32 = 0;
    let (a, b) = ({ count = count + 1; count }, { count = count + 1; count });
    assert(count == 2 && a == 1 && b == 2);
}
}"#,
        "assert(count == 2 && a == 1 && b == 2);",
        "assert(count == 2 && a == 2 && b == 2);",
    );
}

#[test]
fn reference_destructuring_requires_borrow_aware_lowering() {
    let run = common::run(
        "tuple_reference",
        r#"verus! {
fn test() {
    let pair = (1u32, 2u32);
    let (a, b) = &pair;
    assert(*a == 1 && *b == 2);
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "refused", "{run:?}");
    assert!(run.raw.is_empty());
    assert!(
        run.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["tag"] == "let-pattern"),
        "{:?}",
        run.record
    );
}
