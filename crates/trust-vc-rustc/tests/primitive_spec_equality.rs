//! Shared machine-integer values at the native spec-equality boundary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

fn checked(name: &str, source: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
}

#[test]
fn primitive_referents_compare_symmetrically_as_integers() {
    checked(
        "primitive_ref_symmetric",
        "verus! {
        proof fn test(a: &u8, b: u8) requires *a == b {
            assert(a == b);
            assert(b == a);
            assert(a == b as int);
            assert(b as int == a);
        }
        proof fn cross_width(a: &u8, b: &u16) requires *a == *b {
            assert(a == b);
            assert(b == a);
        }
        proof fn signed(a: &i8, b: int) requires *a == b {
            assert(a == b);
            assert(b == a);
        }
    }",
    );
}

#[test]
fn real_false_twins_do_not_become_proved_or_refused() {
    for (name, assertion) in [("left", "a == b + 1"), ("right", "b + 1 == a")] {
        let source = format!(
            "verus! {{ proof fn test(a: &u8, b: u8) requires *a == b {{ assert({assertion}); }} }}"
        );
        let result = common::run(name, &source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verification-failed", "{result:?}");
        assert_eq!(result.errors().len(), 1, "{result:?}");
        assert_eq!(result.errors()[0].message, "assertion failed", "{result:?}");
    }
}

#[test]
fn explicit_shared_borrows_use_the_same_referent() {
    checked(
        "primitive_borrow",
        "verus! {
        proof fn test(a: u8, b: u8) requires a == b {
            assert(&a == b);
            assert(b == &a);
        }
    }",
    );
    let result = common::run(
        "primitive_borrow_false",
        "verus! {
        proof fn test(a: u8, b: u8) requires a != b { assert(&a == b); }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
}

#[test]
fn matching_reference_types_keep_the_existing_path() {
    checked(
        "matching_primitive_refs",
        "verus! {
        proof fn test(a: &u8, b: &u8) requires *a == *b {
            assert(a == b);
            assert(a == a);
        }
    }",
    );
    let result = common::run(
        "matching_primitive_refs_false",
        "verus! {
        proof fn test(a: &u8, b: &u8) requires *a != *b { assert(a == b); }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
}

#[test]
fn other_decorators_and_reference_forms_keep_refusing() {
    for (name, source) in [
        (
            "nominal",
            "verus! { struct S { value: u8 } proof fn test(a: &S, b: S) { assert(a == b); } }",
        ),
        (
            "deep",
            "verus! { proof fn test(a: &&u8, b: u8) { assert(a == b); } }",
        ),
        (
            "boolean",
            "verus! { proof fn test(a: &bool, b: bool) { assert(a == b); } }",
        ),
        (
            "character",
            "verus! { proof fn test(a: &char, b: char) { assert(a == b); } }",
        ),
        (
            "conditional",
            "verus! { proof fn test(flag: bool, a: &u8, b: &u8) { assert((if flag { a } else { b }) == 0u8); } }",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "refused", "{result:?}");
        assert!(!result.errors().is_empty(), "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|f| f["verdict"] != "verified"),
            "{result:?}"
        );
    }
}

#[test]
fn mutable_references_never_gain_an_implicit_scalar_read() {
    for (name, source) in [
        (
            "mutable_left",
            "verus! { proof fn test(a: &mut u8, b: u8) { assert(a == b); } }",
        ),
        (
            "mutable_right",
            "verus! { proof fn test(a: u8, b: &mut u8) { assert(a == b); } }",
        ),
    ] {
        for flags in [&[][..], &["-V", "new-mut-ref"][..]] {
            let result = common::run(name, source, flags);
            assert_eq!(result.exit, 1, "{result:?}");
            assert!(
                matches!(result.outcome().as_str(), "refused" | "verus-rejected"),
                "{result:?}"
            );
            assert!(!result.errors().is_empty(), "{result:?}");
            assert!(
                result.record["functions"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|f| f["verdict"] != "verified"),
                "{result:?}"
            );
        }
    }
}
