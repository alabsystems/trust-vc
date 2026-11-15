//! Boundaries requiring mode erasure rather than original MIR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{assert_refused, checked, common, refused, rejected};

#[test]
fn plain_proof_locals_keep_their_default_spec_mode() {
    let source = r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let tracked b = a;
    consume(b);
}
}"#;
    checked("flow_declared_local", source);
    let twin = source.replace("let tracked b = a;", "let b = a;");
    assert_eq!(
        source
            .lines()
            .zip(twin.lines())
            .filter(|(a, b)| a != b)
            .count(),
        1
    );
    rejected(
        "flow_plain_local",
        &twin,
        "expression has mode spec, expected mode proof",
    );
}

#[test]
fn spec_uses_and_spec_valued_parents_still_require_erasure() {
    for (name, source) in [
        (
            "flow_spec_observe",
            r#"verus! {
spec fn observe<A>(a: A) -> bool { true }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let tracked b = a;
    assert(observe(b));
    consume(b);
}
}"#,
        ),
        (
            "flow_plain_spec_let",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let b = a;
    consume(a);
}
}"#,
        ),
        (
            "flow_spec_helper",
            r#"verus! {
proof fn inspect<A>(a: A) {}
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let tracked b = a;
    inspect(b); inspect(b);
    consume(b);
}
}"#,
        ),
        (
            "flow_spec_parent",
            r#"verus! {
proof fn consume<A>(tracked a: A) -> int { 2 }
proof fn check<A>(tracked a: A) -> int { consume(a) + consume(a) }
}"#,
        ),
        (
            "flow_mixed_signature",
            r#"verus! {
proof fn pass<A>(tracked a: A, b: A) -> (tracked r: A) { a }
proof fn check<A>(tracked a: A, b: A) -> (tracked r: A) { pass(a, b) }
}"#,
        ),
    ] {
        refused(name, source, &[]);
    }
}

#[test]
fn assignments_patterns_borrows_and_headers_remain_outside_the_slice() {
    for (name, source) in [
        (
            "flow_assignment",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A, tracked b: A) {
    let tracked mut x = a;
    x = b;
    consume(x);
    consume(b);
}
}"#,
        ),
        (
            "flow_inferred",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let tracked b;
    b = a;
    consume(b);
}
}"#,
        ),
        (
            "flow_tuple_pattern",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked pair: (A, A)) {
    let tracked (a, b) = pair;
    consume(a); consume(b);
}
}"#,
        ),
        (
            "flow_alias_pattern",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let tracked b @ _ = a;
    consume(b);
}
}"#,
        ),
        (
            "flow_borrow",
            r#"verus! {
proof fn check<A>(tracked a: A) {
    let tracked b = &a;
}
}"#,
        ),
        (
            "flow_reference_result",
            r#"verus! {
proof fn pass<'a, A>(tracked a: &'a A) -> (tracked r: &'a A) { a }
}"#,
        ),
        (
            "flow_header",
            r#"verus! {
proof fn check<A>(tracked a: A) -> (tracked r: A) requires true { a }
}"#,
        ),
        (
            "flow_aggregate_result",
            r#"verus! {
proof fn check<A>(tracked a: A, tracked b: A) -> (tracked r: (A, A)) {
    (a, b)
}
}"#,
        ),
        (
            "flow_wildcard",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) { let tracked _ = a; consume(a); }
}"#,
        ),
    ] {
        refused(name, source, &[]);
    }
}

#[test]
fn unchecked_and_external_returning_callees_cannot_publish_a_caller() {
    for (name, source) in [
        (
            "flow_unchecked_callee",
            r#"verus! {
proof fn pass<A>(tracked a: A) -> (tracked r: A) { assert(true); a }
proof fn check<A>(tracked a: A) -> (tracked r: A) { pass(a) }
}"#,
        ),
        (
            "flow_external_callee",
            r#"verus! {
#[verifier::external_body]
proof fn pass<A>(tracked a: A) -> (tracked r: A) { a }
proof fn check<A>(tracked a: A) -> (tracked r: A) { pass(a) }
}"#,
        ),
    ] {
        refused(name, source, &[]);
    }
}

#[test]
fn returned_and_local_values_require_the_native_lifetime_gate() {
    refused(
        "flow_no_lifetime",
        r#"verus! {
proof fn check<A>(tracked a: A) -> (tracked r: A) {
    let tracked b = a;
    b
}
}"#,
        &["--no-lifetime"],
    );
}

#[test]
fn custom_mir_does_not_gain_a_tracked_value_flow_receipt() {
    let source = format!(
        "#![feature(custom_mir)]\n{}{}",
        common::PRELUDE,
        r#"verus! {
#[custom_mir(dialect = "runtime", phase = "optimized")]
proof fn check<A>(tracked a: A) -> (tracked r: A) {
    let tracked b = a;
    b
}
}"#
    );
    assert_refused(common::run_raw("flow_custom_mir", &source, &[]));
}

#[test]
fn a_proof_result_error_still_reports_independent_exec_moves() {
    let run = common::run(
        "flow_both_phases",
        r#"verus! {
struct Token {}
proof fn consume<A>(tracked a: A) {}
proof fn bad_proof<A>(tracked a: A) -> (tracked r: A) {
    let tracked b = a;
    consume(a);
    b
}
fn bad_exec(a: Token) { let x = a; let y = a; }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 2, "{run:?}");
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() == Some("E0382")),
        "{run:?}"
    );
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}
