//! Native ownership checking of proof calls that need no mode erasure.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn checked(name: &str, source: &str) {
    let run = common::run(name, source, &[]);
    assert_eq!(run.outcome(), "checked", "{run:?}");
    assert_eq!(run.exit, 0);
    assert!(run.raw.is_empty(), "{:?}", run.raw);
    assert!(run.errors().is_empty(), "{:?}", run.errors());
}

fn moved(name: &str, source: &str) {
    let run = common::run(name, source, &[]);
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert_eq!(run.exit, 1);
    assert!(run.raw.is_empty(), "{:?}", run.raw);
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].code.as_deref(), Some("E0382"));
    assert!(errors[0].message.contains("use of moved value"));
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

fn pair(name: &str, source: &str, old: &str, new: &str) {
    assert_eq!(source.matches(old).count(), 1);
    let twin = source.replace(old, new);
    assert_eq!(
        source
            .lines()
            .zip(twin.lines())
            .filter(|(a, b)| a != b)
            .count(),
        1
    );
    checked(name, source);
    moved(&format!("{name}_twin"), &twin);
}

fn refused(name: &str, source: &str, args: &[&str]) {
    assert_refused(common::run(name, source, args));
}

fn assert_refused(run: common::Run) {
    assert_eq!(run.outcome(), "refused", "{run:?}");
    assert_eq!(run.exit, 1);
    assert!(run.raw.is_empty(), "{:?}", run.raw);
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

#[test]
fn generic_non_copy_value_moves_once() {
    pair(
        "owned_generic",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    consume(a);
}
}"#,
        "    consume(a);",
        "    consume(a); consume(a);",
    );
}

#[test]
fn compiler_copy_bound_decides_whether_a_use_moves() {
    pair(
        "owned_copy_bound",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A: Copy>(tracked a: A) {
    consume(a);
    consume(a);
}
}"#,
        "proof fn check<A: Copy>(tracked a: A)",
        "proof fn check<A>(tracked a: A)",
    );
}

#[test]
fn concrete_copy_types_match_the_real_compiler() {
    for ty in ["u64", "bool"] {
        let source = format!(
            "verus! {{\nstruct Token {{}}\nproof fn consume<A>(tracked a: A) {{}}\n\
             proof fn check(tracked a: {ty}) {{ consume(a); consume(a); }}\n}}"
        );
        pair(
            &format!("owned_{ty}"),
            &source,
            &format!("tracked a: {ty}"),
            "tracked a: Token",
        );
    }
}

#[test]
fn spec_uses_and_mixed_modes_still_require_erasure() {
    for (name, source) in [
        (
            "owned_spec_once",
            r#"verus! {
proof fn consume<A>(a: A) {}
proof fn check<A>(tracked a: A) { consume(a); }
}"#,
        ),
        (
            "owned_spec_twice",
            r#"verus! {
proof fn consume<A>(a: A) {}
proof fn check<A>(tracked a: A) { consume(a); consume(a); }
}"#,
        ),
        (
            "owned_mixed_modes",
            r#"verus! {
proof fn consume<A>(tracked a: A, b: A) {}
proof fn check<A>(tracked a: A, b: A) { consume(a, b); }
}"#,
        ),
        (
            "owned_spec_observation",
            r#"verus! {
spec fn observe<A>(a: A) -> bool { true }
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) { assert(observe(a)); consume(a); }
}"#,
        ),
    ] {
        refused(name, source, &[]);
    }
}

#[test]
fn native_ownership_cannot_be_skipped() {
    refused(
        "owned_no_lifetime",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) { consume(a); consume(a); }
}"#,
        &["--no-lifetime"],
    );
}

#[test]
fn authored_destructor_preserves_the_full_source_moves() {
    pair(
        "owned_authored_drop",
        r#"verus! {
struct Token { n: u64 }
impl Drop for Token {
    fn drop(&mut self) opens_invariants none no_unwind {}
}
proof fn consume(tracked a: Token) {}
proof fn check(tracked a: Token) { consume(a); }
}"#,
        "proof fn check(tracked a: Token) { consume(a); }",
        "proof fn check(tracked a: Token) { consume(a); consume(a); }",
    );
}

#[test]
fn external_helper_still_requires_ownership_erasure() {
    refused(
        "owned_external_helper",
        r#"verus! {
#[verifier::external_body]
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) { consume(a); consume(a); }
}"#,
        &[],
    );
}

#[test]
fn an_eligible_caller_cannot_admit_an_unchecked_callee_body() {
    refused(
        "owned_unchecked_callee",
        r#"verus! {
proof fn consume<A>(tracked a: A) { assert(true); }
proof fn check<A>(tracked a: A) { consume(a); consume(a); }
}"#,
        &[],
    );
}

#[test]
fn proof_errors_do_not_hide_exec_ownership_errors() {
    let run = common::run(
        "owned_both_phases",
        r#"verus! {
struct Token {}
proof fn consume<A>(tracked a: A) {}
proof fn bad_proof<A>(tracked a: A) { consume(a); consume(a); }
fn bad_exec(a: Token) { let x = a; let y = a; }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert_eq!(run.exit, 1);
    assert!(run.raw.is_empty(), "{:?}", run.raw);
    let errors = run.errors();
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(errors
        .iter()
        .all(|error| error.code.as_deref() == Some("E0382")));
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

#[test]
fn injected_mir_cannot_claim_native_source_ownership() {
    let source = format!(
        "#![feature(custom_mir)]\n{}{}",
        common::PRELUDE,
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
#[custom_mir(dialect = "runtime", phase = "optimized")]
proof fn check<A>(tracked a: A) { consume(a); consume(a); }
}"#,
    );
    assert_refused(common::run_raw("owned_injected_mir", &source, &[]));
}
