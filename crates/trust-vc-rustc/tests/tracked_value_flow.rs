//! Tracked value moves through checked locals and by-value Proof results.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;
#[path = "tracked_value_flow/controls.rs"]
mod controls;

fn checked(name: &str, source: &str) -> common::Run {
    let run = common::run(name, source, &[]);
    assert_eq!(run.outcome(), "checked", "{run:?}");
    assert_eq!(run.exit, 0, "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    assert!(run.errors().is_empty(), "{run:?}");
    run
}

fn moved(name: &str, source: &str) {
    let run = common::run(name, source, &[]);
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(errors[0].code.as_deref(), Some("E0382"), "{run:?}");
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

fn pair(name: &str, source: &str, from: &str, to: &str) -> common::Run {
    assert_eq!(source.matches(from).count(), 1);
    let twin = source.replace(from, to);
    assert_eq!(source.lines().count(), twin.lines().count());
    assert_eq!(
        source
            .lines()
            .zip(twin.lines())
            .filter(|(a, b)| a != b)
            .count(),
        1
    );
    let run = checked(name, source);
    moved(&format!("{name}_twin"), &twin);
    run
}

fn rejected(name: &str, source: &str, message: &str) {
    let run = common::run(name, source, &[]);
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(errors[0].message, message, "{run:?}");
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

fn assert_refused(run: common::Run) {
    assert_eq!(run.outcome(), "refused", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

fn refused(name: &str, source: &str, args: &[&str]) {
    assert_refused(common::run(name, source, args));
}

fn proof_temporaries(run: &common::Run, minimum: usize) {
    let vcir = run.vcir.as_deref().unwrap();
    let temps: Vec<_> = vcir
        .lines()
        .filter(|line| line.trim_start().starts_with("let ") && line.contains("tmp%"))
        .collect();
    assert!(temps.len() >= minimum, "{vcir}");
    assert!(temps.iter().all(|line| line.contains(": proof ")), "{vcir}");
}

#[test]
fn a_tracked_local_keeps_its_original_move() {
    pair(
        "flow_local",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let tracked b = a;
    consume(b);
}
}"#,
        "    consume(b);",
        "    consume(a); consume(b);",
    );
}

#[test]
fn shadowing_resolves_the_initializer_before_the_new_binding() {
    pair(
        "flow_shadow",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) {
    let tracked b = a;
    let tracked a = b;
    consume(a);
}
}"#,
        "    let tracked a = b;",
        "    let tracked a = a;",
    );
}

#[test]
fn returned_values_and_call_temporaries_retain_proof_mode() {
    let run = pair(
        "flow_result",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn pass<A>(tracked a: A) -> (tracked r: A) { a }
proof fn check<A>(tracked a: A) -> (tracked r: A) {
    let tracked b = pass(a);
    b
}
}"#,
        "    let tracked b = pass(a);",
        "    let tracked b = pass(a); consume(a);",
    );
    let vcir = run.vcir.as_deref().unwrap();
    assert!(vcir.contains("-> result: proof "), "{vcir}");
    assert!(vcir.contains("let b: proof "), "{vcir}");
    proof_temporaries(&run, 1);
}

#[test]
fn a_terminal_explicit_return_keeps_the_move() {
    pair(
        "flow_return",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn check<A>(tracked a: A) -> (tracked r: A) {
    return a;
}
}"#,
        "    return a;",
        "    consume(a); return a;",
    );
}

#[test]
fn nested_proof_values_and_a_unit_tail_call_preserve_both_moves() {
    let run = pair(
        "flow_nested",
        r#"verus! {
proof fn pass<A>(tracked a: A) -> (tracked r: A) { a }
proof fn consume<A>(tracked a: A, tracked b: A) {}
proof fn check<A>(tracked a: A, tracked b: A) {
    consume(pass(a), pass(b))
}
}"#,
        "    consume(pass(a), pass(b))",
        "    consume(pass(a), pass(a))",
    );
    proof_temporaries(&run, 3);
}

#[test]
fn an_earlier_parameter_keeps_proof_mode_before_a_later_call() {
    let run = pair(
        "flow_parameter_snapshot",
        r#"verus! {
proof fn pass<A>(tracked a: A) -> (tracked r: A) { a }
proof fn consume<A>(tracked a: A, tracked b: A) {}
proof fn check<A>(tracked a: A, tracked b: A) {
    consume(a, pass(b))
}
}"#,
        "    consume(a, pass(b))",
        "    consume(a, pass(a))",
    );
    proof_temporaries(&run, 2);
}

#[test]
fn a_real_copy_bound_controls_moves_through_a_result() {
    pair(
        "flow_copy_bound",
        r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn pass<A>(tracked a: A) -> (tracked r: A) { a }
proof fn check<A: Copy>(tracked a: A) {
    let tracked b = pass(a);
    consume(a);
    consume(b);
}
}"#,
        "proof fn check<A: Copy>(tracked a: A)",
        "proof fn check<A>(tracked a: A)",
    );
}

#[test]
fn concrete_copy_values_and_non_copy_tokens_keep_native_semantics() {
    for ty in ["u64", "bool"] {
        let source = format!(
            "verus! {{\nstruct Token {{}}\nproof fn consume<A>(tracked a: A) {{}}\n\
             proof fn pass<A>(tracked a: A) -> (tracked r: A) {{ a }}\n\
             proof fn check(tracked a: {ty}) {{\n    let tracked b = pass(a);\n\
                 consume(a);\n    consume(b);\n}}\n}}"
        );
        pair(
            &format!("flow_{ty}"),
            &source,
            &format!("proof fn check(tracked a: {ty})"),
            "proof fn check(tracked a: Token)",
        );
    }
}

#[test]
fn authored_drop_values_move_through_locals_and_returns() {
    pair(
        "flow_drop",
        r#"verus! {
struct Token { n: u64 }
impl Drop for Token {
    fn drop(&mut self) opens_invariants none no_unwind {}
}
proof fn consume(tracked a: Token) {}
proof fn check(tracked a: Token) -> (tracked r: Token) {
    let tracked b = a;
    b
}
}"#,
        "    let tracked b = a;",
        "    let tracked b = a; consume(a);",
    );
}

#[test]
fn canonical_local_return_and_nested_call_move_errors_are_preserved() {
    for (name, source) in [
        (
            "flow_upstream_temp",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn test1<A>(tracked a: A) {
    let tracked b = a;
    consume(a);
    consume(b);
}
}"#,
        ),
        (
            "flow_upstream_return",
            r#"verus! {
proof fn consume<A>(tracked a: A) {}
proof fn test1<A>(tracked a: A) -> (tracked b: A) {
    consume(a);
    a
}
}"#,
        ),
        (
            "flow_upstream_args",
            r#"verus! {
proof fn f<A>(tracked a: A) -> (tracked b: A) { a }
proof fn g<A>(tracked x: A, tracked y: A) {}
proof fn h<A>(tracked a: A) { g(f(a), f(a)) }
}"#,
        ),
    ] {
        moved(name, source);
    }
}

#[test]
fn admitting_the_identity_preserves_the_proof_call_in_spec_error() {
    rejected(
        "flow_upstream_spec_args",
        r#"verus! {
proof fn f<A>(tracked a: A) -> (tracked b: A) { a }
proof fn g<A>(x: A, y: A) {}
proof fn h<A>(tracked a: A) { g(f(a), f(a)) }
}"#,
        "cannot call function `test_crate::f` with mode proof",
    );
}
