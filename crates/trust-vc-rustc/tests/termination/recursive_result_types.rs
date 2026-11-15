//! Return typing of recursive spec helpers whose child has no fuel/body.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::common;

const BOUND_MERGE: &str = r#"verus! {
spec fn s(i: nat) -> bool
    decreases i
{ if i == 0 { true } else { s((i - 1) as nat) } }
#[verifier::opaque]
spec fn g(n: nat) -> nat
    decreases n when n > 0
{
    if n == 1 { 0 }
    else if n == 2 {
        let v = g((n - 1) as nat);
        let w = g((n - 2) as nat);
        if s(v + SHIFT) == s(w + SHIFT) { v + w + 1 } else { v + w + 2 }
    } else { h((n - 1) as nat) }
}
spec fn h(n: nat) -> nat
    decreases n when n > 1
{ g((n - 1) as nat) + g((n - 2) as nat) + 1 }
proof fn check() {
    assume(h(2) <= 1);
    assert(h(2) == 1);
    reveal(g);
    assert(g(2) == 1);
    assert(s(0));
}
}"#;

fn check_pair(name: &str, source: &str, assertion: &str, false_assertion: &str) {
    assert_eq!(source.matches(assertion).count(), 1);
    let twin = source.replace(assertion, false_assertion);
    assert_eq!(
        source
            .lines()
            .zip(twin.lines())
            .filter(|(a, b)| a != b)
            .count(),
        1
    );
    for (suffix, program, outcome) in [
        ("", source, "checked"),
        ("_twin", twin.as_str(), "verification-failed"),
    ] {
        let run = common::run(&format!("{name}{suffix}"), program, &[]);
        assert_eq!(run.outcome(), outcome, "{run:?}");
        assert!(run.raw.is_empty(), "{:?}", run.raw);
        if suffix.is_empty() {
            assert_eq!(run.exit, 0);
            assert!(run.errors().is_empty());
        } else {
            let errors = run.errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert_eq!(errors[0].message, "assertion failed");
        }
    }
}

#[test]
fn natural_helper_result_with_false_child_decreases_when() {
    check_pair(
        "rf_nat_result",
        r#"verus! {
spec fn count(n: nat) -> nat
    decreases n when n > 0
{
    count((n - 1) as nat) + 1
}
proof fn check() {
    assert(count(1) > 0);
}
}"#,
        "assert(count(1) > 0);",
        "assert(count(1) > 1);",
    );
}

#[test]
fn machine_helper_result_with_false_child_decreases_when() {
    check_pair(
        "rf_u8_result",
        r#"verus! {
spec fn half(n: nat) -> u8
    decreases n when n > 0
{
    (half((n - 1) as nat) / 2) as u8
}
proof fn check() {
    assert(half(1) <= 127);
}
}"#,
        "assert(half(1) <= 127);",
        "assert(half(1) < 127);",
    );
}

#[test]
fn trait_implementation_keeps_only_public_result_typing() {
    check_pair(
        "rf_trait_impl_result",
        r#"verus! {
trait Tr { spec fn f(n: nat) -> nat; }
struct S {}
impl Tr for S {
    spec fn f(n: nat) -> nat
        decreases n
    { if n == 0 { 0 } else { Self::f((n - 1) as nat) + 1 } }
}
proof fn check() {
    assert(S::f(5) >= 0);
}
}"#,
        "assert(S::f(5) >= 0);",
        "assert(S::f(5) > 0);",
    );
}

#[test]
fn trait_implementation_preserves_negative_fuel_case() {
    let run = common::run(
        "rf_trait_impl_fuel",
        r#"verus! {
trait Tr { spec fn f(n: nat) -> nat; }
struct S {}
impl Tr for S {
    spec fn f(n: nat) -> nat
        decreases n
    { if n == 0 { 0 } else { Self::f((n - 1) as nat) + 1 } }
}
proof fn check() {
    assert(S::f(5) == 5);
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].message, "assertion failed");
}

#[test]
fn recursive_default_method_has_no_inherited_helper_axiom() {
    let run = common::run(
        "rf_recursive_default",
        r#"verus! {
trait Tr {
    spec fn f(n: nat) -> nat
        decreases n
    { if n == 0 { 0 } else { Self::f((n - 1) as nat) + 1 } }
}

struct S {}
impl Tr for S {}
proof fn check() { assert(S::f(5) > 0); }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run
        .errors()
        .iter()
        .any(|error| error.message
            == "trait default methods do not yet support recursion and decreases"));
}

#[test]
fn result_bounds_do_not_create_relevance_after_class_merges() {
    for shift in 1..=4 {
        let source = BOUND_MERGE.replace("SHIFT", &shift.to_string());
        check_pair(
            &format!("rf_bound_merge_{shift}"),
            &source,
            "assert(s(0));",
            &format!("assert(s({}));", shift + 1),
        );
    }
}
