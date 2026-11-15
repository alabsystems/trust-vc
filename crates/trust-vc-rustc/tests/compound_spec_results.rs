//! Product-valued spec functions, including opacity, recursion and type bounds.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn pair(name: &str, source: &str, original: &str, changed: &str) {
    assert_eq!(source.matches(original).count(), 1);
    let twin = source.replace(original, changed);
    let positive = common::run(&format!("compound_{name}_positive"), source, &[]);
    let negative = common::run(&format!("compound_{name}_false"), &twin, &[]);
    assert_eq!(positive.outcome(), "checked", "{positive:?}");
    assert_eq!(negative.outcome(), "verification-failed", "{negative:?}");
    assert!(positive.raw.is_empty(), "{positive:?}");
    assert!(negative.raw.is_empty(), "{negative:?}");
    let errors = negative.errors();
    assert_eq!(errors.len(), 1, "{negative:?}");
    assert_eq!(errors[0].message, "assertion failed");
    let verified = |run: &common::Run| {
        run.record["functions"]
            .as_array()
            .expect("function records")
            .iter()
            .filter(|function| function["verdict"] == "verified")
            .count()
    };
    assert_eq!(verified(&positive), verified(&negative) + 1);
}

#[test]
fn nested_tuple_results_preserve_each_field() {
    pair(
        "nested_tuple",
        r#"verus! {
spec fn make(x: int) -> (int, (bool, int), ()) {
    (x + 1, (x > 0, x - 1), ())
}
proof fn test() {
    let p = make(4);
    assert(p.0 == 5 && p.1.0 && p.1.1 == 3);
}
}"#,
        "p.1.1 == 3",
        "p.1.1 == 4",
    );
}

#[test]
fn struct_results_keep_native_field_order_and_bounds() {
    pair(
        "struct",
        r#"verus! {
struct Pair { count: nat, ready: bool }
spec fn make(x: nat) -> Pair { Pair { ready: x == 0, count: x + 1 } }
proof fn test() {
    let p = make(2);
    assert(p.count == 3 && !p.ready);
}
}"#,
        "p.count == 3",
        "p.count == 4",
    );
}

#[test]
fn opaque_products_publish_type_bounds_without_their_bodies() {
    pair(
        "opaque_bounds",
        r#"verus! {
#[verifier::opaque]
spec fn hidden(x: nat) -> (nat, u8) { (x, 3) }
proof fn test(x: nat) {
    assert(hidden(x).0 >= 0 && hidden(x).1 <= 255);
}
}"#,
        "hidden(x).1 <= 255",
        "hidden(x).1 <= 254",
    );
}

#[test]
fn revealing_a_product_controls_all_its_fields() {
    pair(
        "reveal",
        r#"verus! {
#[verifier::opaque]
spec fn hidden() -> (int, bool) { (7, true) }
proof fn test() {
    reveal(hidden);
    assert(hidden().0 == 7 && hidden().1);
}
}"#,
        "reveal(hidden);",
        "",
    );
}

#[test]
fn recursive_product_definitions_share_fuel_and_dependencies() {
    pair(
        "recursive",
        r#"verus! {
spec fn climb(n: nat) -> (nat, nat)
    decreases n,
{
    if n == 0 { (0, 0) } else {
        let p = climb((n - 1) as nat);
        (p.0 + 1, p.1 + 2)
    }
}
proof fn test() {
    reveal_with_fuel(climb, 2);
    assert(climb(1).0 == 1 && climb(1).1 == 2);
}
}"#,
        "climb(1).1 == 2",
        "climb(1).1 == 3",
    );
}

#[test]
fn product_projection_does_not_add_recursive_fuel() {
    pair(
        "fuel",
        r#"verus! {
spec fn climb(n: nat) -> (nat, nat)
    decreases n,
{
    if n == 0 { (0, 0) } else {
        let p = climb((n - 1) as nat);
        (p.0 + 1, p.1 + 2)
    }
}
proof fn test() {
    reveal_with_fuel(climb, 2);
    assert(climb(1).0 == 1 && climb(1).1 == 2);
}
}"#,
        "reveal_with_fuel(climb, 2);",
        "reveal_with_fuel(climb, 1);",
    );
}

#[test]
fn generic_instances_preserve_product_results() {
    pair(
        "generic",
        r#"verus! {
struct Pair<A> { value: A, ready: bool }
spec fn identity<A>(x: A) -> A { x }
proof fn test() {
    let p = identity(Pair { value: 7int, ready: true });
    assert(p.value == 7 && p.ready);
}
}"#,
        "p.value == 7",
        "p.value == 8",
    );
}

#[test]
fn whole_nested_products_cross_a_formal_type_parameter() {
    pair(
        "generic_nested_product",
        r#"verus! {
struct Pair<A> { value: A, ready: bool }
spec fn identity<A>(x: A) -> A { x }
proof fn test() {
    let p = identity(Pair { value: Pair { value: 7int, ready: true }, ready: true });
    assert(p.value.value == 7 && p.value.ready && p.ready);
}
}"#,
        "p.value.value == 7",
        "p.value.value == 8",
    );
}

#[test]
fn product_family_arguments_survive_generic_body_unfolding() {
    pair(
        "generic_nested_unfold",
        r#"verus! {
struct Pair<A> { value: A, ready: bool }
spec fn identity<A>(x: A) -> A { x }
spec fn wrapped<A>(x: A) -> Pair<A> {
    identity(Pair { value: identity(x), ready: true })
}
proof fn test() {
    let p = wrapped(7int);
    assert(p.value == 7 && p.ready);
}
}"#,
        "p.value == 7",
        "p.value == 8",
    );
}

#[test]
fn explicit_formal_products_keep_their_declared_field_abi() {
    pair(
        "generic_formal_product",
        r#"verus! {
struct Pair<A> { value: A, ready: bool }
spec fn pass_pair<A>(x: Pair<A>) -> Pair<A> { x }
proof fn test() {
    let p = pass_pair(Pair { value: 7int, ready: true });
    assert(p.value == 7 && p.ready);
}
}"#,
        "p.value == 7",
        "p.value == 8",
    );
}

#[test]
fn zero_leaf_products_retain_their_structure() {
    pair(
        "zero_leaf",
        r#"verus! {
struct Empty { value: () }
spec fn empty() -> (Empty, ()) { (Empty { value: () }, ()) }
proof fn test() {
    let p = empty();
    assert(p == (Empty { value: () }, ()));
}
}"#,
        "assert(p == (Empty { value: () }, ()));",
        "assert(false);",
    );
}

#[test]
fn recursive_product_leaves_keep_types_at_zero_fuel() {
    pair(
        "recursive_bounds",
        r#"verus! {
spec fn climb(n: nat) -> (nat, u8)
    decreases n,
{
    if n == 0 { (0, 0) } else {
        let p = climb((n - 1) as nat);
        (p.0 + 1, p.1)
    }
}
proof fn test() {
    reveal_with_fuel(climb, 1);
    assert(climb(1).0 >= 1 && climb(1).1 <= 255);
}
}"#,
        "climb(1).1 <= 255",
        "climb(1).1 <= 254",
    );
}

#[test]
fn mutual_recursion_renames_every_product_leaf() {
    pair(
        "mutual",
        r#"verus! {
spec fn left(n: nat) -> (nat, bool)
    decreases n,
{
    if n == 0 { (2, true) } else {
        let p = right((n - 1) as nat);
        (p.0 + 1, !p.1)
    }
}
spec fn right(n: nat) -> (nat, bool)
    decreases n,
{
    if n == 0 { (4, false) } else {
        let p = left((n - 1) as nat);
        (p.0 + 1, !p.1)
    }
}
proof fn test() {
    assert(left(1).0 == 5 && left(1).1);
}
}"#,
        "left(1).0 == 5",
        "left(1).0 == 6",
    );
}

#[test]
fn a_zero_leaf_result_does_not_erase_a_dependency_cycle() {
    let run = common::run(
        "compound_zero_leaf_cycle",
        r#"verus! {
spec fn cycle() -> ((), ()) { cycle() }
proof fn test() { }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(
        errors[0].message,
        "recursive function must have a decreases clause"
    );
}

#[test]
fn observing_one_field_exposes_the_same_recursive_value() {
    pair(
        "shared_value",
        r#"verus! {
spec fn climb(n: nat) -> (nat, nat)
    decreases n,
{
    if n == 0 { (0, 0) } else {
        let p = climb((n - 1) as nat);
        (p.0 + 1, p.1 + 2)
    }
}
proof fn test() {
    reveal_with_fuel(climb, 2);
    assert(climb(0).0 == 0);
    assert(climb(2).1 == 4);
}
}"#,
        "climb(2).1 == 4",
        "climb(3).1 == 6",
    );
}

#[test]
fn unused_component_keeps_whole_value_relevance() {
    pair(
        "review_sibling",
        r#"verus! {
spec fn pair(n: nat) -> (nat, nat)
    decreases n,
{
    if n == 0 { (0, 0) } else {
        let p = pair((n - 1) as nat);
        (p.0 + 1, pair(0).0)
    }
}
proof fn test() {
    reveal_with_fuel(pair, 2);
    assert(pair(2).0 == 2);
}
}
"#,
        "(p.0 + 1, pair(0).0)",
        "(p.0 + 1, 0)",
    );
}

#[test]
fn other_declarations_do_not_share_recursive_equations() {
    pair(
        "review_identity",
        r#"verus! {
spec fn pair(n: nat) -> (nat, nat)
    decreases n,
{
    if n == 0 { (0, 0) } else {
        let p = pair((n - 1) as nat);
        (p.0 + 1, 0)
    }
}
spec fn other(n: nat) -> (nat, nat)
    decreases n,
{
    if n == 0 { (0, 0) } else {
        let p = other((n - 1) as nat);
        (p.0 + 1, 0)
    }
}
proof fn test() {
    reveal_with_fuel(pair, 2);
    assert(pair(0).0 == 0);
    assert(pair(2).0 == 2);
}
}
"#,
        "assert(pair(0).0 == 0);",
        "assert(other(0).0 == 0);",
    );
}

#[test]
fn product_definitions_keep_decreases_when_guard() {
    pair(
        "review_when",
        r#"verus! {
spec fn gated(n: int) -> (nat, nat)
    decreases n when n >= 0
{
    if n <= 0 { (7, 9) } else {
        let p = gated(n - 1);
        (p.0 + 1, p.1 + 1)
    }
}
proof fn test() {
    reveal_with_fuel(gated, 2);
    let p = gated(0);
    assert(p.0 == 7 && p.1 == 9);
}
}
"#,
        "let p = gated(0);",
        "let p = gated(-1);",
    );
}
