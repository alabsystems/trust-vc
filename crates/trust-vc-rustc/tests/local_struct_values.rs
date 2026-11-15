//! Local struct values through the compiler reader and AY, with false twins.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn pair(name: &str, source: &str, yes: &str, no: &str, message: &str) {
    assert_eq!(source.matches(yes).count(), 1);
    let twin = source.replace(yes, no);
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
        assert_eq!(run.outcome(), outcome, "{name}{suffix}: {run:?}");
        assert!(run.raw.is_empty(), "{run:?}");
        if suffix.is_empty() {
            assert_eq!(run.exit, 0);
            assert!(run.errors().is_empty(), "{run:?}");
        } else {
            let errors = run.errors();
            assert_eq!(errors.len(), 1, "{run:?}");
            assert_eq!(errors[0].message, message, "{run:?}");
        }
    }
}

#[test]
fn named_fields_use_compiler_indices_and_instantiated_types() {
    pair(
        "struct_named",
        r#"verus! {
struct Pair<A, B> { first: A, second: B }
fn test() {
    let Pair { second: (flag, mut count), first: number } =
        Pair { first: 99u32, second: (true, 7u8) };
    count = count + 1;
    assert(number == 99 && flag && count == 8);
}
}"#,
        "assert(number == 99 && flag && count == 8);",
        "assert(number == 99 && flag && count == 9);",
        "assertion failed",
    );
}

#[test]
fn tuple_struct_rest_keeps_nested_struct_bindings() {
    pair(
        "struct_tuple_rest",
        r#"verus! {
struct Inner { yes: bool }
struct Bundle<A, B, C>(A, B, C);
fn test() {
    let Bundle(mut first, .., Inner { yes }) = Bundle(4u32, false, Inner { yes: true });
    first = first + 1;
    assert(first == 5 && yes);
}
}"#,
        "assert(first == 5 && yes);",
        "assert(first == 5 && !yes);",
        "assertion failed",
    );
}

#[test]
fn pattern_initializer_runs_once_before_shadowing() {
    pair(
        "struct_pattern_once",
        r#"verus! {
struct Record { a: u32, b: u32 }
fn test() {
    let mut steps: u32 = 0;
    let value: u32 = 7;
    let Record { a: mut value, b } = {
        steps = steps + 1;
        Record { b: value, a: 2 }
    };
    value = value + 1;
    assert(steps == 1 && value == 3 && b == 7);
}
}"#,
        "assert(steps == 1 && value == 3 && b == 7);",
        "assert(steps == 1 && value == 3 && b == 3);",
        "assertion failed",
    );
}

#[test]
fn struct_update_preserves_written_then_base_effect_order() {
    pair(
        "struct_update_order",
        r#"verus! {
struct S { b: u32, a: u32, c: u32 }
fn test() {
    let mut base = S { a: 0, b: 0, c: 19 };
    let mut x: u32 = 24;
    let result = S { a: x, b: { x = 60; 30 },
        ..{ base = S { a: 13, b: 14, c: 199 }; base } };
    assert(result.a == 24 && result.b == 30 && result.c == 199 && x == 60);
}
}"#,
        "assert(result.a == 24 && result.b == 30 && result.c == 199 && x == 60);",
        "assert(result.a == 60 && result.b == 30 && result.c == 199 && x == 60);",
        "assertion failed",
    );
}

#[test]
fn every_field_overridden_still_evaluates_the_base_once() {
    pair(
        "struct_update_all",
        r#"verus! {
struct S { a: u32, b: u32 }
fn test() {
    let mut calls: u32 = 0;
    let base = S { a: 1, b: 2 };
    let result = S { a: 5, b: 7, ..{ calls = calls + 1; base } };
    assert(calls == 1 && result.a == 5 && result.b == 7);
}
}"#,
        "assert(calls == 1 && result.a == 5 && result.b == 7);",
        "assert(calls == 0 && result.a == 5 && result.b == 7);",
        "assertion failed",
    );
}

#[test]
fn generic_update_reads_the_base_fields_at_their_actual_types() {
    pair(
        "struct_update_generic",
        r#"verus! {
struct Wrapped<T> { n: int, payload: T }
proof fn test(x: Wrapped<bool>) {
    let result = Wrapped { n: x.n + 1, ..x };
    assert(result.n == x.n + 1 && result.payload == x.payload);
}
}"#,
        "assert(result.n == x.n + 1 && result.payload == x.payload);",
        "assert(result.n == x.n + 1 && result.payload != x.payload);",
        "assertion failed",
    );
}

#[test]
fn pure_struct_patterns_and_updates_use_scoped_value_lets() {
    pair(
        "struct_spec_values",
        r#"verus! {
struct S<T> { value: T, counter: int }
spec fn adjusted(s: S<bool>) -> bool {
    let S { value, counter } = s;
    let next = S { counter: counter + 1, ..s };
    next.value == value && next.counter == counter + 1
}
proof fn test(s: S<bool>) {
    assert(adjusted(s));
}
}"#,
        "assert(adjusted(s));",
        "assert(!adjusted(s));",
        "assertion failed",
    );
}

#[test]
fn owned_non_copy_struct_fields_keep_their_values() {
    pair(
        "struct_non_copy",
        r#"verus! {
struct Payload { n: u32 }
struct Envelope { payload: Payload, flag: bool }
fn test() {
    let old = Envelope { payload: Payload { n: 7 }, flag: true };
    let Envelope { payload, .. } = old;
    let new = Envelope { flag: false, ..Envelope { payload, flag: true } };
    assert(new.payload.n == 7 && !new.flag);
}
}"#,
        "assert(new.payload.n == 7 && !new.flag);",
        "assert(new.payload.n == 8 && !new.flag);",
        "assertion failed",
    );
}

#[test]
fn an_unused_base_still_checks_its_call_precondition() {
    pair(
        "struct_base_requires",
        r#"verus! {
struct S { a: u32 }
fn base(n: u32) -> (r: S)
    requires n > 0,
    ensures r.a == n,
{ S { a: n } }
fn test() {
    let result = S { a: 4, ..base(1) };
    assert(result.a == 4);
}
}"#,
        "let result = S { a: 4, ..base(1) };",
        "let result = S { a: 4, ..base(0) };",
        "precondition not satisfied",
    );
}

#[test]
fn native_ownership_rejects_a_second_move_of_a_destructured_field() {
    let run = common::run(
        "struct_double_move",
        r#"verus! {
struct Payload { n: u32 }
struct Envelope { payload: Payload, flag: bool }
fn consume(value: Payload) {}
fn test() {
    let original = Envelope { payload: Payload { n: 7 }, flag: true };
    let Envelope { payload, .. } = original;
    consume(payload);
    consume(original.payload);
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "erase-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.code.as_deref() == Some("E0382")),
        "{run:?}"
    );
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}

#[test]
fn all_overridden_destructor_base_keeps_ownership_and_value_checks() {
    pair(
        "struct_drop_base",
        r#"verus! {
struct Payload { n: u32 }
struct Guard { payload: Payload, flag: bool }
impl Drop for Guard {
    fn drop(&mut self) opens_invariants none no_unwind {}
}
fn test() {
    let original = Guard { payload: Payload { n: 1 }, flag: true };
    let result = Guard { payload: Payload { n: 2 }, flag: false, ..original };
    assert(result.payload.n == 2 && !result.flag);
}
}"#,
        "assert(result.payload.n == 2 && !result.flag);",
        "assert(result.payload.n == 3 && !result.flag);",
        "assertion failed",
    );
}

#[test]
fn native_ownership_rejects_moving_a_non_copy_field_from_a_destructor() {
    let run = common::run(
        "struct_drop_move",
        r#"verus! {
struct Payload { n: u32 }
struct Guard { payload: Payload, flag: bool }
impl Drop for Guard {
    fn drop(&mut self) opens_invariants none no_unwind {}
}
fn test() {
    let original = Guard { payload: Payload { n: 1 }, flag: true };
    let result = Guard { flag: false, ..original };
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "erase-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.code.as_deref() == Some("E0509")),
        "{run:?}"
    );
}

#[test]
fn borrowing_aliases_and_mode_decorated_fields_stay_outside_the_slice() {
    for (name, source) in [
        (
            "struct_ref",
            r#"verus! { struct S { a: u32 } fn test() {
            let value = S { a: 1 }; let S { a } = &value; assert(*a == 1);
        } }"#,
        ),
        (
            "struct_explicit_ref",
            r#"verus! { struct S { a: u32 } fn test() {
            let S { ref a } = S { a: 1 }; assert(*a == 1);
        } }"#,
        ),
        (
            "struct_borrowed_update",
            r#"verus! { struct S { a: u32 }
            fn test(value: &S) { let updated = S { a: 2, ..*value }; assert(updated.a == 2); }
        }"#,
        ),
        (
            "struct_nested_borrow",
            r#"verus! {
            #[derive(Copy, Clone)] struct S { x: u32 }
            fn test(r: &S) { let (S { x },) = (*r,); assert(x == r.x); }
        }"#,
        ),
        (
            "struct_nested_block_borrow",
            r#"verus! {
            #[derive(Copy, Clone)] struct S { x: u32 }
            fn test(r: &S) { let (S { x },) = ({ *r },); assert(x == r.x); }
        }"#,
        ),
        (
            "struct_constructor_borrowed",
            r#"verus! {
            #[derive(Copy, Clone)] struct S { x: u32 }
            struct W(S);
            fn test(r: &S) { let W(S { x }) = W(*r); assert(x == r.x); }
            }"#,
        ),
        (
            "struct_alias",
            r#"verus! { struct S { a: u32 } fn test() {
            let whole @ S { a } = S { a: 1 }; assert(whole.a == a);
        } }"#,
        ),
        (
            "struct_enum",
            r#"verus! { enum E { V { a: u32 } } fn test() {
            let E::V { a } = E::V { a: 1 }; assert(a == 1);
        } }"#,
        ),
        (
            "struct_ghost_field",
            r#"verus! { struct S { ghost a: int } proof fn test(s: S) {
            let S { a } = s; assert(a == a);
        } }"#,
        ),
        (
            "struct_tracked_field",
            r#"verus! { struct S { tracked a: u32 } proof fn test(s: S) {
            let S { a } = s; assert(a == a);
        } }"#,
        ),
        (
            "struct_opaque",
            r#"verus! { #[verifier::external_body] struct S { a: u32 }
            proof fn test(s: S) { let S { a } = s; assert(a == a); }
        }"#,
        ),
        (
            "struct_tracked_param",
            r#"verus! { struct S { a: u32 }
            proof fn test(tracked s: S) { let S { a } = s; assert(a == a); }
        }"#,
        ),
    ] {
        let run = common::run(name, source, &[]);
        assert_eq!(run.outcome(), "refused", "{name}: {run:?}");
        assert!(run.raw.is_empty(), "{name}: {run:?}");
        assert!(run.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|function| function["verdict"] != "verified"));
    }
}

#[test]
fn open_spec_pattern_cannot_reveal_private_fields() {
    let run = common::run(
        "struct_private_pattern",
        r#"verus! {
mod m {
    pub struct S { a: u32 }
    pub open spec fn reveal(s: S) -> u32 { let S { a } = s; a }
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.message == "disallowed: pattern constructor for an opaque datatype"),
        "{run:?}"
    );
}

#[test]
fn struct_spec_unused_pattern_retains_inline_proof_obligations() {
    pair(
        "struct_spec_unused_pattern",
        r#"verus! {
struct S { value: bool }
spec fn result(s: S, n: nat) -> bool decreases n {
    if n == 0 { true } else {
        let S { .. } = { proof { assert(true); } s };
        result(s, (n - 1) as nat)
    }
}
proof fn test(s: S) { reveal_with_fuel(result, 2); assert(result(s, 1)); }
}"#,
        "assert(true);",
        "assert(false);",
        "assertion failed",
    );
}

#[test]
fn struct_spec_unused_base_retains_inline_proof_obligations() {
    pair(
        "struct_spec_unused_base",
        r#"verus! {
struct S { value: bool }
spec fn result(s: S, n: nat) -> bool decreases n {
    if n == 0 { true } else {
        let next = S { value: true, ..{ proof { assert(true); } s } };
        result(next, (n - 1) as nat)
    }
}
proof fn test(s: S) { reveal_with_fuel(result, 2); assert(result(s, 1)); }
}"#,
        "assert(true);",
        "assert(false);",
        "assertion failed",
    );
}

#[test]
fn a_plain_spec_binding_keeps_its_earlier_proof_block_rejection() {
    let run = common::run(
        "struct_plain_spec_proof_error",
        r#"verus! {
proof fn p() -> int { 3 }
spec fn f(i: int) -> int decreases i {
    let x = proof { p() };
    x
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(
        errors[0].message, "proof block must have type ()",
        "{run:?}"
    );
    assert!(run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|f| f["verdict"] != "verified"));
}
