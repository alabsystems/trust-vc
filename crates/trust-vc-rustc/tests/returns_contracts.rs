//! Actual native scalar return contracts, false twins and mode boundaries.
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
fn exec_proof_and_symbolic_scalar_contracts_are_checked() {
    checked(
        "scalar_returns",
        "verus! {
        fn literal() -> u8 returns 20u8, { 20u8 }
        proof fn proof_literal() -> u8 returns 20u8, { 20u8 }
        fn symbolic(a: u8, b: u8) -> u8
            requires a + b < 256,
            returns (a + b) as u8,
        { a + b }
        fn caller(a: u8) {
            let value = literal(); assert(value == 20);
            let sum = symbolic(a, 0); assert(sum == a);
        }
        fn boolean(b: bool) -> bool returns !b, { !b }
    }",
    );
}

#[test]
fn false_tail_explicit_return_and_caller_remain_proof_failures() {
    let result = common::run(
        "false_returns",
        "verus! {
        fn tail() -> u8 returns 20u8, { 19u8 }
        fn explicit() -> u8 returns 20u8, { return 19u8; }
        fn correct() -> u8 returns 20u8, { 20u8 }
        fn caller() { let value = correct(); assert(value == 19); }
    }",
        &[],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 3, "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
}

#[test]
fn named_ensures_and_returns_both_constrain_the_result() {
    checked(
        "named_and_returns",
        "verus! {
        fn value(a: u8) -> (r: u8) ensures r == a, returns a, { a }
        fn caller(a: u8) { let r = value(a); assert(r == a); }
    }",
    );
    let result = common::run(
        "false_named_and_returns",
        "verus! {
        fn value(a: u8) -> (r: u8) ensures r < a, returns a, { a }
    }",
        &[],
    );
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 1, "{result:?}");
}

#[test]
fn malformed_and_spec_contracts_keep_the_original_rejections() {
    for (name, source, diagnostic) in [
        (
            "wrong_returns_type",
            "verus! { fn f() -> bool returns 20u8, { true } }",
            "type of `returns` clause does not match function return type",
        ),
        (
            "spec_returns",
            "verus! { spec fn f() -> u8 returns 20u8, { 20u8 } }",
            "spec functions cannot have `returns` clause",
        ),
        (
            "duplicate_returns",
            "verus! { fn f() -> u8 returns 1u8, {
            verus_builtin::returns(1u8); 1u8
        } }",
            "only one call to returns allowed",
        ),
        (
            "ensures_still_needs_name",
            "verus! { fn f() -> u8 ensures true, returns 1u8, { 1u8 } }",
            "the return value must be named in a function with an ensures clause",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
        assert!(
            result
                .errors()
                .iter()
                .any(|error| error.message.contains(diagnostic)),
            "{result:?}"
        );
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
}

#[test]
fn returns_cannot_launder_exec_effects_or_ghost_values() {
    let rejected_walk =
        Some("trust-vc refused: returns-header: a returns value has a rejected native mode walk");
    for (name, source, outcome, diagnostic) in [
        (
            "exec_in_returns",
            "verus! {
            fn effect() -> u8 { 1u8 }
            fn value() -> u8 returns effect(), { 1u8 }
        }",
            "refused",
            rejected_walk,
        ),
        (
            "spec_in_exec_body",
            "verus! {
            spec fn hidden() -> u8 { 1u8 }
            fn value() -> u8 returns 1u8, { hidden() }
        }",
            "refused",
            rejected_walk,
        ),
        (
            "proof_in_exec_body",
            "verus! {
            proof fn hidden() -> u8 returns 1u8, { 1u8 }
            fn value() -> u8 { hidden() }
        }",
            "verus-rejected",
            None,
        ),
        (
            "proof_statement_in_returns",
            "verus! {
            fn value() -> u8 returns ({ assume(false); 1u8 }), { 1u8 }
        }",
            "refused",
            Some("trust-vc refused: expr: a statement inside spec code"),
        ),
        (
            "proof_call_in_returns",
            "verus! {
            proof fn helper() -> u8 { 1u8 }
            fn value() -> u8 returns helper(), { 1u8 }
        }",
            "refused",
            rejected_walk,
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), outcome, "{result:?}");
        if let Some(diagnostic) = diagnostic {
            assert!(
                result
                    .errors()
                    .iter()
                    .any(|error| error.message == diagnostic),
                "{result:?}"
            );
        }
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
}

#[test]
fn an_ordinary_function_named_returns_supplies_no_contract() {
    let result = common::run(
        "returns_name_is_not_permission",
        "verus! {
        fn returns(value: u8) {}
        fn value() -> u8 { returns(1u8); 2u8 }
        fn caller() { let r = value(); assert(r == 1); }
    }",
        &[],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 1, "{result:?}");
}

#[test]
fn unit_returns_are_checked_without_a_generated_result_obligation() {
    checked(
        "unit_returns",
        "verus! {
        fn explicit() -> () returns (), { () }
        fn implicit() returns (), { }
        fn caller() { explicit(); implicit(); assert(true); }
    }",
    );
}

#[test]
fn unsupported_owner_and_entry_state_shapes_still_refuse() {
    for (name, source) in [
        (
            "mutable_parameter",
            "verus! { fn f(mut a: u8) -> u8 returns a, { a = 2; a } }",
        ),
        (
            "trait_returns",
            "verus! { trait T { fn f() -> u8 returns 1u8; } }",
        ),
        (
            "nominal_returns",
            "verus! { struct S { x: u8 } fn f() -> S returns (S { x: 1u8 }), { S { x: 1u8 } } }",
        ),
        (
            "external_returns",
            "verus! { #[verifier::external_body] fn f() -> u8 returns 1u8, { unimplemented!() } }",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "refused", "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
}
