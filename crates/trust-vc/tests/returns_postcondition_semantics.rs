// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Runtime/verification coverage for Verus-style `#[trust_vc::returns(expr)]`.

mod common;

use trust_vc_core::VerifyResult;

#[trust_vc::returns(20u8)]
fn returns_literal_postcondition() -> u8 {
    20u8
}

#[trust_vc::returns(20u8)]
fn returns_literal_postcondition_from_explicit_return(flag: bool) -> u8 {
    if flag {
        return 20u8;
    }
    20u8
}

#[trust_vc::returns(())]
fn returns_unit_postcondition_from_explicit_return(flag: bool) {
    if flag {
        return;
    }
}

#[trust_vc::returns(20u8)]
fn returns_literal_postcondition_wrong_value() -> u8 {
    19u8
}

#[trust_vc::contract(ensures(*result == *x), returns(result))]
fn returns_reference_postcondition<'a>(x: &'a u64) -> &'a u64 {
    x
}

#[trust_vc::contract(ensures(*result == *x), returns(result))]
fn returns_reference_postcondition_wrong<'a>(x: &'a u64, y: &'a u64) -> &'a u64 {
    let _ = x;
    y
}

#[trust_vc::returns(x)]
fn returns_reference_direct_attr_postcondition<'a>(x: &'a u64) -> &'a u64 {
    x
}

#[trust_vc::returns(x)]
fn returns_reference_direct_attr_postcondition_wrong<'a>(x: &'a u64, y: &'a u64) -> &'a u64 {
    let _ = x;
    y
}

#[test]
fn returns_expression_postcondition_verifies_tail_value() {
    let result = common::verify_and_get_result(|| {
        assert_eq!(returns_literal_postcondition(), 20u8);
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "tail-expression returns postcondition should verify, got: {result:?}"
    );
}

#[test]
fn returns_expression_postcondition_verifies_explicit_return_value() {
    let result = common::verify_and_get_result(|| {
        assert_eq!(
            returns_literal_postcondition_from_explicit_return(true),
            20u8
        );
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "explicit-return postcondition should verify, got: {result:?}"
    );
}

#[test]
fn returns_expression_postcondition_verifies_unit_return_value() {
    let result = common::verify_and_get_result(|| {
        returns_unit_postcondition_from_explicit_return(true);
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "unit explicit-return postcondition should verify, got: {result:?}"
    );
}

#[test]
fn returns_expression_postcondition_verifies_reference_return() {
    let result = common::verify_and_get_result(|| {
        let x = 7u64;
        let returned = returns_reference_postcondition(&x);
        assert_eq!(*returned, 7u64);
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "reference-return postcondition should verify, got: {result:?}"
    );
}

#[test]
fn returns_expression_postcondition_verifies_direct_attr_reference_ident() {
    let result = common::verify_and_get_result(|| {
        let x = 7u64;
        let returned = returns_reference_direct_attr_postcondition(&x);
        assert_eq!(*returned, 7u64);
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "direct reference-return postcondition should verify, got: {result:?}"
    );
}

#[test]
fn returns_expression_postcondition_rejects_wrong_value() {
    let result = common::verify_and_get_result(|| {
        assert_eq!(returns_literal_postcondition_wrong_value(), 19u8);
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "wrong return value should be rejected, got: {result:?}"
    );
}

#[test]
fn returns_expression_postcondition_rejects_wrong_reference_return() {
    let result = common::verify_and_get_result(|| {
        let x = 7u64;
        let y = 9u64;
        let returned = returns_reference_postcondition_wrong(&x, &y);
        assert_eq!(*returned, 9u64);
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "wrong reference return should be rejected, got: {result:?}"
    );
}

#[test]
fn returns_expression_postcondition_rejects_wrong_direct_attr_reference_ident() {
    let result = common::verify_and_get_result(|| {
        let x = 7u64;
        let y = 9u64;
        let returned = returns_reference_direct_attr_postcondition_wrong(&x, &y);
        assert_eq!(*returned, 9u64);
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "wrong direct reference return should be rejected, got: {result:?}"
    );
}
