// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;

#[test]
fn test_extract_simple_function() {
    let code = r#"
        #[requires(x > 0)]
        #[ensures(result > x)]
        fn increment(x: i32) -> i32 {
            trust_vc::assert!(x > 0);
            x + 1
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "increment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    // Check that we extracted the variables (x parameter and result)
    assert_eq!(vc.variables.len(), 2);
    assert!(vc.variables.iter().any(|v| v.name == "x"));
    assert!(vc.variables.iter().any(|v| v.name == "result"));

    // Check that we extracted the precondition and return value assumption
    let assumptions_count = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .count();
    assert_eq!(assumptions_count, 2); // precondition + return value

    // Check that we extracted the postcondition
    assert!(!vc.obligations.is_empty());
}

#[test]
fn test_extract_contract_attribute_requires_ensures() {
    let code = r#"
        #[trust_vc::contract(
            requires(x > 0, x < 100),
            ensures(result == x),
            returns(result),
        )]
        fn identity(x: i32) -> i32 {
            x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "identity").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let preconditions: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume) && o.name == "precondition")
        .collect();
    assert_eq!(preconditions.len(), 2);
    assert!(preconditions
        .iter()
        .any(|obligation| obligation.condition == "x > 0"));
    assert!(preconditions
        .iter()
        .any(|obligation| obligation.condition == "x < 100"));

    let postcondition = vc
        .obligations
        .iter()
        .find(|o| o.name == "postcondition")
        .expect("contract ensures should emit a postcondition");
    assert_eq!(postcondition.condition, "result == x");

    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "result == x"));
}

#[test]
fn test_contract_returns_named_binding_connects_postcondition() {
    let code = r#"
        #[trust_vc::contract(
            ensures(ret == 20u8),
            returns(ret),
        )]
        fn returns_twenty() -> u8 {
            20u8
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "returns_twenty").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert!(vc
        .variables
        .iter()
        .any(|v| v.name == "ret" && v.ty == TrustVcType::Uint { width: 8 }));
    assert!(!vc.variables.iter().any(|v| v.name == "result"));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "postcondition" && o.condition == "ret == 20u8"));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "ret == 20u8"));

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "named returns binding should prove the postcondition, got: {result:?}"
    );
}

#[test]
fn test_extract_standalone_recommends_attribute() {
    let code = r#"
        #[recommends(x > 0)]
        fn target(x: i32) {}
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "target").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let recommendation = vc
        .obligations
        .iter()
        .find(|o| matches!(o.kind, ObligationKind::Recommends))
        .expect("standalone recommends should emit a recommendation obligation");
    assert_eq!(recommendation.name, "recommendation");
    assert_eq!(recommendation.condition, "x > 0");
}

#[test]
fn test_find_function_discovers_method_in_impl_block() {
    let code = r#"
        struct Counter { value: u32 }

        impl Counter {
            #[ensures(result == x)]
            fn identity(x: i32) -> i32 {
                x
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "identity")
        .expect("find_function should discover methods inside impl blocks");
    let vc = extract_verification_conditions(func).unwrap();

    assert!(vc.variables.iter().any(|v| v.name == "x"));
    assert!(vc.variables.iter().any(|v| v.name == "result"));
    assert!(!vc.obligations.is_empty());
}

#[test]
fn test_find_function_discovers_function_in_inline_module() {
    let code = r#"
        mod inner {
            #[ensures(result == x)]
            fn identity(x: i32) -> i32 {
                x
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "identity")
        .expect("find_function should discover functions inside inline modules");
    let vc = extract_verification_conditions(func).unwrap();

    assert!(vc.variables.iter().any(|v| v.name == "x"));
    assert!(vc.variables.iter().any(|v| v.name == "result"));
}

#[test]
fn test_find_function_prefers_top_level_over_impl_method() {
    let code = r#"
        #[ensures(result == x + 1)]
        fn add(x: i32) -> i32 {
            x + 1
        }

        struct Foo;
        impl Foo {
            #[ensures(result == x + 2)]
            fn add(x: i32) -> i32 {
                x + 2
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "add").expect("find_function should find the function");
    let vc = extract_verification_conditions(func).unwrap();

    // Should find the top-level function (ensures result == x + 1),
    // not the impl method (ensures result == x + 2).
    let postcondition = vc
        .obligations
        .iter()
        .find(|o| o.name == "postcondition")
        .expect("should have postcondition");
    assert!(
        postcondition.condition.contains("x + 1"),
        "should prefer top-level function, got: {}",
        postcondition.condition
    );
}
