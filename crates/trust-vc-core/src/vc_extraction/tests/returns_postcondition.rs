// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn bare_returns_shared_ref_ident_is_direct_postcondition_from_file() {
    let code = r#"
        #[trust_vc::returns(x)]
        fn returns_input_ref<'a>(x: &'a u64) -> &'a u64 {
            x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "returns_input_ref").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(vc.variables.iter().any(|v| v.name == "result"));
    assert!(vc.variables.iter().any(|v| v.name == "x"));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "postcondition" && o.condition == "result == (x)"));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "result == x"));

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "direct shared-reference returns postcondition should verify, got: {result:?}"
    );
}

#[test]
fn bare_returns_shared_ref_ident_rejects_wrong_return_from_file() {
    let code = r#"
        #[trust_vc::returns(x)]
        fn returns_other_ref<'a>(x: &'a u64, y: &'a u64) -> &'a u64 {
            let _ = x;
            y
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "returns_other_ref").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "wrong direct shared-reference return should be rejected, got: {result:?}"
    );
}

#[test]
fn bare_returns_value_param_ident_collides_with_param_name() {
    // Previously this shape kept a "legacy binding" (the return value bound
    // to the param's own name). Upstream rejects it at macro expansion
    // (builtin_macros check_return_idents; basic.rs
    // test_fail_return_value_parameter_same_name: `fn foo(x: u64) -> (x:
    // bool)`) — "return value name collides with a parameter name". The
    // legacy binding stays available under any NON-colliding name
    // (`returns(ret)`, exercised by the ported returns_postcondition.rs
    // corpus `returns_basic_direct_attr_legacy_ident_binding`).
    let code = r#"
        #[trust_vc::returns(x)]
        fn value_param_binding(x: u8) -> u8 {
            x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "value_param_binding").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();
    assert!(
        err.to_string()
            .contains("return value name collides with a parameter name"),
        "colliding value-param returns binding must carry the upstream message, got: {err}"
    );
}

#[test]
fn bare_returns_shared_ref_ident_unsupported_referent_fails_closed_from_file() {
    let code = r#"
        struct Token {
            value: u64,
        }

        #[trust_vc::returns(x)]
        fn returns_token_ref<'a>(x: &'a Token) -> &'a Token {
            x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "returns_token_ref").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("unsupported direct #[returns] shared-reference identifier `x`"),
        "unsupported referent should fail closed, got: {message}"
    );
}

#[test]
fn bare_returns_typed_literal_mismatch_fails_closed_from_file() {
    let code = r#"
        #[trust_vc::returns(20u8)]
        fn returns_wrong_literal_type() -> bool {
            true
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "returns_wrong_literal_type").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("type of `returns` clause does not match function return type"),
        "typed literal mismatch should fail closed, got: {message}"
    );
}

#[test]
fn bare_returns_legacy_ident_binding_still_extracts_from_file() {
    let code = r#"
        #[trust_vc::returns(ret)]
        fn returns_legacy_binding(x: u8) -> u8 {
            x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "returns_legacy_binding").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(vc.variables.iter().any(|v| v.name == "ret"));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "ret == x"));
    assert!(!vc
        .obligations
        .iter()
        .any(|o| o.name == "postcondition" && o.condition == "result == (ret)"));
}

#[test]
fn direct_returns_on_spec_function_fails_closed_from_file() {
    let code = r#"
        #[trust_vc::spec]
        #[trust_vc::returns(result)]
        fn spec_with_returns(x: u8) -> bool {
            x == 3u8
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "spec_with_returns").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("spec functions cannot have `returns` clause"),
        "spec returns should fail closed, got: {message}"
    );
}

#[test]
fn grouped_returns_on_spec_function_fails_closed_from_file() {
    let code = r#"
        #[trust_vc::spec]
        #[trust_vc::contract(ensures(result == x), returns(result))]
        fn spec_with_grouped_returns(x: u8) -> u8 {
            x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "spec_with_grouped_returns").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("spec functions cannot have `returns` clause"),
        "grouped spec returns should fail closed, got: {message}"
    );
}

#[test]
fn trait_default_returns_postcondition_rejects_wrong_body_from_file() {
    let code = r#"
        #[trust_vc::trait_spec]
        trait DefaultTraitReturnsPostcondition {
            #[trust_vc::returns(true)]
            fn default_returns_false() -> bool {
                false
            }
        }

        #[trust_vc::trait_impl]
        impl DefaultTraitReturnsPostcondition for bool {}
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "default_returns_false").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(vc.variables.iter().any(|v| v.name == "result"));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "postcondition" && o.condition == "result == (true)"));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "result == false"));

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "wrong trait default returns postcondition should be rejected, got: {result:?}"
    );
}
