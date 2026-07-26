// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;

#[test]
fn test_missing_return_expression_returns_error() {
    // A function with a return type but whose body ends with a semicolon
    // (no trailing expression) causes find_return_expression to return None.
    // This leaves the `result` variable unconstrained — postconditions
    // referencing `result` would be trivially satisfiable (unsound).
    // Fail-closed: return error instead of proceeding silently. #2251.
    let code = r#"
        #[ensures(result > 0)]
        fn no_return_expr() -> i32 {
            let x = 42;
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "no_return_expr").unwrap();

    let result = extract_verification_conditions(func);
    assert!(
        result.is_err(),
        "Should return error when return type exists but no return expression detected"
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("no detectable return expression"),
        "Error should mention missing return expression, got: {}",
        err
    );
}

#[test]
fn test_panic_body_with_return_type_returns_error() {
    // `panic!()` is an unsupported macro body expression. Treating it as an
    // opaque return expression would silently skip the macro's control-flow
    // semantics, so extraction must fail closed.
    let code = r#"
        #[ensures(result > 0)]
        fn always_positive() -> i32 {
            panic!("Not implemented")
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "always_positive").unwrap();
    let err = extract_verification_conditions(func)
        .expect_err("unsupported panic! body expression must fail closed");
    let message = err.to_string();
    assert!(
        message.contains("panic"),
        "error should mention the unsupported panic! macro, got: {message}"
    );
}

#[test]
fn test_default_return_unit_statement_extracts_without_result_var() {
    let code = r#"
        fn direct_unit_return() {
            return ();
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "direct_unit_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(
        !vc.variables.iter().any(|v| v.name == "result"),
        "default-return functions should not synthesize result"
    );
}

#[test]
fn test_explicit_unit_return_type_constrains_result_to_unit() {
    let code = r#"
        #[ensures(result == ())]
        fn explicit_unit_return() -> () {
            return ();
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "explicit_unit_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(vc
        .variables
        .iter()
        .any(|v| v.name == "result" && v.ty == TrustVcType::Unit));
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "result == ()"));
}

#[test]
fn test_explicit_unit_return_type_allows_bare_return() {
    let code = r#"
        #[ensures(result == ())]
        fn explicit_unit_bare_return() -> () {
            return;
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "explicit_unit_bare_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "result == ()"));
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "bare unit return postcondition should verify, got: {result:?}"
    );
}

#[test]
fn test_explicit_unit_return_type_allows_empty_body() {
    let code = r#"
        #[ensures(result == ())]
        fn explicit_unit_empty_body() -> () {
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "explicit_unit_empty_body").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert!(vc
        .obligations
        .iter()
        .any(|o| o.name == "return_value" && o.condition == "result == ()"));
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "empty explicit unit body postcondition should verify, got: {result:?}"
    );
}

#[test]
fn test_nested_bare_unit_return_with_tail_constrains_result_to_unit() {
    let code = r#"
        #[ensures(result == ())]
        fn nested_bare_unit_return(flag: bool) -> () {
            if flag {
                return;
            }
            ()
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "nested_bare_unit_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let return_value = vc
        .obligations
        .iter()
        .find(|o| o.name == "return_value")
        .expect("nested bare unit return should emit a return_value assumption");
    assert!(
        return_value.condition.contains("result == ()"),
        "nested bare unit return should constrain result to unit, got: {}",
        return_value.condition
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "unit postcondition should verify for both return paths, got: {result:?}"
    );
}

#[test]
fn test_nested_bare_unit_return_with_implicit_tail_constrains_result_to_unit() {
    let code = r#"
        #[ensures(result == ())]
        fn nested_bare_unit_return_implicit_tail(flag: bool) -> () {
            if flag {
                return;
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "nested_bare_unit_return_implicit_tail").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let return_value = vc
        .obligations
        .iter()
        .find(|o| o.name == "return_value")
        .expect("nested bare unit return should emit a return_value assumption");
    assert!(
        return_value.condition.contains("result == ()"),
        "nested bare unit return should constrain result to unit, got: {}",
        return_value.condition
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "unit postcondition should verify for explicit and implicit unit paths, got: {result:?}"
    );
}

#[test]
fn test_non_unit_bare_return_remains_fail_closed() {
    let code = r#"
        #[ensures(result == 1u64)]
        fn non_unit_bare_return() -> u64 {
            return;
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "non_unit_bare_return").unwrap();
    let err = extract_verification_conditions(func)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("explicit return without value"),
        "non-unit bare return should remain fail-closed, got: {err}"
    );
}

#[test]
fn test_nested_unit_return_with_tail_constrains_result_to_unit() {
    let code = r#"
        #[ensures(result == ())]
        fn nested_unit_return(flag: bool) -> () {
            if flag {
                return ();
            }
            ()
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "nested_unit_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let return_value = vc
        .obligations
        .iter()
        .find(|o| o.name == "return_value")
        .expect("nested unit return should emit a return_value assumption");
    assert!(
        return_value.condition.contains("result == ()"),
        "nested unit return should constrain result to unit, got: {}",
        return_value.condition
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "unit postcondition should verify for both return paths, got: {result:?}"
    );
}

#[test]
fn test_default_return_sibling_helper_registers_unit_type() {
    let code = r#"
        fn returns_unit() {}

        #[ensures(result == returns_unit())]
        fn calls_default_unit_helper() -> () {
            returns_unit()
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "calls_default_unit_helper").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let (return_ty, params, _) = vc
        .helper_functions_typed
        .get("returns_unit")
        .expect("referenced default-return sibling helper should be typed");

    assert_eq!(return_ty, &TrustVcType::Unit);
    assert!(
        params.is_empty(),
        "zero-argument unit helper should keep an empty parameter list"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "unit-return sibling helper postcondition should verify, got: {result:?}"
    );
}

#[test]
fn test_default_return_sibling_helper_unit_argument_verifies() {
    let code = r#"
        fn returns_unit() {}
        fn takes_unit(_u: ()) {}

        #[ensures(result == ())]
        fn passes_default_unit_helper_result() -> () {
            takes_unit(returns_unit())
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "passes_default_unit_helper_result").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    for helper in ["returns_unit", "takes_unit"] {
        let (return_ty, _, _) = vc
            .helper_functions_typed
            .get(helper)
            .expect("referenced default-return sibling helper should be typed");
        assert_eq!(return_ty, &TrustVcType::Unit);
    }

    let (_, takes_unit_params, _) = vc
        .helper_functions_typed
        .get("takes_unit")
        .expect("takes_unit should be registered");
    assert_eq!(
        takes_unit_params,
        &vec![("_u".to_string(), TrustVcType::Unit)]
    );

    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "unit helper result should be accepted as a unit argument, got: {result:?}"
    );
}

#[test]
fn test_async_default_return_sibling_helper_is_not_typed_as_unit() {
    let code = r#"
        async fn async_returns_unit() {}

        #[ensures(async_returns_unit() == ())]
        fn mentions_async_helper() -> () {
            ()
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "mentions_async_helper").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        !vc.helper_functions_typed.contains_key("async_returns_unit"),
        "async fn calls produce futures, so default async helpers must not be typed as Unit"
    );
}
