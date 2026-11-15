// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// #1801: Silent drops in vc_extraction — parse failures, unhandled
// expr variants, and unsupported parameter patterns
// ================================================================

#[test]
fn test_requires_parse_failure_returns_error() {
    // A malformed #[requires] attribute should return Err, not silently
    // drop the precondition (which would produce a false verification pass).
    let code = r#"
        #[requires(!!!)]
        fn bad_requires(x: i32) {
            let _ = x;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "bad_requires").unwrap();
    let result = extract_verification_conditions(func);
    assert!(
        result.is_err(),
        "malformed #[requires] must produce an error, not silently drop (#1801)"
    );
}

#[test]
fn test_ensures_parse_failure_returns_error() {
    // A malformed #[ensures] attribute should return Err.
    let code = r#"
        #[ensures(!!!)]
        fn bad_ensures(x: i32) -> i32 {
            x
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "bad_ensures").unwrap();
    let result = extract_verification_conditions(func);
    assert!(
        result.is_err(),
        "malformed #[ensures] must produce an error, not silently drop (#1801)"
    );
}

#[test]
fn test_contract_parse_failure_returns_error() {
    let code = r#"
        #[trust_vc::contract(requires(!!!))]
        fn bad_contract(x: i32) {
            let _ = x;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "bad_contract").unwrap();
    let result = extract_verification_conditions(func);
    assert!(
        result.is_err(),
        "malformed #[contract] must produce an error, not silently drop (#1801)"
    );
}

#[test]
fn test_contract_unknown_clause_returns_error() {
    let code = r#"
        #[trust_vc::contract(unknown_clause(true))]
        fn bad_contract_clause() {}
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "bad_contract_clause").unwrap();
    let result = extract_verification_conditions(func);
    assert!(
        result.is_err(),
        "unknown #[contract] clauses must produce an error, not silently drop"
    );
}

#[test]
fn test_extract_assertion_in_closure_body() {
    // Assertions inside closure bodies were silently dropped before #1801.
    let code = r#"
        fn check_closure(x: i32) {
            let f = || { assert!(x > 0); };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_closure").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside closure body must be extracted (#1801)"
    );
}

#[test]
fn test_extract_assertion_in_return_expr() {
    // Assertions in return expressions (return { assert!(...); val })
    // were silently dropped before #1801.
    let code = r#"
        fn check_return(x: i32) -> i32 {
            return { assert!(x > 0); x };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside return expression must be extracted (#1801)"
    );
}

#[test]
fn test_extract_assert_eq_and_assert_ne() {
    let code = r#"
        fn check_eq_ne(x: i32, y: i32) {
            assert_eq!(x + 1, y, "ignored message");
            assert_ne!(x, y + 2, "ignored message");
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_eq_ne").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        collect_assert_conditions(&vc),
        vec!["x + 1 == y".to_string(), "x != y + 2".to_string()],
        "assert_eq!/assert_ne! should lower to comparison obligations"
    );
}

#[test]
fn test_literal_assertion_ignores_surrounding_lowercase_noise_1139() {
    let code = r#"
        fn check_literal_assertion() {
            let helper_name = "lowercase text should not affect extraction";
            let _ = helper_name;
            assert!(true);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_literal_assertion").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        collect_assert_conditions(&vc),
        vec!["true".to_string()],
        "literal assert! extraction must depend on the macro expression, not nearby lowercase text"
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "assert!(true) with lowercase identifiers/string literals nearby should still verify"
    );
}

#[test]
fn test_debug_assert_eq_returns_error() {
    assert_debug_assert_macro_returns_error(
        "debug_assert_eq!(x, x, \"debug-only\")",
        "debug_assert_eq",
    );
}

#[test]
fn test_debug_assert_returns_error() {
    assert_debug_assert_macro_returns_error("debug_assert!(x > 0, \"debug-only\")", "debug_assert");
}

#[test]
fn test_debug_assert_ne_returns_error() {
    assert_debug_assert_macro_returns_error(
        "debug_assert_ne!(x, 0, \"debug-only\")",
        "debug_assert_ne",
    );
}

fn assert_debug_assert_macro_returns_error(invocation: &str, expected_name: &str) {
    let code = r#"
        fn check_debug_assert(x: i32) {
            PLACEHOLDER_MACRO;
        }
    "#
    .replace("PLACEHOLDER_MACRO", invocation);
    let file = parse_file(&code).unwrap();
    let func = find_function(&file, "check_debug_assert").unwrap();
    let result = extract_verification_conditions(func);

    assert!(
        result.is_err(),
        "{expected_name}! must fail closed instead of being silently skipped"
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains(expected_name),
        "error should mention the unsupported {expected_name}! macro, got: {err}"
    );
}

#[test]
fn test_unknown_statement_macro_returns_error() {
    let code = r#"
        fn check_unknown_macro(x: i32) {
            unsupported_proof_step!(x);
            assert!(x > 0);
        }
    "#;

    assert_body_extraction_error(code, "check_unknown_macro", "unsupported_proof_step");
}

#[test]
fn test_unknown_expression_macro_returns_error() {
    let code = r#"
        fn check_unknown_expr_macro(x: i32) {
            let _ = (unsupported_expr_proof!(x), x);
        }
    "#;

    assert_body_extraction_error(code, "check_unknown_expr_macro", "unsupported_expr_proof");
}

#[test]
fn test_unknown_macro_in_indexed_assignment_index_returns_error() {
    let code = r#"
        fn check_unknown_macro_index(x: usize) {
            let mut a = [0, 1];
            a[unsupported_expr_proof!(x)] = 9;
        }
    "#;

    assert_body_extraction_error(code, "check_unknown_macro_index", "unsupported_expr_proof");
}

#[test]
fn test_supported_expression_macros_in_body_remain_allowed() {
    let code = r#"
        fn check_supported_expression_macros() {
            let s = seq![1i32, 2i32];
            let m = map![1i32 => 2i32];
            let witness = choose!(|n: i32| n >= 0);
            assert!(ext_eq!(s, s));
            assert!(m[1i32] == 2i32);
            assert!(witness >= 0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_supported_expression_macros").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        count_asserts(&vc),
        3,
        "supported expression macros should remain available to lowering"
    );
}

#[test]
fn test_nested_function_item_returns_error() {
    let code = r#"
        fn check_nested_function_item() {
            fn helper() {
                assert!(false);
            }
            helper();
        }
    "#;

    assert_body_extraction_error(code, "check_nested_function_item", "nested fn item");
}

#[test]
fn test_block_use_item_remains_supported() {
    let code = r#"
        fn check_block_use_item() {
            use crate::some_helper as helper;
            assert!(true);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_block_use_item").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        collect_assert_conditions(&vc),
        vec!["true".to_string()],
        "body extraction should continue to permit block use aliases"
    );
}

#[test]
fn test_function_local_macro_rules_item_expands_statement_invocation() {
    let code = r#"
        fn check_local_macro_rules_item() {
            let mut x = 1;
            macro_rules! add_1 {
                () => {
                    x = x + 1;
                };
            }
            add_1!();
            assert!(x == 2);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_local_macro_rules_item").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert_eq!(conditions.len(), 1);
    assert!(
        conditions[0].contains("== 2"),
        "expanded macro assignment should feed the assertion, got: {:?}",
        conditions
    );
    assert!(
        !conditions[0].contains('x'),
        "local macro assignment should be reflected in scoped extraction, got: {:?}",
        conditions
    );
}

#[test]
fn test_function_local_macro_rules_item_verifies_contract() {
    let code = r#"
        #[requires(start == 1)]
        #[ensures(result == start + 1)]
        #[ensures(result == 2)]
        fn check_local_macro_rules_contract(start: i32) -> i32 {
            let mut x = start;
            macro_rules! add_1 {
                () => {
                    x = x + 1;
                };
            }
            add_1!();
            assert!(x == 2);
            x
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_local_macro_rules_contract").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "function-local macro_rules! assignment should verify the mirrored nested_items contract, got: {:?}",
        result
    );
}

#[test]
fn test_function_local_macro_assignment_in_branch_invalidates_outer_scope() {
    let code = r#"
        fn check_local_macro_rules_branch(cond: bool) {
            let mut x = 1;
            macro_rules! add_1 {
                () => {
                    x = x + 1;
                };
            }
            if cond {
                add_1!();
            }
            assert!(x == 1);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_local_macro_rules_branch").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    // The silent-drop shape this guards against is `1 == 1` (the branch's
    // macro assignment ignored, `x` kept at its pre-`if` value). Since the
    // conditional join (2026-09-10) the branch write is SEEN and joined:
    // `x` renders as `if (cond) { x + 1 } else { 1 }`, an even stronger
    // witness than the bare `x == 1` invalidation this test used to pin.
    let conditions = collect_assert_conditions(&vc);
    assert_eq!(conditions.len(), 1, "exactly one assertion: {conditions:?}");
    let condition = &conditions[0];
    assert_ne!(
        condition, "1 == 1",
        "macro assignments in control-flow blocks must not be silently dropped"
    );
    assert!(
        condition == "x == 1" || condition.contains("if (cond)"),
        "the branch's macro assignment must invalidate or conditionally join the \
         outer scoped value, got: {condition}"
    );
}

#[test]
fn test_unsupported_function_local_macro_rules_item_returns_error() {
    let code = r#"
        fn check_unsupported_local_macro_rule() {
            let mut x = 1;
            macro_rules! add {
                ($n:expr) => {
                    x = x + $n;
                };
            }
            add!(1);
            assert!(x == 2);
        }
    "#;

    assert_body_extraction_error(
        code,
        "check_unsupported_local_macro_rule",
        "nested macro_rules! item",
    );
}

fn assert_body_extraction_error(code: &str, function_name: &str, expected_detail: &str) {
    let file = parse_file(code).unwrap();
    let func = find_function(&file, function_name).unwrap();
    let err = extract_verification_conditions(func)
        .expect_err("unsupported body syntax must fail closed instead of being silently skipped");
    let message = err.to_string();
    assert!(
        message.contains(expected_detail),
        "error should mention {expected_detail}, got: {message}"
    );
    assert!(
        message.contains("silently dropping proof obligations"),
        "error should explain the silent-drop risk, got: {message}"
    );
}

#[test]
fn test_wildcard_pattern_accepted() {
    // Wildcard `_` patterns are intentional — they should not error.
    let code = r#"
        fn with_wildcard(_: i32) {
            assert!(true);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "with_wildcard").unwrap();
    let result = extract_verification_conditions(func);
    assert!(
        result.is_ok(),
        "wildcard pattern _ must be accepted without error"
    );
}

// ================================================================
// Audit Round 2: Call/MethodCall arguments and let-else diverge
// ================================================================

#[test]
fn test_extract_assertion_in_call_argument() {
    // Assertions inside function call arguments were silently dropped
    // because Expr::Call was treated as a leaf expression.
    let code = r#"
        fn check_call_arg(x: i32) {
            some_fn({ assert!(x > 0); x });
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_call_arg").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside function call argument block must be extracted"
    );
}

#[test]
fn test_extract_assertion_in_method_call_argument() {
    // Assertions inside method call arguments were silently dropped
    // because Expr::MethodCall was treated as a leaf expression.
    let code = r#"
        fn check_method_arg(x: i32) {
            x.foo({ assert!(x > 0); x });
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_method_arg").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside method call argument block must be extracted"
    );
}

#[test]
fn test_extract_assertion_in_let_else_diverge() {
    // Assertions in the else branch of let-else were silently dropped
    // because only local.init.expr was recursed, not local.init.diverge.
    let code = r#"
        fn check_let_else(x: Option<i32>) {
            let Some(val) = x else {
                assert!(false);
                return;
            };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_let_else").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside let-else diverge branch must be extracted"
    );
}

#[test]
fn test_malformed_assert_stmt_returns_error() {
    // A top-level assert!() with unparseable expression must return Err,
    // not silently drop the assertion (Stmt::Macro path, #1801).
    let code = r#"
        fn bad_assert(x: i32) {
            assert!(x >);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "bad_assert").unwrap();
    let result = extract_verification_conditions(func);
    assert!(
        result.is_err(),
        "malformed assert!() must produce an error, not silently drop (#1801)"
    );
}

#[test]
fn test_malformed_assert_in_block_returns_error() {
    // A nested assert!() with unparseable expression must return Err
    // (Expr::Macro path inside a block, #1801).
    let code = r#"
        fn bad_nested_assert(x: i32) {
            if x > 0 {
                assert!(x >);
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "bad_nested_assert").unwrap();
    let result = extract_verification_conditions(func);
    assert!(
        result.is_err(),
        "malformed assert!() inside block must produce an error, not silently drop (#1801)"
    );
}

#[test]
fn test_extract_assertions_in_tuple_array_struct_and_range_expressions() {
    let code = r#"
        struct Holder {
            field: (),
        }

        fn check_nested(x: i32) {
            let _ = (
                assert!(x > 0),
                [assert!(x > 1)],
                Holder { field: assert!(x > 2) },
                0..{ assert!(x > 3); x },
            );
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_nested").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        collect_assert_conditions(&vc),
        vec![
            "x > 0".to_string(),
            "x > 1".to_string(),
            "x > 2".to_string(),
            "x > 3".to_string(),
        ],
        "visitor-backed extraction must traverse tuple, array, struct, and range forms"
    );
}

#[test]
fn test_assertions_from_same_statement_use_unique_names() {
    let code = r#"
        fn check_unique_names(x: i32) {
            let _ = (assert!(x > 0), assert_eq!(x, x));
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_unique_names").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let assertion_names: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .map(|o| o.name.clone())
        .collect();

    assert_eq!(
        assertion_names,
        vec!["assertion_0".to_string(), "assertion_1".to_string()],
        "assertions discovered from one statement must get unique monotonic names"
    );
}

#[test]
fn test_extract_chained_assertion_macro() {
    let code = r#"
        fn chained(n: u64) {
            assert!(0u64 <= n < n + 1u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "chained").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert_eq!(
        conditions.len(),
        1,
        "chained assert! should still produce one assertion obligation"
    );
    assert!(
        conditions[0].contains("0u64 <= n") && conditions[0].contains("n < n + 1u64"),
        "chained assert! should be normalized into pairwise comparisons, got {:?}",
        conditions
    );
}

#[test]
fn test_verifier_nonlinear_marks_contract_and_plain_assertions() {
    let code = r#"
        #[verifier(nonlinear)]
        #[ensures(x * x >= 0)]
        fn check_nonlinear_attr(x: i32) {
            assert!(x * x == x * x);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_nonlinear_attr").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let modes = vc
        .obligations
        .iter()
        .filter(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && (obligation.name == "postcondition" || obligation.name == "assertion_0")
        })
        .map(|obligation| obligation.solver_mode)
        .collect::<Vec<_>>();

    assert_eq!(
        modes,
        vec![
            Some(crate::vc::SolverMode::NonlinearArith),
            Some(crate::vc::SolverMode::NonlinearArith)
        ],
        "function-level #[verifier(nonlinear)] must apply to postconditions and plain assertions"
    );
}

#[test]
fn test_verifier_bit_vector_marks_plain_assertions() {
    let code = r#"
        #[trust_vc::verifier(bit_vector)]
        fn check_bv_attr(x: u32) {
            assert!(x & x == x);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_bv_attr").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| obligation.name == "assertion_0")
        .expect("plain assertion should be extracted");
    assert_eq!(
        obligation.solver_mode,
        Some(crate::vc::SolverMode::BitVector)
    );
}

#[test]
fn test_explicit_assert_by_solver_mode_overrides_verifier_attribute() {
    let code = r#"
        #[verifier(bit_vector)]
        fn check_explicit_override(x: u32) {
            trust_vc::assert_by_nonlinear!(x * x == x * x);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_explicit_override").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("assert_by_nonlinear! should lower to AssertBy");
    assert_eq!(
        obligation.solver_mode,
        Some(crate::vc::SolverMode::NonlinearArith)
    );
}

#[test]
fn test_assert_by_bit_vector_extracts_scoped_requires() {
    let code = r#"
        fn check_bv_requires(x: u32) {
            trust_vc::assert_by_bit_vector!(
                (x << 1u32) == 0x200u32;
                requires x == 0x100u32
            );
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_bv_requires").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("assert_by_bit_vector! should lower to AssertBy");
    assert_eq!(
        obligation.solver_mode,
        Some(crate::vc::SolverMode::BitVector)
    );
    assert_eq!(obligation.condition, "(x << 1u32) == 0x200u32");

    let scoped = vc
        .assert_by_scopes
        .get(&obligation.name)
        .expect("AssertBy scope should be registered");
    assert_eq!(scoped.len(), 1);
    assert_eq!(scoped[0].kind, ObligationKind::Requires);
    assert_eq!(
        scoped[0].solver_mode,
        Some(crate::vc::SolverMode::BitVector)
    );
    assert_eq!(scoped[0].condition, "x == 0x100u32");
}

#[test]
fn test_assert_by_bit_vector_registers_body_helper_calls() {
    let code = r#"
        fn add(x: u32, y: u32) -> u32 {
            x.wrapping_add(y)
        }

        fn shifter(x: u32) -> u32 {
            x >> 1u32
        }

        fn bitand_alias(x: u32, y: u32) -> u32 {
            x & y
        }

        fn check_helper_calls(u: u32, v: u32) {
            trust_vc::assert_by_bit_vector!(shifter(42u32) == 21u32);
            trust_vc::assert_by_bit_vector!(
                bitand_alias(add(u, v), add(v, u)) == add(u, v)
            );
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_helper_calls").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    for helper in ["add", "shifter", "bitand_alias"] {
        assert!(
            vc.helper_functions_typed.contains_key(helper),
            "helper `{helper}` called inside assert_by_bit_vector! should be registered"
        );
    }
}

#[test]
fn test_assert_by_compute_extracts_compute_mode_obligation() {
    let code = r#"
        fn check_compute_direct_source() {
            trust_vc::assert_by_compute!(2u32 + 3u32 == 5u32);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_compute_direct_source").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("assert_by_compute! should lower to AssertBy");
    assert_eq!(obligation.solver_mode, Some(crate::vc::SolverMode::Compute));
    assert_eq!(obligation.condition, "2u32 + 3u32 == 5u32");
}

#[test]
fn test_assert_by_compute_extracts_compute_only_clause() {
    let code = r#"
        fn check_compute_only_direct_source() {
            trust_vc::assert_by_compute!(2u32 + 3u32 == 5u32; compute_only);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_compute_only_direct_source").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("assert_by_compute!(...; compute_only) should lower to AssertBy");
    assert_eq!(obligation.solver_mode, Some(crate::vc::SolverMode::Compute));
    assert_eq!(obligation.condition, "2u32 + 3u32 == 5u32");
}

#[test]
fn test_assert_by_compute_extracts_compute_only_recursive_call_condition() {
    let code = r#"
        fn check_compute_only_recursive_direct_source() {
            trust_vc::assert_by_compute!(fib_compute(6) == 8; compute_only);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_compute_only_recursive_direct_source").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("recursive assert_by_compute!(...; compute_only) should lower to AssertBy");
    assert_eq!(obligation.solver_mode, Some(crate::vc::SolverMode::Compute));
    assert_eq!(obligation.condition, "fib_compute(6) == 8");
}

#[test]
fn test_assert_by_compute_rejects_scoped_requires_in_direct_source() {
    let code = r#"
        fn check_compute_requires_direct_source() {
            trust_vc::assert_by_compute!(x == 1u32; requires x == 1u32);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_compute_requires_direct_source").unwrap();
    let err = extract_verification_conditions(func)
        .expect_err("assert_by_compute! direct extraction should reject scoped requires");
    assert!(
        err.to_string()
            .contains("`requires` clauses are not supported by assert_by_compute!()"),
        "error should match public macro behavior, got: {err}"
    );
}

#[test]
fn test_assert_by_bit_vector_scoped_requires_names_are_unique() {
    let code = r#"
        fn check_bv_requires_unique(x: u32, y: u32) {
            trust_vc::assert_by_bit_vector!(
                (x << 1u32) == 0x200u32;
                requires x == 0x100u32
            );
            trust_vc::assert_by_bit_vector!(
                (y << 1u32) == 0x400u32;
                requires y == 0x200u32
            );
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_bv_requires_unique").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let mut scoped_names = vc
        .assert_by_scopes
        .values()
        .flat_map(|scope| scope.iter().map(|obligation| obligation.name.clone()))
        .collect::<Vec<_>>();
    scoped_names.sort();
    assert_eq!(
        scoped_names,
        vec![
            "assert_by_bit_vector_0_requires_0".to_string(),
            "assert_by_bit_vector_1_requires_0".to_string()
        ],
        "multiple bit-vector assert_by scoped requires must not reuse proof-step names"
    );
}

#[test]
fn test_assert_by_bit_vector_scoped_requires_are_checked() {
    let code = r#"
        fn check_bv_requires_negative(x: u32) {
            trust_vc::assert_by_bit_vector!(
                (x << 1u32) == 0x200u32;
                requires x == 0x100u32
            );
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_bv_requires_negative").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "unproved scoped requires must fail before the bitvector assertion is trusted, got: {result:?}"
    );
}

#[test]
fn test_assert_by_nonlinear_extracts_solver_mode_and_scoped_requires() {
    let code = r#"
        fn check_nonlinear_requires(x: u32) {
            trust_vc::assert_by_nonlinear!(
                x * x + x == x * (x + 1u32);
                requires x < 0xfffu32
            );
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_nonlinear_requires").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("assert_by_nonlinear! should lower to AssertBy");
    assert_eq!(
        obligation.solver_mode,
        Some(crate::vc::SolverMode::NonlinearArith)
    );
    assert_eq!(obligation.condition, "x * x + x == x * (x + 1u32)");

    let scoped = vc
        .assert_by_scopes
        .get(&obligation.name)
        .expect("AssertBy scope should be registered");
    assert_eq!(scoped.len(), 1);
    assert_eq!(scoped[0].kind, ObligationKind::Requires);
    assert_eq!(
        scoped[0].solver_mode,
        Some(crate::vc::SolverMode::NonlinearArith)
    );
    assert_eq!(scoped[0].condition, "x < 0xfffu32");
}

#[test]
fn test_assert_forall_by_source_extracts_bound_vars_and_scope() {
    let code = r#"
        fn check_forall_by() {
            trust_vc::assert_forall_by!(|k: u32| k + 0u32 == k, {
                trust_vc::assume!(k + 0u32 == k);
            });
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_forall_by").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("assert_forall_by! should lower to AssertBy");
    assert_eq!(obligation.condition, "(k) + 0u32 == (k)");
    assert_eq!(
        obligation.bound_vars.as_deref(),
        Some(&["k".to_string()][..])
    );

    let bound_vars = vc
        .forall_bound_vars()
        .get(&obligation.name)
        .expect("assert_forall_by! should register scoped bound variables");
    assert_eq!(bound_vars.len(), 1);
    assert_eq!(bound_vars[0].name, "k");
    assert_eq!(bound_vars[0].ty, crate::ir::TrustVcType::Uint { width: 32 });

    let scoped = vc
        .assert_by_scopes()
        .get(&obligation.name)
        .expect("assert_forall_by! should register scoped proof obligations");
    assert_eq!(scoped.len(), 1);
    assert_eq!(scoped[0].kind, ObligationKind::Assume);
    assert_eq!(scoped[0].condition, "(k) + 0u32 == (k)");
}

#[test]
fn test_bare_assert_forall_by_statement_extracts_bound_vars_and_scope() {
    let code = r#"
        fn check_bare_forall_by() {
            assert forall |k: u32| k + 0u32 == k by {
                trust_vc::assume!(k + 0u32 == k);
            };
        }
    "#;
    let file = crate::parse_file_allow_tracked(code).unwrap();
    let func = find_function(&file, "check_bare_forall_by").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("bare assert forall by statement should lower to AssertBy");
    assert_eq!(obligation.condition, "(k) + 0u32 == (k)");
    assert_eq!(
        obligation.bound_vars.as_deref(),
        Some(&["k".to_string()][..])
    );

    let bound_vars = vc
        .forall_bound_vars()
        .get(&obligation.name)
        .expect("bare assert forall by should register typed bound variables");
    assert_eq!(bound_vars.len(), 1);
    assert_eq!(bound_vars[0].name, "k");
    assert_eq!(bound_vars[0].ty, crate::ir::TrustVcType::Uint { width: 32 });

    let scoped = vc
        .assert_by_scopes()
        .get(&obligation.name)
        .expect("bare assert forall by should register scoped proof obligations");
    assert_eq!(scoped.len(), 1);
    assert_eq!(scoped[0].kind, ObligationKind::Assume);
    assert_eq!(scoped[0].condition, "(k) + 0u32 == (k)");
}

#[test]
fn test_assert_forall_by_source_extracts_trigger_patterns() {
    let code = r#"
        fn f(_: u32) -> bool { true }

        fn check_forall_by_trigger() {
            trust_vc::assert_forall_by!(|k: u32| #[trigger] f(k) && k + 0u32 == k, {
                trust_vc::assume!(k + 0u32 == k);
            });
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_forall_by_trigger").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let obligation = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::AssertBy))
        .expect("assert_forall_by! should lower to AssertBy");
    let patterns = obligation
        .trigger_patterns
        .as_ref()
        .expect("assert_forall_by! should preserve trigger patterns");
    assert_eq!(patterns, &vec![vec!["f((k))".to_string()]]);
}

#[test]
fn test_file_context_registers_structs_for_field_projection_locals() {
    let code = r#"
        struct Thing<A> {
            a: A,
        }

        fn field_projection(v: Thing<u8>) {
            let t1 = Thing { a: v.a };
            let t2 = Thing { a: t1.a };
            let a: u8 = t2.a;
            trust_vc::assert!(a >= 0u8);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "field_projection").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let v_ty = vc
        .get_variable_type("v")
        .expect("parameter v should be declared")
        .to_type_string();
    assert_eq!(v_ty, "Thing<u8>");
    assert!(
        vc.struct_types.iter().any(|def| def.name == "Thing"),
        "file-context extraction should register source structs"
    );
    let assertion = vc
        .obligations
        .iter()
        .find(|obligation| matches!(obligation.kind, ObligationKind::Assert))
        .expect("assertion should be collected");
    // `let a: u8 = t2.a;` is substituted as its value BOUND at `u8` (§5b
    // rule 6, `ir_lowering::LET_BOUND_MARKER`).
    assert_eq!(
        assertion.condition,
        "(__trust_vc_let_bound::<u8>(((Thing { a: ((Thing { a: (v).a })).a })).a)) >= 0u8"
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "field-projection struct assertion should verify, got {result:?}"
    );
}

#[test]
fn test_file_context_verifies_struct_update_projection_locals() {
    let code = r#"
        struct S2 {
            u: u64,
            v: u64,
        }

        fn struct_update_projection() {
            let s2 = S2 { u: 10u64, v: 20u64 };
            let s3 = S2 { v: 23u64, ..s2 };
            trust_vc::assert!(s3.u == 10u64);
            trust_vc::assert!(s3.v == 23u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "struct_update_projection").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.struct_types.iter().any(|def| def.name == "S2"),
        "file-context extraction should register the struct update type"
    );
    assert_eq!(
        vc.obligations
            .iter()
            .filter(|obligation| matches!(obligation.kind, ObligationKind::Assert))
            .count(),
        2,
        "struct update port should preserve both field assertions"
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "struct update field assertions should verify, got {result:?}"
    );
}

#[test]
fn test_ported_adts_struct_update_file_verifies() {
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .and_then(|path| path.parent())
        .expect("trust-vc-core crate should live under repo_root/crates")
        .to_path_buf();
    let port_path = repo_root.join("evals/verus/ported/adts.rs");

    let result = try_verify_function_from_file(
        port_path
            .to_str()
            .expect("ported ADT path should be valid UTF-8"),
        "struct_update_copies_omitted_fields",
    )
    .expect("ported ADT struct update case should extract");
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "ported ADT struct update case should verify, got {result:?}"
    );
}

#[test]
fn test_calc_extracts_adjacent_steps_and_transitive_conclusion() {
    let code = r#"
        fn check_calc(x: i32, y: i32, z: i32) {
            calc! {
                x;
                <= {} y;
                < {} z;
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        collect_assert_and_assert_by_conditions(&vc),
        vec![
            "x <= y".to_string(),
            "y < z".to_string(),
            "x < z".to_string(),
        ],
        "calc! must emit each adjacent step plus the multi-step transitive conclusion"
    );
}

#[test]
fn test_qualified_calc_extracts_single_step_without_extra_conclusion() {
    let code = r#"
        fn check_qualified_calc(x: i32, y: i32) {
            trust_vc::calc! {
                x + 0;
                == {} y;
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_qualified_calc").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        collect_assert_and_assert_by_conditions(&vc),
        vec!["x + 0 == y".to_string()],
        "trust_vc::calc! single-step chains should emit only the adjacent step"
    );
}

#[test]
fn test_verus_style_calc_header_sets_transitive_conclusion() {
    let code = r#"
        fn check_verus_style_calc() {
            calc! {
                (<=)
                2i32;
                (==) {} 3i32 - 1i32;
                (<) {} 5i32;
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_verus_style_calc").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert_eq!(
        collect_assert_and_assert_by_conditions(&vc),
        vec![
            "2i32 == 3i32 - 1i32".to_string(),
            "3i32 - 1i32 < 5i32".to_string(),
            "2i32 <= 5i32".to_string(),
        ],
        "Verus-style calc header should be accepted and used as the conclusion relation"
    );
}

#[test]
fn test_calc_proof_blocks_are_scoped_assert_by_obligations() {
    let code = r#"
        fn check_calc_scopes() {
            calc! {
                (==)
                1i32;
                (==) { assume!(false); } 2i32;
                (==) { assert!(1i32 == 2i32); } 1i32;
            }
            assert!(1i32 == 1i32);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_scopes").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let top_level_assumes = vc
        .obligations
        .iter()
        .filter(|obligation| obligation.kind == ObligationKind::Assume)
        .count();
    assert_eq!(
        top_level_assumes, 0,
        "calc proof-block assumptions must not leak into the outer VC"
    );
    let scoped_kinds = vc
        .assert_by_scopes()
        .values()
        .map(|scoped| {
            scoped
                .iter()
                .map(|obligation| obligation.kind)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert!(
        scoped_kinds
            .iter()
            .any(|kinds| kinds == &vec![ObligationKind::Assume]),
        "first calc proof block should store its assumption in the step scope: {:?}",
        scoped_kinds
    );
    assert!(
        scoped_kinds
            .iter()
            .any(|kinds| kinds == &vec![ObligationKind::Assert]),
        "second calc proof block should store its assertion in the step scope: {:?}",
        scoped_kinds
    );
}

#[test]
fn test_invalid_calc_syntax_returns_encoding_error() {
    let code = r#"
        fn bad_calc_syntax(x: i32) {
            calc! {
                x;
            }
        }
    "#;

    assert_calc_extraction_error(code, "bad_calc_syntax", "calc!");
}

#[test]
fn test_incompatible_calc_operators_return_encoding_error() {
    let code = r#"
        fn bad_calc_operators(x: i32, y: i32, z: i32) {
            calc! {
                x;
                <= {} y;
                >= {} z;
            }
        }
    "#;

    assert_calc_extraction_error(code, "bad_calc_operators", "incompatible");
}

fn assert_calc_extraction_error(code: &str, function_name: &str, expected_detail: &str) {
    let file = parse_file(code).unwrap();
    let func = find_function(&file, function_name).unwrap();
    let err = extract_verification_conditions(func)
        .expect_err("invalid calc! input must fail closed instead of being silently skipped");

    assert!(
        matches!(err, crate::TrustVcError::Encoding { .. }),
        "calc extraction failures must be Encoding errors, got: {err:?}"
    );
    let message = err.to_string();
    assert!(
        message.contains("calc"),
        "calc extraction error should mention calc, got: {message}"
    );
    assert!(
        message.contains(expected_detail),
        "calc extraction error should mention {expected_detail}, got: {message}"
    );
}

// ================================================================
// #2778: exec arithmetic-safety on discarded results
//
// Verus checks integer overflow / divide-by-zero at every exec
// arithmetic site, even when the result is bound to a fresh local
// or reassigned and then dropped. Such sites carry no assertion, so
// before the arithmetic-safety wiring the encoder emitted no
// obligation and silently accepted programs Verus rejects (the
// upstream overflow.rs failures). Each discarded site now pins a
// reflexive obligation so the overflow precheck fires.
// ================================================================

#[test]
fn test_discarded_assignment_overflow_is_counterexample() {
    // upstream overflow.rs test_overflow_fails_1: `j = j + 2` can overflow.
    let code = r#"
        fn test_overflow_fails_1(a: u64) {
            let mut j = a;
            j = j + 2u64;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "test_overflow_fails_1").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "discarded `j = j + 2` exec overflow must fail like Verus, got: {result:?}"
    );
}

#[test]
fn test_discarded_let_division_by_zero_is_counterexample() {
    // upstream overflow.rs test_divide_by_zero::fail1: `a / b` can divide by zero.
    let code = r#"
        fn divide_by_zero_fail(a: u8, b: u8) {
            let _x = a / b;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "divide_by_zero_fail").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "discarded `let _x = a / b` divide-by-zero must fail like Verus, got: {result:?}"
    );
}

#[test]
fn test_returned_let_binding_overflow_is_counterexample() {
    // upstream overflow.rs test_overflow_fails_usize shape: `let b = a + 1; b`.
    let code = r#"
        fn add_one(a: u64) -> u64 {
            let b = a + 1u64;
            b
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "add_one").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "`let b = a + 1` exec overflow must fail like Verus, got: {result:?}"
    );
}

#[test]
fn test_guarded_let_binding_arithmetic_verifies() {
    // Verus test_overflow_ensures_pass analogue: a precondition that bounds the
    // operand discharges the safety obligation, so the site verifies.
    let code = r#"
        #[requires(a < 30u64)]
        fn guarded_add(a: u64) {
            let _b = a + 1u64;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "guarded_add").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "guarded `let _b = a + 1` must verify once the operand is bounded, got: {result:?}"
    );
}

#[test]
fn test_proof_function_discarded_arithmetic_is_not_checked() {
    // Proof/spec arithmetic uses unbounded-integer semantics, so a discarded
    // arithmetic site emits no overflow obligation (matches Verus). The assert
    // gives the verifier something to prove; if exec overflow checking leaked
    // into proof mode the unbounded `a + 1` would be a spurious counterexample.
    let code = r#"
        #[trust_vc::proof]
        fn proof_add(a: u64) {
            let b = a + 1u64;
            trust_vc::assert!(b == a + 1u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "proof_add").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "proof-mode arithmetic must not emit exec overflow obligations, got: {result:?}"
    );
}
