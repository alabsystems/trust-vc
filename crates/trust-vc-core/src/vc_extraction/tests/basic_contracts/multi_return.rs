// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;

// ========================================================================
// SOUNDNESS: #1857 — multi-return postcondition bug
// ========================================================================

fn return_value_condition(vc: &VerificationContext) -> String {
    vc.obligations
        .iter()
        .find(|o| matches!(o.kind, ObligationKind::Assume) && o.name == "return_value")
        .expect("expected return_value assumption")
        .condition
        .clone()
}

/// #1857: a nested early return must not silently constrain `result` with only
/// the trailing expression. It is now modeled as a conservative set of possible
/// return values, so this false postcondition produces a counterexample.
#[test]
fn test_multi_return_includes_early_return_path_1857() {
    let code = r#"
        #[ensures(result >= 0)]
        fn clamp_positive(x: i32) -> i32 {
            if x < 0 {
                return -1;
            }
            x
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "clamp_positive").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        (condition.contains("result == -1") || condition.contains("result == - 1"))
            && condition.contains("result == x"),
        "return_value must include both early and tail return values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must not verify after early-return extraction, got: {result:?}"
    );
}

#[test]
fn test_nested_early_return_result_postcondition_verifies() {
    let code = r#"
        #[ensures(10u64 <= result && 20u64 <= result)]
        fn bounded(flag: bool) -> u64 {
            if flag {
                return 20u64;
            }
            30u64
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "bounded").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == 20u64") && condition.contains("result == 30u64"),
        "return_value must include both nested and tail return values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for every modeled return value, got: {result:?}"
    );
}

#[test]
fn test_nested_early_return_scopes_branch_locals_1857() {
    let code = r#"
        #[requires(outer == 2u64)]
        #[ensures(result == 2u64)]
        fn scoped_shadow(flag: bool, outer: u64) -> u64 {
            if flag {
                let outer = 1u64;
                return outer;
            }
            2u64
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "scoped_shadow").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == (1u64)") && condition.contains("result == 2u64"),
        "early return must use branch-local substitution, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "branch-local early return must not be captured by the outer parameter, got: {result:?}"
    );
}

/// #1857 variant: a tail if/else whose arms are explicit returns has no
/// fall-through tail value, so model the arm values with the multi-return
/// assumption.
#[test]
fn test_return_only_tail_if_models_all_explicit_returns_1857() {
    let code = r#"
        #[ensures(result == x || result == 1)]
        fn abs_like(x: i32) -> i32 {
            if x >= 0 {
                return x;
            } else {
                return 1;
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "abs_like").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == x") && condition.contains("result == 1"),
        "return-only tail if should model both explicit return values, got: {condition}"
    );
    assert!(
        !condition.contains("if x >= 0"),
        "return-only tail if must not add the whole tail if expression as a value, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should follow from the modeled explicit return values, got: {result:?}"
    );
}

#[test]
fn test_mixed_tail_if_return_and_value_models_all_values_1857() {
    let code = r#"
        #[ensures(result == -1 || result == 1)]
        fn mixed_tail_if(flag: bool) -> i32 {
            if flag {
                return -1;
            } else {
                1
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "mixed_tail_if").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        (condition.contains("result == -1") || condition.contains("result == - 1"))
            && condition.contains("result == 1"),
        "mixed tail if should include explicit and normal return values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for modeled mixed tail-if values, got: {result:?}"
    );
}

#[test]
fn test_mixed_tail_if_return_and_value_rejects_false_postcondition_1857() {
    let code = r#"
        #[ensures(result == 1)]
        fn mixed_tail_if_false_postcondition(flag: bool) -> i32 {
            if flag {
                return -1;
            } else {
                1
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "mixed_tail_if_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must reject the explicit mixed tail-if return path, got: {result:?}"
    );
}

#[test]
fn test_tail_if_expression_stays_supported_1857() {
    let code = r#"
        #[ensures(result >= 0)]
        fn sign_like(x: i32) -> i32 {
            if x >= 0 { x } else { 0 - x }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "sign_like").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let return_assumptions: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume) && o.name == "return_value")
        .collect();

    assert_eq!(
        return_assumptions.len(),
        1,
        "tail if/else expressions remain a single canonical return value"
    );
}

#[test]
fn test_tail_if_short_circuit_return_condition_models_reachable_values() {
    let code = r#"
        #[ensures(result == 11u64 || result == 17u64)]
        fn short_circuit_return(flag: bool) -> u64 {
            if flag || {
                return 11u64;
            } {
                17u64
            } else {
                13u64
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "short_circuit_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == 11u64") && condition.contains("result == 17u64"),
        "short-circuit return should include explicit return and normal then value, got: {condition}"
    );
    assert!(
        !condition.contains("result == 13u64"),
        "short-circuit return must not include unreachable else value, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for short-circuit return values, got: {result:?}"
    );
}

#[test]
fn test_tail_if_short_circuit_return_condition_rejects_false_postcondition() {
    let code = r#"
        #[ensures(result == 17u64)]
        fn short_circuit_return_false_postcondition(flag: bool) -> u64 {
            if flag || {
                return 11u64;
            } {
                17u64
            } else {
                13u64
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "short_circuit_return_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must reject the short-circuit explicit return path, got: {result:?}"
    );
}

#[test]
fn test_tail_block_expression_models_explicit_and_normal_values_1857() {
    let code = r#"
        #[ensures(result == 11u64 || result == 17u64)]
        fn tail_block_return(flag: bool) -> u64 {
            {
                if flag {
                    return 11u64;
                }
                17u64
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "tail_block_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == 11u64") && condition.contains("result == 17u64"),
        "tail-block return should include explicit and normal completion values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for modeled tail-block return values, got: {result:?}"
    );
}

#[test]
fn test_tail_block_expression_rejects_false_postcondition_1857() {
    let code = r#"
        #[ensures(result == 17u64)]
        fn tail_block_return_false_postcondition(flag: bool) -> u64 {
            {
                if flag {
                    return 11u64;
                }
                17u64
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "tail_block_return_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must reject the explicit tail-block return path, got: {result:?}"
    );
}

/// #1857 variant: a narrow match with no arm bindings can be modeled as a
/// conservative set of explicit-return and normal arm values.
#[test]
fn test_match_with_return_in_arm_models_all_values_1857() {
    let code = r#"
        #[ensures(result == 11u64 || result == 13u64)]
        fn match_early_return(flag: bool) -> u64 {
            match flag {
                true => {
                    return 11u64;
                }
                false => 13u64,
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "match_early_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == 11u64") && condition.contains("result == 13u64"),
        "match-arm return should include explicit and normal arm values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for modeled match-arm return values, got: {result:?}"
    );
}

#[test]
fn test_match_with_return_in_arm_rejects_false_postcondition_1857() {
    let code = r#"
        #[ensures(result == 13u64)]
        fn match_early_return_false_postcondition(flag: bool) -> u64 {
            match flag {
                true => {
                    return 11u64;
                }
                false => 13u64,
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "match_early_return_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must reject the explicit match-arm return path, got: {result:?}"
    );
}

#[test]
fn test_match_with_binding_return_remains_ambiguous_1857() {
    let code = r#"
        #[ensures(result >= 0)]
        fn match_binding_early_return(x: Option<i32>) -> i32 {
            match x {
                Some(v) => return v,
                None => 0,
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "match_binding_early_return").unwrap();
    let err = extract_verification_conditions(func)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("match explicit return path"),
        "match-arm return with bindings should remain a precise fail-closed blocker, got: {err}"
    );
}

/// Phase E early-return-from-loop: a `return X` inside a `loop`/`while`/`for`
/// whose `X` is LOOP-INVARIANT (here the literal `1`) is now admitted into the
/// multiple-return disjunction alongside the fall-through tail (`2`), rather than
/// being rejected. Both 1 and 2 are `> 0`, so the postcondition verifies. (The
/// loop body is havoc'd, so this admission is sound only because the literal is
/// identical on every iteration — see the loop-mutated companion below, which
/// stays fail-closed.)
#[test]
fn test_loop_with_invariant_literal_return_models_disjunction_1857() {
    let code = r#"
        #[ensures(result > 0)]
        fn loop_early_return(flag: bool) -> i32 {
            while flag {
                return 1;
            }
            2
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "loop_early_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == 1") && condition.contains("result == 2"),
        "loop-invariant literal return should model both the loop-return and the \
         fall-through values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for the modeled loop-return disjunction, got: {result:?}"
    );
}

/// Companion soundness guard: a `return X` inside a loop whose `X` reads
/// loop-MUTATED state (`acc`, reassigned each iteration) is NOT loop-invariant.
/// Under the loop's havoc its value is indeterminate, so it MUST stay a precise
/// fail-closed blocker ("loop explicit return path") — never admitted into the
/// disjunction, which would let a false postcondition verify.
#[test]
fn test_loop_with_mutated_local_return_remains_ambiguous_1857() {
    let code = r#"
        #[ensures(result > 0)]
        fn loop_mutated_return(flag: bool) -> i32 {
            let mut acc = 0;
            loop {
                acc = acc + 1;
                if flag {
                    return acc;
                }
                break;
            }
            2
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "loop_mutated_return").unwrap();
    let err = extract_verification_conditions(func)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("loop explicit return path"),
        "loop-mutated return should remain a precise fail-closed blocker, got: {err}"
    );
}

#[test]
fn test_local_initializer_tail_return_models_explicit_and_normal_values_1857() {
    let code = r#"
        #[ensures(result == -1 || result == 1)]
        fn local_initializer_return(flag: bool) -> i32 {
            let value = if flag {
                return -1;
            } else {
                1
            };
            value
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "local_initializer_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        (condition.contains("result == -1") || condition.contains("result == - 1"))
            && condition.contains("result == 1"),
        "local-initializer return should include explicit and normal values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for modeled local-initializer return values, got: {result:?}"
    );
}

#[test]
fn test_local_initializer_tail_return_rejects_false_postcondition_1857() {
    let code = r#"
        #[ensures(result == 1)]
        fn local_initializer_false_postcondition(flag: bool) -> i32 {
            let value = if flag {
                return -1;
            } else {
                1
            };
            value
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "local_initializer_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must reject the explicit local-initializer return path, got: {result:?}"
    );
}

#[test]
fn test_local_initializer_tail_return_does_not_assume_infeasible_branch_1857() {
    let code = r#"
        #[ensures(result == 1)]
        fn local_initializer_infeasible_return_branch() -> i32 {
            let value = if false {
                return -1;
            } else {
                1
            };
            value
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "local_initializer_infeasible_return_branch").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == 1")
            && (condition.contains("result == -1") || condition.contains("result == - 1")),
        "local-initializer extraction must over-approximate infeasible branches, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "infeasible branch must not be assumed away during extraction, got: {result:?}"
    );
}

#[test]
fn test_local_initializer_non_tail_return_remains_ambiguous_1857() {
    let code = r#"
        #[ensures(result >= 0)]
        fn local_initializer_return_in_computed_tail(flag: bool) -> i32 {
            let value = if flag {
                return -1;
            } else {
                1
            };
            value + 1
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "local_initializer_return_in_computed_tail").unwrap();
    let err = extract_verification_conditions(func)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("local initializer explicit return path"),
        "non-tail local-initializer return should remain a precise fail-closed blocker, got: {err}"
    );
}

#[test]
fn test_if_let_return_remains_ambiguous_1857() {
    let code = r#"
        #[ensures(result >= 0)]
        fn if_let_return(value: Option<i32>) -> i32 {
            if let Some(inner) = value {
                return inner;
            }
            0
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "if_let_return").unwrap();
    let err = extract_verification_conditions(func)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("if-let explicit return path"),
        "if-let return should remain a precise fail-closed blocker, got: {err}"
    );
}

#[test]
fn test_if_let_without_bindings_models_explicit_and_normal_values_1857() {
    let code = r#"
        #[ensures(result == 11u64 || result == 13u64)]
        fn if_let_no_binding_return(value: u64) -> u64 {
            if let 0u64 = value {
                return 11u64;
            } else {
                13u64
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "if_let_no_binding_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert!(
        condition.contains("result == 11u64") && condition.contains("result == 13u64"),
        "no-binding if-let return should include explicit and normal values, got: {condition}"
    );
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "postcondition should verify for modeled no-binding if-let values, got: {result:?}"
    );
}

#[test]
fn test_if_let_without_bindings_rejects_false_postcondition_1857() {
    let code = r#"
        #[ensures(result == 13u64)]
        fn if_let_no_binding_false_postcondition(value: u64) -> u64 {
            if let 0u64 = value {
                return 11u64;
            } else {
                13u64
            }
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "if_let_no_binding_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition must reject the explicit no-binding if-let return path, got: {result:?}"
    );
}

#[test]
fn test_if_let_without_return_stays_supported_1857() {
    let code = r#"
        #[ensures(result == 0)]
        fn if_let_without_return(value: Option<i32>) -> i32 {
            if let Some(_) = value {
            }
            0
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "if_let_without_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let condition = return_value_condition(&vc);
    assert_eq!(condition, "result == 0");
}

#[test]
fn test_nested_return_call_value_remains_ambiguous_for_alias_shadowing() {
    let code = r#"
        #[ensures(result)]
        fn nested_call_return(flag: bool) -> bool {
            if flag {
                return h();
            }
            true
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "nested_call_return").unwrap();
    let err = extract_verification_conditions(func)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("nested explicit return value with call expression"),
        "nested return call values should remain fail-closed until lexical alias shadowing is preserved, got: {err}"
    );
}

/// #1857 edge case: `return` inside a closure body must NOT make the
/// outer function ambiguous — ExplicitReturnFinder skips closures.
#[test]
fn test_closure_return_does_not_affect_outer_function_1857() {
    let code = r#"
        #[ensures(result > 0)]
        fn uses_closure(x: i32) -> i32 {
            let _f = |y: i32| -> i32 { return y + 1; };
            x + 1
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "uses_closure").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let return_assumptions: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume) && o.name == "return_value")
        .collect();

    assert_eq!(
        return_assumptions.len(),
        1,
        "closure return should not trigger ambiguous detection for outer function"
    );
}

/// #1857 edge case: `return` inside an async block must NOT make the
/// outer function ambiguous — ExplicitReturnFinder skips async bodies.
#[test]
fn test_async_return_does_not_affect_outer_function_1857() {
    let code = r#"
        #[ensures(result > 0)]
        fn uses_async_block() -> i32 {
            let _fut = async {
                return 7;
            };
            1
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "uses_async_block").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let return_assumptions: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume) && o.name == "return_value")
        .collect();

    assert_eq!(
        return_assumptions.len(),
        1,
        "async-block return should not trigger ambiguous detection for outer function"
    );
}

/// #1857 edge case: single top-level `return expr;` with no tail expression
/// is unambiguous — exactly one return path.
#[test]
fn test_single_explicit_return_is_unambiguous_1857() {
    let code = r#"
        #[ensures(result > 0)]
        fn single_return(x: i32) -> i32 {
            return x + 1;
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "single_return").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let return_assumptions: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume) && o.name == "return_value")
        .collect();

    assert_eq!(
        return_assumptions.len(),
        1,
        "single explicit return should produce exactly one return_value assumption"
    );
}

/// #1857 edge case: with multiple top-level `return` statements the FIRST
/// top-level `return` DOMINATES. A statement-level `return` unconditionally
/// diverges, so the first return is the sole reachable return value and every
/// later statement (the second `return` here) is dead code. Extraction therefore
/// succeeds and pins `result` to the first return (`result == 1`), NOT to the
/// dead second return (`result == 2`) — the precise, sound classification the
/// `> 1 → Ambiguous` conservatism guard was relaxed to `>= 1 → Single(first)`.
#[test]
fn test_multiple_top_level_returns_first_dominates_1857() {
    let code = r#"
        #[ensures(result > 0)]
        fn duplicate_returns() -> i32 {
            return 1;
            return 2;
        }
    "#;

    let file = parse_file(code).unwrap();
    let func = find_function(&file, "duplicate_returns").unwrap();
    let vc = extract_verification_conditions(func)
        .expect("first top-level return dominates, so extraction should succeed");

    // The FIRST return dominates: `result == 1`, not the dead `result == 2`.
    assert_eq!(
        return_value_condition(&vc),
        "result == 1",
        "the first top-level return must dominate; the second is dead code"
    );

    let return_assumptions: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume) && o.name == "return_value")
        .collect();
    assert_eq!(
        return_assumptions.len(),
        1,
        "multiple top-level returns should still bind result exactly once (first dominates)"
    );
}
