// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// True when `name` is a call-site `requires` obligation
/// (`__call_requires_pp{N}_{helper}_{call_index}_{index}`) for the helper/method
/// whose mangled symbol is `helper`. The `pp{N}` program-point infix (round-8
/// findings 11/12) forward-orders the precondition check; this matcher anchors
/// on it then on the `_{helper}_` boundary so it cannot be fooled by the `pp`
/// digits.
fn is_call_requires_for(name: &str, helper: &str) -> bool {
    let Some(rest) = name.strip_prefix("__call_requires_pp") else {
        return false;
    };
    let rest = rest.trim_start_matches(|c: char| c.is_ascii_digit());
    rest.starts_with(&format!("_{helper}_"))
}

#[test]
fn test_extract_assertions_substitute_block_scoped_let_bindings() {
    let code = r#"
        fn check_scope() {
            let mut x = 6;
            x = 60;
            let x = 7;
            let y = {
                let mut x = 5;
                x = { let x = x + 50; x + 50 };
                x
            };
            assert!(x == 7);
            assert!(y == 105);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_scope").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(7) == 7")),
        "outer shadowed x should be substituted from the active block scope: {:?}",
        conditions
    );
    assert!(
        conditions.iter().any(|condition| condition.contains("105")),
        "block-expression let result should be substituted into y assertion: {:?}",
        conditions
    );
}

#[test]
fn test_typed_tuple_default_local_substitutes_concrete_tuple() {
    let code = r#"
        fn check_tuple_default() {
            let pair: (u32, bool) = <(u32, bool)>::default();
            let triple: (u32, bool, char) = <(u32, bool, char)>::default();
            trust_vc::assert!(pair.0 == 0u32);
            trust_vc::assert!(pair.1 == false);
            trust_vc::assert!(triple.2 == '\0');
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_tuple_default").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(((0u32, false))).0 == 0u32")),
        "tuple default should substitute pair literal into field assertion: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(((0u32, false, '\\0'))).2 == '\\0'")),
        "tuple default should substitute triple literal into char field assertion: {:?}",
        conditions
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "tuple default field assertions should verify, got {result:?}"
    );
}

#[test]
fn test_while_invariant_exit_fact_verifies_post_assertion() {
    let code = r#"
        #[requires(limit == 10u64)]
        fn check_while(mut i: u64, limit: u64) {
            while i < limit {
                trust_vc::invariant!(limit == 10u64);
                i = i + 1u64;
            }
            trust_vc::assert!(i >= 10u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_while").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert!(
        vc.obligations().iter().any(|obligation| obligation.kind()
            == ObligationKind::LoopInvariant
            && obligation.condition() == "limit == 10u64"),
        "while invariant should be extracted as a LoopInvariant: {:?}",
        vc.obligations()
    );
    assert!(
        vc.obligations().iter().any(|obligation| obligation.kind()
            == ObligationKind::PostLoopAssume
            && obligation.condition() == "!(i < limit)"),
        "while normal-exit fact should be extracted as a PostLoopAssume: {:?}",
        vc.obligations()
    );

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "while invariant plus normal-exit fact should verify final assertion, got: {:?}",
        result
    );
}

#[test]
fn test_while_let_invariant_does_not_emit_boolean_loop_guard() {
    let code = r#"
        fn check_while_let(mut opt: Option<u64>) {
            while let Some(x) = opt {
                trust_vc::invariant!(true);
                trust_vc::assert!(x == x);
                opt = None;
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_while_let").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert!(
        !vc.obligations()
            .iter()
            .any(|obligation| obligation.kind() == ObligationKind::PostLoopAssume),
        "while-let must not emit a boolean normal-exit assumption: {:?}",
        vc.obligations()
    );
    assert!(
        vc.loop_guards().is_empty(),
        "while-let must not attach non-boolean guard metadata: {:?}",
        vc.loop_guards()
    );
}

#[test]
fn test_scoped_substitution_does_not_leak_between_if_branches() {
    let code = r#"
        fn check_branch(c: bool) {
            let mut x = 0;
            if c {
                x = 1;
                assert!(x == 1);
            } else {
                assert!(x == 0);
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_branch").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(1) == 1")),
        "then branch should see its own assignment: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(0) == 0")),
        "else branch must not inherit the then-branch assignment: {:?}",
        conditions
    );
}

#[test]
fn test_mutable_param_assignment_same_in_all_if_branches_updates_return_value() {
    let code = r#"
        #[ensures(result == x)]
        fn branch_mut_param_false_postcondition(mut x: u64, choose_left: bool) -> u64 {
            if choose_left {
                x = 20u64;
            } else {
                x = 20u64;
            }
            x
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "branch_mut_param_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let return_condition = vc
        .obligations
        .iter()
        .find(|obligation| {
            matches!(obligation.kind, ObligationKind::Assume) && obligation.name == "return_value"
        })
        .expect("expected return_value assumption")
        .condition
        .clone();
    assert!(
        return_condition.contains("20u64"),
        "return_value should use the joined branch assignment, got: {return_condition}"
    );
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "returning a branch-mutated value parameter must not fall back to the original parameter symbol, got: {result:?}"
    );
}

#[test]
fn test_mutable_param_assignment_same_in_nested_if_branches_updates_return_value() {
    let code = r#"
        #[ensures(result == x)]
        fn nested_branch_mut_param_false_postcondition(
            mut x: u64,
            outer: bool,
            inner: bool,
        ) -> u64 {
            if outer {
                if inner {
                    x = 20u64;
                } else {
                    x = 20u64;
                }
            } else {
                x = 20u64;
            }
            x
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "nested_branch_mut_param_false_postcondition").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let return_condition = vc
        .obligations
        .iter()
        .find(|obligation| {
            matches!(obligation.kind, ObligationKind::Assume) && obligation.name == "return_value"
        })
        .expect("expected return_value assumption")
        .condition
        .clone();
    assert!(
        return_condition.contains("20u64"),
        "nested return_value should use the joined branch assignment, got: {return_condition}"
    );
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "nested branches that all assign the same mutable parameter value should feed that value into return extraction, got: {result:?}"
    );
}

#[test]
fn test_scoped_substitution_visits_assignment_rhs_before_update() {
    let code = r#"
        fn check_assignment_rhs() {
            let mut x = 0;
            x = { assert!(x == 0); 1 };
            assert!(x == 1);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_assignment_rhs").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(0) == 0")),
        "assertions in an assignment RHS should use the pre-assignment value: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(1) == 1")),
        "assertions after the assignment should use the updated value: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_tracks_indexed_assignment_as_update() {
    let code = r#"
        fn check_indexed_assignment() {
            let mut a = [0, 1];
            a[1] = 9;
            assert!(a[1] == 9);
            assert!(a[0] == 0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_indexed_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(1, 9)") && condition.contains("[1] == 9")),
        "indexed assignment should rewrite the array binding through update(): {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(1, 9)") && condition.contains("[0] == 0")),
        "subsequent reads of other indices should use the updated array binding: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .all(|condition| !condition.contains("[0, 1][1] == 9")),
        "indexed assignment must not leave stale pre-assignment array reads: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_visits_indexed_assignment_index() {
    let code = r#"
        fn check_indexed_assignment_index_assertion() {
            let mut a = [0, 1];
            a[{ assert!(false); 1 }] = 9;
            assert!(a[1] == 9);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_indexed_assignment_index_assertion").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| condition == "false"),
        "assertions inside indexed-assignment indices must be extracted: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(1, 9)") && condition.contains("[1] == 9")),
        "indexed assignment should still rewrite through update(): {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_tracks_nested_indexed_assignment_as_nested_update() {
    let code = r#"
        fn check_nested_indexed_assignment() {
            let mut a = [[0u64, 1u64], [2u64, 3u64]];
            a[0][1] = 9u64;
            assert!(a[0][1] == 9u64);
            assert!(a[1][1] == 3u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_nested_indexed_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains(".update(0,")
                && condition.contains("[0].update(1, 9u64)")
                && condition.contains("[0][1] == 9u64")
        }),
        "nested indexed assignment should rewrite through nested update(): {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(0,")
                && condition.contains("[1][1] == 3u64")),
        "nested indexed assignment should frame other rows through the outer update: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_tracks_indexed_compound_assignment_as_update() {
    let code = r#"
        fn check_indexed_compound_assignment() {
            let mut a = [0, 1];
            a[1] += 8;
            assert!(a[1] == 9);
            assert!(a[0] == 0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_indexed_compound_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains(".update(1,")
                && condition.contains("[1] + (8)")
                && condition.contains("[1] == 9")
        }),
        "indexed compound assignment should update from the old indexed value: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(1,") && condition.contains("[0] == 0")),
        "indexed compound assignment should frame other array elements through the update: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .all(|condition| !condition.contains("[0, 1][1] == 9")),
        "indexed compound assignment must not leave stale pre-assignment array reads: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_tracks_nested_indexed_compound_assignment_as_nested_update() {
    let code = r#"
        fn check_nested_indexed_compound_assignment() {
            let mut a = [[0u64, 1u64], [2u64, 3u64]];
            a[0][0] += 5u64;
            assert!(a[0][0] == 5u64);
            assert!(a[1][1] == 3u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_nested_indexed_compound_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains(".update(0,")
                && condition.contains("[0].update(0,")
                && condition.contains("[0][0] + (5u64)")
                && condition.contains("[0][0] == 5u64")
        }),
        "nested indexed compound assignment should update from old nested value: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(0,")
                && condition.contains("[1][1] == 3u64")),
        "nested indexed compound assignment should frame other rows through the outer update: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_invalidates_indexed_compound_assignment_target_side_effects() {
    let code = r#"
        fn check_indexed_compound_side_effect() {
            let mut a = [0, 1];
            a[{ a[0] = 7; 1 }] += 8;
            assert!(a[0] == 0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_indexed_compound_side_effect").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| condition == "a[0] == 0"),
        "target-mutating index expressions should invalidate scoped array state: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .all(|condition| !condition.contains("[0, 1]")),
        "target-mutating index expressions must not replay stale array literals: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_rejects_nonlocal_indexed_assignment_target() {
    let code = r#"
        fn check_deref_indexed_assignment(ar: &mut [u8; 3]) {
            (*ar)[1] = 9;
            assert!((*ar)[1] == 9);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_deref_indexed_assignment").unwrap();
    let err = extract_verification_conditions(func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("indexed assignment target is unsupported")
            && message.contains("directly indexed local array/Seq variables"),
        "unsupported indexed assignment targets should fail closed before stale-state reasoning, got: {message}"
    );
}

#[test]
fn test_scoped_substitution_rejects_out_of_bounds_vec_literal_assignment() {
    let code = r#"
        fn check_vec_oob_assignment() {
            let mut v = vec![1u64, 2u64, 3u64];
            v[3] = 5u64;
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_vec_oob_assignment").unwrap();
    let err = extract_verification_conditions(func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("Vec literal indexed assignment is out of bounds")
            && message.contains("length 3")
            && message.contains("index is 3"),
        "out-of-bounds Vec literal assignment should fail closed before no-obligation verification, got: {message}"
    );
}

#[test]
fn test_scoped_substitution_rejects_out_of_bounds_vec_literal_read() {
    let code = r#"
        fn check_vec_oob_read() {
            let v = vec![1u64, 2u64, 3u64];
            let r = v[3];
            trust_vc::assert!(r == 0u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_vec_oob_read").unwrap();
    let err = extract_verification_conditions(func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("Vec literal index is out of bounds")
            && message.contains("length 3")
            && message.contains("index is 3"),
        "out-of-bounds Vec literal read should fail closed before solver Unknown, got: {message}"
    );
}

#[test]
fn test_scoped_substitution_updates_direct_struct_field_indexed_assignment() {
    let code = r#"
        struct Holder {
            ar: [u8; 3],
            other: u8,
        }

        fn check_struct_field_indexed_assignment(mut s: Holder) {
            s.ar[1usize] = 9u8;
            trust_vc::assert!(s.ar[1usize] == 9u8);
            trust_vc::assert!(s.ar[0usize] == s.ar[0usize]);
            trust_vc::assert!(s.other == s.other);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_struct_field_indexed_assignment").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("Holder { ar: (s).ar.update(1usize, 9u8), ..s }")),
        "direct struct-field indexed assignment should rewrite the owner through a struct update: {:?}",
        conditions
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "direct struct-field indexed assignment should verify updated and framed fields, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_rejects_borrowed_indexed_assignment_alias() {
    let code = r#"
        fn check_borrowed_indexed_assignment_alias(ar: &mut [u8; 3]) {
            let alias: &mut [u8; 3] = ar;
            alias[1] += 1;
            assert!(alias[1] == 1);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_borrowed_indexed_assignment_alias").unwrap();
    let err = extract_verification_conditions(func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("indexed assignment through a borrowed array/reference alias")
            && message.contains("aliased state as an independent array"),
        "borrowed indexed assignment aliases should fail closed before alias state is modeled independently, got: {message}"
    );
}

#[test]
fn test_scoped_substitution_erases_read_only_local_mut_ref_alias() {
    let code = r#"
        fn check_local_mut_ref_alias(p: u64) {
            let mut a = p;
            let b: &mut u64 = &mut a;
            trust_vc::assert!(*b == p);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_local_mut_ref_alias").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains("p") && condition.contains("== p") && !condition.contains("*")
        }),
        "read-only local mutable-reference aliases should erase deref reads to the referent value: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_erases_read_only_mut_ref_param_alias() {
    let code = r#"
        fn check_mut_ref_param_alias(p: &mut u64) {
            let b: &mut u64 = p;
            trust_vc::assert!(*b == p);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_mut_ref_param_alias").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains("p") && condition.contains("== p") && !condition.contains("*")
        }),
        "read-only mutable-reference parameter aliases should erase deref reads to the parameter referent value: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_updates_direct_local_mut_ref_alias_assignment() {
    let code = r#"
        fn check_local_mut_ref_alias_assignment() {
            let mut a = 12u64;
            let b: &mut u64 = &mut a;
            *b = 13u64;
            trust_vc::assert!(a == 13u64);
            trust_vc::assert!(*b == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_local_mut_ref_alias_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .filter(|condition| condition.contains("13u64") && !condition.contains('*'))
            .count()
            >= 2,
        "direct mutable-reference assignment should update both the local and alias scoped values: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_updates_symbolic_local_mut_ref_alias_assignment() {
    let code = r#"
        #[trust_vc::requires(p < 1000u64)]
        fn check_symbolic_local_mut_ref_alias_assignment(p: u64) {
            let mut a = p;
            let b: &mut u64 = &mut a;
            *b = p + 1u64;
            trust_vc::assert!(a == p + 1u64);
            trust_vc::assert!(*b == p + 1u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_symbolic_local_mut_ref_alias_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "mutable-reference assignment should update scoped symbolic locals, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_scalar_mut_ref_reborrow_assignment() {
    let code = r#"
        fn check_scalar_mut_ref_reborrow_assignment() {
            let mut a = 12u64;
            let b: &mut u64 = &mut a;
            *b = 13u64;
            let c: &mut u64 = &mut *b;
            *c = 14u64;
            trust_vc::assert!(a == 14u64);
            trust_vc::assert!(*b == 14u64);
            trust_vc::assert!(*c == 14u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_scalar_mut_ref_reborrow_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "scalar mutable-reference reborrow assignment should update local and aliases, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_scalar_mut_ref_alias_reborrow_assignment() {
    let code = r#"
        fn check_scalar_mut_ref_alias_reborrow_assignment() {
            let mut a = 12u64;
            let b: &mut u64 = &mut a;
            let c: &mut u64 = b;
            *c = 14u64;
            trust_vc::assert!(a == 14u64);
            trust_vc::assert!(*b == 14u64);
            trust_vc::assert!(*c == 14u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_scalar_mut_ref_alias_reborrow_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "scalar mutable-reference alias reborrow assignment should update local and aliases, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_indexed_mut_ref_alias_assignment() {
    let code = r#"
        fn check_indexed_mut_ref_alias_assignment() {
            let mut a: [u64; 3] = [5u64, 7u64, 8u64];
            let b: &mut [u64; 3] = &mut a;
            b[1usize] = 20u64;
            trust_vc::assert!(a[0usize] == 5u64);
            trust_vc::assert!(a[1usize] == 20u64);
            trust_vc::assert!(a[2usize] == 8u64);
            trust_vc::assert!(b[1usize] == 20u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_indexed_mut_ref_alias_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "indexed mutable-reference alias assignment should update local and alias, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_mut_ref_array_tuple_field_assignment() {
    let code = r#"
        #[trust_vc::requires(a[0usize].0 == 5u64)]
        #[trust_vc::requires(a[0usize].1 == 6u64)]
        #[trust_vc::requires(a[1usize].0 == 7u64)]
        #[trust_vc::requires(a[1usize].1 == 8u64)]
        #[trust_vc::requires(a[2usize].0 == 9u64)]
        #[trust_vc::requires(a[2usize].1 == 10u64)]
        fn check_mut_ref_array_tuple_field_assignment(a: &mut [(u64, u64); 3]) {
            a[1usize].1 = 200u64;
            trust_vc::assert!(a[0usize].0 == 5u64);
            trust_vc::assert!(a[0usize].1 == 6u64);
            trust_vc::assert!(a[1usize].0 == 7u64);
            trust_vc::assert!(a[1usize].1 == 200u64);
            trust_vc::assert!(a[2usize].0 == 9u64);
            trust_vc::assert!(a[2usize].1 == 10u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_mut_ref_array_tuple_field_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains(".update(1usize,")
                && condition.contains(".0")
                && condition.contains("200u64")
                && condition.contains(".1 == 200u64")
        }),
        "tuple-field assignment through a fixed-array mutable reference should rewrite the array element: {:?}",
        conditions
    );
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "fixed-array tuple-field assignment through a mutable reference should verify updated and framed fields, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_rejects_tuple_struct_array_field_assignment() {
    let code = r#"
        struct Pair(u64, u64);

        fn check_tuple_struct_array_field_assignment(a: &mut [Pair; 3]) {
            a[1usize].1 = 200u64;
            trust_vc::assert!(a[1usize].1 == 200u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_tuple_struct_array_field_assignment").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("indexed assignment target is unsupported")
            && message.contains("directly indexed local array/Seq variables"),
        "tuple-struct array field assignment should fail closed instead of rewriting the element as a plain tuple, got: {message}"
    );
}

#[test]
fn test_scoped_substitution_updates_mut_ref_slice_tuple_field_assignment() {
    let code = r#"
        #[trust_vc::requires(a.len() == 3usize)]
        #[trust_vc::requires(a[0usize].0 == 5u64)]
        #[trust_vc::requires(a[0usize].1 == 6u64)]
        #[trust_vc::requires(a[1usize].0 == 7u64)]
        #[trust_vc::requires(a[1usize].1 == 8u64)]
        #[trust_vc::requires(a[2usize].0 == 9u64)]
        #[trust_vc::requires(a[2usize].1 == 10u64)]
        fn check_mut_ref_slice_tuple_field_assignment(a: &mut [(u64, u64)]) {
            a[1usize].1 = 200u64;
            trust_vc::assert!(a[0usize].0 == 5u64);
            trust_vc::assert!(a[0usize].1 == 6u64);
            trust_vc::assert!(a[1usize].0 == 7u64);
            trust_vc::assert!(a[1usize].1 == 200u64);
            trust_vc::assert!(a[2usize].0 == 9u64);
            trust_vc::assert!(a[2usize].1 == 10u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_mut_ref_slice_tuple_field_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains(".update(1usize,")
                && condition.contains(".0")
                && condition.contains("200u64")
                && condition.contains(".1 == 200u64")
        }),
        "tuple-field assignment through a mutable slice should rewrite the element: {:?}",
        conditions
    );
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "tuple-field assignment through a mutable slice should verify updated and framed fields, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_indexed_mut_ref_alias_compound_assignment() {
    let code = r#"
        fn check_indexed_mut_ref_alias_compound_assignment() {
            let mut a: [u64; 3] = [5u64, 7u64, 8u64];
            let b: &mut [u64; 3] = &mut a;
            b[1usize] += 13u64;
            trust_vc::assert!(a[0usize] == 5u64);
            trust_vc::assert!(a[1usize] == 20u64);
            trust_vc::assert!(a[2usize] == 8u64);
            trust_vc::assert!(b[1usize] == 20u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_indexed_mut_ref_alias_compound_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "indexed mutable-reference alias compound assignment should update local and alias, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_index_projection_mut_ref_assignment() {
    let code = r#"
        fn check_index_projection_mut_ref_assignment() {
            let mut a: [u64; 3] = [5u64, 7u64, 8u64];
            let b = &mut a[1usize];
            *b = 20u64;
            trust_vc::assert!(a[0usize] == 5u64);
            trust_vc::assert!(a[1usize] == 20u64);
            trust_vc::assert!(a[2usize] == 8u64);
            trust_vc::assert!(*b == 20u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_index_projection_mut_ref_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "index-projection mutable-reference assignment should update owner and alias, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_index_projection_mut_ref_param_assignment() {
    let code = r#"
        #[trust_vc::requires(a[0usize] == 5u64)]
        #[trust_vc::requires(a[1usize] == 7u64)]
        #[trust_vc::requires(a[2usize] == 8u64)]
        fn check_index_projection_mut_ref_param_assignment(a: &mut [u64; 3]) {
            let b = &mut a[1usize];
            *b = 20u64;
            trust_vc::assert!(a[0usize] == 5u64);
            trust_vc::assert!(a[1usize] == 20u64);
            trust_vc::assert!(a[2usize] == 8u64);
            trust_vc::assert!(*b == 20u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_index_projection_mut_ref_param_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "index-projection mutable-reference parameter assignment should update owner and alias, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_direct_local_mut_ref_alias_field_assignment() {
    let code = r#"
        struct Pair {
            x: u64,
            y: u64,
        }

        fn check_local_mut_ref_alias_field_assignment() {
            let mut a = Pair { x: 12u64, y: 20u64 };
            let b: &mut Pair = &mut a;
            b.x = 13u64;
            trust_vc::assert!(a.x == 13u64);
            trust_vc::assert!(a.y == 20u64);
            trust_vc::assert!(b.x == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_local_mut_ref_alias_field_assignment").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("Pair { x: 13u64, ..")),
        "direct mutable-reference field assignment should rewrite the owner through struct update syntax: {:?}",
        conditions
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "direct mutable-reference field assignment should verify updated and framed fields, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_direct_local_mut_ref_field_borrow_assignment() {
    let code = r#"
        struct Pair {
            x: u64,
            y: u64,
        }

        #[trust_vc::requires(p < 1000u64)]
        fn check_local_mut_ref_field_borrow_assignment(p: u64) {
            let mut a = Pair { x: p, y: p + 1u64 };
            let b: &mut u64 = &mut a.x;
            *b = p + 2u64;
            trust_vc::assert!(a.x == p + 2u64);
            trust_vc::assert!(a.y == p + 1u64);
            trust_vc::assert!(*b == p + 2u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_local_mut_ref_field_borrow_assignment").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("Pair { x: p + 2u64, ..")),
        "field-borrow mutable-reference assignment should rewrite the owner through struct update syntax: {:?}",
        conditions
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "field-borrow mutable-reference assignment should verify updated and framed fields, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_direct_temporary_mut_ref_assignments() {
    let code = r#"
        struct Pair {
            x: u64,
            y: u64,
        }

        fn check_direct_temporary_mut_ref_assignments() {
            let mut a = 12u64;
            let mut pair = Pair { x: 20u64, y: 30u64 };
            *(&mut a) = 13u64;
            *(&mut pair.x) = 21u64;
            trust_vc::assert!(a == 13u64);
            trust_vc::assert!(pair.x == 21u64);
            trust_vc::assert!(pair.y == 30u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_direct_temporary_mut_ref_assignments").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "direct temporary mutable-reference assignments should verify, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_updates_deref_assignment_through_mut_ref_param_alias() {
    let code = r#"
        fn check_mut_ref_param_alias_assignment(p: &mut u64) {
            let b: &mut u64 = p;
            *b = 13u64;
            trust_vc::assert!(p == 13u64);
            trust_vc::assert!(*b == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_mut_ref_param_alias_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .filter(|condition| condition.contains("13u64") && !condition.contains('*'))
            .count()
            >= 2,
        "mutable-reference parameter alias assignment should update both parameter and alias scoped values: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_updates_direct_mut_ref_param_assignment() {
    let code = r#"
        fn check_direct_mut_ref_param_assignment(p: &mut u64) {
            *p = 13u64;
            trust_vc::assert!(p == 13u64);
            trust_vc::assert!(*p == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_direct_mut_ref_param_assignment").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "direct scalar mutable-reference parameter assignment should verify, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_rejects_field_assignment_through_mut_ref_param_alias() {
    let code = r#"
        struct Pair {
            x: u64,
            y: u64,
        }

        fn check_mut_ref_param_alias_field_assignment(p: &mut Pair) {
            let b: &mut Pair = p;
            b.x = 13u64;
            trust_vc::assert!(b.x == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_mut_ref_param_alias_field_assignment").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("assignment through a mutable-reference projection is unsupported")
            && message.contains("parameter-derived aliases"),
        "mutable-reference parameter field assignment should fail closed instead of treating aliased state as local struct state: {message}"
    );
}

#[test]
fn test_scoped_substitution_updates_owner_through_mut_ref_reborrow_field_assignment() {
    // A field write through a reborrowed `&mut local` alias updates the owning
    // local. `c` reborrows `b`, which borrows `a`; `c.x = 13` must update `a`.
    let code = r#"
        struct Pair {
            x: u64,
            y: u64,
        }

        fn check_mut_ref_reborrow_field_assignment() {
            let mut a = Pair { x: 12u64, y: 20u64 };
            let b: &mut Pair = &mut a;
            let c: &mut Pair = b;
            c.x = 13u64;
            trust_vc::assert!(a.x == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_mut_ref_reborrow_field_assignment").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "reborrow field assignment should update the owning local, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_mut_ref_reborrow_field_assignment_updates_intermediate_alias() {
    // Soundness guard: the intermediate reborrow alias `b` must observe the
    // write through `c`. Reading the stale pre-write value must NOT verify.
    let stale_read = r#"
        struct Pair {
            x: u64,
            y: u64,
        }

        fn check_mut_ref_reborrow_intermediate_stale() {
            let mut a = Pair { x: 12u64, y: 20u64 };
            let b: &mut Pair = &mut a;
            let c: &mut Pair = b;
            c.x = 13u64;
            trust_vc::assert!(b.x == 12u64);
        }
    "#;
    let file = parse_file(stale_read).unwrap();
    let func = find_function(&file, "check_mut_ref_reborrow_intermediate_stale").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "stale intermediate-alias read `b.x == 12` must not verify after `c.x = 13`, got: {:?}",
        result
    );

    let current_read = r#"
        struct Pair {
            x: u64,
            y: u64,
        }

        fn check_mut_ref_reborrow_intermediate_current() {
            let mut a = Pair { x: 12u64, y: 20u64 };
            let b: &mut Pair = &mut a;
            let c: &mut Pair = b;
            c.x = 13u64;
            trust_vc::assert!(b.x == 13u64);
        }
    "#;
    let file = parse_file(current_read).unwrap();
    let func = find_function(&file, "check_mut_ref_reborrow_intermediate_current").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "intermediate-alias read `b.x == 13` should verify after `c.x = 13`, got: {:?}",
        result
    );
}

#[test]
fn test_scoped_substitution_reference_shadowing_uses_nearest_binding() {
    let code = r#"
        fn check_reference_shadowing(x: &u64) {
            let x = 5u64;
            trust_vc::assert!(*x == 5u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_reference_shadowing").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("*(5u64) == 5u64")),
        "a local value that shadows a shared-reference parameter must not inherit erased-reference handling: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_index_receiver_shadowing_uses_nearest_binding() {
    let code = r#"
        fn check_index_receiver_shadowing(ar: &mut [u8; 3]) {
            let alias: &mut [u8; 3] = ar;
            {
                let mut alias = [1u8, 2u8, 3u8];
                alias[0usize] = 9u8;
                trust_vc::assert!(alias[0usize] == 9u8);
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_index_receiver_shadowing").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("update(0usize, 9u8)")),
        "a local array that shadows a borrowed mutable-reference alias should keep local indexed assignment support: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_rejects_old_state_call_in_body_assertion() {
    let code = r#"
        fn check_old_state_call(ar: &mut [u8; 3]) {
            ar[1] += 1;
            assert!(ar[1] == old(ar)[1] + 1);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_old_state_call").unwrap();
    let err = extract_verification_conditions(func).unwrap_err();
    let message = err.to_string();

    assert!(
        message.contains("Unsupported old-state expression `old(...)`")
            && message.contains("current state as pre-state"),
        "old-state body assertions should fail closed until array pre-state is modeled, got: {message}"
    );
}

#[test]
fn test_scoped_substitution_does_not_replay_block_initializer_side_effects() {
    let code = r#"
        fn check_block_initializer() {
            let mut x = 0;
            let _y = { x = x + 1; x };
            assert!(x == 2);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_block_initializer").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("x == 2")),
        "external block-initializer assignment should invalidate the stale local value: {:?}",
        conditions
    );
    assert!(
        !conditions
            .iter()
            .any(|condition| condition.contains("(2) == 2")),
        "block-initializer side effects must not be replayed into a false proof: {:?}",
        conditions
    );
}

#[test]
fn test_statement_expr_helper_call_value_yield_is_sequenced_without_replaying_outer_state() {
    let code = r#"
        fn id(v: u64) -> u64 {
            v
        }

        fn check_helper_call_value() {
            let mut a = 12u64;
            let b = id({
                a = a + 1u64;
                a
            });
            assert!(b == 13u64);
            assert!(a == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_helper_call_value").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| condition.contains("id")
            && condition.contains("12u64")
            && condition.contains("+ 1u64")
            && condition.contains("== 13u64")),
        "helper-call argument should use the statement block's yielded value: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("a == 13u64")),
        "side effects from the call-argument block must invalidate a instead of replaying a stale scoped value: {:?}",
        conditions
    );
    assert!(
        !conditions
            .iter()
            .any(|condition| condition.contains("(13u64) == 13u64")
                || condition.contains("(12u64) == 13u64")
                || condition.contains("a = a + 1u64")),
        "statement-expression helper calls must not replay block side effects into outer state or leave raw assignments in the call argument: {:?}",
        conditions
    );
}

#[test]
fn test_statement_expr_helper_call_shared_ref_yield_is_sequenced_without_replaying_outer_state() {
    let code = r#"
        fn id(v: &u64) -> u64 {
            0u64
        }

        fn check_helper_call_ref() {
            let mut a = 12u64;
            let b = id({
                a = a + 1u64;
                &a
            });
            assert!(b == 13u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_helper_call_ref").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| condition.contains("id")
            && condition.contains("12u64")
            && condition.contains("+ 1u64")
            && condition.contains("== 13u64")),
        "erased shared-reference helper-call argument should use the statement block's yielded value: {:?}",
        conditions
    );
    assert!(
        !conditions
            .iter()
            .any(|condition| condition.contains("(13u64) == 13u64")
                || condition.contains("a = a + 1u64")),
        "shared-reference helper calls must not erase the call or leave raw assignments in the call argument: {:?}",
        conditions
    );
}

#[test]
fn test_statement_expr_helper_call_value_verifies_with_file_context() {
    let code = r#"
        #[trust_vc::ensures(result == v)]
        fn id(v: u64) -> u64 {
            v
        }

        #[trust_vc::ensures(result == 13u64)]
        fn check_helper_call_value() -> u64 {
            let mut a = 12u64;
            let b = id({
                a = a + 1u64;
                a
            });
            trust_vc::assert!(b == 13u64);
            b
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_helper_call_value").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "file context should register same-file helper body facts for statement-expression calls, got: {:?}",
        result
    );
}

#[test]
fn test_statement_expr_helper_call_shared_ref_verifies_with_file_context() {
    let code = r#"
        #[trust_vc::ensures(result == *v)]
        fn id(v: &u64) -> u64 {
            *v
        }

        #[trust_vc::ensures(result == 13u64)]
        fn check_helper_call_ref() -> u64 {
            let mut a = 12u64;
            let b = id({
                a = a + 1u64;
                &a
            });
            trust_vc::assert!(b == 13u64);
            b
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_helper_call_ref").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "file context should treat shared-reference deref and reference arguments as the referent value, got: {:?}",
        result
    );
}

#[test]
fn test_explicit_local_returned_ref_alias_erases_deref_with_file_context() {
    let code = r#"
        fn return_ref(p: &u64) -> &u64 {
            p
        }

        #[trust_vc::requires(p == 12u64)]
        #[trust_vc::ensures(true)]
        fn check_returned_ref_alias(p: u64) {
            let a = p;
            let b: &u64 = return_ref(&a);
            trust_vc::assert!(*b == 12u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_returned_ref_alias").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains("return_ref")
                && condition.contains("== 12u64")
                && !condition.contains("*")
        }),
        "explicit returned-reference local aliases should erase deref reads to the call result: {:?}",
        conditions
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "body axiom for returned-reference helper should prove the erased alias read, got: {:?}",
        result
    );
}

#[test]
fn test_unannotated_local_returned_ref_alias_erases_deref_with_file_context() {
    let code = r#"
        #[trust_vc::ensures(result == p)]
        fn return_ref(p: &u64) -> &u64 {
            p
        }

        #[trust_vc::requires(p == 12u64)]
        #[trust_vc::ensures(true)]
        fn check_returned_ref_alias(p: u64) {
            let a = p;
            let b = return_ref(&a);
            trust_vc::assert!(*b == 12u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_returned_ref_alias").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains("return_ref")
                && condition.contains("== 12u64")
                && !condition.contains("*")
        }),
        "unannotated returned-reference local aliases should erase deref reads through the helper contract: {:?}",
        conditions
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "body axiom for returned-reference helper should prove the unannotated alias read, got: {:?}",
        result
    );
}

#[test]
fn test_sibling_helper_body_axiom_uses_helper_scoped_return() {
    let code = r#"
        #[trust_vc::ensures(result == v + 1u64)]
        fn add1(v: u64) -> u64 {
            let y = v + 1u64;
            y
        }

        #[trust_vc::ensures(result == 13u64)]
        fn check_helper_local_return(y: u64) -> u64 {
            let b = add1(12u64);
            trust_vc::assert!(b == 13u64);
            b
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_helper_local_return").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "helper-local return bindings must not leak into sibling body axioms or capture target locals, got: {:?}",
        result
    );
}

#[test]
fn test_sibling_helper_requires_is_checked_at_call_site() {
    let code = r#"
        #[trust_vc::requires(v > 0)]
        #[trust_vc::ensures(result == v)]
        fn positive_id(v: int) -> int {
            v
        }

        #[trust_vc::ensures(true)]
        fn check_bad_call() {
            let _value = positive_id(0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_bad_call").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && is_call_requires_for(&obligation.name, "positive_id")
                && obligation.condition == "0 > 0"
        }),
        "sibling helper requires clause should become a call-site assertion: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "violating a sibling helper requires clause must not verify, got: {result:?}"
    );
}

/// Regression test (loops_no_spinoff nested case, soundness): a no-invariant
/// `while` whose guard reads a modified counter (`let mut inner = i;
/// while inner < 20 { inner += 1 }`) must NOT leak the counter's PRE-loop scoped
/// value into the post-loop exit fact — that asserted `!(i < 20)` about the
/// ENTRY state, a false fact whenever the loop iterates, and false-Verified
/// `assert!(i >= 20u64)`. A TYPABLE modified counter is now DECLARED at the loop
/// head (Phase-E let-local loop support) and havoc'd to a FRESH exit symbol, so
/// the exit fact references that fresh symbol, not the entry value — sound. (An
/// un-typable counter stays undeclared and the exit fact is DROPPED instead;
/// both directions keep the entry value out of the exit fact.) The load-bearing
/// check is the verdict: `assert!(i >= 20)` must refute for entry `i < 20`.
#[test]
fn test_modified_counter_guard_does_not_leak_pre_loop_value() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn f(i: u64) {
            let mut inner = i;
            while inner < 20u64 {
                inner = inner + 1u64;
            }
            trust_vc::assert!(i >= 20u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "f").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "the counter's pre-loop value must not leak into the exit fact: `assert!(i >= 20)` is \
         false for entry `i < 20` and must counterexample, got: {result:?}"
    );
}

/// Companion no-over-rejection guard: a DECLARED loop counter (a parameter)
/// keeps its normal-exit fact over the fresh exit symbol, so the genuine
/// post-loop bound still verifies.
#[test]
fn test_declared_counter_guard_keeps_exit_fact() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn f(mut i: u64) {
            while i < 20u64 {
                i = i + 1u64;
            }
            trust_vc::assert!(i >= 20u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "f").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "declared counter keeps the exit fact; post-loop bound must verify, got: {result:?}"
    );
}

/// Regression test (refs `test_mut_ref_forward`, root cause d568e2e): the
/// call-site `requires` of a helper taking `&mut` args must be substituted
/// with the PRE-havoc argument values (the state the callee actually
/// receives). d568e2e's free-call `&mut` havoc rebound `p` to `p__havoc_0`
/// BEFORE the contract was recorded, so a satisfied precondition became an
/// unprovable claim about the fresh unconstrained post-call symbol and a
/// correct caller was wrongly counterexampled. The `ensures` assumption must
/// KEEP the post-havoc rendering (it constrains the fresh post-call value).
#[test]
fn test_mut_ref_call_requires_uses_pre_havoc_state() {
    let code = r#"
        #[trust_vc::requires(p == 12u64)]
        #[trust_vc::ensures(p == 12u64)]
        fn callee(p: &mut u64) {}

        #[trust_vc::requires(p == 12u64)]
        #[trust_vc::ensures(true)]
        fn caller(p: &mut u64) {
            callee(p);
            trust_vc::assert!(p == 12u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let requires_obligation = vc
        .obligations
        .iter()
        .find(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && is_call_requires_for(&obligation.name, "callee")
        })
        .expect("call-site requires obligation must be emitted");
    assert!(
        !requires_obligation.condition.contains("__havoc"),
        "call-site requires must be rendered over the PRE-havoc argument value, got: {}",
        requires_obligation.condition
    );
    let ensures_assume = vc
        .obligations
        .iter()
        .find(|obligation| obligation.name.contains("__call_ensures"))
        .expect("call-site ensures assumption must be emitted");
    assert!(
        ensures_assume.condition.contains("__havoc"),
        "call-site ensures must constrain the POST-havoc value, got: {}",
        ensures_assume.condition
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "caller satisfying the callee requires must verify, got: {result:?}"
    );
}

/// Regression test (refs `mutref_arg_ref_unsupported`, root cause d568e2e): a
/// call argument of the literal shape `&mut &y` passes a mutable reference to
/// a TEMPORARY shared reference — the callee can only rebind the temporary,
/// never write to `y` — so the free-call `&mut`-arg havoc must not fire. It
/// previously havoced `y`, the fresh-rebind failed, `invalidate_scoped(y)`
/// dropped the binding, and the post-call `assert!(y == 0u8)` fail-closed with
/// `unresolved variable`.
#[test]
fn test_mut_ref_to_shared_ref_temporary_arg_does_not_havoc_local() {
    let code = r#"
        fn sink(_x: &mut &u8) {}

        #[trust_vc::ensures(true)]
        fn caller() {
            let mut y: u8 = 0u8;
            sink(&mut &y);
            trust_vc::assert!(y == 0u8);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "`&mut &y` cannot mutate `y`; the post-call read must verify, got: {result:?}"
    );
}

#[test]
fn test_generic_trait_method_requires_is_checked_at_call_site() {
    // A generic trait-bounded call `a.f()` where `f` has `requires(self.req())`
    // and the caller never establishes `a.req()`. Before unit 1 this produced
    // ZERO precondition obligations (the requires was only ever consumed as the
    // antecedent of the assumed postcondition axiom) — an unsoundness relative
    // to Verus (`assert req%T.f` at the call). It must now (1) emit a
    // call-site `requires` assertion with `self := a`, and (2) fail to verify
    // (abstract `T__req(a)` is unestablished → fail-closed).
    let code = r#"
        #[trust_vc::trait_spec]
        trait T {
            fn req(&self) -> bool;

            #[trust_vc::requires(self.req())]
            fn f(&self);
        }

        struct S;

        #[trust_vc::trait_impl]
        impl T for S {
            fn req(&self) -> bool {
                true
            }

            fn f(&self) {}
        }

        #[trust_vc::ensures(true)]
        fn test2<A: T>(a: &A) {
            a.f();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "test2").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && is_call_requires_for(&obligation.name, "T__f")
                && obligation.condition.contains("req")
                // Proves `self := a` substitution: no bare `self` survives.
                && !condition_contains_bare_self(&obligation.condition)
        }),
        "generic trait-bounded `requires` should become a call-site assertion with `self := a`: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "an unestablished generic trait-method precondition must not verify, got: {result:?}"
    );
}

#[test]
fn test_generic_trait_method_requires_discharges_when_established() {
    // Same trait/impl, but the caller's OWN `requires(a.req())` supplies the
    // matching `T__req(a)` hypothesis, so the call-site obligation both EXISTS
    // and is dischargeable — pinning that the obligation is real (not dead /
    // vacuous) and that the discharge path works.
    let code = r#"
        #[trust_vc::trait_spec]
        trait T {
            fn req(&self) -> bool;

            #[trust_vc::requires(self.req())]
            fn f(&self);
        }

        struct S;

        #[trust_vc::trait_impl]
        impl T for S {
            fn req(&self) -> bool {
                true
            }

            fn f(&self) {}
        }

        #[trust_vc::requires(a.req())]
        #[trust_vc::ensures(true)]
        fn test1<A: T>(a: &A) {
            a.f();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "test1").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && is_call_requires_for(&obligation.name, "T__f")
                && obligation.condition.contains("req")
        }),
        "the generic trait-bounded `requires` obligation must still be emitted: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "an established generic trait-method precondition must discharge, got: {result:?}"
    );
}

/// True if `condition` contains the token `self` as a standalone identifier
/// (not as a substring of a longer identifier such as `myself`). Used to
/// confirm the `self := receiver` substitution left no bare `self` behind.
fn condition_contains_bare_self(condition: &str) -> bool {
    condition
        .split(|c: char| !c.is_alphanumeric() && c != '_')
        .any(|tok| tok == "self")
}

#[test]
fn test_concrete_trait_method_requires_is_checked_at_call_site() {
    // REAL-PATH WIRING PROOF (unit 2). A concrete-receiver call `s.f()` where
    // `s: S`, `impl T for S`, and `T::f` has `requires(self.req())`. Before
    // unit 2 this produced ZERO precondition obligations: unit 1's dispatch
    // early-returned because a concrete `S` is not a `TypeParam`. Verus emits
    // `assert req%T.f` here unconditionally. This drives the FULL extraction
    // path (`extract_verification_conditions_with_file_context`, NOT direct
    // contract construction): source registration of the trait impl
    // (obstacle 1), the relaxed source-trait gate (obstacle 2), and the
    // bare-`TypeParam` concrete-keying fix (obstacle 3) must all be in place
    // for the obligation to fire.
    let code = r#"
        #[trust_vc::trait_spec]
        trait T {
            fn req(&self) -> bool;

            #[trust_vc::requires(self.req())]
            fn f(&self);
        }

        struct S;

        #[trust_vc::trait_impl]
        impl T for S {
            fn req(&self) -> bool {
                true
            }

            fn f(&self) {}
        }

        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            s.f();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let call_requires: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| {
            matches!(o.kind, ObligationKind::Assert) && is_call_requires_for(&o.name, "T__f")
        })
        .collect();
    assert_eq!(
        call_requires.len(),
        1,
        "concrete-receiver `s.f()` must emit EXACTLY ONE `__call_requires_T__f_*` obligation via the real extraction path: {:?}",
        vc.obligations
    );
    let obligation = call_requires[0];
    assert!(
        obligation.condition.contains("req"),
        "the emitted obligation must carry the `requires` body `req`: {:?}",
        obligation
    );
    // Proves `self := s` substitution: no bare `self` survives, and the actual
    // receiver `s` appears.
    assert!(
        !condition_contains_bare_self(&obligation.condition),
        "the `self := s` substitution must leave no bare `self`: {:?}",
        obligation.condition
    );
    assert!(
        obligation
            .condition
            .split(|c: char| !c.is_alphanumeric() && c != '_')
            .any(|tok| tok == "s"),
        "the substituted receiver `s` must appear in the obligation: {:?}",
        obligation.condition
    );
}

#[test]
fn test_concrete_trait_method_requires_free_method_falls_through() {
    // Fall-through (conservative): the called method `g` has an EMPTY
    // `requires`, so NO obligation is emitted (a missed obligation is sound;
    // a guessed one is not). Confirms the concrete path is requires-scoped.
    let code = r#"
        #[trust_vc::trait_spec]
        trait T {
            fn g(&self);
        }

        struct S;

        #[trust_vc::trait_impl]
        impl T for S {
            fn g(&self) {}
        }

        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            s.g();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        !vc.obligations
            .iter()
            .any(|o| o.name.starts_with("__call_requires_")),
        "a requires-free trait method on a concrete receiver must emit NO call-site obligation: {:?}",
        vc.obligations
    );
}

#[test]
fn test_concrete_default_method_requires_is_checked_at_call_site() {
    // REAL-PATH WIRING PROOF (unit 5). A concrete-receiver call `s.d()` of a
    // trait DEFAULT method `d` that `S` does NOT override. Unit 1 already
    // covers the GENERIC default call (`z.d()`, z: TypeParam) because
    // `trait_bound_method_requires` iterates `trait_decl.methods` (which
    // includes default-bodied methods with their requires). Unit 2's concrete
    // map previously MISSED them: it iterated `impl_decl.method_bindings`, built
    // only from the `ImplItem::Fn` PHYSICALLY WRITTEN in the impl block, so a
    // non-overridden inherited default `d` was absent → no `(S, d)` entry →
    // `s.d()` silently verified while Verus emits `assert req%T.d`. Unit 5 makes
    // `concrete_impl_method_requires` iterate `trait_decl.methods` directly, so
    // the inherited default's requires now keys `(S, d)` and fires here. This
    // drives the FULL extraction path
    // (`extract_verification_conditions_with_file_context`).
    let code = r#"
        #[trust_vc::trait_spec]
        trait T {
            fn req(&self) -> bool;

            #[trust_vc::requires(self.req())]
            fn d(&self) {}
        }

        struct S;

        #[trust_vc::trait_impl]
        impl T for S {
            fn req(&self) -> bool {
                true
            }
        }

        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            s.d();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let call_requires: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| {
            matches!(o.kind, ObligationKind::Assert) && is_call_requires_for(&o.name, "T__d")
        })
        .collect();
    assert_eq!(
        call_requires.len(),
        1,
        "a non-overridden inherited default `s.d()` must emit EXACTLY ONE `__call_requires_T__d_*` obligation via the real extraction path: {:?}",
        vc.obligations
    );
    let obligation = call_requires[0];
    assert!(
        obligation.condition.contains("req"),
        "the emitted obligation must carry the default method's `requires` body `req`: {:?}",
        obligation
    );
    // Proves `self := s` substitution: no bare `self` survives, and the actual
    // receiver `s` appears.
    assert!(
        !condition_contains_bare_self(&obligation.condition),
        "the `self := s` substitution must leave no bare `self`: {:?}",
        obligation.condition
    );
    assert!(
        obligation
            .condition
            .split(|c: char| !c.is_alphanumeric() && c != '_')
            .any(|tok| tok == "s"),
        "the substituted receiver `s` must appear in the obligation: {:?}",
        obligation.condition
    );
}

#[test]
fn test_inherent_method_requires_is_checked_at_call_site() {
    // REAL-PATH WIRING PROOF (unit 3). An INHERENT (non-trait) method call
    // `s.m()` where `s: S` and `impl S { #[requires(self.v > 0)] fn m(&self) }`.
    // Inherent impls never enter `trait_impl_decls` (`parse_trait_impl_decl`
    // hard-errors on `impl Type` without a trait), so before unit 3 this
    // produced ZERO precondition obligations: `m`'s `requires` was assumed at
    // `m`'s entry but never asserted at any call site (the textbook
    // caller/callee asymmetry). Verus emits `assert req%S.m` unconditionally
    // (StmX::Call makes no inherent-vs-trait distinction). This drives the FULL
    // extraction path: the inherent map is built from `file.items` and MERGED
    // into the concrete map, then resolved by the existing `other =>` dispatch
    // arm keyed by the receiver's `to_type_string()`.
    let code = r#"
        struct S { v: i32 }

        impl S {
            #[trust_vc::proof]
            #[requires(self.v > 0)]
            fn m(&self) {}
        }

        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            s.m();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let call_requires: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| {
            matches!(o.kind, ObligationKind::Assert) && is_call_requires_for(&o.name, "S__m")
        })
        .collect();
    assert_eq!(
        call_requires.len(),
        1,
        "inherent `s.m()` must emit EXACTLY ONE `__call_requires_S__m_*` obligation via the real extraction path: {:?}",
        vc.obligations
    );
    let obligation = call_requires[0];
    assert!(
        obligation.condition.contains('v'),
        "the emitted obligation must carry the `requires` body field `v`: {:?}",
        obligation
    );
    // Proves `self := s` substitution: no bare `self` survives, and the actual
    // receiver `s` appears.
    assert!(
        !condition_contains_bare_self(&obligation.condition),
        "the `self := s` substitution must leave no bare `self`: {:?}",
        obligation.condition
    );
    assert!(
        obligation
            .condition
            .split(|c: char| !c.is_alphanumeric() && c != '_')
            .any(|tok| tok == "s"),
        "the substituted receiver `s` must appear in the obligation: {:?}",
        obligation.condition
    );
}

#[test]
fn test_inherent_method_requires_discharges_when_established() {
    // POSITIVE companion: the caller's OWN `requires(s.v > 0)` supplies the
    // matching ground hypothesis, so the inherent call-site obligation both
    // EXISTS and is dischargeable — pinning that it is real (not dead/vacuous)
    // and that the discharge path works. An inherent `requires` is a plain
    // ground condition over the receiver's fields, so no linking axiom is
    // involved.
    let code = r#"
        struct S { v: i32 }

        impl S {
            #[trust_vc::proof]
            #[requires(self.v > 0)]
            fn m(&self) {}
        }

        #[trust_vc::requires(s.v > 0)]
        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            s.m();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|o| {
            matches!(o.kind, ObligationKind::Assert) && is_call_requires_for(&o.name, "S__m")
        }),
        "the inherent-method `requires` obligation must still be emitted: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "an established inherent-method precondition must discharge, got: {result:?}"
    );
}

#[test]
fn test_inherent_method_requires_free_method_falls_through() {
    // Fall-through (conservative): the inherent method `m` has an EMPTY
    // `requires`, so NO obligation is emitted (a missed obligation is sound; a
    // guessed one is not). Confirms the inherent path is requires-scoped.
    let code = r#"
        struct S { v: i32 }

        impl S {
            #[trust_vc::proof]
            fn m(&self) {}
        }

        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            s.m();
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        !vc.obligations
            .iter()
            .any(|o| o.name.starts_with("__call_requires_")),
        "a requires-free inherent method must emit NO call-site obligation: {:?}",
        vc.obligations
    );
}

#[test]
fn test_qualified_ufcs_trait_method_requires_is_checked_at_call_site() {
    // REAL-PATH WIRING PROOF (unit 4). The qualified-UFCS form
    // `<S as T>::f(&s)` of the SAME `(S, f)` the unit-2 concrete map keys.
    // `<S as T>::f(...)` is an `Expr::Call` whose `func` is an `Expr::Path`
    // with `qself.is_some()`; before unit 4, `visit_expr_call` routed it only
    // to `record_helper_contract_call`, which bails the moment `qself.is_some()`
    // → ZERO precondition obligations, while Verus emits the unconditional
    // `assert req%T.f` at StmX::Call for the UFCS kind too. This drives the
    // FULL extraction path (`extract_verification_conditions_with_file_context`),
    // so the unit-2 concrete-map population AND the new unit-4 dispatch must both
    // be in place for the obligation to fire. Mirrors the committed unit-2 test
    // `test_concrete_trait_method_requires_is_checked_at_call_site`, swapping the
    // `s.f()` sugar for the `<S as T>::f(&s)` qualified form.
    let code = r#"
        #[trust_vc::trait_spec]
        trait T {
            fn req(&self) -> bool;

            #[trust_vc::requires(self.req())]
            fn f(&self);
        }

        struct S;

        #[trust_vc::trait_impl]
        impl T for S {
            fn req(&self) -> bool {
                true
            }

            fn f(&self) {}
        }

        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            <S as T>::f(&s);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let call_requires: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| {
            matches!(o.kind, ObligationKind::Assert) && is_call_requires_for(&o.name, "T__f")
        })
        .collect();
    assert_eq!(
        call_requires.len(),
        1,
        "qualified-UFCS `<S as T>::f(&s)` must emit EXACTLY ONE `__call_requires_T__f_*` obligation via the real extraction path: {:?}",
        vc.obligations
    );
    let obligation = call_requires[0];
    assert!(
        obligation.condition.contains("req"),
        "the emitted obligation must carry the `requires` body `req`: {:?}",
        obligation
    );
    // Proves `self := s` substitution: no bare `self` survives (and no stray `&`
    // from the `&s` receiver), and the actual receiver `s` appears.
    assert!(
        !condition_contains_bare_self(&obligation.condition),
        "the `self := s` substitution must leave no bare `self`: {:?}",
        obligation.condition
    );
    assert!(
        obligation
            .condition
            .split(|c: char| !c.is_alphanumeric() && c != '_')
            .any(|tok| tok == "s"),
        "the substituted receiver `s` must appear in the obligation: {:?}",
        obligation.condition
    );
}

#[test]
fn test_qualified_ufcs_trait_method_requires_free_method_falls_through() {
    // Fall-through (conservative): the qualified-UFCS call targets a method `g`
    // with an EMPTY `requires`, so NO obligation is emitted (a missed obligation
    // is sound; a guessed one is not). Confirms the unit-4 path is requires-
    // scoped and that a non-requires-bearing qself call stays silent.
    let code = r#"
        #[trust_vc::trait_spec]
        trait T {
            fn g(&self);
        }

        struct S;

        #[trust_vc::trait_impl]
        impl T for S {
            fn g(&self) {}
        }

        #[trust_vc::ensures(true)]
        fn caller(s: S) {
            <S as T>::g(&s);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "caller").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        !vc.obligations
            .iter()
            .any(|o| o.name.starts_with("__call_requires_")),
        "a requires-free trait method called via qualified-UFCS must emit NO call-site obligation: {:?}",
        vc.obligations
    );
}

#[test]
fn test_aliased_sibling_helper_contracts_are_checked_at_call_site() {
    let code = r#"
        #[trust_vc::requires(v > 0)]
        #[trust_vc::ensures(result == v)]
        fn positive_id(v: int) -> int {
            v
        }

        #[trust_vc::ensures(true)]
        fn check_bad_alias_call() {
            use crate::positive_id as p;
            let _value = p(0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_bad_alias_call").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && is_call_requires_for(&obligation.name, "p")
                && obligation.condition == "0 > 0"
        }),
        "aliased sibling helper requires clause should become a call-site assertion: {:?}",
        vc.obligations
    );
    assert!(
        vc.obligations.iter().any(|obligation| {
            let compact_condition = obligation.condition.split_whitespace().collect::<String>();
            matches!(obligation.kind, ObligationKind::Assume)
                && obligation.name.starts_with("__call_ensures_pp")
                && obligation.name.contains("_p_")
                && obligation.condition.contains("0 > 0")
                && compact_condition.contains("p(0)==0")
        }),
        "aliased sibling helper ensures clause should be guarded and assumed at the call site: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "violating an aliased sibling helper requires clause must not verify, got: {result:?}"
    );
}

#[test]
fn test_crate_qualified_sibling_helper_contracts_are_checked_at_call_site() {
    let code = r#"
        #[trust_vc::requires(v > 0)]
        #[trust_vc::ensures(result == v)]
        fn positive_id(v: int) -> int {
            v
        }

        #[trust_vc::ensures(true)]
        fn check_bad_qualified_call() {
            let _value = crate::positive_id(0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_bad_qualified_call").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.helper_functions_typed.contains_key("crate::positive_id"),
        "crate-qualified helper calls should register the qualified function symbol"
    );
    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && is_call_requires_for(&obligation.name, "crate::positive_id")
                && obligation.condition == "0 > 0"
        }),
        "crate-qualified sibling helper requires should become a call-site assertion: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "violating a crate-qualified sibling helper requires clause must not verify, got: {result:?}"
    );
}

#[test]
fn test_module_qualified_sibling_helper_ensures_propagates_when_requires_established() {
    let code = r#"
        mod helpers {
            #[trust_vc::requires(v >= 0)]
            #[trust_vc::ensures(result > v)]
            pub fn inc_positive(v: int) -> int {
                v + 1
            }
        }

        #[trust_vc::requires(x >= 0)]
        #[trust_vc::ensures(result > x)]
        fn check_qualified_helper_contract(x: int) -> int {
            let y = helpers::inc_positive(x);
            trust_vc::assert!(y > x);
            y
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_qualified_helper_contract").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.helper_functions_typed
            .contains_key("helpers::inc_positive"),
        "module-qualified helper calls should register the full same-file path"
    );
    assert!(
        vc.obligations.iter().any(|obligation| {
            let compact_condition = obligation.condition.split_whitespace().collect::<String>();
            matches!(obligation.kind, ObligationKind::Assume)
                && obligation.name.starts_with("__call_ensures_pp")
                && obligation.name.contains("_helpers::inc_positive_")
                && obligation.condition.contains("x >= 0")
                && compact_condition.contains("helpers::inc_positive")
                && obligation.condition.contains("> x")
        }),
        "module-qualified sibling helper ensures should be guarded and assumed: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "established module-qualified helper requires should expose the helper ensures, got: {result:?}"
    );
}

#[test]
fn test_sibling_helper_ensures_propagates_when_requires_established() {
    let code = r#"
        #[trust_vc::requires(v >= 0)]
        #[trust_vc::ensures(result > v)]
        fn inc_positive(v: int) -> int {
            v + 1
        }

        #[trust_vc::requires(x >= 0)]
        #[trust_vc::ensures(result > x)]
        fn check_helper_contract(x: int) -> int {
            let y = inc_positive(x);
            trust_vc::assert!(y > x);
            y
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_helper_contract").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assume)
                && obligation.name.starts_with("__call_ensures_pp")
                && obligation.name.contains("_inc_positive_")
                && obligation.condition.contains("x >= 0")
                && obligation.condition.contains("||")
                && obligation.condition.contains("inc_positive")
                && obligation.condition.contains("> x")
        }),
        "sibling helper ensures should be assumed under its call-site requires guard: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "established helper requires should expose the helper ensures, got: {result:?}"
    );
}

#[test]
fn test_sibling_helper_ensures_guard_does_not_prove_its_own_requires() {
    let code = r#"
        #[trust_vc::requires(v > 0)]
        #[trust_vc::ensures(v > 0)]
        fn positive_only(v: int) -> int {
            v
        }

        #[trust_vc::ensures(true)]
        fn check_unproven_call(x: int) {
            let _value = positive_only(x);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_unproven_call").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assume)
                && obligation.name.starts_with("__call_ensures_pp")
                && obligation.name.contains("_positive_only_")
                && obligation.condition.contains("||")
                && obligation.condition.contains("x > 0")
        }),
        "helper ensures should be guarded by requires rather than assumed unconditionally: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "a guarded helper ensures must not prove the same call's requires, got: {result:?}"
    );
}

#[test]
fn test_multi_arg_sibling_helper_contract_substitution_is_left_to_right() {
    let code = r#"
        #[trust_vc::requires(second >= first)]
        #[trust_vc::ensures(result == second)]
        fn pick_second(first: int, second: int) -> int {
            second
        }

        #[trust_vc::ensures(true)]
        fn check_arg_order() {
            let mut x = 0;
            let _value = pick_second(
                {
                    x = 2;
                    1
                },
                x,
            );
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_arg_order").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let requires = vc
        .obligations
        .iter()
        .find(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert)
                && is_call_requires_for(&obligation.name, "pick_second")
        })
        .expect("expected call-site requires obligation for pick_second");

    assert!(
        requires.condition.contains("x >= 1"),
        "second argument should be rendered after invalidating side effects from the first argument: {:?}",
        requires
    );
    assert!(
        !requires.condition.contains("(0) >= 1"),
        "second argument must not reuse the stale pre-call local binding: {:?}",
        requires
    );
}

#[test]
fn test_target_contract_sibling_helper_call_fails_closed() {
    let code = r#"
        #[trust_vc::requires(v > 0)]
        #[trust_vc::ensures(result == v)]
        fn positive_id(v: int) -> int {
            v
        }

        #[trust_vc::contract(requires(positive_id(0) == 0))]
        fn check_contract_call() {}
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_contract_call").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func).unwrap_err();

    assert!(
        format!("{err:?}").contains("inside target requires/ensures"),
        "helper calls inside target contracts should fail closed until call-site contract propagation supports them, got: {err:?}"
    );
}

#[test]
fn test_unreferenced_sibling_helper_does_not_break_file_context() {
    let code = r#"
        fn unrelated(v: u64) -> u64 {
            missing_helper(v)
        }

        #[trust_vc::ensures(result == v)]
        fn id(v: u64) -> u64 {
            v
        }

        #[trust_vc::ensures(result == 13u64)]
        fn check_referenced_only() -> u64 {
            let b = id(13u64);
            trust_vc::assert!(b == 13u64);
            b
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_referenced_only").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    let result = vc.verify();

    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "file-context helper collection should ignore unreferenced siblings, got: {:?}",
        result
    );
}

#[test]
fn test_statement_expr_direct_assert_invalidates_outer_state() {
    let code = r#"
        fn id(v: u64) -> u64 {
            v
        }

        fn check_direct_assert() {
            let mut a = 12u64;
            assert!(id({
                a = a + 1u64;
                a
            }) == 13u64);
            assert!(a == 12u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_direct_assert").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| condition.contains("id")
            && condition.contains("12u64")
            && condition.contains("+ 1u64")
            && condition.contains("== 13u64")),
        "direct assertion should render the call argument from the block yield: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("a == 12u64")),
        "direct assertion side effects must invalidate later outer-state assertions: {:?}",
        conditions
    );
    assert!(
        !conditions
            .iter()
            .any(|condition| condition.contains("(12u64) == 12u64")
                || condition.contains("a = a + 1u64")),
        "direct assertion must not keep stale outer bindings or raw assignment expressions: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_applies_to_calc_steps() {
    let code = r#"
        fn check_calc_scope() {
            let x = 5;
            calc! {
                x;
                == {} 5;
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_scope").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_and_assert_by_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("(5) == 5")),
        "calc obligations should use active scoped local bindings: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_applies_to_calc_method_calls_and_ext_eq_args() {
    let code = r#"
        use trust_vc_types::Seq;

        fn check_calc_seq_scope() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8];
            let c: Seq<u8> = trust_vc_types::seq![2u8];
            let d: Seq<u8> = trust_vc_types::seq![1u8, 2u8];

            calc! {
                (==)
                a;
                { assert!(trust_vc::ext_eq!(a, b.add(c))); } b.add(c);
                { assert!(trust_vc::ext_eq!(b.add(c), d)); } d;
            };

            assert!(trust_vc::ext_eq!(b, d));
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_seq_scope").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let mut conditions = collect_assert_and_assert_by_conditions(&vc);
    conditions.extend(
        vc.assert_by_scopes()
            .values()
            .flat_map(|scoped| scoped.iter().map(|obligation| obligation.condition.clone())),
    );
    let compact_conditions = conditions
        .iter()
        .map(|condition| condition.split_whitespace().collect::<String>())
        .collect::<Vec<_>>();

    assert!(
        compact_conditions.iter().any(|condition| {
            condition.contains("trust_vc_types::seq![1u8]")
                && condition.contains(".add(")
                && condition.contains("trust_vc_types::seq![2u8]")
        }),
        "calc method-call intermediates should substitute local Seq bindings: {:?}",
        conditions
    );
    assert!(
        compact_conditions.iter().all(|condition| {
            !condition.contains("b.add")
                && !condition.contains("ext_eq!(b,")
                && !condition.contains("ext_eq!(b)")
        }),
        "calc and ext_eq obligations must not retain raw local `b`: {:?}",
        conditions
    );
}

#[test]
fn test_calc_omitted_ops_extract_assert_seqs_equal_in_step_scopes() {
    let code = r#"
        use trust_vc_types::Seq;

        fn check_calc_assert_seqs_equal_scope() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8];
            let c: Seq<u8> = trust_vc_types::seq![2u8];
            let d: Seq<u8> = trust_vc_types::seq![1u8, 2u8];

            calc! {
                (==)
                a;
                { trust_vc::assert_seqs_equal!(a == b.add(c)); }
                b.add(c);
                { trust_vc::assert_seqs_equal!(b.add(c) == d); }
                d;
            };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_assert_seqs_equal_scope").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let top_level_conditions = collect_assert_and_assert_by_conditions(&vc);
    assert_eq!(
        top_level_conditions.len(),
        3,
        "calc should emit two adjacent steps and one transitive conclusion: {:?}",
        top_level_conditions
    );

    let scoped_conditions = vc
        .assert_by_scopes()
        .values()
        .flat_map(|scoped| scoped.iter().map(|obligation| obligation.condition.clone()))
        .collect::<Vec<_>>();
    let ext_eq_conditions = scoped_conditions
        .iter()
        .filter(|condition| condition.contains("ext_eq!("))
        .collect::<Vec<_>>();
    assert_eq!(
        ext_eq_conditions.len(),
        2,
        "assert_seqs_equal! inside calc proof blocks should stay in step scopes: {:?}",
        scoped_conditions
    );
    assert!(
        ext_eq_conditions
            .iter()
            .all(|condition| condition.contains(".add(") && !condition.contains("b.add")),
        "scoped assert_seqs_equal! obligations should substitute calc locals: {:?}",
        scoped_conditions
    );
}

#[test]
fn test_calc_seq_add_assert_seqs_equal_extracts_without_counterexample() {
    let code = r#"
        use trust_vc_types::Seq;

        #[trust_vc::ensures(true)]
        fn check_calc_seq_add_assert_seqs_equal() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8];
            let c: Seq<u8> = trust_vc_types::seq![2u8];
            let d: Seq<u8> = trust_vc_types::seq![1u8, 2u8];

            trust_vc::calc! {
                (==)
                a;
                { trust_vc::assert_seqs_equal!(a == b + c); }
                b + c;
                { trust_vc::assert_seqs_equal!(b + c == d); }
                d;
            };

            trust_vc::assert!(a == d);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_seq_add_assert_seqs_equal").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert!(
        vc.obligations
            .iter()
            .any(|obligation| obligation.condition.contains(" + ")),
        "upstream-style Seq calc should preserve `+` obligations for lowering: {:?}",
        vc.obligations
    );

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "upstream-style Seq calc with `+` and assert_seqs_equal! should verify deterministically, got {result:?}"
    );
}

/// Adversarial soundness guard (direction A — true must VERIFY): a single-step
/// `calc!` whose proof block proves the step with `assert_seqs_equal!` over a
/// `Seq` concat of concrete literals must verify. This is the minimal repro of
/// the calc-scope incompleteness gap: the identical goal verifies as a
/// straight-line `assert!`, and the calc-step path must reach the same verdict.
#[test]
fn test_calc_seq_single_step_assert_seqs_equal_verifies() {
    let code = r#"
        use trust_vc_types::Seq;

        #[trust_vc::ensures(true)]
        fn check_calc_single_step() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8];
            let c: Seq<u8> = trust_vc_types::seq![2u8];

            trust_vc::calc! {
                (==)
                a;
                { trust_vc::assert_seqs_equal!(a == b + c); }
                b + c;
            };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_single_step").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "single-step Seq calc with assert_seqs_equal! over concat literals should verify, got {result:?}"
    );
}

/// Adversarial soundness guard (direction B — false must NOT verify): the SAME
/// calc shape, but the `assert_seqs_equal!` step asserts equality between seqs
/// that are NOT equal (`[1,2]` vs `[9]+[2] = [9,2]`). The concrete-compute
/// incompleteness recovery only ever upgrades on a definitive `true`, so a goal
/// that concretely evaluates to `false` must NOT verify (fail-closed). A FALSE
/// step verifying here would be a soundness regression.
#[test]
fn test_calc_seq_step_false_assert_seqs_equal_does_not_verify() {
    let code = r#"
        use trust_vc_types::Seq;

        #[trust_vc::ensures(true)]
        fn check_calc_false_step() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![9u8];
            let c: Seq<u8> = trust_vc_types::seq![2u8];

            trust_vc::calc! {
                (==)
                a;
                { trust_vc::assert_seqs_equal!(a == b + c); }
                b + c;
            };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_false_step").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "a calc step asserting a FALSE Seq extensional equality must NOT verify, got {result:?}"
    );
}

/// Adversarial soundness guard (direction C — wrong intermediate step fails):
/// a multi-step `calc!` whose FIRST step is true but whose SECOND step asserts a
/// false Seq equality (`b + c = [1,2]` vs `e = [3,4]`) must NOT verify. This
/// confirms the recovery does not let a bad intermediate calc step (and hence
/// the bogus transitive conclusion `a == e`) slip through.
#[test]
fn test_calc_seq_wrong_intermediate_step_does_not_verify() {
    let code = r#"
        use trust_vc_types::Seq;

        #[trust_vc::ensures(true)]
        fn check_calc_wrong_intermediate() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8];
            let c: Seq<u8> = trust_vc_types::seq![2u8];
            let e: Seq<u8> = trust_vc_types::seq![3u8, 4u8];

            trust_vc::calc! {
                (==)
                a;
                { trust_vc::assert_seqs_equal!(a == b + c); }
                b + c;
                { trust_vc::assert_seqs_equal!(b + c == e); }
                e;
            };

            trust_vc::assert!(a == e);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_wrong_intermediate").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "a calc chain with a FALSE intermediate Seq step must NOT verify, got {result:?}"
    );
}

#[test]
fn test_finite_seq_literal_equality_refutes_different_values() {
    let code = r#"
        use trust_vc_types::Seq;

        #[trust_vc::ensures(true)]
        fn check_finite_seq_literal_inequality() {
            let b: Seq<u8> = trust_vc_types::seq![123u8, 45u8];
            let d: Seq<u8> = trust_vc_types::seq![1u8, 2u8];

            trust_vc::assert!(b == d);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_finite_seq_literal_inequality").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "different finite Seq literals should refute deterministically, got {result:?}"
    );
}

#[test]
fn test_finite_seq_literal_equality_variants_are_deterministic() {
    let code = r#"
        use trust_vc_types::Seq;

        #[trust_vc::ensures(true)]
        fn check_finite_seq_literal_equality_same_values() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8, 2u8];

            trust_vc::assert!(a == b);
        }

        #[trust_vc::ensures(true)]
        fn check_finite_seq_literal_equality_ne_values() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8, 3u8];

            trust_vc::assert!(a != b);
        }

        #[trust_vc::ensures(true)]
        fn check_finite_seq_literal_equality_refutes_different_lengths() {
            let a: Seq<u8> = trust_vc_types::seq![1u8, 2u8];
            let b: Seq<u8> = trust_vc_types::seq![1u8, 2u8, 3u8];

            trust_vc::assert!(a == b);
        }

        #[trust_vc::ensures(true)]
        fn check_finite_seq_literal_equality_flattens_concat() {
            let a: Seq<u8> = trust_vc_types::seq![1u8];
            let b: Seq<u8> = trust_vc_types::seq![2u8];
            let c: Seq<u8> = trust_vc_types::seq![1u8, 2u8];

            trust_vc::assert!(a + b == c);
        }
    "#;
    let file = parse_file(code).unwrap();

    for case_id in [
        "check_finite_seq_literal_equality_same_values",
        "check_finite_seq_literal_equality_ne_values",
        "check_finite_seq_literal_equality_flattens_concat",
    ] {
        let func = find_function(&file, case_id).unwrap();
        let vc = extract_verification_conditions(func).unwrap();
        let result = vc.verify();
        assert!(
            matches!(result, crate::encoder::VerifyResult::Verified),
            "{case_id} should verify deterministically, got {result:?}"
        );
    }

    let func = find_function(
        &file,
        "check_finite_seq_literal_equality_refutes_different_lengths",
    )
    .unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "different-length finite Seq literals should refute deterministically, got {result:?}"
    );
}

#[test]
fn test_calc_step_assumption_does_not_leak_into_later_step_proof() {
    let code = r#"
        fn check_calc_step_scope() {
            let a = 3i32;
            let b = 10i32;
            let c = 20i32;
            let d = 3i32;

            calc! {
                (==)
                a;
                { assume!(false); }
                b + c;
                { assert!(1i32 == 2i32); }
                d;
            };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_calc_step_scope").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
        "assume(false) from the first calc step must not discharge later step assertions, got {result:?}"
    );
}

#[test]
fn test_assert_seqs_equal_source_macro_extracts_extensional_obligation() {
    let code = r#"
        use trust_vc_types::Seq;

        fn check_assert_seqs_equal_scope() {
            let lhs = Seq::<u8>::empty().push(1u8);
            let rhs = Seq::<u8>::empty().push(1u8);

            trust_vc::assert_seqs_equal!(lhs == rhs);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_assert_seqs_equal_scope").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions.iter().any(|condition| {
            condition.contains("ext_eq!(")
                && condition.contains("Seq :: < u8 > :: empty")
                && condition.contains(".push(1u8)")
        }),
        "assert_seqs_equal! should extract to a scoped ext_eq! obligation: {:?}",
        conditions
    );
}

#[test]
fn test_assert_by_contradiction_source_macro_extracts_scoped_proof() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn contradiction_smoke() {
            trust_vc::assert_by_contradiction!(1u64 == 0u64 + 1u64, {
                trust_vc::assert!(false);
            });
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "contradiction_smoke").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert!(
        vc.assert_by_scopes()
            .keys()
            .any(|name| name.starts_with("assert_by_contradiction_")),
        "assert_by_contradiction! should lower into an assert_by scope: {:?}",
        vc.assert_by_scopes().keys().collect::<Vec<_>>()
    );

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "assert_by_contradiction! should verify a contradiction proof scope, got {result:?}"
    );
}

#[test]
fn test_scoped_substitution_does_not_assume_loop_first_iteration_state() {
    let code = r#"
        fn check_loop_state(c: bool) {
            let mut x = 0;
            while c {
                assert!(x == 0);
                x = 1;
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_loop_state").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("x == 0")),
        "loop body assertions should keep loop-carried variables symbolic: {:?}",
        conditions
    );
    assert!(
        !conditions
            .iter()
            .any(|condition| condition.contains("(0) == 0")),
        "loop body assertions must not assume the pre-loop value on every iteration: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_respects_pattern_shadowing() {
    let code = r#"
        fn check_pattern_shadowing(opt: Option<i32>, xs: Vec<i32>) {
            let x = 0;
            match opt {
                Some(x) => assert!(x == 0),
                None => {}
            }
            for x in xs {
                assert!(x == 0);
            }
            let (x,) = (1,);
            assert!(x == 0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_pattern_shadowing").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .all(|condition| !condition.contains("(0) == 0")),
        "pattern binders must shadow outer scoped substitutions: {:?}",
        conditions
    );
}

#[test]
fn test_scoped_substitution_tracks_local_compound_and_invalidates_borrows() {
    let code = r#"
        fn touch(_: &mut i32) {}

        fn check_mutations() {
            let mut x = 0;
            x += 1;
            assert!(x == 0);

            let mut y = 0;
            touch(&mut y);
            assert!(y == 0);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_mutations").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    // A STRAIGHT-LINE local compound assignment is now DESUGARED to the rebind
    // `x = (x) op (rhs)` (mirroring the deref compound path), so the later read
    // of `x` resolves to its tracked value `(0) + (1)` rather than being
    // invalidated (which used to fail the read closed as unresolved). The `+ (1)`
    // increment must therefore appear in the x assertion — proving the value is
    // tracked, so `assert!(x == 0)` becomes the refutable `((0) + (1)) == 0`.
    assert!(
        conditions.iter().any(|condition| condition.contains("(1)")),
        "compound assignment should track x to its incremented value: {:?}",
        conditions
    );
    // A `&mut` borrow through a CONTRACT-LESS call still invalidates the prior
    // binding (no ensures to relate old/new), so `y` stays a bare symbol.
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("y == 0")),
        "mutable borrows should invalidate the prior y binding: {:?}",
        conditions
    );
    // SOUNDNESS INVARIANT (unchanged): a mutating operation must never leave the
    // STALE pre-mutation constant behind — that would false-verify. The rebind
    // tracks the real value (`(0) + (1)`), never the stale `(0)`.
    assert!(
        conditions
            .iter()
            .all(|condition| !condition.contains("(0) == 0")),
        "mutating operations must not leave stale constants behind: {:?}",
        conditions
    );
}

#[test]
fn test_extract_assertion_in_else_if_chain() {
    // else-if chains produce Expr::If in the else branch, not Expr::Block.
    // Before #1741, only Expr::Block else branches were traversed.
    let code = r#"
        fn check(x: i32) {
            if x > 10 {
                assert!(x > 5);
            } else if x > 0 {
                assert!(x > -1);
            } else {
                assert!(x <= 0);
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        3,
        "all 3 assertions (then, else-if, else) must be extracted: {:?}",
        vc.obligations
    );
    // Verify content is distinct — a buggy extractor duplicating one
    // assertion 3 times would pass the count check but fail here (#1780).
    let conditions = collect_assert_conditions(&vc);
    assert!(
        conditions.iter().any(|c| c.contains("x > 5")),
        "must extract 'x > 5' from then branch, got: {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|c| c.contains("x > - 1") || c.contains("x > -1")),
        "must extract 'x > -1' from else-if branch, got: {:?}",
        conditions
    );
    assert!(
        conditions.iter().any(|c| c.contains("x <= 0")),
        "must extract 'x <= 0' from else branch, got: {:?}",
        conditions
    );
}

#[test]
fn test_extract_assertion_in_while_loop() {
    let code = r#"
        fn check_loop(x: i32) {
            while x > 0 {
                assert!(x >= 0);
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_loop").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside while loop must be extracted"
    );
}

#[test]
fn test_extract_assertion_in_for_loop() {
    let code = r#"
        fn check_for(xs: Vec<i32>) {
            for x in xs {
                assert!(x > 0);
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_for").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside for loop must be extracted"
    );
}

#[test]
fn test_extract_assertion_in_infinite_loop() {
    let code = r#"
        fn check_infinite() {
            loop {
                assert!(true);
                break;
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_infinite").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside loop {{}} must be extracted"
    );
}

#[test]
fn test_extract_assertion_in_match_arms() {
    let code = r#"
        fn check_match(x: i32) {
            match x {
                0 => { assert!(x == 0); }
                1 => { assert!(x == 1); }
                _ => { assert!(x > 1); }
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_match").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        3,
        "all 3 match arm assertions must be extracted"
    );
    // Verify distinct content per arm (#1780).
    let conditions = collect_assert_conditions(&vc);
    assert!(
        conditions.iter().any(|c| c.contains("x == 0")),
        "must extract 'x == 0' from arm 0, got: {:?}",
        conditions
    );
    assert!(
        conditions.iter().any(|c| c.contains("x == 1")),
        "must extract 'x == 1' from arm 1, got: {:?}",
        conditions
    );
    assert!(
        conditions.iter().any(|c| c.contains("x > 1")),
        "must extract 'x > 1' from wildcard arm, got: {:?}",
        conditions
    );
}

#[test]
fn test_extract_assertion_in_unsafe_block() {
    let code = r#"
        fn check_unsafe() {
            unsafe {
                assert!(true);
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_unsafe").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside unsafe block must be extracted"
    );
}

#[test]
fn test_extract_assertion_in_let_initializer() {
    // Assertions in block-valued let initializers were previously missed
    // because extract_body_assertions only handled Stmt::Expr.
    let code = r#"
        fn check_let(x: i32) {
            let _y = {
                assert!(x > 0);
                x + 1
            };
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_let").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    // Count only USER assertions: the block-tail `x + 1` is real exec arithmetic
    // that now correctly carries an auto-emitted exec arithmetic-safety obligation
    // (a synthetic reflexive `overflow_check_*`), which `collect_assert_conditions`
    // deliberately excludes. The test's intent — that the nested `assert!(x > 0)`
    // is extracted from the let-initializer block — is unchanged.
    let user_conditions = collect_assert_conditions(&vc);
    assert_eq!(
        user_conditions.len(),
        1,
        "assertion inside let binding initializer block must be extracted, got: {user_conditions:?}"
    );
    assert!(
        user_conditions.iter().any(|c| c.contains("x > 0")),
        "the nested user assertion `x > 0` must be extracted, got: {user_conditions:?}"
    );
}

#[test]
fn test_extract_nested_control_flow() {
    // Deeply nested: if → while → match with assertions at each level.
    let code = r#"
        fn check_nested(x: i32) {
            if x > 0 {
                assert!(x > 0);
                while x > 1 {
                    match x {
                        2 => { assert!(x == 2); }
                        _ => { assert!(x > 2); }
                    }
                }
            }
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_nested").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        3,
        "all 3 nested assertions must be extracted (if, match arm 1, match arm 2)"
    );
    // Verify distinct content across nesting levels (#1780).
    let conditions = collect_assert_conditions(&vc);
    assert!(
        conditions.iter().any(|c| c.contains("x > 0")),
        "must extract 'x > 0' from if body, got: {:?}",
        conditions
    );
    assert!(
        conditions.iter().any(|c| c.contains("x == 2")),
        "must extract 'x == 2' from inner match arm, got: {:?}",
        conditions
    );
    assert!(
        conditions.iter().any(|c| c.contains("x > 2")),
        "must extract 'x > 2' from inner wildcard arm, got: {:?}",
        conditions
    );
}

// ================================================================
// #1777: Paren/Group wrapper nodes must recurse into inner expr
// ================================================================

#[test]
fn test_extract_assertion_in_paren_wrapper() {
    // Parenthesized assertion: (assert!(x > 0)) as expression.
    // Before fix, Expr::Paren fell through to catch-all and the assertion
    // was silently dropped — a false verification pass.
    let code = r#"
        fn check_paren(x: i32) {
            (assert!(x > 0));
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_paren").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside parenthesized expression must be extracted (#1777)"
    );
}

#[test]
fn test_extract_assertion_in_group_wrapper() {
    // Expr::Group (invisible delimiter from proc macros) wrapping an
    // assertion. Group is never produced by source parsing — we construct
    // it from tokens and inject into the VC extraction pipeline directly.
    use proc_macro2::{Delimiter, Group, TokenTree};

    // Build: Group(None, `assert!(x > 0)`) as a syn::Expr
    let inner: proc_macro2::TokenStream = "assert!(x > 0)".parse().unwrap();
    let group = Group::new(Delimiter::None, inner);
    let wrapped: proc_macro2::TokenStream = TokenTree::Group(group).into();
    let expr: Expr = syn::parse2(wrapped).expect("should parse Group-wrapped assert");

    assert!(matches!(&expr, Expr::Group(_)));

    let mut vc = VerificationContext::new();
    vc.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    extract_expr_assertions(&expr, &mut vc, 0).unwrap();
    assert_eq!(
        count_asserts(&vc),
        1,
        "assertion inside Expr::Group must be extracted (#1777)"
    );
}

#[test]
fn top_level_scalar_const_read_registers_value_assumption() {
    let code = r#"
        const BASE: u64 = 3 + 5;

        fn check_const_read() {
            let x = BASE;
            assert!(x == 8u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_read").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.get_variable_type("BASE").is_some(),
        "top-level scalar const should be registered as a typed verification variable"
    );
    assert!(
        vc.obligations.iter().any(|obligation| {
            matches!(obligation.kind, ObligationKind::Assume)
                && obligation.name == "BASE_value"
                && obligation.condition.contains("BASE == ((3 + 5) as u64)")
        }),
        "top-level scalar const should add an initializer assumption, got: {:?}",
        vc.obligations
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "const initializer assumption should prove the const read assertion"
    );
}

#[test]
fn top_level_static_read_stays_unregistered() {
    let code = r#"
        static VALUE: u64 = 8;

        fn check_static_read() {
            let x = VALUE;
            assert!(x == 8u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_static_read").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.get_variable_type("VALUE").is_none(),
        "static items are not part of the top-level scalar const slice"
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Error { .. }),
        "static item reads should continue to fail closed"
    );
}

#[test]
fn top_level_usize_const_array_length_parameter_resolves() {
    let code = r#"
        const N: usize = 3;

        fn check_const_len(ar: [u8; N]) {
            assert!(ar[0usize] == ar[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_len").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert_eq!(
        vc.get_variable_type("ar").cloned(),
        Some(crate::ir::TrustVcType::Array(
            Box::new(crate::ir::TrustVcType::Uint { width: 8 }),
            3,
        )),
        "top-level usize const length should become a concrete array parameter type"
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "resolved const-generic array length should verify the reflexive index assertion"
    );
}

#[test]
fn unresolved_const_array_length_parameter_stays_fail_closed() {
    let code = r#"
        fn check_const_len(ar: [u8; MISSING]) {
            assert!(ar[0usize] == ar[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_len").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("unresolved const-generic array length should fail closed");
    let message = err.to_string();
    assert!(
        message.contains("unsupported const-generic array length")
            && message.contains("parameter `ar`")
            && message.contains("[u8; MISSING]"),
        "unresolved const-generic array length should keep the fail-closed diagnostic, got: {message}"
    );
}

#[test]
fn function_const_generic_array_length_shadows_top_level_const() {
    // The function's own `const N` must NOT resolve through the top-level
    // `const N: usize = 3`. Instead the parameter is modeled symbolically: a
    // variable-length sequence whose view length equals the `N` parameter.
    // Crucially, the length is NOT pinned to `3` — `ar.view().len() == 3` must
    // not be provable here (it would be, unsoundly, if `N` collapsed to the
    // top-level const).
    let code = r#"
        const N: usize = 3;

        fn check_const_len<const N: usize>(ar: [u8; N]) {
            assert!(ar.view().len() == N);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_len").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    // The array length did NOT collapse to the literal `3` — it is modeled as a
    // symbolic-length sequence, with `N` declared as a usize parameter.
    assert_eq!(
        vc.get_variable_type("ar").cloned(),
        Some(crate::ir::TrustVcType::Seq(Box::new(
            crate::ir::TrustVcType::Uint { width: 8 }
        ))),
        "function const-generic array length should be modeled symbolically as a sequence"
    );
    assert!(
        vc.get_variable_type("N").is_some(),
        "the const-generic length parameter should be declared as a verification variable"
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "ar.view().len() == N should verify under the symbolic-length model"
    );

    // The shadowing top-level `const N = 3` must NOT pin the symbolic length:
    // proving `ar.view().len() == 3` must fail closed.
    let pinned_code = r#"
        const N: usize = 3;

        fn check_const_len<const N: usize>(ar: [u8; N]) {
            assert!(ar.view().len() == 3usize);
        }
    "#;
    let pinned_file = parse_file(pinned_code).unwrap();
    let pinned_func = find_function(&pinned_file, "check_const_len").unwrap();
    let pinned_vc =
        extract_verification_conditions_with_file_context(&pinned_file, pinned_func).unwrap();
    assert!(
        !matches!(pinned_vc.verify(), crate::encoder::VerifyResult::Verified),
        "symbolic length must not be pinned to the shadowed top-level const value"
    );
}

#[test]
fn function_const_generic_array_view_len_equals_param() {
    // Upstream Verus `arrays.rs` test5 / generics.rs const_generic: the length
    // of a `[u8; N]` array's view is exactly the const-generic `N`.
    let code = r#"
        fn test5<const N: usize>(ar: [u8; N]) {
            assert!(ar.view().len() == N);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "test5").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "ar@.len() == N should verify for a symbolic const-generic array length"
    );
}

#[test]
fn function_const_generic_array_ref_view_len_equals_param() {
    // Upstream Verus `arrays.rs` test3 (array-to-slice subset): a `&[u8; N]`
    // reference parameter's view length is the const-generic `N`.
    let code = r#"
        fn test3<const N: usize>(ar: &[u8; N]) {
            assert!(ar.view().len() == N);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "test3").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "ar@.len() == N should verify for a &[u8; N] symbolic const-generic length"
    );
}

#[test]
fn function_const_generic_array_view_len_wrong_value_fails_closed() {
    // Soundness guard: a symbolic length must NOT be pinned to any concrete
    // value. `ar@.len() == N + 1` is false for `N == usize::MAX` (and is not a
    // theorem in general), so it must NOT verify — fail closed.
    let code = r#"
        fn test_bad<const N: usize>(ar: [u8; N]) {
            assert!(ar.view().len() == 3usize);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "test_bad").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        !matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "a wrong concrete length must not verify under the symbolic-length model"
    );
}

#[test]
fn non_usize_top_level_const_array_length_stays_fail_closed() {
    let code = r#"
        const N: u64 = 3;

        fn check_const_len(ar: [u8; N]) {
            assert!(ar[0usize] == ar[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_len").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("non-usize top-level const array length should fail closed");
    let message = err.to_string();
    assert!(
        message.contains("unsupported const-generic array length")
            && message.contains("parameter `ar`")
            && message.contains("[u8; N]"),
        "non-usize const should keep fail-closed diagnostic, got: {message}"
    );
}

#[test]
fn static_array_length_stays_fail_closed() {
    let code = r#"
        static N: usize = 3;

        fn check_const_len(ar: [u8; N]) {
            assert!(ar[0usize] == ar[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_len").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("static array length should fail closed");
    let message = err.to_string();
    assert!(
        message.contains("unsupported const-generic array length")
            && message.contains("parameter `ar`")
            && message.contains("[u8; N]"),
        "static array length should keep fail-closed diagnostic, got: {message}"
    );
}

#[test]
fn associated_const_array_length_stays_fail_closed() {
    let code = r#"
        struct Len;
        impl Len {
            const N: usize = 3;
        }

        fn check_const_len(ar: [u8; Len::N]) {
            assert!(ar[0usize] == ar[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_len").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("associated const array length should fail closed");
    let message = err.to_string();
    assert!(
        message.contains("unsupported const-generic array length")
            && message.contains("parameter `ar`")
            && message.contains("[u8; Len::N]"),
        "associated const array length should keep fail-closed diagnostic, got: {message}"
    );
}

#[test]
fn expression_const_array_length_folds_and_resolves() {
    // Previously `expression_const_array_length_stays_fail_closed` (a pinned
    // *unsupported* gap, not an unsoundness): a non-literal `usize` const array
    // length was a hard reject. The checked `const_eval_usize` folder now folds
    // exact integer arithmetic, so `const N: usize = 1 + 2` resolves to the
    // concrete length `3` — exactly rustc's value.
    let code = r#"
        const N: usize = 1 + 2;

        fn check_const_len(ar: [u8; N]) {
            assert!(ar[0usize] == ar[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_const_len").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert_eq!(
        vc.get_variable_type("ar").cloned(),
        Some(crate::ir::TrustVcType::Array(
            Box::new(crate::ir::TrustVcType::Uint { width: 8 }),
            3,
        )),
        "`const N: usize = 1 + 2` should fold to the concrete array length 3"
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "folded const-arithmetic array length should verify the reflexive index assertion"
    );
}

// ── Checked `usize` const array-length folding (`const_eval_usize`) ──
//
// A folded array length feeds index-bounds obligations: `[T; N]` ⇒
// `a@.len() == N` ⇒ `a[i]` requires `i < N`. The folder must equal rustc's
// value EXACTLY or fail closed — over-sizing `N` would falsely accept an
// out-of-bounds access. These tests pin completeness (arithmetic / chained
// refs resolve) AND exactness (an access at `index == N` refutes) AND
// fail-closed on overflow / underflow / unsupported ops.

#[test]
fn const_arith_array_length_index_in_bounds_verifies() {
    // Completeness: `const N: usize = 2 + 2` folds to 4; `a[3]` (3 < 4) verifies.
    let code = r#"
        const N: usize = 2 + 2;

        fn f(a: [u8; N]) {
            assert!(a[3usize] == a[3usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "f").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert_eq!(
        vc.get_variable_type("a").cloned(),
        Some(crate::ir::TrustVcType::Array(
            Box::new(crate::ir::TrustVcType::Uint { width: 8 }),
            4,
        )),
        "`const N: usize = 2 + 2` should fold to the concrete array length 4"
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "in-bounds index 3 into a folded length-4 array should verify"
    );
}

#[test]
fn const_arith_array_length_exactness_witness_fails_closed() {
    // SOUNDNESS WITNESS (exactness, not over-approximation): with N == 4, an
    // access at `index == N` (== 4) must REFUTE — `4 < 4` is false. If the
    // folder had over-sized N (e.g. >= 5) this would falsely verify.
    let at_n = r#"
        const N: usize = 2 + 2;

        fn g(a: [u8; N]) {
            assert!(a[4usize] == a[4usize]);
        }
    "#;
    let file = parse_file(at_n).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        matches!(
            vc.verify(),
            crate::encoder::VerifyResult::Counterexample { .. }
        ),
        "index == folded length (4) must refute with a Counterexample (exactness)"
    );

    // A further out-of-bounds index also refutes.
    let past_n = r#"
        const N: usize = 2 + 2;

        fn g(a: [u8; N]) {
            assert!(a[5usize] == a[5usize]);
        }
    "#;
    let file = parse_file(past_n).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        matches!(
            vc.verify(),
            crate::encoder::VerifyResult::Counterexample { .. }
        ),
        "index 5 past the folded length 4 must refute with a Counterexample"
    );
}

#[test]
fn const_ref_array_length_resolves_and_stays_exact() {
    // Chained reference: `const B: usize = N + 1` resolves against the
    // already-folded `N` (4) to 5. `a[4]` (4 < 5) verifies; `a[5]` (== B)
    // refutes — exactness through a const reference.
    let in_bounds = r#"
        const N: usize = 2 + 2;
        const B: usize = N + 1;

        fn f(a: [u8; B]) {
            assert!(a[4usize] == a[4usize]);
        }
    "#;
    let file = parse_file(in_bounds).unwrap();
    let func = find_function(&file, "f").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert_eq!(
        vc.get_variable_type("a").cloned(),
        Some(crate::ir::TrustVcType::Array(
            Box::new(crate::ir::TrustVcType::Uint { width: 8 }),
            5,
        )),
        "`const B: usize = N + 1` should fold to 5 via the registered `N`"
    );
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "index 4 into a folded length-5 array should verify"
    );

    let at_b = r#"
        const N: usize = 2 + 2;
        const B: usize = N + 1;

        fn g(a: [u8; B]) {
            assert!(a[5usize] == a[5usize]);
        }
    "#;
    let file = parse_file(at_b).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        matches!(
            vc.verify(),
            crate::encoder::VerifyResult::Counterexample { .. }
        ),
        "index == folded chained length (5) must refute (exactness through a ref)"
    );
}

#[test]
fn overflowing_const_array_length_fails_closed() {
    // 2^32 * 2^32 == 2^64 overflows `usize` (max 2^64 - 1): `checked_mul`
    // returns `None`, so the length is NOT folded and the parameter is
    // rejected — never a wrong-but-accepted length. (Such a const is itself a
    // rustc compile error.)
    let code = r#"
        const HUGE: usize = 4294967296 * 4294967296;

        fn f(a: [u8; HUGE]) {
            assert!(a[0usize] == a[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "f").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("overflowing const array length must fail closed");
    let message = err.to_string();
    assert!(
        message.contains("unsupported const-generic array length")
            && message.contains("parameter `a`")
            && message.contains("[u8; HUGE]"),
        "overflowing const length should keep the fail-closed diagnostic, got: {message}"
    );
}

#[test]
fn underflowing_const_array_length_fails_closed() {
    // `1 - 2` underflows `usize` (negative): `checked_sub` returns `None` ⇒
    // fail closed. (Also a rustc compile error.)
    let code = r#"
        const NEG: usize = 1 - 2;

        fn f(a: [u8; NEG]) {
            assert!(a[0usize] == a[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "f").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("underflowing const array length must fail closed");
    let message = err.to_string();
    assert!(
        message.contains("unsupported const-generic array length")
            && message.contains("parameter `a`")
            && message.contains("[u8; NEG]"),
        "underflowing const length should keep the fail-closed diagnostic, got: {message}"
    );
}

#[test]
fn unsupported_op_const_array_length_fails_closed() {
    // Division is not a supported fold op (and `/ 0` would be div-by-zero):
    // the folder returns `None` ⇒ fail closed, never a guessed length.
    let code = r#"
        const D: usize = 4 / 0;

        fn f(a: [u8; D]) {
            assert!(a[0usize] == a[0usize]);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "f").unwrap();
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("unsupported-op const array length must fail closed");
    let message = err.to_string();
    assert!(
        message.contains("unsupported const-generic array length")
            && message.contains("parameter `a`")
            && message.contains("[u8; D]"),
        "unsupported-op const length should keep the fail-closed diagnostic, got: {message}"
    );
}

#[test]
fn literal_array_length_unchanged_in_bounds_and_exact() {
    // Control: a plain literal `[u8; 4]` (never routed through the const
    // registry) is unchanged — `a[3]` verifies, `a[4]` refutes.
    let ok = r#"
        fn f(a: [u8; 4]) {
            assert!(a[3usize] == a[3usize]);
        }
    "#;
    let file = parse_file(ok).unwrap();
    let func = find_function(&file, "f").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        matches!(vc.verify(), crate::encoder::VerifyResult::Verified),
        "literal length-4 array with in-bounds index 3 should still verify"
    );

    let oob = r#"
        fn g(a: [u8; 4]) {
            assert!(a[4usize] == a[4usize]);
        }
    "#;
    let file = parse_file(oob).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();
    assert!(
        matches!(
            vc.verify(),
            crate::encoder::VerifyResult::Counterexample { .. }
        ),
        "literal length-4 array with index 4 should still refute"
    );
}

// ── Function-local `const`/`static` initializer overflow obligations (#2778) ──
//
// Faithful to Verus, an exec `const`/`static` whose initializer overflows its
// declared type is a verification error; a safe one verifies. The initializer
// is routed through the same exec-mode arithmetic-overflow obligation path as
// `let` bindings (no second overflow definition).

#[test]
fn test_const_overflowing_initializer_fails_closed() {
    let code = r#"
        fn check() {
            const C: u8 = 255u8 + 1u8;
            trust_vc::assert!(C == C);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert!(
        vc.obligations()
            .iter()
            .any(|obligation| obligation.name().starts_with("overflow_check_")),
        "overflowing const initializer should emit an exec arithmetic overflow obligation: {:?}",
        vc.obligations()
    );

    let result = vc.verify();
    assert!(
        !result.is_verified(),
        "u8::MAX + 1 const initializer must not verify (overflow), got: {result:?}"
    );
}

#[test]
fn test_const_safe_initializer_verifies_and_substitutes_value() {
    let code = r#"
        fn check() {
            const C: u8 = 200u8 + 50u8;
            trust_vc::assert!(C == 250u8);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("200u8 + 50u8")),
        "const initializer value should substitute into later references: {conditions:?}"
    );

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "safe const initializer (200 + 50 = 250) should verify, got: {result:?}"
    );
}

#[test]
fn test_static_overflowing_initializer_fails_closed() {
    let code = r#"
        fn check() {
            static C: u8 = 255u8 + 1u8;
            trust_vc::assert!(C == C);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    assert!(
        vc.obligations()
            .iter()
            .any(|obligation| obligation.name().starts_with("overflow_check_")),
        "overflowing static initializer should emit an exec arithmetic overflow obligation: {:?}",
        vc.obligations()
    );

    let result = vc.verify();
    assert!(
        !result.is_verified(),
        "u8::MAX + 1 static initializer must not verify (overflow), got: {result:?}"
    );
}

#[test]
fn test_static_safe_initializer_verifies_and_substitutes_value() {
    let code = r#"
        fn check() {
            static C: u8 = 200u8 + 50u8;
            trust_vc::assert!(C == 250u8);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains("200u8 + 50u8")),
        "static initializer value should substitute into later references: {conditions:?}"
    );

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "safe static initializer (200 + 50 = 250) should verify, got: {result:?}"
    );
}

#[test]
fn test_local_const_used_in_overflowing_arithmetic_yields_counterexample() {
    let code = r#"
        fn check(x: u8) {
            const ONE: u8 = 1u8;
            let y: u8 = x + ONE;
            trust_vc::assert!(y == y);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check").unwrap();
    let vc = extract_verification_conditions(func).unwrap();

    let result = vc.verify();
    assert!(
        result.is_counterexample(),
        "x + ONE where x: u8 and ONE = 1 can overflow at x = 255; expected counterexample, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Statement-level mutable-slice `.set(idx, val)` in-place update lowering
// (cluster #2779; upstream Verus `slices.rs` test1 `test_set`/`test_set3`).
//
// A discarded `recv.set(idx, val)` on a mutable slice/Vec/array place is routed
// to the same `recv = recv.update(idx, val)` scoped re-binding that
// `recv[idx] = val` already uses. The bounds obligation `idx < recv.len()` is
// carried by `native_seq_update`, matching vstd `<[T]>::set`'s
// `requires idx < self@.len()`, so the lowering is at least as conservative as
// Verus. Before this lowering, `recv.set(idx, val)` was silently dropped (the
// receiver was merely invalidated), so a faithful port returned a spurious
// counterexample because contents were never updated.
// ---------------------------------------------------------------------------

#[test]
fn test_mut_slice_set_method_updates_contents_verifies() {
    // Faithful port of upstream `test_set` (minus the trailing `assert(false)`):
    // after two `.set` calls the slice contents are known and the reads verify.
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set(x: &mut [u64]) {
            x.set(0usize, 5u64);
            x.set(1usize, 20u64);
            trust_vc::assert!(x[0usize] == 5u64);
            trust_vc::assert!(x[1usize] == 20u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(0usize, 5u64)")),
        "statement-level `.set` should rewrite the slice binding through update(): {:?}",
        conditions
    );
    assert!(
        conditions
            .iter()
            .any(|condition| condition.contains(".update(1usize, 20u64)")),
        "the second `.set` should compose on the updated binding: {:?}",
        conditions
    );

    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "mutable-slice `.set` should update contents so both reads verify, got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_method_wrong_value_counterexample() {
    // DISCRIMINATING: a read that contradicts the value written by `.set` must
    // not verify — proves the lowering models the actual stored value, not a
    // free one.
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set_wrong(x: &mut [u64]) {
            x.set(0usize, 5u64);
            trust_vc::assert!(x[0usize] == 7u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_wrong").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        result.is_counterexample(),
        "`.set(0, 5)` then asserting `x[0] == 7` must NOT verify, got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_method_assert_false_counterexample() {
    // Faithful port of the full upstream `test_set`, which Verus reports as a
    // FAILURE: the trailing `assert(false)` is unreachable from the known facts.
    // Even though both `.set` reads are correct, `false` must not verify — this
    // guards against the lowering over-proving (collapsing the path condition).
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set_assert_false(x: &mut [u64]) {
            x.set(0usize, 5u64);
            x.set(1usize, 20u64);
            trust_vc::assert!(x[0usize] == 5u64);
            trust_vc::assert!(x[1usize] == 20u64);
            trust_vc::assert!(false);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_assert_false").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        result.is_counterexample(),
        "faithful `test_set` asserts `false`, which Verus rejects; expected counterexample, got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_method_no_bounds_precondition_counterexample() {
    // Faithful port of upstream `test_set3`, which Verus reports as a FAILURE:
    // `x.set(0, 5)` with NO length precondition cannot discharge vstd `set`'s
    // `requires idx < self@.len()` (the slice may be empty). The result of
    // `.set` is discarded, so the bounds obligation must still be emitted at the
    // statement site to match Verus.
    let code = r#"
        #[trust_vc::ensures(true)]
        fn check_set3(x: &mut [u64]) {
            x.set(0usize, 5u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set3").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        result.is_counterexample(),
        "discarded `.set` with no length precondition must fail the bounds check (test_set3), got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_method_in_bounds_from_requires_discarded_verifies() {
    // Companion to the test_set3 fail direction: once the length precondition
    // guarantees the index is in bounds, the discarded `.set` bounds obligation
    // is discharged and the (otherwise trivial) function verifies. This proves
    // the statement-site bounds obligation is not a blanket failure.
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set_in_bounds(x: &mut [u64]) {
            x.set(0usize, 5u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_in_bounds").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "discarded in-bounds `.set` should discharge its bounds obligation and verify, got: {result:?}"
    );
}

#[test]
fn test_vec_set_method_updates_contents_verifies() {
    // `.set` lowering also applies to a `Vec<T>` place (vstd `Vec::set`), which
    // models the same backend Seq shape as a mutable slice.
    let code = r#"
        #[trust_vc::requires(v.len() == 2usize)]
        #[trust_vc::ensures(true)]
        fn check_vec_set(v: &mut Vec<u64>) {
            v.set(0usize, 9u64);
            trust_vc::assert!(v[0usize] == 9u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_vec_set").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "mutable Vec `.set` should update contents so the read verifies, got: {result:?}"
    );
}

#[test]
fn test_set_method_on_non_sequence_receiver_not_lowered() {
    // SOUNDNESS GUARD: a `.set(idx, val)` call whose receiver is NOT a modeled
    // sequence place (here a scalar local) must NOT be lowered to a sequence
    // `update()` — doing so would fabricate sequence contents for a value that
    // has none. The fall-through path conservatively invalidates the receiver,
    // so no `.update(` model is produced and a later read is non-provable
    // (fail-closed), never wrongly proven.
    let code = r#"
        fn check_scalar_set() {
            let mut x: u64 = 3u64;
            x.set(0usize, 5u64);
            trust_vc::assert!(x == 3u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_scalar_set").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let conditions = collect_assert_conditions(&vc);

    assert!(
        conditions
            .iter()
            .all(|condition| !condition.contains(".update(")),
        "a `.set` on a non-sequence receiver must not be lowered to a sequence update(): {:?}",
        conditions
    );
    let result = vc.verify();
    // The receiver was invalidated rather than mis-modeled, so the read of `x`
    // is non-provable. The verdict must be fail-closed — anything but Verified
    // (here an unresolved-variable Error, which is strictly more conservative
    // than a counterexample). The soundness property is "not wrongly Verified".
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "a `.set` on a non-sequence receiver must never be wrongly proven (fail-closed), got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Unit 6: supertrait-method `requires` discharge (`trait T: Super`)
// ---------------------------------------------------------------------------

#[test]
fn test_generic_supertrait_method_requires_is_checked_at_call_site() {
    // REAL-PATH WIRING PROOF (unit 6, GENERIC). `z.super_m(5)` where `z: Z`,
    // `Z: T`, `trait T: Super`, and `Super::super_m` has `requires(n > 10)`.
    // Before unit 6 neither requires builder saw `Super`'s methods (TraitDecl
    // carried no supertraits; the `: Super` bound was unparsed), so this call
    // silently verified while Verus emits `assert req%Super.super_m`. The
    // obligation name MUST be `__call_requires_Super__super_m_*` — keyed on the
    // DECLARING trait `Super`, NOT the bound trait `T` — because the encoder
    // linking axiom grounds `Super__super_m`. With `n = 5` (< 10) unestablished,
    // verify() must NOT be Verified (fail-closed).
    let code = r#"
        #[trust_vc::trait_spec]
        trait Super {
            #[trust_vc::requires(n > 10)]
            fn super_m(&self, n: u64);
        }

        #[trust_vc::trait_spec]
        trait T: Super {}

        struct S;

        #[trust_vc::trait_impl]
        impl Super for S {
            fn super_m(&self, n: u64) {}
        }

        #[trust_vc::trait_impl]
        impl T for S {}

        #[trust_vc::ensures(true)]
        fn g<Z: T>(z: &Z) {
            z.super_m(5);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let call_requires: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| {
            matches!(o.kind, ObligationKind::Assert)
                && is_call_requires_for(&o.name, "Super__super_m")
        })
        .collect();
    assert_eq!(
        call_requires.len(),
        1,
        "a generic supertrait-method call `z.super_m(5)` must emit EXACTLY ONE \
         `__call_requires_Super__super_m_*` obligation (declaring-trait keyed): {:?}",
        vc.obligations
    );
    // No obligation should use the BOUND trait `T` as the prefix — that would
    // be ungrounded by the linking axiom.
    assert!(
        !vc.obligations
            .iter()
            .any(|o| is_call_requires_for(&o.name, "T__super_m")),
        "the obligation must NOT be keyed on the bound trait `T`: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "an unestablished supertrait precondition (5 > 10) must not verify, got: {result:?}"
    );
}

#[test]
fn test_generic_supertrait_method_requires_discharges_when_established() {
    // Same trait/impl as above, but the call passes `super_m(11)` (11 > 10), so
    // the supertrait precondition holds and the obligation discharges. Pins that
    // the obligation is LIVE (not dead/vacuous) — it must still EXIST and
    // verify() must be Verified.
    let code = r#"
        #[trust_vc::trait_spec]
        trait Super {
            #[trust_vc::requires(n > 10)]
            fn super_m(&self, n: u64);
        }

        #[trust_vc::trait_spec]
        trait T: Super {}

        struct S;

        #[trust_vc::trait_impl]
        impl Super for S {
            fn super_m(&self, n: u64) {}
        }

        #[trust_vc::trait_impl]
        impl T for S {}

        #[trust_vc::ensures(true)]
        fn g<Z: T>(z: &Z) {
            z.super_m(11);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|o| {
            matches!(o.kind, ObligationKind::Assert)
                && is_call_requires_for(&o.name, "Super__super_m")
        }),
        "the supertrait-method obligation must still be emitted: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "an established supertrait precondition (11 > 10) must discharge, got: {result:?}"
    );
}

#[test]
fn test_concrete_supertrait_method_requires_is_checked_at_call_site() {
    // REAL-PATH WIRING PROOF (unit 6, CONCRETE). `s.super_m(5)` where `s: S`,
    // `impl T for S`, `trait T: Super`, and `Super::super_m` has
    // `requires(n > 10)`. The concrete builder must walk the supertrait closure
    // from `T` and emit `__call_requires_Super__super_m_*` (declaring-trait
    // keyed). With `n = 5`, verify() must NOT be Verified.
    let code = r#"
        #[trust_vc::trait_spec]
        trait Super {
            #[trust_vc::requires(n > 10)]
            fn super_m(&self, n: u64);
        }

        #[trust_vc::trait_spec]
        trait T: Super {}

        struct S;

        #[trust_vc::trait_impl]
        impl Super for S {
            fn super_m(&self, n: u64) {}
        }

        #[trust_vc::trait_impl]
        impl T for S {}

        #[trust_vc::ensures(true)]
        fn g(s: &S) {
            s.super_m(5);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    let call_requires: Vec<_> = vc
        .obligations
        .iter()
        .filter(|o| {
            matches!(o.kind, ObligationKind::Assert)
                && is_call_requires_for(&o.name, "Super__super_m")
        })
        .collect();
    assert_eq!(
        call_requires.len(),
        1,
        "a concrete supertrait-method call `s.super_m(5)` must emit EXACTLY ONE \
         `__call_requires_Super__super_m_*` obligation (declaring-trait keyed): {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        !matches!(result, crate::encoder::VerifyResult::Verified),
        "an unestablished concrete supertrait precondition (5 > 10) must not verify, got: {result:?}"
    );
}

#[test]
fn test_concrete_supertrait_method_requires_discharges_when_established() {
    // Same as the concrete FAIL test but `s.super_m(11)` (11 > 10) — the
    // obligation must still EXIST and now discharge (LIVE, not vacuous).
    let code = r#"
        #[trust_vc::trait_spec]
        trait Super {
            #[trust_vc::requires(n > 10)]
            fn super_m(&self, n: u64);
        }

        #[trust_vc::trait_spec]
        trait T: Super {}

        struct S;

        #[trust_vc::trait_impl]
        impl Super for S {
            fn super_m(&self, n: u64) {}
        }

        #[trust_vc::trait_impl]
        impl T for S {}

        #[trust_vc::ensures(true)]
        fn g(s: &S) {
            s.super_m(11);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "g").unwrap();
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap();

    assert!(
        vc.obligations.iter().any(|o| {
            matches!(o.kind, ObligationKind::Assert)
                && is_call_requires_for(&o.name, "Super__super_m")
        }),
        "the concrete supertrait-method obligation must still be emitted: {:?}",
        vc.obligations
    );
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "an established concrete supertrait precondition (11 > 10) must discharge, got: {result:?}"
    );
}

// ── Adversarial regression suite for the mut-slice `.set()` update + index
// read encoding (robustness bug #10). A `.set` followed by a genuinely-false
// read must refute with a CLEAN concrete counterexample model (never the
// `internal-error` that the redundant read-over-write `forall` + reflexive
// extensional-equality `forall` used to inject into ay's SAT model
// generation), while every true read must still Verify and no wrong read may
// ever produce a false Verified.

#[test]
fn test_mut_slice_set_wrong_value_refutes_with_concrete_model() {
    // (a) The false read must produce a Counterexample carrying a concrete
    // witness model (Some + non-empty bindings), not an Unknown/internal-error.
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set_wrong_model(x: &mut [u64]) {
            x.set(0usize, 5u64);
            trust_vc::assert!(x[0usize] == 7u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_wrong_model").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    match result {
        crate::encoder::VerifyResult::Counterexample {
            ref model,
            ref bindings,
            ..
        } => {
            assert!(
                model.is_some(),
                "false `.set` read must refute with a concrete model, got empty model: {result:?}"
            );
            assert!(
                !bindings.is_empty(),
                "counterexample must carry at least one structured binding: {result:?}"
            );
        }
        other => panic!(
            "`.set(0,5)` then `x[0]==7` must refute with a clean Counterexample \
             (NOT Unknown/internal-error), got: {other:?}"
        ),
    }
}

#[test]
fn test_mut_slice_set_true_value_read_verifies() {
    // (b) The matching true read must Verify (the lowering models the stored
    // value, so `x[0] == 5` after `.set(0,5)` is provable).
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set_true(x: &mut [u64]) {
            x.set(0usize, 5u64);
            trust_vc::assert!(x[0usize] == 5u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_true").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "`.set(0,5)` then `x[0]==5` must Verify, got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_unaffected_index_preserved_verifies() {
    // (c) A `.set` at index 0 must leave index 1 unchanged: with a precondition
    // pinning `x[1] == 9`, reading `x[1] == 9` after `x.set(0, 5)` Verifies —
    // proving the read-over-write at a DIFFERENT index is still sound after the
    // redundant frame `forall` was removed.
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize && x[1usize] == 9u64)]
        #[trust_vc::ensures(true)]
        fn check_set_other_idx(x: &mut [u64]) {
            x.set(0usize, 5u64);
            trust_vc::assert!(x[1usize] == 9u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_other_idx").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "`.set(0,5)` must preserve `x[1]`, so `x[1]==9` should Verify, got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_two_indices_wrong_read_refutes() {
    // (c/d) Two `.set`s at distinct indices must each store independently: after
    // `x.set(0,5); x.set(1,9)`, reading `x[1] == 8` (wrong) must refute with a
    // Counterexample — the index-0 write must not corrupt the index-1 value, and
    // the index-1 read-over-write must resolve through the nested `store`s
    // natively (the removed frame `forall` is not needed for this).
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set_two_idx_wrong(x: &mut [u64]) {
            x.set(0usize, 5u64);
            x.set(1usize, 9u64);
            trust_vc::assert!(x[1usize] == 8u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_two_idx_wrong").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        result.is_counterexample(),
        "`x.set(0,5); x.set(1,9)` then `x[1]==8` must refute, got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_two_indices_true_read_verifies() {
    // (c) Dual to the above: the matching true read `x[1] == 9` Verifies and the
    // index-0 write is independently confirmed (`x[0] == 5`).
    let code = r#"
        #[trust_vc::requires(x.len() == 3usize)]
        #[trust_vc::ensures(true)]
        fn check_set_two_idx_true(x: &mut [u64]) {
            x.set(0usize, 5u64);
            x.set(1usize, 9u64);
            trust_vc::assert!(x[0usize] == 5u64);
            trust_vc::assert!(x[1usize] == 9u64);
        }
    "#;
    let file = parse_file(code).unwrap();
    let func = find_function(&file, "check_set_two_idx_true").unwrap();
    let vc = extract_verification_conditions(func).unwrap();
    let result = vc.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "`x.set(0,5); x.set(1,9)` then both correct reads must Verify, got: {result:?}"
    );
}

#[test]
fn test_mut_slice_set_updated_index_wrong_values_never_verify() {
    // (d) No false Verified on any wrong read of the updated index. Every value
    // other than the stored `5` must refute with a Counterexample.
    for wrong in [0u64, 1, 4, 6, 7, 99] {
        let code = format!(
            r#"
            #[trust_vc::requires(x.len() == 3usize)]
            #[trust_vc::ensures(true)]
            fn check_set_wrong_n(x: &mut [u64]) {{
                x.set(0usize, 5u64);
                trust_vc::assert!(x[0usize] == {wrong}u64);
            }}
        "#
        );
        let file = parse_file(&code).unwrap();
        let func = find_function(&file, "check_set_wrong_n").unwrap();
        let vc = extract_verification_conditions(func).unwrap();
        let result = vc.verify();
        assert!(
            result.is_counterexample(),
            "`.set(0,5)` then `x[0]=={wrong}` must refute (no false Verified), got: {result:?}"
        );
    }
}
