//! #1979 regressions: ground instantiation soundness for chained sequence ops.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[cfg(feature = "native-seq")]
fn any_overflow_check_falsifiable_under(
    solver: &mut Solver,
    checks: &[(std::borrow::Cow<'static, str>, Term)],
    constraint: Term,
) -> bool {
    solver.try_push().unwrap();
    solver.try_assert_term(constraint).unwrap();
    let mut found = false;
    for (_name, pred) in checks {
        solver.try_push().unwrap();
        let neg = solver.try_not(*pred).unwrap();
        solver.try_assert_term(neg).unwrap();
        let sat = solver.try_check_sat().unwrap();
        solver.try_pop().unwrap();
        if sat.is_sat() {
            found = true;
            break;
        }
    }
    solver.try_pop().unwrap();
    found
}

#[cfg(feature = "native-seq")]
fn declare_native_seq_i32(env: &mut QuantifierTestEnv) -> TrustVcType {
    let seq_ty = TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }));
    let seq_term = env.solver.declare_const("s", Sort::seq(Sort::bitvec(32)));
    env.variables.insert("s".to_string(), seq_term);
    env.var_types.insert("s".to_string(), seq_ty.clone());
    seq_ty
}

#[cfg(feature = "native-seq")]
fn native_seq_var(seq_ty: &TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "s".to_string(),
        ty: seq_ty.clone(),
    }
}

// ========================================================================
// #1979: Ground instantiation axioms for last() are sound
// ========================================================================
//
// W3's facd9ee3 added assert_last_ground_insts() which asserts:
//   len == k+1 => result == select(arr, k_bv64)  for k in 0..8
//
// This is a ground-truth consequence of last()'s definition:
//   result = select(arr, zext(bvsub(len, 1)))
// When len == k+1, bvsub(len, 1) == k, zext(k_bv32) == k_bv64,
// so result == select(arr, k_bv64).
//
// These tests verify soundness by constructing a Seq with known elements,
// calling last(), and checking the solver can prove the result equals the
// expected element.

/// SOUNDNESS: last() on a 3-element Seq must return element at index 2.
/// Exercises the ground instantiation axiom at k=2: len==3 => result==select(arr,2).
/// Without ground instantiation, ay may not close this chain due to BV-EUF gap.
#[test]
fn test_1979_last_ground_inst_soundness_len3() {
    use ay_dpll::api::ArraySort;

    let mut solver = Solver::try_new(Logic::All).unwrap();

    // Create a Seq: Array<BV_ptr, BV32> with known elements at indices 0, 1, 2.
    let pw = crate::ir::pointer_width();
    let arr_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let arr = solver.declare_const("seq", arr_sort);

    // Store known elements: arr[0]=10, arr[1]=20, arr[2]=30.
    let idx0 = solver.try_bv_const(0, pw).unwrap();
    let idx1 = solver.try_bv_const(1, pw).unwrap();
    let idx2 = solver.try_bv_const(2, pw).unwrap();
    let val10 = solver.try_bv_const(10, 32).unwrap();
    let val20 = solver.try_bv_const(20, 32).unwrap();
    let val30 = solver.try_bv_const(30, 32).unwrap();

    let arr1 = solver.try_store(arr, idx0, val10).unwrap();
    let arr2 = solver.try_store(arr1, idx1, val20).unwrap();
    let arr3 = solver.try_store(arr2, idx2, val30).unwrap();

    // Length = 3 (pointer_width, unsigned). Matches encoder encoding (#1745).
    let len = solver.try_bv_const(3, pw).unwrap();

    // Compute last() the same way the encoder does:
    // last_idx = bvsub(len, 1) = 2 (already pointer_width)
    let one = solver.try_bv_const(1, pw).unwrap();
    let last_idx = solver.try_bvsub(len, one).unwrap();
    let result = solver.try_select(arr3, last_idx).unwrap();

    // Now add ground instantiation axioms (same as assert_last_ground_insts)
    for k in 0i64..8 {
        let len_val = solver.try_bv_const(k + 1, pw).unwrap();
        let len_eq = solver.try_eq(len, len_val).unwrap();
        let kidx64 = solver.try_bv_const(k, pw).unwrap();
        let sel = solver.try_select(arr3, kidx64).unwrap();
        let eq = solver.try_eq(result, sel).unwrap();
        let inst = solver.try_implies(len_eq, eq).unwrap();
        solver.try_assert_term(inst).unwrap();
    }

    // Assert that elements are stored correctly
    let sel0 = solver.try_select(arr3, idx0).unwrap();
    let sel1 = solver.try_select(arr3, idx1).unwrap();
    let sel2 = solver.try_select(arr3, idx2).unwrap();
    let eq0 = solver.try_eq(sel0, val10).unwrap();
    solver.try_assert_term(eq0).unwrap();
    let eq1 = solver.try_eq(sel1, val20).unwrap();
    solver.try_assert_term(eq1).unwrap();
    let eq2 = solver.try_eq(sel2, val30).unwrap();
    solver.try_assert_term(eq2).unwrap();

    // Prove: result == 30 (the last element)
    // If the ground instantiation is sound, then with len==3, the axiom
    // len==3 => result==select(arr,2) fires, and select(arr3,2)==30.
    let expected = solver.try_bv_const(30, 32).unwrap();
    let claim = solver.try_eq(result, expected).unwrap();
    solver.try_push().unwrap();
    let neg_claim = solver.try_not(claim).unwrap();
    solver.try_assert_term(neg_claim).unwrap();
    let sat = solver.try_check_sat().unwrap();
    solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#1979 soundness: last() of [10, 20, 30] should be 30, solver says: {:?}",
        sat
    );
}

/// SOUNDNESS BOUNDARY: Ground instantiation must not introduce false equalities.
/// For len=3, the axiom len==2 => result==select(arr,1) should NOT force
/// result==select(arr,1) because len!=2.
#[test]
fn test_1979_last_ground_inst_non_matching_len_does_not_force() {
    use ay_dpll::api::ArraySort;

    let mut solver = Solver::try_new(Logic::All).unwrap();

    let pw = crate::ir::pointer_width();
    let arr_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let arr = solver.declare_const("seq", arr_sort);

    let idx0 = solver.try_bv_const(0, pw).unwrap();
    let idx1 = solver.try_bv_const(1, pw).unwrap();
    let idx2 = solver.try_bv_const(2, pw).unwrap();
    let val10 = solver.try_bv_const(10, 32).unwrap();
    let val20 = solver.try_bv_const(20, 32).unwrap();
    let val30 = solver.try_bv_const(30, 32).unwrap();

    let arr1 = solver.try_store(arr, idx0, val10).unwrap();
    let arr2 = solver.try_store(arr1, idx1, val20).unwrap();
    let arr3 = solver.try_store(arr2, idx2, val30).unwrap();

    // Length = 3 (pointer_width, unsigned). Matches encoder encoding (#1745).
    let len = solver.try_bv_const(3, pw).unwrap();

    let one = solver.try_bv_const(1, pw).unwrap();
    let last_idx = solver.try_bvsub(len, one).unwrap();
    let result = solver.try_select(arr3, last_idx).unwrap();

    // Add ground instantiations
    for k in 0i64..8 {
        let len_val = solver.try_bv_const(k + 1, pw).unwrap();
        let len_eq = solver.try_eq(len, len_val).unwrap();
        let kidx64 = solver.try_bv_const(k, pw).unwrap();
        let sel = solver.try_select(arr3, kidx64).unwrap();
        let eq = solver.try_eq(result, sel).unwrap();
        let inst = solver.try_implies(len_eq, eq).unwrap();
        solver.try_assert_term(inst).unwrap();
    }

    let sel0 = solver.try_select(arr3, idx0).unwrap();
    let sel1 = solver.try_select(arr3, idx1).unwrap();
    let sel2 = solver.try_select(arr3, idx2).unwrap();
    let eq0 = solver.try_eq(sel0, val10).unwrap();
    solver.try_assert_term(eq0).unwrap();
    let eq1 = solver.try_eq(sel1, val20).unwrap();
    solver.try_assert_term(eq1).unwrap();
    let eq2 = solver.try_eq(sel2, val30).unwrap();
    solver.try_assert_term(eq2).unwrap();

    // Verify that result != 20 (the k=1 element) is satisfiable.
    // The axiom len==2 => result==select(arr,1) is vacuously true since len==3,
    // so it should NOT force result==20.  result is arr3[2] = 30.
    let val20b = solver.try_bv_const(20, 32).unwrap();
    let result_is_20 = solver.try_eq(result, val20b).unwrap();
    solver.try_push().unwrap();
    let neg = solver.try_not(result_is_20).unwrap();
    solver.try_assert_term(neg).unwrap();
    let sat = solver.try_check_sat().unwrap();
    solver.try_pop().unwrap();
    // result == 30 (from arr3[last_idx=2]), so result != 20 is satisfiable.
    // Sat proves the axiom len==2 => result==arr3[1] did NOT force result==20.
    assert!(
        sat.is_sat(),
        "#1979 boundary: result should not be forced to 20 when len=3, solver says: {:?}",
        sat
    );
}

// ========================================================================
// #2695: native-seq negative slice indices must stay guarded and avoid
// caching impossible arithmetic lengths in direct IR.
// ========================================================================

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_take_negative_index_emits_guard_and_rejects_impossible_len() {
    let mut env = QuantifierTestEnv::new();
    let seq_ty = declare_native_seq_i32(&mut env);

    let take_expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Take,
        receiver: Box::new(native_seq_var(&seq_ty)),
        receiver_name: Some("s".to_string()),
        args: vec![TrustVcExpr::IntLit {
            value: -1,
            ty: TrustVcType::MathInt,
        }],
        ty: seq_ty.clone(),
    };
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::CollectionOp {
            op: crate::ir::CollectionOp::Len,
            receiver: Box::new(take_expr),
            receiver_name: None,
            args: vec![],
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: -1,
            ty: TrustVcType::MathInt,
        }),
    };

    let (encoded, overflow_checks) = {
        let mut parser = env.parser_with_overflow();
        let encoded = parser
            .encode_trust_vc_expr(&expr)
            .expect("native-seq negative take should encode for soundness audit");
        (encoded, parser.take_overflow_checks())
    };

    let always = env.solver.bool_const(true);
    assert!(
        any_overflow_check_falsifiable_under(&mut env.solver, &overflow_checks, always),
        "#2695: negative take must emit a falsifiable overflow guard"
    );

    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(encoded).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        !sat.is_unsat(),
        "#2695: negative take len must not collapse to -1; solver returned {sat:?}"
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_skip_negative_index_emits_guard_and_rejects_impossible_len() {
    let mut env = QuantifierTestEnv::new();
    let seq_ty = declare_native_seq_i32(&mut env);

    let skip_expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Skip,
        receiver: Box::new(native_seq_var(&seq_ty)),
        receiver_name: Some("s".to_string()),
        args: vec![TrustVcExpr::IntLit {
            value: -1,
            ty: TrustVcType::MathInt,
        }],
        ty: seq_ty.clone(),
    };
    let seq_len = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Len,
        receiver: Box::new(native_seq_var(&seq_ty)),
        receiver_name: Some("s".to_string()),
        args: vec![],
        ty: TrustVcType::MathInt,
    };
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::CollectionOp {
            op: crate::ir::CollectionOp::Len,
            receiver: Box::new(skip_expr),
            receiver_name: None,
            args: vec![],
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(seq_len),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::MathInt,
            }),
            ty: TrustVcType::MathInt,
        }),
    };

    let (encoded, overflow_checks) = {
        let mut parser = env.parser_with_overflow();
        let encoded = parser
            .encode_trust_vc_expr(&expr)
            .expect("native-seq negative skip should encode for soundness audit");
        (encoded, parser.take_overflow_checks())
    };

    let always = env.solver.bool_const(true);
    assert!(
        any_overflow_check_falsifiable_under(&mut env.solver, &overflow_checks, always),
        "#2695: negative skip must emit a falsifiable overflow guard"
    );

    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(encoded).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        !sat.is_unsat(),
        "#2695: negative skip len must not collapse to len + 1; solver returned {sat:?}"
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_subrange_negative_start_emits_guard_and_rejects_impossible_len() {
    let mut env = QuantifierTestEnv::new();
    let seq_ty = declare_native_seq_i32(&mut env);

    let subrange_expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Subrange,
        receiver: Box::new(native_seq_var(&seq_ty)),
        receiver_name: Some("s".to_string()),
        args: vec![
            TrustVcExpr::IntLit {
                value: -1,
                ty: TrustVcType::MathInt,
            },
            TrustVcExpr::IntLit {
                value: 2,
                ty: TrustVcType::MathInt,
            },
        ],
        ty: seq_ty.clone(),
    };
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::CollectionOp {
            op: crate::ir::CollectionOp::Len,
            receiver: Box::new(subrange_expr),
            receiver_name: None,
            args: vec![],
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 3,
            ty: TrustVcType::MathInt,
        }),
    };

    let (encoded, overflow_checks) = {
        let mut parser = env.parser_with_overflow();
        let encoded = parser
            .encode_trust_vc_expr(&expr)
            .expect("native-seq negative subrange should encode for soundness audit");
        (encoded, parser.take_overflow_checks())
    };

    let always = env.solver.bool_const(true);
    assert!(
        any_overflow_check_falsifiable_under(&mut env.solver, &overflow_checks, always),
        "#2695: negative subrange must emit a falsifiable overflow guard"
    );

    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(encoded).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        !sat.is_unsat(),
        "#2695: negative subrange len must not collapse to 3; solver returned {sat:?}"
    );
}

// ========================================================================
