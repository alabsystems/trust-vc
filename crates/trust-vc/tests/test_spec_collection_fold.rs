// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerificationPipeline-backed regression tests for `Seq::fold_left`,
//! `Seq::fold_right`, and `Set::fold`.

mod common;

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

fn assume_seq_i32(ctx: &mut VerificationContext, name: &str, values: &[i32]) {
    ctx.declare_var_parsed(name, "Seq<i32>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", values.len()),
    );
    for (index, value) in values.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {value}"),
        );
    }
}

#[test]
fn test_seq_fold_left_positive_sum_verifies() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[1, 2, 3]);

    ctx.push_assert(
        "fold_left_sum",
        "s.fold_left(0, SpecFn::new(|acc: i32, x: i32| acc + x)) == 6",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::fold_left summation should verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_fold_left_negative_false_sum_claim() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[1, 2, 3]);

    ctx.push_assert(
        "fold_left_wrong",
        "s.fold_left(0, SpecFn::new(|acc: i32, x: i32| acc + x)) == 7",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Seq::fold_left false sum claim must not verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_fold_right_positive_order_sensitive_result_verifies() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[1, 2, 3]);

    ctx.push_assert(
        "fold_right_ordered",
        "s.fold_right(0, SpecFn::new(|x: i32, acc: i32| x - acc)) == 2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::fold_right order-sensitive case should verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_fold_right_negative_false_claim() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[1, 2, 3]);

    ctx.push_assert(
        "fold_right_wrong",
        "s.fold_right(0, SpecFn::new(|x: i32, acc: i32| x - acc)) == -2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Seq::fold_right false claim must not verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_fold_left_fail_closed_for_collection_accumulator() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[1, 2]);

    ctx.push_assert(
        "fold_left_collection_acc",
        "s.fold_left(Seq::<i32>::empty(), SpecFn::new(|acc: Seq<i32>, x: i32| acc.push(x))).len() == 2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains(
                    "Seq::fold_left currently supports non-collection accumulator/result types only"
                ),
                "collection-accumulator error should explain the fail-closed subset, got: {message}",
            );
        }
        other => panic!(
            "Seq::fold_left collection accumulator should fail closed with Error, got {:?}",
            other
        ),
    }
}

// --- Set::fold ---

fn assume_set_i32(ctx: &mut VerificationContext, name: &str, values: &[i32]) {
    ctx.declare_var_parsed(name, "Set<i32>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", values.len()),
    );
    for value in values {
        ctx.push_assume(
            &format!("{name}_has_{}", value.unsigned_abs()),
            &format!("{name}.contains({value})"),
        );
    }
    // Assert distinctness: no two assumed elements are the same
    // (implicit from the set semantics, but elements are already distinct by construction)
}

/// Gated: Set::fold solver timeout >10s. Needs v2 collection theory. (#2658 Category H)
#[test]
#[cfg(feature = "expensive-tests")]
fn test_set_fold_positive_sum_verifies() {
    let mut ctx = VerificationContext::new();
    assume_set_i32(&mut ctx, "s", &[1, 2, 3]);

    // Sum of {1,2,3} = 6 regardless of fold order (addition is commutative)
    ctx.push_assert(
        "set_fold_sum",
        "s.fold(0, SpecFn::new(|acc: i32, x: i32| acc + x)) == 6",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Set::fold summation should verify, got: {:?}",
        result,
    );
}

/// Gated: non-empty Set::fold still explodes on staged/public solver paths.
/// Keep this under expensive-tests until v2 collection theory lands (#2658).
#[test]
#[cfg(feature = "expensive-tests")]
fn test_set_fold_negative_false_sum_claim() {
    let mut ctx = VerificationContext::new();
    assume_set_i32(&mut ctx, "s", &[1, 2, 3]);

    ctx.push_assert(
        "set_fold_wrong",
        "s.fold(0, SpecFn::new(|acc: i32, x: i32| acc + x)) == 7",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Set::fold false sum claim must not verify, got: {:?}",
        result,
    );
}

#[test]
fn test_set_fold_empty_set_returns_init() {
    let mut ctx = VerificationContext::new();
    assume_set_i32(&mut ctx, "s", &[]);

    ctx.push_assert(
        "set_fold_empty",
        "s.fold(42, SpecFn::new(|acc: i32, x: i32| acc + x)) == 42",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Set::fold on empty set must return init value, got: {:?}",
        result,
    );
}

#[test]
fn test_set_fold_fail_closed_for_collection_accumulator() {
    let mut ctx = VerificationContext::new();
    assume_set_i32(&mut ctx, "s", &[1, 2]);

    ctx.push_assert(
        "set_fold_collection_acc",
        "s.fold(Seq::<i32>::empty(), SpecFn::new(|acc: Seq<i32>, x: i32| acc.push(x))).len() == 2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains(
                    "Set::fold currently supports non-collection accumulator/result types only"
                ),
                "collection-accumulator error should explain the fail-closed subset, got: {message}",
            );
        }
        other => panic!(
            "Set::fold collection accumulator should fail closed with Error, got {:?}",
            other
        ),
    }
}
