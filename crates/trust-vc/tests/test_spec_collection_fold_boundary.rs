// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Boundary-condition regression tests for `Seq::fold_left` and
//! `Seq::fold_right`: empty sequences must return the initial accumulator.

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
fn test_seq_fold_left_empty_sequence_returns_init() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[]);

    ctx.push_assert(
        "fold_left_empty",
        "s.fold_left(42, SpecFn::new(|acc: i32, x: i32| acc + x)) == 42",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::fold_left on empty sequence must return init value, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_fold_right_empty_sequence_returns_init() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[]);

    ctx.push_assert(
        "fold_right_empty",
        "s.fold_right(99, SpecFn::new(|x: i32, acc: i32| x - acc)) == 99",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::fold_right on empty sequence must return init value, got: {:?}",
        result,
    );
}
