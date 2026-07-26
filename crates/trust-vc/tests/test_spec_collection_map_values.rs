// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerificationPipeline-backed regression tests for `Seq::map_values`.
//!
//! This is the first higher-order spec collection slice for #2466: the parser,
//! typed IR, and encoder must all agree on `SpecFn::new(|x: T| ...)` flowing
//! into `Seq::map_values`.

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
fn test_seq_map_values_positive_verifies() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[5]);

    ctx.push_assert(
        "mapped_len",
        "s.map_values(SpecFn::new(|x: i32| x + 1)).len() == s.len()",
    );
    ctx.push_assert(
        "mapped_head",
        "s.map_values(SpecFn::new(|x: i32| x + 1)).index(0) == 6",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::map_values positive case should verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_map_values_negative_rejects_false_value_claim() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[5]);

    ctx.push_assert(
        "mapped_head_wrong",
        "s.map_values(SpecFn::new(|x: i32| x + 1)).index(0) == 5",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Seq::map_values false value claim must not verify, got: {:?}",
        result,
    );
}
