// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerificationPipeline-backed regression tests for `Seq::flat_map`.
//!
//! This slice intentionally exercises the supported binder-dependent body
//! shapes for #2466: `Seq::empty()`, `push`, and `add`/`concat`.

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
fn test_seq_flat_map_positive_singleton_segments_preserve_length() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[5, 7]);

    ctx.push_assert(
        "flat_mapped_len",
        "s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x + 1))).len() == 2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::flat_map singleton-segment length should verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_flat_map_positive_singleton_segments_verify_tail_element() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[5, 7]);

    ctx.push_assert(
        "flat_mapped_tail",
        "s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x + 1))).index(1) == 8",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::flat_map singleton-segment tail should verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_flat_map_positive_two_element_segments_verify() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[5]);

    ctx.push_assert(
        "flat_mapped_len",
        "s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x).push(x + 1))).len() == 2",
    );
    ctx.push_assert(
        "flat_mapped_second",
        "s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x).push(x + 1))).index(1) == 6",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::flat_map two-element-segment case should verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_flat_map_negative_rejects_false_length_claim() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[5]);

    ctx.push_assert(
        "flat_mapped_wrong",
        "s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x + 1))).len() == 2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Seq::flat_map false length claim must not verify, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_flat_map_fail_closed_for_unsupported_binder_dependent_body() {
    let mut ctx = VerificationContext::new();
    assume_seq_i32(&mut ctx, "s", &[5]);

    ctx.push_assert(
        "unsupported_body",
        "s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x).take(x as usize))).len() == 1",
    );

    let result = common::verify_context_with_pipeline(ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Seq::flat_map currently supports binder-dependent bodies"),
                "unsupported-body error should explain the fail-closed subset, got: {message}",
            );
        }
        other => panic!(
            "Seq::flat_map unsupported binder-dependent body should fail closed with Error, got {:?}",
            other
        ),
    }
}
