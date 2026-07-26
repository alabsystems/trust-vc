// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proc-macro integration tests for inline spec functions through the full
//! verification pipeline.
//!
//! Part of #2488.

mod common;

use trust_vc::{proof, spec};

#[spec]
#[trust_vc::inline]
fn inline_double(x: u64) -> u64 {
    x + x
}

#[spec]
#[trust_vc::inline]
fn inline_quad(x: u64) -> u64 {
    inline_double(inline_double(x))
}

#[spec]
fn plain_double(x: u64) -> u64 {
    x + x
}

#[proof]
fn proof_inline_spec_verifies() {
    let _ = inline_double(0u64);
    trust_vc::assert!(inline_double(3u64) == 6u64);
}

#[test]
fn test_inline_spec_verifies() {
    let _ = common::verify_should_pass(proof_inline_spec_verifies);
}

#[proof]
fn proof_nested_inline_spec_verifies() {
    let _ = inline_quad(0u64);
    trust_vc::assert!(inline_quad(2u64) == 8u64);
}

#[test]
fn test_nested_inline_spec_verifies() {
    let _ = common::verify_should_pass(proof_nested_inline_spec_verifies);
}

#[proof]
fn proof_plain_spec_control_verifies() {
    let _ = plain_double(0u64);
    trust_vc::assert!(plain_double(4u64) == 8u64);
}

#[test]
fn test_plain_spec_control_verifies() {
    let _ = common::verify_should_pass(proof_plain_spec_control_verifies);
}

#[proof]
fn proof_inline_spec_wrong_value_fails() {
    let _ = inline_double(0u64);
    trust_vc::assert!(inline_double(3u64) == 7u64);
}

#[test]
fn test_inline_spec_wrong_value_fails() {
    let _ = common::verify_should_fail(proof_inline_spec_wrong_value_fails);
}
