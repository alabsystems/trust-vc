// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// view() should return the receiver unchanged (identity operation).
/// Tests multiple concrete indices to verify view() is identity —
/// symbolic `i < s.len()` fails due to BV64/BV32 width mismatch (#2154).
#[test]
fn test_view_returns_receiver_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_bound", "s.len() > 2"));
    ctx.push_obligation(ProofObligation::assert(
        "view_id_0",
        "s.view().index(0) == s.index(0)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "view_id_1",
        "s.view().index(1) == s.index(1)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "view_id_2",
        "s.view().index(2) == s.index(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.view().index(i) should equal s.index(i) for all valid i",
    );
}

#[test]
fn test_view_set_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "view_set",
        "s.view().contains(x) == s.contains(x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.view().contains(x) should equal s.contains(x)");
}

#[test]
fn test_seq_push_increases_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert("new_len", "s.push(42).len() == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.push(42).len() should be 3 when len==2");
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_push_len_matches_source_plus_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "push_len_plus_one",
        "s.push(42).len() == s.len() + 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "native-seq push length should reuse the source len term plus one",
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_push_len_matches_source_plus_bv_variable() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("k_is_one", "k == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "push_len_plus_bv_var",
        "s.push(42).len() == s.len() + k",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "native-seq push length should coerce BV vars before Int arithmetic",
    );
}

#[test]
fn test_seq_push_preserves_existing() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "s.push(42).index(0) == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.push(42) should preserve s[0]==10");
}

#[test]
fn test_seq_update_replaces_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "updated",
        "s.update(0, 99).index(0) == 99",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.update(0, 99).index(0) should be 99");
}

#[test]
fn test_seq_update_preserves_other_elements() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "s.update(1, 99).index(0) == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.update(1, 99) should preserve s[0]==10");
}
