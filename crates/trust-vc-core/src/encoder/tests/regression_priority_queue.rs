// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn min_of_two() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "min_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "min_def",
        "min_val == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_min", "min_val == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min(5, 3) = 3");
}

#[test]
fn insert_maintains_min() {
    let mut ctx = VerificationContext::new();
    for v in &["old_min", "new_val", "new_min"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("old_min_val", "old_min == 5"));
    ctx.push_obligation(ProofObligation::assume("new_val_val", "new_val == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "new_min_def",
        "new_min == if new_val < old_min { new_val } else { old_min }",
    ));
    ctx.push_obligation(ProofObligation::assert("updated", "new_min == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inserting 3 into queue with min=5 gives new min=3");
}

#[test]
fn insert_larger_preserves_min() {
    let mut ctx = VerificationContext::new();
    for v in &["old_min", "new_val", "new_min"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("old_min_val", "old_min == 3"));
    ctx.push_obligation(ProofObligation::assume("new_val_val", "new_val == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "new_min_def",
        "new_min == if new_val < old_min { new_val } else { old_min }",
    ));
    ctx.push_obligation(ProofObligation::assert("preserved", "new_min == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inserting 7 into queue with min=3 preserves min");
}

#[test]
fn parent_child_heap_order() {
    // In a min-heap: parent <= children
    let mut ctx = VerificationContext::new();
    for v in &["parent", "left", "right"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("parent_val", "parent == 1"));
    ctx.push_obligation(ProofObligation::assume("left_val", "left == 3"));
    ctx.push_obligation(ProofObligation::assume("right_val", "right == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "heap_order",
        "parent <= left && parent <= right",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min-heap: 1 <= 3 and 1 <= 5");
}

#[test]
fn sift_down_swap() {
    let mut ctx = VerificationContext::new();
    for v in &["parent", "child", "new_parent", "new_child"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("parent_val", "parent == 10"));
    ctx.push_obligation(ProofObligation::assume("child_val", "child == 3"));
    // Swap if parent > child (restore heap order)
    ctx.push_obligation(ProofObligation::assume(
        "new_parent_def",
        "new_parent == if parent > child { child } else { parent }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_child_def",
        "new_child == if parent > child { parent } else { child }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "restored",
        "new_parent <= new_child",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sift down: swap 10 and 3 restores order");
}

#[test]
fn extract_min_from_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "extracted"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "extracted_def",
        "extracted == if a < b { if a < c { a } else { c } } else { if b < c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_min", "extracted == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "extract min from {7, 2, 9} = 2");
}

#[test]
fn size_after_insert() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("size_val", "size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "new_size_def",
        "new_size == size + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert increases size from 4 to 5");
}

#[test]
fn size_after_extract() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("size_val", "size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "new_size_def",
        "new_size == size - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("shrunk", "new_size == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "extract decreases size from 4 to 3");
}

#[test]
fn heap_index_parent() {
    let mut ctx = VerificationContext::new();
    for v in &["child_idx", "parent_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("child_val", "child_idx == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "parent_def",
        "parent_idx == (child_idx - 1) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("parent_is_2", "parent_idx == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "parent of index 5 is (5-1)/2 = 2");
}

#[test]
fn two_inserts_min_correct() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "min_after_a", "min_after_both"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 8"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    // After inserting a into empty queue
    ctx.push_obligation(ProofObligation::assume(
        "min_after_a_def",
        "min_after_a == a",
    ));
    // After inserting b
    ctx.push_obligation(ProofObligation::assume(
        "min_after_both_def",
        "min_after_both == if b < min_after_a { b } else { min_after_a }",
    ));
    ctx.push_obligation(ProofObligation::assert("final_min", "min_after_both == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert 8 then 4: min = 4");
}
