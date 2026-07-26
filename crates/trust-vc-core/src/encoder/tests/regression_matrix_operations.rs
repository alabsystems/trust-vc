// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn row_major_index() {
    // 2D index in row-major: index = row * cols + col
    let mut ctx = VerificationContext::new();
    for v in &["row", "col", "cols", "index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("row_val", "row == 2"));
    ctx.push_obligation(ProofObligation::assume("col_val", "col == 3"));
    ctx.push_obligation(ProofObligation::assume("cols_val", "cols == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "index_def",
        "index == row * cols + col",
    ));
    // 2*5 + 3 = 13
    ctx.push_obligation(ProofObligation::assert("is_13", "index == 13"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "row-major index: [2][3] in 5-col = 13");
}

#[test]
fn column_major_index() {
    // 2D index in column-major: index = col * rows + row
    let mut ctx = VerificationContext::new();
    for v in &["row", "col", "rows", "index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("row_val", "row == 2"));
    ctx.push_obligation(ProofObligation::assume("col_val", "col == 3"));
    ctx.push_obligation(ProofObligation::assume("rows_val", "rows == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "index_def",
        "index == col * rows + row",
    ));
    // 3*4 + 2 = 14
    ctx.push_obligation(ProofObligation::assert("is_14", "index == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "column-major index: [2][3] in 4-row = 14");
}

#[test]
fn matrix_total_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["rows", "cols", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rows_val", "rows == 3"));
    ctx.push_obligation(ProofObligation::assume("cols_val", "cols == 4"));
    ctx.push_obligation(ProofObligation::assume("total_def", "total == rows * cols"));
    ctx.push_obligation(ProofObligation::assert("is_12", "total == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3x4 matrix has 12 elements");
}

#[test]
fn transpose_index_swap() {
    // Transpose: (row, col) → (col, row), so new index = col * rows + row
    let mut ctx = VerificationContext::new();
    for v in &[
        "row",
        "col",
        "orig_cols",
        "orig_rows",
        "orig_idx",
        "trans_idx",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("row_val", "row == 1"));
    ctx.push_obligation(ProofObligation::assume("col_val", "col == 2"));
    ctx.push_obligation(ProofObligation::assume("oc", "orig_cols == 4"));
    ctx.push_obligation(ProofObligation::assume("or_val", "orig_rows == 3"));
    // Original: row * orig_cols + col = 1*4 + 2 = 6
    ctx.push_obligation(ProofObligation::assume(
        "orig_def",
        "orig_idx == row * orig_cols + col",
    ));
    // Transposed: col * orig_rows + row = 2*3 + 1 = 7
    ctx.push_obligation(ProofObligation::assume(
        "trans_def",
        "trans_idx == col * orig_rows + row",
    ));
    ctx.push_obligation(ProofObligation::assert("orig_is_6", "orig_idx == 6"));
    ctx.push_obligation(ProofObligation::assert("trans_is_7", "trans_idx == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "transpose swaps indexing");
}

#[test]
fn diagonal_element() {
    // Diagonal element [i][i] in row-major: index = i * cols + i = i * (cols + 1)
    let mut ctx = VerificationContext::new();
    for v in &["i", "cols", "index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 2"));
    ctx.push_obligation(ProofObligation::assume("cols_val", "cols == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "index_def",
        "index == i * cols + i",
    ));
    // 2*4 + 2 = 10
    ctx.push_obligation(ProofObligation::assert("is_10", "index == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "diagonal [2][2] in 4-col = index 10");
}

#[test]
fn trace_of_2x2() {
    // Trace = sum of diagonal elements
    let mut ctx = VerificationContext::new();
    for v in &["a00", "a11", "trace"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a00_val", "a00 == 5"));
    ctx.push_obligation(ProofObligation::assume("a11_val", "a11 == 3"));
    ctx.push_obligation(ProofObligation::assume("trace_def", "trace == a00 + a11"));
    ctx.push_obligation(ProofObligation::assert("is_8", "trace == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trace of [[5,_],[_,3]] = 8");
}

#[test]
fn matrix_add_element() {
    let mut ctx = VerificationContext::new();
    for v in &["a_ij", "b_ij", "c_ij"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_ij == 3"));
    ctx.push_obligation(ProofObligation::assume("b", "b_ij == 7"));
    ctx.push_obligation(ProofObligation::assume("c_def", "c_ij == a_ij + b_ij"));
    ctx.push_obligation(ProofObligation::assert("is_10", "c_ij == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "matrix add: 3 + 7 = 10");
}

#[test]
fn matrix_scalar_multiply() {
    let mut ctx = VerificationContext::new();
    for v in &["a_ij", "scalar", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_ij == 4"));
    ctx.push_obligation(ProofObligation::assume("s", "scalar == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == a_ij * scalar",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "result == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "scalar multiply: 4 * 3 = 12");
}

#[test]
fn dot_product_2d() {
    // [a0, a1] · [b0, b1] = a0*b0 + a1*b1
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "b0", "b1", "prod0", "prod1", "dot"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 2"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 3"));
    ctx.push_obligation(ProofObligation::assume("b0_val", "b0 == 4"));
    ctx.push_obligation(ProofObligation::assume("b1_val", "b1 == 5"));
    ctx.push_obligation(ProofObligation::assume("p0_def", "prod0 == a0 * b0"));
    ctx.push_obligation(ProofObligation::assume("p1_def", "prod1 == a1 * b1"));
    ctx.push_obligation(ProofObligation::assume("dot_def", "dot == prod0 + prod1"));
    // 2*4 + 3*5 = 8 + 15 = 23
    ctx.push_obligation(ProofObligation::assert("is_23", "dot == 23"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "dot product [2,3]·[4,5] = 23");
}

#[test]
fn submatrix_offset() {
    // Submatrix starting at (r0, c0) in a matrix with `cols` columns
    // Element (i, j) in submatrix → global index (r0+i)*cols + (c0+j)
    let mut ctx = VerificationContext::new();
    for v in &["r0", "c0", "i", "j", "cols", "global_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r0_val", "r0 == 1"));
    ctx.push_obligation(ProofObligation::assume("c0_val", "c0 == 2"));
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 1"));
    ctx.push_obligation(ProofObligation::assume("j_val", "j == 1"));
    ctx.push_obligation(ProofObligation::assume("cols_val", "cols == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "global_def",
        "global_idx == (r0 + i) * cols + (c0 + j)",
    ));
    // (1+1)*5 + (2+1) = 10 + 3 = 13
    ctx.push_obligation(ProofObligation::assert("is_13", "global_idx == 13"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "submatrix(1,2)[1][1] in 5-col = global 13");
}
