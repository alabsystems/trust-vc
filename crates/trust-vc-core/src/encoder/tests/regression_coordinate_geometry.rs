// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn manhattan_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["x1", "y1", "x2", "y2", "dx", "dy", "dist"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x1_val", "x1 == 1"));
    ctx.push_obligation(ProofObligation::assume("y1_val", "y1 == 2"));
    ctx.push_obligation(ProofObligation::assume("x2_val", "x2 == 4"));
    ctx.push_obligation(ProofObligation::assume("y2_val", "y2 == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "dx_def",
        "dx == if x2 >= x1 { x2 - x1 } else { x1 - x2 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "dy_def",
        "dy == if y2 >= y1 { y2 - y1 } else { y1 - y2 }",
    ));
    ctx.push_obligation(ProofObligation::assume("dist_def", "dist == dx + dy"));
    ctx.push_obligation(ProofObligation::assert("is_7", "dist == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Manhattan distance (1,2)→(4,6) = 7");
}

#[test]
fn chebyshev_distance() {
    // max(|dx|, |dy|)
    let mut ctx = VerificationContext::new();
    for v in &["x1", "y1", "x2", "y2", "dx", "dy", "dist"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x1_val", "x1 == 1"));
    ctx.push_obligation(ProofObligation::assume("y1_val", "y1 == 2"));
    ctx.push_obligation(ProofObligation::assume("x2_val", "x2 == 4"));
    ctx.push_obligation(ProofObligation::assume("y2_val", "y2 == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "dx_def",
        "dx == if x2 >= x1 { x2 - x1 } else { x1 - x2 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "dy_def",
        "dy == if y2 >= y1 { y2 - y1 } else { y1 - y2 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "dist_def",
        "dist == if dx >= dy { dx } else { dy }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "dist == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chebyshev distance (1,2)→(4,6) = 4");
}

#[test]
fn midpoint_2d() {
    let mut ctx = VerificationContext::new();
    for v in &["x1", "y1", "x2", "y2", "mx", "my"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x1_val", "x1 == 2"));
    ctx.push_obligation(ProofObligation::assume("y1_val", "y1 == 4"));
    ctx.push_obligation(ProofObligation::assume("x2_val", "x2 == 8"));
    ctx.push_obligation(ProofObligation::assume("y2_val", "y2 == 10"));
    ctx.push_obligation(ProofObligation::assume("mx_def", "mx == (x1 + x2) / 2"));
    ctx.push_obligation(ProofObligation::assume("my_def", "my == (y1 + y2) / 2"));
    ctx.push_obligation(ProofObligation::assert("mx_is_5", "mx == 5"));
    ctx.push_obligation(ProofObligation::assert("my_is_7", "my == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "midpoint of (2,4)-(8,10) = (5,7)");
}

#[test]
fn bounding_box_from_two_points() {
    let mut ctx = VerificationContext::new();
    for v in &["x1", "y1", "x2", "y2", "min_x", "min_y", "max_x", "max_y"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x1_val", "x1 == 5"));
    ctx.push_obligation(ProofObligation::assume("y1_val", "y1 == 3"));
    ctx.push_obligation(ProofObligation::assume("x2_val", "x2 == 2"));
    ctx.push_obligation(ProofObligation::assume("y2_val", "y2 == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "minx",
        "min_x == if x1 <= x2 { x1 } else { x2 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "miny",
        "min_y == if y1 <= y2 { y1 } else { y2 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "maxx",
        "max_x == if x1 >= x2 { x1 } else { x2 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "maxy",
        "max_y == if y1 >= y2 { y1 } else { y2 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bb",
        "min_x == 2 && min_y == 3 && max_x == 5 && max_y == 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounding box of (5,3),(2,7) = (2,3)-(5,7)");
}

#[test]
fn point_in_rectangle() {
    let mut ctx = VerificationContext::new();
    for v in &["px", "py", "rx", "ry", "rw", "rh"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("inside", i32_ty());
    ctx.push_obligation(ProofObligation::assume("px_val", "px == 5"));
    ctx.push_obligation(ProofObligation::assume("py_val", "py == 5"));
    ctx.push_obligation(ProofObligation::assume("rx_val", "rx == 2"));
    ctx.push_obligation(ProofObligation::assume("ry_val", "ry == 2"));
    ctx.push_obligation(ProofObligation::assume("rw_val", "rw == 6"));
    ctx.push_obligation(ProofObligation::assume("rh_val", "rh == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "inside_def",
        "inside == if px >= rx && px < rx + rw && py >= ry && py < ry + rh { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_inside", "inside == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(5,5) inside rect (2,2)-(8,8)");
}

#[test]
fn rectangle_area() {
    let mut ctx = VerificationContext::new();
    for v in &["width", "height", "area"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("w", "width == 5"));
    ctx.push_obligation(ProofObligation::assume("h", "height == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "area_def",
        "area == width * height",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "area == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 * 3 = 15");
}

#[test]
fn rectangle_perimeter() {
    let mut ctx = VerificationContext::new();
    for v in &["width", "height", "perimeter"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("w", "width == 5"));
    ctx.push_obligation(ProofObligation::assume("h", "height == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "perim_def",
        "perimeter == width + width + height + height",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "perimeter == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "perimeter of 5x3 = 16");
}

#[test]
fn translation_2d() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "y", "dx", "dy", "nx", "ny"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 4"));
    ctx.push_obligation(ProofObligation::assume("dx_val", "dx == 2"));
    ctx.push_obligation(ProofObligation::assume("dy_val", "dy == 0 - 1"));
    ctx.push_obligation(ProofObligation::assume("nx_def", "nx == x + dx"));
    ctx.push_obligation(ProofObligation::assume("ny_def", "ny == y + dy"));
    ctx.push_obligation(ProofObligation::assert("nx_is_5", "nx == 5"));
    ctx.push_obligation(ProofObligation::assert("ny_is_3", "ny == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "translate (3,4) by (2,-1) = (5,3)");
}

#[test]
fn grid_cell_from_coordinate() {
    // Map continuous coordinate to grid cell
    let mut ctx = VerificationContext::new();
    for v in &["x", "cell_size", "cell"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    ctx.push_obligation(ProofObligation::assume("cs", "cell_size == 5"));
    ctx.push_obligation(ProofObligation::assume("cell_def", "cell == x / cell_size"));
    ctx.push_obligation(ProofObligation::assert("is_3", "cell == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "coordinate 17, cell_size 5 → cell 3");
}

#[test]
fn origin_distance_zero() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "y", "dist"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "dist_def",
        "dist == if x >= 0 { x } else { 0 - x } + if y >= 0 { y } else { 0 - y }",
    ));
    ctx.push_obligation(ProofObligation::assert("zero_dist", "dist == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Manhattan distance from origin to origin = 0");
}
