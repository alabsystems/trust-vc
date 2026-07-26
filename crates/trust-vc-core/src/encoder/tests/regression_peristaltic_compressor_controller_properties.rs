// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_peristaltic_roller_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("roller_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rs_a",
        "roller_x10 >= 1 && roller_x10 <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rs_c",
        "roller_x10 >= 1 && roller_x10 <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "roller speed x10 in [1, 6000] representing 0.1-600.0 RPM",
    );
}

#[test]
fn test_peristaltic_tube_bore_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bore_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tb_a",
        "bore_x100 >= 10 && bore_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tb_c",
        "bore_x100 >= 10 && bore_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tube bore x100 in [10, 5000] representing 0.10-50.00 mm",
    );
}

#[test]
fn test_peristaltic_occlusion_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("occ_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oc_a",
        "occ_x100 >= 5000 && occ_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oc_c",
        "occ_x100 >= 5000 && occ_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "occlusion x100 in [5000, 10000] representing 50.00-100.00%",
    );
}

#[test]
fn test_peristaltic_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "disc_x10 >= 1 && disc_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "disc_x10 >= 1 && disc_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 in [1, 300] representing 0.1-30.0 bar",
    );
}

#[test]
fn test_peristaltic_roller_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rollers", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rc_a",
        "rollers >= 2 && rollers <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rc_c",
        "rollers >= 2 && rollers <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roller count in [2, 12]");
}

#[test]
fn test_peristaltic_tube_wall_thickness_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wall_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wt_a",
        "wall_x100 >= 50 && wall_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wt_c",
        "wall_x100 >= 50 && wall_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wall thickness x100 in [50, 500] representing 0.50-5.00 mm",
    );
}

#[test]
fn test_peristaltic_tube_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tm_a",
        "tube_mat == 1 || tube_mat == 2 || tube_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tm_c",
        "tube_mat >= 1 && tube_mat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube material 3-way (silicone/norprene/pharmed)");
}

#[test]
fn test_peristaltic_rotor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_a",
        "rotor == 1 || rotor == 2 || rotor == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("rt_c", "rotor >= 1 && rotor <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotor type 3-way (standard/high-pressure/micro-flow)",
    );
}

#[test]
fn test_peristaltic_flow_direction_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_dir", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fd_a",
        "flow_dir == 1 || flow_dir == 2 || flow_dir == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fd_c",
        "flow_dir >= 1 && flow_dir <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow direction 3-way (forward/reverse/alternating)",
    );
}

#[test]
fn test_peristaltic_pulsation_dampener_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulsation dampener flag is boolean (0 or 1)");
}
