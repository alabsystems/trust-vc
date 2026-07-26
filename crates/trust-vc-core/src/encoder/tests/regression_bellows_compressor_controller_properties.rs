// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_bellows_stroke_length_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sl_a",
        "stroke_x100 >= 100 && stroke_x100 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sl_c",
        "stroke_x100 >= 100 && stroke_x100 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stroke length x100 in [100, 20000] representing 1.00-200.00 mm",
    );
}

#[test]
fn test_bellows_operating_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "of_a",
        "freq_x10 >= 1 && freq_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "of_c",
        "freq_x10 >= 1 && freq_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating frequency x10 in [1, 1000] representing 0.1-100.0 Hz",
    );
}

#[test]
fn test_bellows_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "disc_x10 >= 1 && disc_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "disc_x10 >= 1 && disc_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 in [1, 5000] representing 0.1-500.0 bar",
    );
}

#[test]
fn test_bellows_convolution_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("convolutions", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "convolutions >= 2 && convolutions <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "convolutions >= 2 && convolutions <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "convolution count in [2, 100]");
}

#[test]
fn test_bellows_wall_thickness_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wall_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wt_a",
        "wall_x1000 >= 50 && wall_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wt_c",
        "wall_x1000 >= 50 && wall_x1000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wall thickness x1000 in [50, 5000] representing 0.050-5.000 mm",
    );
}

#[test]
fn test_bellows_effective_area_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ea_a",
        "area_x100 >= 10 && area_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ea_c",
        "area_x100 >= 10 && area_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "effective area x100 in [10, 100000] representing 0.10-1000.00 cm2",
    );
}

#[test]
fn test_bellows_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_a",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("mat_c", "mat >= 1 && mat <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bellows material 3-way (stainless-steel/inconel/hastelloy)",
    );
}

#[test]
fn test_bellows_forming_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("forming", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fm_a",
        "forming == 1 || forming == 2 || forming == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fm_c",
        "forming >= 1 && forming <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forming method 3-way (hydroformed/welded/electroformed)",
    );
}

#[test]
fn test_bellows_drive_mechanism_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dm_a",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("dm_c", "drive >= 1 && drive <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive mechanism 3-way (mechanical-crank/hydraulic/piezoelectric)",
    );
}

#[test]
fn test_bellows_leak_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leak detection flag is boolean (0 or 1)");
}
