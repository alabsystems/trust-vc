// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_eddy_current_conductivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ec_a",
        "cond_x100 >= 50 && cond_x100 <= 11600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ec_c",
        "cond_x100 >= 50 && cond_x100 <= 11600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "conductivity x100 in [50, 11600] representing 0.50-116.00 %IACS",
    );
}

#[test]
fn test_eddy_current_probe_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pf_a",
        "freq_khz >= 10 && freq_khz <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pf_c",
        "freq_khz >= 10 && freq_khz <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe frequency in [10, 10000] kHz");
}

#[test]
fn test_eddy_current_lift_off_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liftoff_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lo_a",
        "liftoff_x1000 >= 0 && liftoff_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lo_c",
        "liftoff_x1000 >= 0 && liftoff_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lift-off x1000 in [0, 10000] representing 0.000-10.000 mm",
    );
}

#[test]
fn test_eddy_current_penetration_depth_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pd_a",
        "depth_x100 >= 1 && depth_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pd_c",
        "depth_x100 >= 1 && depth_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "penetration depth x100 in [1, 50000] representing 0.01-500.00 mm",
    );
}

#[test]
fn test_eddy_current_specimen_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spec_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "spec_temp >= 80 && spec_temp <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "spec_temp >= 80 && spec_temp <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "specimen temp offset+100 in [80, 200] representing -20 to 100 C",
    );
}

#[test]
fn test_eddy_current_coil_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coil_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cd_a",
        "coil_x10 >= 10 && coil_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cd_c",
        "coil_x10 >= 10 && coil_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "coil diameter x10 in [10, 5000] representing 1.0-500.0 mm",
    );
}

#[test]
fn test_eddy_current_probe_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pt_a",
        "probe == 1 || probe == 2 || probe == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("pt_c", "probe >= 1 && probe <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe type 3-way (pencil/surface/encircling)");
}

#[test]
fn test_eddy_current_calibration_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal_std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cs_a",
        "cal_std == 1 || cal_std == 2 || cal_std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cs_c",
        "cal_std >= 1 && cal_std <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "calibration standard 3-way (copper/aluminum/titanium)",
    );
}

#[test]
fn test_eddy_current_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mm_a",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mm_c",
        "meas_mode >= 1 && meas_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode 3-way (absolute/differential/bridge)",
    );
}

#[test]
fn test_eddy_current_auto_temp_compensation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto temp compensation flag is boolean (0 or 1)");
}
