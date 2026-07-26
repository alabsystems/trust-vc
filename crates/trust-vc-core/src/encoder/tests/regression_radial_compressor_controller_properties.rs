// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_radial_compressor_pressure_ratio_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_ratio_x100", i32_ty());
    // Pressure ratio x100: 1.0-10.0 maps to 100..1000
    ctx.push_obligation(ProofObligation::assume(
        "pr_range_a",
        "pressure_ratio_x100 >= 100 && pressure_ratio_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pr_range_c",
        "pressure_ratio_x100 >= 100 && pressure_ratio_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure ratio x100 in [100, 1000] (1.0-10.0)");
}

#[test]
fn test_radial_compressor_impeller_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_speed", i32_ty());
    // Impeller speed in RPM: valid range 5000 to 120000
    ctx.push_obligation(ProofObligation::assume(
        "is_range_a",
        "impeller_speed >= 5000 && impeller_speed <= 120000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_range_c",
        "impeller_speed >= 5000 && impeller_speed <= 120000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller speed in [5000, 120000] RPM");
}

#[test]
fn test_radial_compressor_inlet_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset100", i32_ty());
    // Inlet temperature offset +100 deg C: valid range 50 to 400
    ctx.push_obligation(ProofObligation::assume(
        "it_range_a",
        "inlet_temp_offset100 >= 50 && inlet_temp_offset100 <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "it_range_c",
        "inlet_temp_offset100 >= 50 && inlet_temp_offset100 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet temp offset+100 in [50, 400] deg C");
}

#[test]
fn test_radial_compressor_flow_coefficient_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_coeff_x10000", i32_ty());
    // Flow coefficient x10000: valid range 100 to 5000
    ctx.push_obligation(ProofObligation::assume(
        "fc_range_a",
        "flow_coeff_x10000 >= 100 && flow_coeff_x10000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fc_range_c",
        "flow_coeff_x10000 >= 100 && flow_coeff_x10000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow coefficient x10000 in [100, 5000]");
}

#[test]
fn test_radial_compressor_tip_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_speed", i32_ty());
    // Tip speed in m/s: valid range 100 to 700
    ctx.push_obligation(ProofObligation::assume(
        "ts_range_a",
        "tip_speed >= 100 && tip_speed <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ts_range_c",
        "tip_speed >= 100 && tip_speed <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tip speed in [100, 700] m/s");
}

#[test]
fn test_radial_compressor_surge_margin_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("surge_margin_x100", i32_ty());
    // Surge margin x100 %: 5.0-30.0% maps to 500..3000
    ctx.push_obligation(ProofObligation::assume(
        "sm_range_a",
        "surge_margin_x100 >= 500 && surge_margin_x100 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_range_c",
        "surge_margin_x100 >= 500 && surge_margin_x100 <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "surge margin x100 in [500, 3000] (5.0-30.0%)");
}

#[test]
fn test_radial_compressor_impeller_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    // Impeller material: 1=aluminum, 2=titanium, 3=steel
    ctx.push_obligation(ProofObligation::assume(
        "mat_valid_a",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_valid_c",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller material 3-way (aluminum/titanium/steel)");
}

#[test]
fn test_radial_compressor_diffuser_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diffuser", i32_ty());
    // Diffuser configuration: 1=vaneless, 2=vaned, 3=pipe
    ctx.push_obligation(ProofObligation::assume(
        "diff_valid_a",
        "diffuser == 1 || diffuser == 2 || diffuser == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diff_valid_c",
        "diffuser >= 1 && diffuser <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "diffuser config 3-way (vaneless/vaned/pipe)");
}

#[test]
fn test_radial_compressor_bearing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing", i32_ty());
    // Bearing type: 1=journal, 2=magnetic, 3=air-foil
    ctx.push_obligation(ProofObligation::assume(
        "brg_valid_a",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "brg_valid_c",
        "bearing >= 1 && bearing <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bearing type 3-way (journal/magnetic/air-foil)");
}

#[test]
fn test_radial_compressor_auto_surge_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    // Auto surge protection flag: 0=disabled, 1=enabled
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid_a",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid_c",
        "flag >= 0 && flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto surge protection flag is boolean (0 or 1)");
}
