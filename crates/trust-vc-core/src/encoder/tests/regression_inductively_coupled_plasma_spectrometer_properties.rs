// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn wavelength_min_bounded() {
    // ICP-OES minimum wavelength range: 130-200 nm (vacuum UV)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_min_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wavelength_min_nm == 165"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wavelength_min_nm >= 130 && wavelength_min_nm <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP wavelength min: 165nm in [130, 200]");
}

#[test]
fn wavelength_max_bounded() {
    // ICP-OES maximum wavelength range: 700-900 nm (near-IR)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_max_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wavelength_max_nm == 770"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wavelength_max_nm >= 700 && wavelength_max_nm <= 900 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP wavelength max: 770nm in [700, 900]");
}

#[test]
fn rf_power_bounded() {
    // RF generator power range: 700-1700 W
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rf_power_w", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rf", "rf_power_w == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if rf_power_w >= 700 && rf_power_w <= 1700 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP RF power: 1200W in [700, 1700]");
}

#[test]
fn detection_limit_scaled() {
    // Detection limit scaled x1000: 0.001 ppb = 1 in x1000 units
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detection_limit_x1000_ppb", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dl",
        "detection_limit_x1000_ppb == 1",
    )); // 0.001 ppb
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if detection_limit_x1000_ppb <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ICP detection limit: 0.001 ppb (1 x1000) <= 0.010 ppb",
    );
}

#[test]
fn plasma_gas_flow_scaled() {
    // Plasma gas flow scaled x10: 15.0 L/min = 150 in x10 units
    // Typical range: 8.0-20.0 L/min = 80-200 in x10 units
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_flow_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("gf", "gas_flow_x10 == 150")); // 15.0 L/min
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if gas_flow_x10 >= 80 && gas_flow_x10 <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ICP plasma gas: 15.0 L/min (150 x10) in [8.0, 20.0]",
    );
}

#[test]
fn viewing_mode_disjunction() {
    // Viewing mode: 1=axial, 2=radial, 3=dual
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viewing_mode", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vm", "viewing_mode == 3")); // dual view
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if viewing_mode == 1 || viewing_mode == 2 || viewing_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP viewing mode: dual (3) is valid");
}

#[test]
fn nebulizer_type_disjunction() {
    // Nebulizer type: 1=concentric, 2=cross-flow, 3=ultrasonic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nebulizer_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nt", "nebulizer_type == 2")); // cross-flow
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if nebulizer_type == 1 || nebulizer_type == 2 || nebulizer_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP nebulizer: cross-flow (2) is valid");
}

#[test]
fn simultaneous_elements_bounded() {
    // Simultaneous multi-element capability: 1 to 73 elements
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_elements", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ne", "num_elements == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if num_elements >= 1 && num_elements <= 73 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP simultaneous elements: 40 in [1, 73]");
}

#[test]
fn resolution_scaled() {
    // Spectral resolution scaled x1000: 0.007 nm = 7 in x1000 units
    // Typical range: 0.001-0.020 nm = 1-20 in x1000 units
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x1000_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res", "resolution_x1000_nm == 7")); // 0.007 nm
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if resolution_x1000_nm >= 1 && resolution_x1000_nm <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ICP resolution: 0.007nm (7 x1000) in [0.001, 0.020]",
    );
}

#[test]
fn autosampler_flag() {
    // Autosampler present: boolean flag (i32, 1=yes, 0=no)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_autosampler", i32_ty());
    ctx.declare_var_typed("enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ha", "has_autosampler == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "enabled == if has_autosampler == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP autosampler: present (flag=1)");
}
