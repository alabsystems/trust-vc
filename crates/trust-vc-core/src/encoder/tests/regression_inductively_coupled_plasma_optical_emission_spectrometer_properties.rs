// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_icp_oes_wavelength_range() {
    // ICP-OES wavelength range: 160-900 nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wavelength_nm == 328"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wavelength_nm >= 160 && wavelength_nm <= 900 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES wavelength: 328nm in [160, 900]");
}

#[test]
fn test_icp_oes_resolution_scaled() {
    // Spectral resolution scaled x100: 0.01-10.00 pm → 1-1000 in x100 units
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x100_pm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res", "resolution_x100_pm == 200")); // 2.00 pm
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if resolution_x100_pm >= 1 && resolution_x100_pm <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ICP-OES resolution: 2.00pm (200 x100) in [0.01, 10.00]",
    );
}

#[test]
fn test_icp_oes_detection_limit() {
    // Detection limit: 1-1000 ppb
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detection_limit_ppb", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dl", "detection_limit_ppb == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if detection_limit_ppb >= 1 && detection_limit_ppb <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES detection limit: 5 ppb in [1, 1000]");
}

#[test]
fn test_icp_oes_plasma_power() {
    // Plasma power range: 500-2000 W
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plasma_power_w", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pp", "plasma_power_w == 1350"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if plasma_power_w >= 500 && plasma_power_w <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES plasma power: 1350W in [500, 2000]");
}

#[test]
fn test_icp_oes_sample_uptake_rate_scaled() {
    // Sample uptake rate scaled x10: 0.1-10.0 mL/min → 1-100 in x10 units
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("uptake_rate_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ur", "uptake_rate_x10 == 15")); // 1.5 mL/min
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if uptake_rate_x10 >= 1 && uptake_rate_x10 <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ICP-OES uptake rate: 1.5 mL/min (15 x10) in [0.1, 10.0]",
    );
}

#[test]
fn test_icp_oes_viewing_mode() {
    // Viewing mode: 1=axial, 2=radial, 3=dual-view
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viewing_mode", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vm", "viewing_mode == 1")); // axial
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if viewing_mode == 1 || viewing_mode == 2 || viewing_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES viewing mode: axial (1) is valid");
}

#[test]
fn test_icp_oes_nebulizer_type() {
    // Nebulizer type: 1=concentric, 2=cross-flow, 3=ultrasonic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nebulizer_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nt", "nebulizer_type == 3")); // ultrasonic
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if nebulizer_type == 1 || nebulizer_type == 2 || nebulizer_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES nebulizer: ultrasonic (3) is valid");
}

#[test]
fn test_icp_oes_detector_type() {
    // Detector type: 1=CCD, 2=CID, 3=PMT-array
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "detector_type == 2")); // CID
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if detector_type == 1 || detector_type == 2 || detector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES detector: CID (2) is valid");
}

#[test]
fn test_icp_oes_simultaneous_elements() {
    // Simultaneous elements: 1-73
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_elements", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ne", "num_elements == 55"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if num_elements >= 1 && num_elements <= 73 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES simultaneous elements: 55 in [1, 73]");
}

#[test]
fn test_icp_oes_argon_humidifier_flag() {
    // Argon humidifier present: boolean flag (i32, 1=yes, 0=no)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_humidifier", i32_ty());
    ctx.declare_var_typed("enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hh", "has_humidifier == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "enabled == if has_humidifier == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ICP-OES argon humidifier: present (flag=1)");
}
