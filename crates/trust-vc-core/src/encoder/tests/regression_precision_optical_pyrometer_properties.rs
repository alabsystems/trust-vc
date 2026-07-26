// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn temp_range_min_offset() {
    // Minimum measurable temperature: 200°C → offset +500 = 700
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("min_offset", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 700")); // 200°C + 500
    ctx.push_obligation(ProofObligation::assume("mo", "min_offset == 700")); // 200°C + 500
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= min_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: 200°C (offset 700) >= min 200°C");
}

#[test]
fn temp_range_max_offset() {
    // Maximum measurable temperature: 3000°C → offset +500 = 3500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("max_offset", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 2800")); // 2300°C + 500
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset == 3500")); // 3000°C + 500
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pyrometer: 2300°C (offset 2800) <= max 3000°C (offset 3500)",
    );
}

#[test]
fn accuracy_scaled_tenths() {
    // Accuracy ±0.5°C scaled ×10 → 5 units; reading error within tolerance
    let mut ctx = VerificationContext::new();
    for v in &["reading_x10", "true_val_x10", "tolerance_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accurate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rd", "reading_x10 == 12503")); // 1250.3°C
    ctx.push_obligation(ProofObligation::assume("tv", "true_val_x10 == 12500")); // 1250.0°C
    ctx.push_obligation(ProofObligation::assume("tol", "tolerance_x10 == 5")); // ±0.5°C
    ctx.push_obligation(ProofObligation::assume(
        "acc_def",
        "accurate == if reading_x10 >= true_val_x10 - tolerance_x10 && reading_x10 <= true_val_x10 + tolerance_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "accurate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: 1250.3°C within ±0.5°C of 1250.0°C");
}

#[test]
fn response_time_bounded() {
    // Response time must be between 1ms and 500ms
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_ms", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt", "response_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if response_ms >= 1 && response_ms <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: response 10ms in [1, 500]");
}

#[test]
fn emissivity_range_scaled() {
    // Emissivity 0.10–1.00 scaled ×100 → 10–100
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emissivity_x100", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("em", "emissivity_x100 == 95")); // 0.95
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if emissivity_x100 >= 10 && emissivity_x100 <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: emissivity 0.95 (95) in [0.10, 1.00]");
}

#[test]
fn spectral_band_selection() {
    // 1=short wave (0.9–1.7µm), 2=mid wave (3–5µm), 3=long wave (8–14µm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spectral_band", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sb", "spectral_band == 1")); // short wave
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if spectral_band == 1 || spectral_band == 2 || spectral_band == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: spectral band short wave (1) valid");
}

#[test]
fn optics_type_selection() {
    // 1=fixed focus, 2=variable focus, 3=fiber optic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("optics_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot", "optics_type == 3")); // fiber optic
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if optics_type == 1 || optics_type == 2 || optics_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: optics fiber optic (3) valid");
}

#[test]
fn distance_ratio_bounded() {
    // Distance-to-spot ratio: 10:1 to 300:1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distance_ratio", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dr", "distance_ratio == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if distance_ratio >= 10 && distance_ratio <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: distance ratio 150:1 in [10, 300]");
}

#[test]
fn output_type_selection() {
    // 1=4-20mA analog, 2=RS-485 digital, 3=Ethernet/IP
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 2")); // RS-485
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if output_type == 1 || output_type == 2 || output_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: output RS-485 (2) valid");
}

#[test]
fn laser_sighting_flag() {
    // Boolean flag: 1=laser sighting enabled, 0=disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_laser", i32_ty());
    ctx.declare_var_typed("sighting_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hl", "has_laser == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "sighting_active == if has_laser == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "sighting_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: laser sighting enabled");
}
