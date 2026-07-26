// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn wavelength_range_bounded() {
    // Wavelength in nm: valid range 200–2000, assume 1550nm (C-band telecom)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wavelength_nm == 1550"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if wavelength_nm >= 200 && wavelength_nm <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "optical power meter: 1550nm in [200, 2000]");
}

#[test]
fn power_range_code_bounded() {
    // Power range code 1–20 (each code maps to a dBm window), assume code 10
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_range", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pr", "power_range == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if power_range >= 1 && power_range <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optical power meter: power range code 10 in [1, 20]",
    );
}

#[test]
fn accuracy_scaled_thousandths() {
    // Accuracy as % x1000: 50 = 0.050%; valid range 1–1000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc", "accuracy_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if accuracy_x1000 >= 1 && accuracy_x1000 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optical power meter: accuracy 0.050% (50) in [1, 1000]",
    );
}

#[test]
fn resolution_scaled_ten_thousandths() {
    // Resolution in dBm x10000: 10 = 0.0010 dBm; valid range 1–100
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x10000", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res", "resolution_x10000 == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if resolution_x10000 >= 1 && resolution_x10000 <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optical power meter: resolution 0.0010 dBm (10) in [1, 100]",
    );
}

#[test]
fn response_time_scaled_hundredths() {
    // Response time in ms x100: 100 = 1.00ms; valid range 1–10000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_x100", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt", "response_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if response_x100 >= 1 && response_x100 <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optical power meter: response 1.00ms (100) in [1, 10000]",
    );
}

#[test]
fn channel_count_bounded() {
    // Number of measurement channels: 1–8, assume 2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if channels >= 1 && channels <= 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "optical power meter: 2 channels in [1, 8]");
}

#[test]
fn detector_type_selection() {
    // 1=silicon, 2=InGaAs, 3=germanium; assume InGaAs
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "detector_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if detector_type == 1 || detector_type == 2 || detector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "optical power meter: detector InGaAs (2) valid");
}

#[test]
fn measurement_mode_selection() {
    // 1=CW (continuous wave), 2=pulsed, 3=modulated; assume CW
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mm", "meas_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if meas_mode == 1 || meas_mode == 2 || meas_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optical power meter: measurement mode CW (1) valid",
    );
}

#[test]
fn connector_type_selection() {
    // 1=FC, 2=SC, 3=LC; assume FC
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("connector_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "connector_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if connector_type == 1 || connector_type == 2 || connector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "optical power meter: connector FC (1) valid");
}

#[test]
fn auto_wavelength_detection_flag() {
    // Boolean flag: 1=automatic wavelength detection enabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_detect", i32_ty());
    ctx.declare_var_typed("detection_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ad", "auto_detect == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "da_def",
        "detection_active == if auto_detect == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "detection_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optical power meter: auto wavelength detection enabled",
    );
}
