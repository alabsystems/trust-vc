// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn power_range_low() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_offset", u32_ty());
    ctx.declare_var_typed("range_ok", i32_ty());
    // Power in dBm with +100 offset: 30 = -70 dBm, valid range 0 (-100 dBm) to 50 (-50 dBm)
    ctx.push_obligation(ProofObligation::assume("val", "power_offset == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "range_ok == if power_offset >= 0 && power_offset <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: -70 dBm (offset 30) in low range [0, 50]",
    );
}

#[test]
fn power_range_high() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_offset", u32_ty());
    ctx.declare_var_typed("range_ok", i32_ty());
    // Power in dBm with +100 offset: 123 = +23 dBm, valid range 110 (+10 dBm) to 130 (+30 dBm)
    ctx.push_obligation(ProofObligation::assume("val", "power_offset == 123"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "range_ok == if power_offset >= 110 && power_offset <= 130 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: +23 dBm (offset 123) in high range [110, 130]",
    );
}

#[test]
fn wavelength() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.declare_var_typed("valid_wl", i32_ty());
    // Calibrated wavelength in nm: 5-way disjunction 850/1310/1490/1550/1625
    ctx.push_obligation(ProofObligation::assume("val", "wavelength_nm == 1550"));
    ctx.push_obligation(ProofObligation::assume(
        "vw_def",
        "valid_wl == if wavelength_nm == 850 || wavelength_nm == 1310 || wavelength_nm == 1490 || wavelength_nm == 1550 || wavelength_nm == 1625 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_wl == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: 1550nm is valid calibrated wavelength",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", u32_ty());
    ctx.declare_var_typed("accuracy_ok", i32_ty());
    // Measurement accuracy in dB x100: 20 = 0.20 dB, max 50 = 0.50 dB
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x100 == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "accuracy_ok == if accuracy_x100 <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "accuracy_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: 0.20 dB accuracy (20) within max 0.50 dB (50)",
    );
}

#[test]
fn connector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("connector", u32_ty());
    ctx.declare_var_typed("valid_conn", i32_ty());
    // 1=FC, 2=SC, 3=LC, 4=ST, 5=MPO
    ctx.push_obligation(ProofObligation::assume("val", "connector == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_conn == if connector == 1 || connector == 2 || connector == 3 || connector == 4 || connector == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_conn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: LC (3) is valid connector type",
    );
}

#[test]
fn detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", u32_ty());
    ctx.declare_var_typed("valid_det", i32_ty());
    // 1=InGaAs, 2=Ge, 3=Si
    ctx.push_obligation(ProofObligation::assume("val", "detector == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_det == if detector == 1 || detector == 2 || detector == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_det == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: InGaAs (1) is valid detector type",
    );
}

#[test]
fn display_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x100", u32_ty());
    ctx.declare_var_typed("resolution_ok", i32_ty());
    // Display resolution in dB x100: 1 = 0.01 dB, max 10 = 0.10 dB
    ctx.push_obligation(ProofObligation::assume("val", "resolution_x100 == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "resolution_ok == if resolution_x100 <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "resolution_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: 0.01 dB resolution (1) within max 0.10 dB (10)",
    );
}

#[test]
fn measurement_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("readings_per_sec", u32_ty());
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Readings per second: 10, valid range 1-1000
    ctx.push_obligation(ProofObligation::assume("val", "readings_per_sec == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "speed_ok == if readings_per_sec >= 1 && readings_per_sec <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical power meter: 10 readings/sec in [1, 1000]");
}

#[test]
fn fiber_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fiber", u32_ty());
    ctx.declare_var_typed("valid_fiber", i32_ty());
    // 1=single-mode, 2=multimode 50um, 3=multimode 62.5um
    ctx.push_obligation(ProofObligation::assume("val", "fiber == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fiber == if fiber == 1 || fiber == 2 || fiber == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_fiber == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: single-mode (1) is valid fiber type",
    );
}

#[test]
fn battery_life() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("runtime_hours", u32_ty());
    ctx.declare_var_typed("battery_ok", i32_ty());
    // Battery runtime in hours: 40, minimum 8
    ctx.push_obligation(ProofObligation::assume("val", "runtime_hours == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "battery_ok == if runtime_hours >= 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("meets_min", "battery_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical power meter: 40h battery life meets minimum 8h",
    );
}
