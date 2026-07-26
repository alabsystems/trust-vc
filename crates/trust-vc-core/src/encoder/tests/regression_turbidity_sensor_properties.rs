// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ntu_range() {
    let mut ctx = VerificationContext::new();
    for v in &["ntu", "max_ntu"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ntu_ok", i32_ty());
    // Nephelometric Turbidity Units (NTU)
    ctx.push_obligation(ProofObligation::assume("n", "ntu == 5"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_ntu == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "ntu_ok == if ntu <= max_ntu { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ntu_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 5 NTU ≤ 4000 max → OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "max_accuracy_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy as % of reading (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x10 == 20")); // 2.0%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x10 == 50")); // 5.0%
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 2.0% accuracy ≤ 5.0% max → OK");
}

#[test]
fn measurement_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", u32_ty());
    ctx.declare_var_typed("valid_method", i32_ty());
    // Methods: 1=nephelometric (90°), 2=ratiometric, 3=absorption, 4=backscatter
    ctx.push_obligation(ProofObligation::assume("m", "method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_method == if method == 1 || method == 2 || method == 3 || method == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_method == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: nephelometric is valid method");
}

#[test]
fn wavelength() {
    let mut ctx = VerificationContext::new();
    for v in &["wavelength_nm", "min_wl_nm", "max_wl_nm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wl_ok", i32_ty());
    // Light source wavelength in nm
    ctx.push_obligation(ProofObligation::assume("wn", "wavelength_nm == 860")); // NIR
    ctx.push_obligation(ProofObligation::assume("mn", "min_wl_nm == 400")); // visible
    ctx.push_obligation(ProofObligation::assume("mx", "max_wl_nm == 1000")); // NIR
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wl_ok == if wavelength_nm >= min_wl_nm && wavelength_nm <= max_wl_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 860nm wavelength in [400, 1000] → OK");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_sec", "max_resp_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Measurement response time (T90)
    ctx.push_obligation(ProofObligation::assume("rs", "resp_sec == 30"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resp_sec == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_sec <= max_resp_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 30s T90 response ≤ 120s max → OK");
}

#[test]
fn cleaning_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["clean_hours", "min_clean_hours"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("clean_ok", i32_ty());
    // Minimum cleaning interval (wiper/ultrasonic)
    ctx.push_obligation(ProofObligation::assume("ch", "clean_hours == 168")); // weekly
    ctx.push_obligation(ProofObligation::assume("mc", "min_clean_hours == 24")); // daily min
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "clean_ok == if clean_hours >= min_clean_hours { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "clean_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 168h cleaning interval ≥ 24h min → OK");
}

#[test]
fn depth_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["depth_m", "max_depth_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth_ok", i32_ty());
    // Submersion depth rating in meters
    ctx.push_obligation(ProofObligation::assume("dm", "depth_m == 5"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth_m == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if depth_m <= max_depth_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 5m depth ≤ 20m max → OK");
}

#[test]
fn epa_compliance() {
    let mut ctx = VerificationContext::new();
    for v in &["reading_ntu", "epa_limit_ntu"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("epa_ok", i32_ty());
    // EPA drinking water: <1 NTU (using integers, 0 is valid)
    ctx.push_obligation(ProofObligation::assume("rn", "reading_ntu == 0"));
    ctx.push_obligation(ProofObligation::assume("el", "epa_limit_ntu == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "epa_ok == if reading_ntu < epa_limit_ntu { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "epa_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 0 NTU < 1 EPA limit → OK");
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature: 0°C to +50°C (offset +500)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 500")); // 0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 550")); // 50°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 20°C in [0, 50] → OK");
}

#[test]
fn calibration_point_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cal_points", "min_cal_points"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cal_ok", i32_ty());
    // Minimum calibration reference points
    ctx.push_obligation(ProofObligation::assume("cp", "cal_points == 3"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cal_points == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cal_ok == if cal_points >= min_cal_points { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Turbidity: 3 cal points ≥ 2 min → OK");
}
