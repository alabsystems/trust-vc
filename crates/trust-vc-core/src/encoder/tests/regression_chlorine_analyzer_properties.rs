// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["cl_ppb", "max_cl_ppb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cl_ok", i32_ty());
    // Free chlorine in parts per billion
    ctx.push_obligation(ProofObligation::assume("cp", "cl_ppb == 500")); // 0.5 ppm
    ctx.push_obligation(ProofObligation::assume("mc", "max_cl_ppb == 20000")); // 20 ppm
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cl_ok == if cl_ppb <= max_cl_ppb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: 0.5 ppm ≤ 20 ppm max → OK");
}

#[test]
fn measurement_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Types: 1=free chlorine, 2=total chlorine, 3=chlorine dioxide, 4=monochloramine
    ctx.push_obligation(ProofObligation::assume("mt", "meas_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if meas_type == 1 || meas_type == 2 || meas_type == 3 || meas_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: free chlorine is valid measurement type");
}

#[test]
fn sensor_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", u32_ty());
    ctx.declare_var_typed("valid_method", i32_ty());
    // Sensing methods: 1=amperometric, 2=colorimetric (DPD), 3=polarographic, 4=voltammetric
    ctx.push_obligation(ProofObligation::assume("m", "method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_method == if method == 1 || method == 2 || method == 3 || method == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_method == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: amperometric is valid method");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_ppb", "max_accuracy_ppb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy in ppb
    ctx.push_obligation(ProofObligation::assume("ap", "accuracy_ppb == 10")); // 0.01 ppm
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_ppb == 50")); // 0.05 ppm
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_ppb <= max_accuracy_ppb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: 0.01 ppm accuracy ≤ 0.05 ppm max → OK");
}

#[test]
fn sample_flow() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_ml_min", "min_flow_ml_min", "max_flow_ml_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Sample flow rate in mL/min
    ctx.push_obligation(ProofObligation::assume("fm", "flow_ml_min == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow_ml_min == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow_ml_min == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_ml_min >= min_flow_ml_min && flow_ml_min <= max_flow_ml_min { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: 250 mL/min flow in [100, 1000] → OK");
}

#[test]
fn ph_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["ph_x100", "min_ph_x100", "max_ph_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ph_ok", i32_ty());
    // pH compensation range (×100, offset +200)
    // pH 5.0 → 700, pH 7.0 → 900, pH 9.0 → 1100
    ctx.push_obligation(ProofObligation::assume("px", "ph_x100 == 900")); // pH 7.0
    ctx.push_obligation(ProofObligation::assume("mn", "min_ph_x100 == 700")); // pH 5.0
    ctx.push_obligation(ProofObligation::assume("mx", "max_ph_x100 == 1100")); // pH 9.0
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "ph_ok == if ph_x100 >= min_ph_x100 && ph_x100 <= max_ph_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ph_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: pH 7.0 in [5.0, 9.0] compensation → OK");
}

#[test]
fn reagent_lifetime() {
    let mut ctx = VerificationContext::new();
    for v in &["lifetime_days", "min_lifetime_days"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("life_ok", i32_ty());
    // DPD reagent lifetime in days
    ctx.push_obligation(ProofObligation::assume("ld", "lifetime_days == 30"));
    ctx.push_obligation(ProofObligation::assume("ml", "min_lifetime_days == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if lifetime_days >= min_lifetime_days { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: 30-day reagent ≥ 7-day min → OK");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_sec", "max_resp_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // T90 response time in seconds
    ctx.push_obligation(ProofObligation::assume("rs", "resp_sec == 45"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resp_sec == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_sec <= max_resp_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: 45s T90 response ≤ 120s max → OK");
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature (offset +500): 2°C to 45°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 502")); // 2°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 545")); // 45°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: 20°C in [2, 45] → OK");
}

#[test]
fn epa_compliance() {
    let mut ctx = VerificationContext::new();
    for v in &["reading_ppb", "epa_min_ppb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("epa_ok", i32_ty());
    // EPA requires ≥0.2 ppm free chlorine (200 ppb) in distribution
    ctx.push_obligation(ProofObligation::assume("rp", "reading_ppb == 500")); // 0.5 ppm
    ctx.push_obligation(ProofObligation::assume("em", "epa_min_ppb == 200")); // 0.2 ppm
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "epa_ok == if reading_ppb >= epa_min_ppb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "epa_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chlorine: 0.5 ppm ≥ 0.2 ppm EPA min → OK");
}
