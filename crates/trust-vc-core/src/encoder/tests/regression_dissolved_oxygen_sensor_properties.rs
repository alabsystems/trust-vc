// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["do_ppb", "max_do_ppb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("do_ok", i32_ty());
    // Dissolved oxygen in parts per billion
    ctx.push_obligation(ProofObligation::assume("dp", "do_ppb == 8000")); // 8 ppm = 8000 ppb
    ctx.push_obligation(ProofObligation::assume("md", "max_do_ppb == 20000")); // 20 ppm
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "do_ok == if do_ppb <= max_do_ppb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "do_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 8 ppm ≤ 20 ppm max → OK");
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // DO sensor technologies: 1=galvanic, 2=polarographic, 3=optical/luminescent, 4=amperometric
    ctx.push_obligation(ProofObligation::assume("st", "sens_type == 3")); // optical
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if sens_type == 1 || sens_type == 2 || sens_type == 3 || sens_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: optical/luminescent is valid sensor type");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_ppb", "max_accuracy_ppb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy in ppb
    ctx.push_obligation(ProofObligation::assume("ap", "accuracy_ppb == 100")); // 0.1 ppm
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_ppb == 500")); // 0.5 ppm
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_ppb <= max_accuracy_ppb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 0.1 ppm accuracy ≤ 0.5 ppm max → OK");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_sec", "max_resp_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // T90 response time in seconds
    ctx.push_obligation(ProofObligation::assume("rs", "resp_sec == 60"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resp_sec == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_sec <= max_resp_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 60s T90 response ≤ 300s max → OK");
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature (offset +500): 0°C to 50°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525")); // 25°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 500")); // 0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 550")); // 50°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 25°C in [0, 50] → OK");
}

#[test]
fn calibration_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["cal_days", "min_cal_days"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cal_ok", i32_ty());
    // Calibration interval in days
    ctx.push_obligation(ProofObligation::assume("cd", "cal_days == 30"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cal_days == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cal_ok == if cal_days >= min_cal_days { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 30-day cal interval ≥ 7-day min → OK");
}

#[test]
fn membrane_life() {
    let mut ctx = VerificationContext::new();
    for v in &["life_months", "min_life_months"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("life_ok", i32_ty());
    // Membrane/cap replacement interval in months
    ctx.push_obligation(ProofObligation::assume("lm", "life_months == 12"));
    ctx.push_obligation(ProofObligation::assume("ml", "min_life_months == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if life_months >= min_life_months { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 12-month membrane ≥ 3-month min → OK");
}

#[test]
fn pressure_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_mbar", "min_press_mbar", "max_press_mbar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Atmospheric pressure compensation range in mbar
    ctx.push_obligation(ProofObligation::assume("pm", "pressure_mbar == 1013")); // std atm
    ctx.push_obligation(ProofObligation::assume("mn", "min_press_mbar == 500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_press_mbar == 1100"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_mbar >= min_press_mbar && pressure_mbar <= max_press_mbar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 1013 mbar in [500, 1100] → OK");
}

#[test]
fn salinity_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["salinity_ppt", "max_salinity_ppt"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sal_ok", i32_ty());
    // Salinity compensation in parts per thousand (ppt)
    ctx.push_obligation(ProofObligation::assume("sp", "salinity_ppt == 35")); // seawater
    ctx.push_obligation(ProofObligation::assume("ms", "max_salinity_ppt == 70")); // hypersaline
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sal_ok == if salinity_ppt <= max_salinity_ppt { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 35 ppt salinity ≤ 70 ppt max → OK");
}

#[test]
fn flow_requirement() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_cm_s", "min_flow_cm_s"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Minimum sample flow past sensor in cm/s
    ctx.push_obligation(ProofObligation::assume("fc", "flow_cm_s == 30"));
    ctx.push_obligation(ProofObligation::assume("mf", "min_flow_cm_s == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_cm_s >= min_flow_cm_s { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 30 cm/s flow ≥ 5 cm/s min → OK");
}
