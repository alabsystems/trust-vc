// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["ppm", "ppm_min", "ppm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Dissolved hydrogen measurement in ppm: value 150, valid range 1 to 5000
    ctx.push_obligation(ProofObligation::assume("mr_val", "ppm == 150"));
    ctx.push_obligation(ProofObligation::assume("mr_min", "ppm_min == 1"));
    ctx.push_obligation(ProofObligation::assume("mr_max", "ppm_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "mr_in_range",
        "ppm >= ppm_min && ppm <= ppm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dissolved hydrogen 150 ppm in range [1,5000]");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x10", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy in ppm x10: value 50 (5.0 ppm), valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "acc_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "acc_x10 >= acc_min && acc_x10 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 5.0 ppm in range [0.1,50.0]");
}

#[test]
fn sensor_technology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor", u32_ty());
    ctx.declare_var_typed("valid_sensor", i32_ty());
    // 1=electrochemical, 2=thermal conductivity, 3=Pd-Ni thin film
    ctx.push_obligation(ProofObligation::assume("st_val", "sensor == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "valid_sensor == if sensor == 1 || sensor == 2 || sensor == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_chk", "valid_sensor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor technology 3 (Pd-Ni thin film) is valid");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["t90_min", "t90_min_r", "t90_max_r"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time T90 in minutes: value 15, valid range 1 to 120
    ctx.push_obligation(ProofObligation::assume("rt_val", "t90_min == 15"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "t90_min_r == 1"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "t90_max_r == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "t90_min >= t90_min_r && t90_min <= t90_max_r",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time T90 15 min in range [1,120]");
}

#[test]
fn oil_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Oil temperature -20 to 120 deg C, offset +500: 480 to 620
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp_offset == 540")); // 40 deg C + 500
    ctx.push_obligation(ProofObligation::assume("ot_min", "min_temp_offset == 480")); // -20 deg C + 500
    ctx.push_obligation(ProofObligation::assume("ot_max", "max_temp_offset == 620")); // 120 deg C + 500
    ctx.push_obligation(ProofObligation::assume(
        "ot_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_chk", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil temperature 40 deg C in [-20,120] operating range",
    );
}

#[test]
fn communication() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // 1=4-20mA, 2=Modbus RTU, 3=IEC 61850, 4=DNP3
    ctx.push_obligation(ProofObligation::assume("cm_val", "comm == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "valid_comm == if comm == 1 || comm == 2 || comm == 3 || comm == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication protocol 2 (Modbus RTU) is valid");
}

#[test]
fn alarm_setpoints() {
    let mut ctx = VerificationContext::new();
    for v in &["alarms", "alarms_min", "alarms_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Alarm setpoint count: value 2, valid range 1 to 4
    ctx.push_obligation(ProofObligation::assume("as_val", "alarms == 2"));
    ctx.push_obligation(ProofObligation::assume("as_min", "alarms_min == 1"));
    ctx.push_obligation(ProofObligation::assume("as_max", "alarms_max == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "as_in_range",
        "alarms >= alarms_min && alarms <= alarms_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alarm setpoints 2 in range [1,4]");
}

#[test]
fn sample_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_min", "rate_lo", "rate_hi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sample rate in minutes per reading: value 5, valid range 1 to 60
    ctx.push_obligation(ProofObligation::assume("sr_val", "rate_min == 5"));
    ctx.push_obligation(ProofObligation::assume("sr_min", "rate_lo == 1"));
    ctx.push_obligation(ProofObligation::assume("sr_max", "rate_hi == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "sr_in_range",
        "rate_min >= rate_lo && rate_min <= rate_hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample rate 5 min per reading in range [1,60]");
}

#[test]
fn calibration_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["cal_months", "cal_min", "cal_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Calibration interval in months: value 6, valid range 1 to 24
    ctx.push_obligation(ProofObligation::assume("ci_val", "cal_months == 6"));
    ctx.push_obligation(ProofObligation::assume("ci_min", "cal_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ci_max", "cal_max == 24"));
    ctx.push_obligation(ProofObligation::assert(
        "ci_in_range",
        "cal_months >= cal_min && cal_months <= cal_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "calibration interval 6 months in range [1,24]");
}

#[test]
fn installation_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("install", u32_ty());
    ctx.declare_var_typed("valid_install", i32_ty());
    // 1=online/in-line, 2=headspace, 3=bypass loop
    ctx.push_obligation(ProofObligation::assume("it_val", "install == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "it_def",
        "valid_install == if install == 1 || install == 2 || install == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("it_chk", "valid_install == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "installation type 1 (online/in-line) is valid");
}
