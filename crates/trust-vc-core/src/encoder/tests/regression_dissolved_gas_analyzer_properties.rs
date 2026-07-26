// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gas_count() {
    let mut ctx = VerificationContext::new();
    for v in &["gases", "gases_min", "gases_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of monitored gases (H2, CH4, C2H2, C2H4, C2H6, CO, CO2, O2, N2): value 9, range 1-9
    ctx.push_obligation(ProofObligation::assume("gc_val", "gases == 9"));
    ctx.push_obligation(ProofObligation::assume("gc_min", "gases_min == 1"));
    ctx.push_obligation(ProofObligation::assume("gc_max", "gases_max == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "gc_in_range",
        "gases >= gases_min && gases <= gases_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas count 9 (IEC 60599 full suite) in range [1,9]");
}

#[test]
fn detection_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", u32_ty());
    ctx.declare_var_typed("valid_method", i32_ty());
    // 1=gas chromatography, 2=photo-acoustic, 3=thermal conductivity, 4=NDIR
    ctx.push_obligation(ProofObligation::assume("dm_val", "method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_valid_def",
        "valid_method == if method == 1 || method == 2 || method == 3 || method == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dm_check", "valid_method == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection method 1 (gas chromatography) is valid");
}

#[test]
fn hydrogen_range() {
    let mut ctx = VerificationContext::new();
    for v in &["h2_ppm", "h2_min", "h2_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Hydrogen concentration in ppm: value 150, valid range 1-50000
    ctx.push_obligation(ProofObligation::assume("hr_val", "h2_ppm == 150"));
    ctx.push_obligation(ProofObligation::assume("hr_min", "h2_min == 1"));
    ctx.push_obligation(ProofObligation::assume("hr_max", "h2_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "hr_in_range",
        "h2_ppm >= h2_min && h2_ppm <= h2_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hydrogen 150 ppm in range [1,50000]");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x10", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy in x10 ppm (0.1-50.0 ppm mapped to 1-500): value 20 (2.0 ppm), range 1-500
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "acc_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "acc_x10 >= acc_min && acc_x10 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 20 (2.0 ppm) in range [1,500]");
}

#[test]
fn sample_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["interval", "int_min", "int_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sample interval in minutes: value 60, valid range 1-1440 (up to 24 hours)
    ctx.push_obligation(ProofObligation::assume("si_val", "interval == 60"));
    ctx.push_obligation(ProofObligation::assume("si_min", "int_min == 1"));
    ctx.push_obligation(ProofObligation::assume("si_max", "int_max == 1440"));
    ctx.push_obligation(ProofObligation::assert(
        "si_in_range",
        "interval >= int_min && interval <= int_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample interval 60 min in range [1,1440]");
}

#[test]
fn oil_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_off", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Oil temperature offset +500 (-20C to 120C mapped to 480-620): value 545 (45C), range 480-620
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp_off == 545"));
    ctx.push_obligation(ProofObligation::assume("ot_min", "temp_min == 480"));
    ctx.push_obligation(ProofObligation::assume("ot_max", "temp_max == 620"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "temp_off >= temp_min && temp_off <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil temperature 545 (45C offset+500) in range [480,620]",
    );
}

#[test]
fn extraction_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("extraction", u32_ty());
    ctx.declare_var_typed("valid_extraction", i32_ty());
    // 1=headspace, 2=membrane, 3=vacuum extraction
    ctx.push_obligation(ProofObligation::assume("em_val", "extraction == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "em_valid_def",
        "valid_extraction == if extraction == 1 || extraction == 2 || extraction == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("em_check", "valid_extraction == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "extraction method 2 (membrane) is valid");
}

#[test]
fn communication() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // 1=Modbus RTU, 2=Modbus TCP, 3=IEC 61850, 4=DNP3
    ctx.push_obligation(ProofObligation::assume("cm_val", "comm == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_valid_def",
        "valid_comm == if comm == 1 || comm == 2 || comm == 3 || comm == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_check", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication 3 (IEC 61850) is valid");
}

#[test]
fn alarm_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm", u32_ty());
    ctx.declare_var_typed("valid_alarm", i32_ty());
    // 1=normal, 2=caution, 3=critical
    ctx.push_obligation(ProofObligation::assume("al_val", "alarm == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "al_valid_def",
        "valid_alarm == if alarm == 1 || alarm == 2 || alarm == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("al_check", "valid_alarm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alarm level 2 (caution) is valid");
}

#[test]
fn moisture_range() {
    let mut ctx = VerificationContext::new();
    for v in &["moisture", "moist_min", "moist_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Moisture in ppm water in oil: value 25, valid range 1-500
    ctx.push_obligation(ProofObligation::assume("mr_val", "moisture == 25"));
    ctx.push_obligation(ProofObligation::assume("mr_min", "moist_min == 1"));
    ctx.push_obligation(ProofObligation::assume("mr_max", "moist_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "mr_in_range",
        "moisture >= moist_min && moisture <= moist_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "moisture 25 ppm in range [1,500]");
}
