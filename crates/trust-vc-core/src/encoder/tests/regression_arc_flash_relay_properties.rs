// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn detection_time() {
    let mut ctx = VerificationContext::new();
    for v in &["dt_us", "dt_min", "dt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Detection time in microseconds: value 5, valid range 1 to 10 (must be <1ms for arc flash)
    ctx.push_obligation(ProofObligation::assume("dt_val", "dt_us == 5"));
    ctx.push_obligation(ProofObligation::assume("dt_min", "dt_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dt_max", "dt_max == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "dt_in_range",
        "dt_us >= dt_min && dt_us <= dt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection time 5 us in range [1,10]");
}

#[test]
fn total_clearing_time() {
    let mut ctx = VerificationContext::new();
    for v in &["tc_ms", "tc_min", "tc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Total clearing time in ms: value 35, valid range 1 to 100
    ctx.push_obligation(ProofObligation::assume("tc_val", "tc_ms == 35"));
    ctx.push_obligation(ProofObligation::assume("tc_min", "tc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("tc_max", "tc_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "tc_in_range",
        "tc_ms >= tc_min && tc_ms <= tc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total clearing time 35 ms in range [1,100]");
}

#[test]
fn detection_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_method", u32_ty());
    ctx.declare_var_typed("valid_dm", i32_ty());
    // Detection methods: 1=light only, 2=light+overcurrent, 3=pressure
    ctx.push_obligation(ProofObligation::assume("dm_val", "det_method == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "valid_dm == if det_method == 1 || det_method == 2 || det_method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dm_chk", "valid_dm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection method 2 (light+overcurrent) is valid arc flash detection method",
    );
}

#[test]
fn sensor_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sc_val", "sc_min", "sc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sensor count: value 8, valid range 1 to 24
    ctx.push_obligation(ProofObligation::assume("sc_val", "sc_val == 8"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "sc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "sc_max == 24"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_in_range",
        "sc_val >= sc_min && sc_val <= sc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor count 8 in range [1,24]");
}

#[test]
fn voltage_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v_class", u32_ty());
    ctx.declare_var_typed("valid_vc", i32_ty());
    // Voltage classes: 480, 4160, 13800, 34500 V (non-sequential)
    ctx.push_obligation(ProofObligation::assume("vc_val", "v_class == 4160"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_vc == if v_class == 480 || v_class == 4160 || v_class == 13800 || v_class == 34500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vc_chk", "valid_vc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage class 4160 V is valid arc flash relay voltage class",
    );
}

#[test]
fn arc_energy() {
    let mut ctx = VerificationContext::new();
    for v in &["ae_val", "ae_min", "ae_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Arc energy x10 cal/cm2 incident energy: value 80 (8.0 cal/cm2), valid range 1 to 400
    ctx.push_obligation(ProofObligation::assume("ae_val", "ae_val == 80"));
    ctx.push_obligation(ProofObligation::assume("ae_min", "ae_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ae_max", "ae_max == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "ae_in_range",
        "ae_val >= ae_min && ae_val <= ae_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "arc energy 80 (8.0 cal/cm2) in range [1,400]");
}

#[test]
fn fiber_length() {
    let mut ctx = VerificationContext::new();
    for v in &["fl_val", "fl_min", "fl_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Fiber optic sensor length in meters: value 15, valid range 1 to 50
    ctx.push_obligation(ProofObligation::assume("fl_val", "fl_val == 15"));
    ctx.push_obligation(ProofObligation::assume("fl_min", "fl_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fl_max", "fl_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "fl_in_range",
        "fl_val >= fl_min && fl_val <= fl_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fiber length 15 m in range [1,50]");
}

#[test]
fn relay_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rly_out", u32_ty());
    ctx.declare_var_typed("valid_ro", i32_ty());
    // Relay output modes: 1=trip, 2=trip+alarm, 3=trip+alarm+lockout
    ctx.push_obligation(ProofObligation::assume("ro_val", "rly_out == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "valid_ro == if rly_out == 1 || rly_out == 2 || rly_out == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ro_chk", "valid_ro == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "relay output 3 (trip+alarm+lockout) is valid arc flash relay output mode",
    );
}

#[test]
fn iec_compliance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iec_flag", i32_ty());
    ctx.declare_var_typed("valid_ic", i32_ty());
    // IEC 62271-200 compliance: 1=compliant, 0=not compliant
    ctx.push_obligation(ProofObligation::assume("ic_val", "iec_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "valid_ic == if iec_flag == 0 || iec_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ic_chk", "valid_ic == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IEC compliance 1 (IEC 62271-200 compliant) is valid compliance flag",
    );
}

#[test]
fn self_test() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("st_flag", i32_ty());
    ctx.declare_var_typed("valid_st", i32_ty());
    // Self-test mode: 1=continuous, 0=manual
    ctx.push_obligation(ProofObligation::assume("st_val", "st_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "valid_st == if st_flag == 0 || st_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_chk", "valid_st == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-test 1 (continuous) is valid self-test mode");
}
