// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn parameter_count() {
    let mut ctx = VerificationContext::new();
    for v in &["param_count", "min_params", "max_params"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // Number of measured parameters (pH, DO, conductivity, turbidity, etc.)
    ctx.push_obligation(ProofObligation::assume("pc", "param_count == 8"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_params == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_params == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if param_count >= min_params && param_count <= max_params { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: 8 parameters in [1, 20] range");
}

#[test]
fn conductivity() {
    let mut ctx = VerificationContext::new();
    for v in &["cond_us_cm", "max_cond_us_cm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cond_ok", i32_ty());
    // Conductivity in microsiemens per centimeter
    ctx.push_obligation(ProofObligation::assume("cu", "cond_us_cm == 500"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cond_us_cm == 200000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cond_ok == if cond_us_cm <= max_cond_us_cm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cond_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: 500 uS/cm conductivity <= 200000 max");
}

#[test]
fn orp() {
    let mut ctx = VerificationContext::new();
    for v in &["orp_offset", "min_orp_offset", "max_orp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("orp_ok", i32_ty());
    // ORP in mV (offset +2000 for range -2000 to +2000 mV)
    ctx.push_obligation(ProofObligation::assume("oo", "orp_offset == 2200")); // +200 mV
    ctx.push_obligation(ProofObligation::assume("mn", "min_orp_offset == 0")); // -2000 mV
    ctx.push_obligation(ProofObligation::assume("mx", "max_orp_offset == 4000")); // +2000 mV
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "orp_ok == if orp_offset >= min_orp_offset && orp_offset <= max_orp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "orp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: +200 mV ORP in [-2000, +2000] range");
}

#[test]
fn turbidity() {
    let mut ctx = VerificationContext::new();
    for v in &["turb_ntu_x10", "max_turb_ntu_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("turb_ok", i32_ty());
    // Turbidity in NTU x10 (5.0 NTU = 50)
    ctx.push_obligation(ProofObligation::assume("tn", "turb_ntu_x10 == 50")); // 5.0 NTU
    ctx.push_obligation(ProofObligation::assume("mt", "max_turb_ntu_x10 == 10000")); // 1000.0 NTU
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "turb_ok == if turb_ntu_x10 <= max_turb_ntu_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "turb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: 5.0 NTU turbidity <= 1000.0 max");
}

#[test]
fn dissolved_oxygen() {
    let mut ctx = VerificationContext::new();
    for v in &["do_ppb", "max_do_ppb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("do_ok", i32_ty());
    // Dissolved oxygen in parts per billion (8.0 ppm = 8000 ppb)
    ctx.push_obligation(ProofObligation::assume("dp", "do_ppb == 8000")); // 8.0 ppm
    ctx.push_obligation(ProofObligation::assume("md", "max_do_ppb == 20000")); // 20.0 ppm
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "do_ok == if do_ppb <= max_do_ppb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "do_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: 8.0 ppm DO <= 20.0 ppm max");
}

#[test]
fn sample_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["interval_sec", "min_interval_sec", "max_interval_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("interval_ok", i32_ty());
    // Measurement interval in seconds
    ctx.push_obligation(ProofObligation::assume("is", "interval_sec == 60"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_interval_sec == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_interval_sec == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "interval_ok == if interval_sec >= min_interval_sec && interval_sec <= max_interval_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "interval_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: 60s sample interval in [1, 3600] range");
}

#[test]
fn sensor_port_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ports", "min_ports", "max_ports"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ports_ok", i32_ty());
    // Number of sensor ports on the analyzer
    ctx.push_obligation(ProofObligation::assume("p", "ports == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ports == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ports == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "ports_ok == if ports >= min_ports && ports <= max_ports { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ports_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: 4 sensor ports in [1, 8] range");
}

#[test]
fn communication() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_type", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // Communication protocols: 1=4-20mA, 2=Modbus RTU, 3=PROFIBUS DP, 4=Ethernet/IP
    ctx.push_obligation(ProofObligation::assume("ct", "comm_type == 2")); // Modbus RTU
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_comm == if comm_type == 1 || comm_type == 2 || comm_type == 3 || comm_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: Modbus RTU is valid communication type");
}

#[test]
fn cleaning_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clean_method", u32_ty());
    ctx.declare_var_typed("valid_clean", i32_ty());
    // Cleaning methods: 1=ultrasonic, 2=compressed air, 3=mechanical wiper
    ctx.push_obligation(ProofObligation::assume("cm", "clean_method == 1")); // ultrasonic
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_clean == if clean_method == 1 || clean_method == 2 || clean_method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_clean == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WQ multi: ultrasonic is valid cleaning method");
}

#[test]
fn data_logging() {
    let mut ctx = VerificationContext::new();
    for v in &["log_records", "min_records", "max_records"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("log_ok", i32_ty());
    // Data log storage capacity in records
    ctx.push_obligation(ProofObligation::assume("lr", "log_records == 100000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_records == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_records == 10000000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "log_ok == if log_records >= min_records && log_records <= max_records { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "log_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WQ multi: 100000 log records in [1000, 10000000] range",
    );
}
