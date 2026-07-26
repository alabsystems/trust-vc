// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn moisture_range() {
    let mut ctx = VerificationContext::new();
    for v in &["moisture_pct100", "min_moisture", "max_moisture"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("moisture_ok", i32_ty());
    // Moisture reading x100 %: 8.50% -> 850, range [0, 5000] (0% to 50%)
    ctx.push_obligation(ProofObligation::assume("mp", "moisture_pct100 == 850"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_moisture == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_moisture == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "moisture_ok == if moisture_pct100 >= min_moisture && moisture_pct100 <= max_moisture { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "moisture_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Paper moisture: 8.50% (850) in [0, 5000] -> OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_pct100", "min_accuracy", "max_accuracy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy x100 %: 0.05% -> 5, range [1, 100] (0.01% to 1.00%)
    ctx.push_obligation(ProofObligation::assume("ap", "accuracy_pct100 == 5"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_accuracy == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_accuracy == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_pct100 >= min_accuracy && accuracy_pct100 <= max_accuracy { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: 0.05% accuracy (5) in [1, 100] -> OK",
    );
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Sensor types: 1=infrared, 2=microwave, 3=capacitive
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: microwave (2) is valid sensor type",
    );
}

#[test]
fn measurement_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["web_speed_mm_s", "min_speed", "max_speed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Paper web speed in mm/s, range [100, 30000]
    ctx.push_obligation(ProofObligation::assume("ws", "web_speed_mm_s == 15000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_speed == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_speed == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if web_speed_mm_s >= min_speed && web_speed_mm_s <= max_speed { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: 15000 mm/s web speed in [100, 30000] -> OK",
    );
}

#[test]
fn basis_weight_range() {
    let mut ctx = VerificationContext::new();
    for v in &["basis_weight_gsm", "min_bw", "max_bw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Basis weight in g/m^2, range [10, 1000]
    ctx.push_obligation(ProofObligation::assume("bw", "basis_weight_gsm == 80"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if basis_weight_gsm >= min_bw && basis_weight_gsm <= max_bw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: 80 g/m^2 basis weight in [10, 1000] -> OK",
    );
}

#[test]
fn scan_width() {
    let mut ctx = VerificationContext::new();
    for v in &["scan_width_mm", "min_scan", "max_scan"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("scan_ok", i32_ty());
    // Scan width in mm, range [500, 12000]
    ctx.push_obligation(ProofObligation::assume("sw", "scan_width_mm == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_scan == 500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_scan == 12000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "scan_ok == if scan_width_mm >= min_scan && scan_width_mm <= max_scan { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "scan_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: 5000 mm scan width in [500, 12000] -> OK",
    );
}

#[test]
fn communication_protocol() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_proto", u32_ty());
    ctx.declare_var_typed("valid_proto", i32_ty());
    // Communication protocols: 1=Profibus, 2=Ethernet/IP, 3=OPC-UA, 4=Modbus TCP
    ctx.push_obligation(ProofObligation::assume("cp", "comm_proto == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_proto == if comm_proto == 1 || comm_proto == 2 || comm_proto == 3 || comm_proto == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_proto == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: OPC-UA (3) is valid communication protocol",
    );
}

#[test]
fn calibration_samples() {
    let mut ctx = VerificationContext::new();
    for v in &["cal_samples", "min_samples", "max_samples"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cal_ok", i32_ty());
    // Calibration sample count, range [1, 50]
    ctx.push_obligation(ProofObligation::assume("cs", "cal_samples == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_samples == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_samples == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cal_ok == if cal_samples >= min_samples && cal_samples <= max_samples { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: 10 calibration samples in [1, 50] -> OK",
    );
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature: offset +500, actual 25 C -> 525, range -50 C (450) to 100 C (600)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525")); // 25 C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 450")); // -50 C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 600")); // 100 C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: 25 C operating temp in [-50, 100] (offset +500) -> OK",
    );
}

#[test]
fn cross_direction_profile() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cd_profile_enabled", i32_ty());
    ctx.declare_var_typed("cd_valid", i32_ty());
    // Cross-direction profile: boolean flag (1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("cd", "cd_profile_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "cd_valid == if cd_profile_enabled == 0 || cd_profile_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cd_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Paper moisture: cross-direction profile enabled (1) is valid boolean",
    );
}
