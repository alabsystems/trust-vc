// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn full_scale_range() {
    let mut ctx = VerificationContext::new();
    for v in &["sccm", "sccm_min", "sccm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Full scale range in sccm (standard cm3/min): value 500, valid range 1 to 50000
    ctx.push_obligation(ProofObligation::assume("fr_val", "sccm == 500"));
    ctx.push_obligation(ProofObligation::assume("fr_min", "sccm_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fr_max", "sccm_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "fr_in_range",
        "sccm >= sccm_min && sccm <= sccm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "full scale range 500 sccm in range [1,50000]");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x100", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy as x100 % of full scale: value 100 (1.00%), valid range 10 (0.10%) to 500 (5.00%)
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "acc_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "acc_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "acc_x100 >= acc_min && acc_x100 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy 100 (1.00% FS) in range [10,500] (0.10%-5.00%)",
    );
}

#[test]
fn gas_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", u32_ty());
    ctx.declare_var_typed("valid_gas", i32_ty());
    // 1=N2, 2=O2, 3=Ar, 4=H2, 5=He
    ctx.push_obligation(ProofObligation::assume("gt_val", "gas == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "gt_valid_def",
        "valid_gas == if gas == 1 || gas == 2 || gas == 3 || gas == 4 || gas == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gt_check", "valid_gas == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas type 3 (Ar) is valid");
}

#[test]
fn control_valve() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve", u32_ty());
    ctx.declare_var_typed("valid_valve", i32_ty());
    // 1=solenoid, 2=piezo, 3=thermal
    ctx.push_obligation(ProofObligation::assume("cv_val", "valve == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_valid_def",
        "valid_valve == if valve == 1 || valve == 2 || valve == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cv_check", "valid_valve == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "control valve 2 (piezo) is valid");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["t98_ms", "t98_min", "t98_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time T98 in ms: value 200, valid range 10 to 5000
    ctx.push_obligation(ProofObligation::assume("rt_val", "t98_ms == 200"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "t98_min == 10"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "t98_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "t98_ms >= t98_min && t98_ms <= t98_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 200 ms (T98) in range [10,5000]");
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor", u32_ty());
    ctx.declare_var_typed("valid_sensor", i32_ty());
    // 1=thermal, 2=differential pressure, 3=Coriolis
    ctx.push_obligation(ProofObligation::assume("st_val", "sensor == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "st_valid_def",
        "valid_sensor == if sensor == 1 || sensor == 2 || sensor == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_check", "valid_sensor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor type 1 (thermal) is valid");
}

#[test]
fn communication() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // 1=analog 0-5V, 2=RS-485, 3=DeviceNet, 4=EtherCAT
    ctx.push_obligation(ProofObligation::assume("cm_val", "comm == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_valid_def",
        "valid_comm == if comm == 1 || comm == 2 || comm == 3 || comm == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_check", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication 4 (EtherCAT) is valid");
}

#[test]
fn operating_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_kpa", "press_min", "press_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating pressure in kPa: value 300, valid range 100 to 1000
    ctx.push_obligation(ProofObligation::assume("op_val", "pressure_kpa == 300"));
    ctx.push_obligation(ProofObligation::assume("op_min", "press_min == 100"));
    ctx.push_obligation(ProofObligation::assume("op_max", "press_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "op_in_range",
        "pressure_kpa >= press_min && pressure_kpa <= press_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating pressure 300 kPa in range [100,1000]");
}

#[test]
fn leak_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["leak_x10", "leak_min", "leak_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Leak rate as x10 % FS: value 5 (0.5%), valid range 1 (0.1%) to 50 (5.0%)
    ctx.push_obligation(ProofObligation::assume("lr_val", "leak_x10 == 5"));
    ctx.push_obligation(ProofObligation::assume("lr_min", "leak_min == 1"));
    ctx.push_obligation(ProofObligation::assume("lr_max", "leak_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "lr_in_range",
        "leak_x10 >= leak_min && leak_x10 <= leak_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leak rate 5 (0.5% FS) in range [1,50] (0.1%-5.0%)");
}

#[test]
fn turndown_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["turndown", "td_min", "td_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Turndown ratio: value 50 (50:1), valid range 10 (10:1) to 200 (200:1)
    ctx.push_obligation(ProofObligation::assume("td_val", "turndown == 50"));
    ctx.push_obligation(ProofObligation::assume("td_min_a", "td_min == 10"));
    ctx.push_obligation(ProofObligation::assume("td_max_a", "td_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "td_in_range",
        "turndown >= td_min && turndown <= td_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turndown ratio 50 (50:1) in range [10,200]");
}
