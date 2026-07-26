// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gauge_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gauge", u32_ty());
    ctx.declare_var_typed("valid_gauge", i32_ty());
    // 1=Pirani, 2=cold cathode, 3=capacitance manometer, 4=hot cathode BA, 5=spinning rotor
    ctx.push_obligation(ProofObligation::assume("gy_val", "gauge == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "gy_valid_def",
        "valid_gauge == if gauge == 1 || gauge == 2 || gauge == 3 || gauge == 4 || gauge == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gy_check", "valid_gauge == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gauge type 3 (capacitance manometer) is valid");
}

#[test]
fn pressure_range_low() {
    let mut ctx = VerificationContext::new();
    for v in &["mpa", "mpa_min", "mpa_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pressure range low in mPa (millipascal): value 10, valid range 1 to 100000
    ctx.push_obligation(ProofObligation::assume("pl_val", "mpa == 10"));
    ctx.push_obligation(ProofObligation::assume("pl_min", "mpa_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pl_max", "mpa_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "pl_in_range",
        "mpa >= mpa_min && mpa <= mpa_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure range low 10 mPa in range [1,100000]");
}

#[test]
fn pressure_range_high() {
    let mut ctx = VerificationContext::new();
    for v in &["pa", "pa_min", "pa_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pressure range high in Pa: value 101325, valid range 1 to 200000
    ctx.push_obligation(ProofObligation::assume("ph_val", "pa == 101325"));
    ctx.push_obligation(ProofObligation::assume("ph_min", "pa_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ph_max", "pa_max == 200000"));
    ctx.push_obligation(ProofObligation::assert(
        "ph_in_range",
        "pa >= pa_min && pa <= pa_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure range high 101325 Pa in range [1,200000]");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x10", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy as x10 % of reading: value 50 (5.0%), valid range 1 (0.1%) to 300 (30.0%)
    ctx.push_obligation(ProofObligation::assume("ay_val", "acc_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume("ay_min", "acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ay_max", "acc_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "ay_in_range",
        "acc_x10 >= acc_min && acc_x10 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy 50 (5.0% rdg) in range [1,300] (0.1%-30.0%)",
    );
}

#[test]
fn setpoint_count() {
    let mut ctx = VerificationContext::new();
    for v in &["setpts", "sp_min", "sp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of setpoints: value 4, valid range 1 to 6
    ctx.push_obligation(ProofObligation::assume("sc_val", "setpts == 4"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "sp_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "sp_max == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_in_range",
        "setpts >= sp_min && setpts <= sp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "setpoint count 4 in range [1,6]");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // 1=analog 0-10V, 2=analog 1-10V log, 3=RS-485, 4=Profinet
    ctx.push_obligation(ProofObligation::assume("ot_val", "output == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_valid_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_check", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 2 (analog 1-10V log) is valid");
}

#[test]
fn gas_correction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", u32_ty());
    ctx.declare_var_typed("valid_gas", i32_ty());
    // 1=N2/air, 2=Ar, 3=He, 4=H2
    ctx.push_obligation(ProofObligation::assume("gc_val", "gas == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "gc_valid_def",
        "valid_gas == if gas == 1 || gas == 2 || gas == 3 || gas == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gc_check", "valid_gas == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas correction 1 (N2/air) is valid");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_ms", "resp_min", "resp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time in ms: value 100, valid range 1 to 5000
    ctx.push_obligation(ProofObligation::assume("rt_val", "resp_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "resp_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "resp_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "resp_ms >= resp_min && resp_ms <= resp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 100 ms in range [1,5000]");
}

#[test]
fn bakeout_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["bake_off", "bk_min", "bk_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bakeout temp offset +500: 150C=650, 450C=950, valid range 500 to 1000
    ctx.push_obligation(ProofObligation::assume("bk_val", "bake_off == 650"));
    ctx.push_obligation(ProofObligation::assume("bk_min_a", "bk_min == 500"));
    ctx.push_obligation(ProofObligation::assume("bk_max_a", "bk_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bk_in_range",
        "bake_off >= bk_min && bake_off <= bk_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bakeout temp 650 (150C+500 offset) in range [500,1000]",
    );
}

#[test]
fn relay_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("relay", u32_ty());
    ctx.declare_var_typed("valid_relay", i32_ty());
    // 1=SPDT, 2=open-collector, 3=solid-state
    ctx.push_obligation(ProofObligation::assume("ro_val", "relay == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_valid_def",
        "valid_relay == if relay == 1 || relay == 2 || relay == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ro_check", "valid_relay == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "relay output 3 (solid-state) is valid");
}
