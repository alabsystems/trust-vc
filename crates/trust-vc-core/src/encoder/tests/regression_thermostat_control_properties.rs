// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn setpoint_range() {
    let mut ctx = VerificationContext::new();
    for v in &["setpoint_x10", "min_sp_x10", "max_sp_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sp_ok", i32_ty());
    // Setpoint range (×10 for 0.1°C, offset +500 for negative temps)
    ctx.push_obligation(ProofObligation::assume("sx", "setpoint_x10 == 720")); // 22.0°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_sp_x10 == 550")); // 5.0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_sp_x10 == 850")); // 35.0°C
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sp_ok == if setpoint_x10 >= min_sp_x10 && setpoint_x10 <= max_sp_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 22.0°C setpoint in [5.0, 35.0] → OK");
}

#[test]
fn hysteresis_band() {
    let mut ctx = VerificationContext::new();
    for v in &["hyst_x10", "min_hyst_x10", "max_hyst_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hyst_ok", i32_ty());
    // Hysteresis band (×10 for 0.1°C): prevents rapid cycling
    ctx.push_obligation(ProofObligation::assume("hx", "hyst_x10 == 5")); // 0.5°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_hyst_x10 == 2")); // 0.2°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_hyst_x10 == 30")); // 3.0°C
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hyst_ok == if hyst_x10 >= min_hyst_x10 && hyst_x10 <= max_hyst_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hyst_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 0.5°C hysteresis in [0.2, 3.0] → OK");
}

#[test]
fn cycle_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles_per_hour", "max_cph"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cph_ok", i32_ty());
    // Compressor short-cycling protection
    ctx.push_obligation(ProofObligation::assume("ch", "cycles_per_hour == 6"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cph == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cph_ok == if cycles_per_hour <= max_cph { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cph_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 6 cycles/hr ≤ 10 max → OK");
}

#[test]
fn sensor_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["offset_x10", "max_offset_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("off_ok", i32_ty());
    // Temperature sensor calibration offset (×10 for 0.1°C)
    ctx.push_obligation(ProofObligation::assume("ox", "offset_x10 == 3")); // 0.3°C
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset_x10 == 20")); // 2.0°C
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "off_ok == if offset_x10 <= max_offset_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "off_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 0.3°C sensor offset ≤ 2.0°C max → OK");
}

#[test]
fn control_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Control modes: 0=off, 1=heat, 2=cool, 3=auto, 4=fan-only
    ctx.push_obligation(ProofObligation::assume("m", "mode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 0 || mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: mode=3 → valid auto mode");
}

#[test]
fn duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_pct", "max_duty_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_ok", i32_ty());
    // Modulating output duty cycle
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 75"));
    ctx.push_obligation(ProofObligation::assume("md", "max_duty_pct == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if duty_pct <= max_duty_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 75% duty ≤ 100% max → OK");
}

#[test]
fn stage_count() {
    let mut ctx = VerificationContext::new();
    for v in &["stages", "max_stages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stage_ok", i32_ty());
    // Multi-stage HVAC: 1-4 heating/cooling stages
    ctx.push_obligation(ProofObligation::assume("s", "stages == 2"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_stages == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stage_ok == if stages >= 1 && stages <= max_stages { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 2 stages in [1, 4] → OK");
}

#[test]
fn anticipator_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["antic_x100", "min_antic_x100", "max_antic_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("antic_ok", i32_ty());
    // Heat anticipator current (×100 for 0.01A resolution)
    ctx.push_obligation(ProofObligation::assume("ax", "antic_x100 == 40")); // 0.40A
    ctx.push_obligation(ProofObligation::assume("mn", "min_antic_x100 == 10")); // 0.10A
    ctx.push_obligation(ProofObligation::assume("mx", "max_antic_x100 == 120")); // 1.20A
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "antic_ok == if antic_x100 >= min_antic_x100 && antic_x100 <= max_antic_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "antic_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Thermostat: 0.40A anticipator in [0.10, 1.20] → OK",
    );
}

#[test]
fn differential_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["diff_x10", "min_diff_x10", "max_diff_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("diff_ok", i32_ty());
    // Switching differential (×10 for 0.1°C)
    ctx.push_obligation(ProofObligation::assume("dx", "diff_x10 == 10")); // 1.0°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_diff_x10 == 5")); // 0.5°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_diff_x10 == 50")); // 5.0°C
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "diff_ok == if diff_x10 >= min_diff_x10 && diff_x10 <= max_diff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "diff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 1.0°C differential in [0.5, 5.0] → OK");
}

#[test]
fn deadband() {
    let mut ctx = VerificationContext::new();
    for v in &["deadband_x10", "min_db_x10", "max_db_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("db_ok", i32_ty());
    // Deadband between heat and cool setpoints in auto mode (×10 for 0.1°C)
    ctx.push_obligation(ProofObligation::assume("dx", "deadband_x10 == 20")); // 2.0°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_db_x10 == 10")); // 1.0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_db_x10 == 50")); // 5.0°C
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "db_ok == if deadband_x10 >= min_db_x10 && deadband_x10 <= max_db_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "db_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Thermostat: 2.0°C deadband in [1.0, 5.0] → OK");
}
