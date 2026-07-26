// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ldo_dropout_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mv", "output_mv", "dropout_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("regulating", i32_ty());
    // LDO: needs Vin > Vout + dropout
    ctx.push_obligation(ProofObligation::assume("im", "input_mv == 3600"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("dm", "dropout_mv == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "regulating == if input_mv > output_mv + dropout_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "regulating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LDO: 3600mV > 3300+200 = 3500mV → regulating");
}

#[test]
fn buck_duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "vin_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_percent", u32_ty());
    // Buck: duty = Vout/Vin × 100. Precompute: 3300/12000 × 100 = 27 (truncated)
    ctx.push_obligation(ProofObligation::assume("vo", "vout_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("vi", "vin_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("dp", "duty_percent == 27")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_27", "duty_percent == 27"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck: 3300/12000 ≈ 27% duty cycle (precomputed)");
}

#[test]
fn output_voltage_tolerance() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_mv", "nominal_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_spec", i32_ty());
    // Within spec: |measured - nominal| ≤ tolerance
    // Use: measured ≥ nominal - tolerance && measured ≤ nominal + tolerance
    ctx.push_obligation(ProofObligation::assume("mm", "measured_mv == 3280"));
    ctx.push_obligation(ProofObligation::assume("nm", "nominal_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("tm", "tolerance_mv == 33")); // 1%
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_spec == if measured_mv >= nominal_mv - tolerance_mv && measured_mv <= nominal_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: 3280mV in [3267, 3333] → within 1% spec");
}

#[test]
fn overcurrent_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["load_current_ma", "ocp_threshold_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ocp_triggered", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lc", "load_current_ma == 1200"));
    ctx.push_obligation(ProofObligation::assume("ot", "ocp_threshold_ma == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ocp_def",
        "ocp_triggered == if load_current_ma > ocp_threshold_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ocp_triggered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: 1200mA > 1000mA OCP → triggered");
}

#[test]
fn thermal_shutdown() {
    let mut ctx = VerificationContext::new();
    for v in &["junction_temp_mc", "shutdown_temp_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shutdown", i32_ty());
    // Thermal shutdown at 150°C = 150000 m°C
    ctx.push_obligation(ProofObligation::assume("jt", "junction_temp_mc == 155000"));
    ctx.push_obligation(ProofObligation::assume("st", "shutdown_temp_mc == 150000"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "shutdown == if junction_temp_mc >= shutdown_temp_mc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: 155°C ≥ 150°C → thermal shutdown");
}

#[test]
fn power_good_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["stable_time_ms", "pg_delay_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_good", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "stable_time_ms == 20"));
    ctx.push_obligation(ProofObligation::assume("pd", "pg_delay_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "pg_def",
        "power_good == if stable_time_ms >= pg_delay_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_good == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: 20ms stable ≥ 10ms delay → power good");
}

#[test]
fn sequencing_order() {
    let mut ctx = VerificationContext::new();
    for v in &["rail_1_ready", "rail_2_ready"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_enable_rail3", i32_ty());
    // Power sequencing: rail 3 requires rail 1 and rail 2 ready
    ctx.push_obligation(ProofObligation::assume("r1", "rail_1_ready == 1"));
    ctx.push_obligation(ProofObligation::assume("r2", "rail_2_ready == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ce_def",
        "can_enable_rail3 == if rail_1_ready == 1 && rail_2_ready == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_enable_rail3 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: rail 1+2 ready → can enable rail 3");
}

#[test]
fn efficiency_check() {
    let mut ctx = VerificationContext::new();
    for v in &["output_power_mw", "input_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("efficiency_percent", u32_ty());
    // Efficiency = Pout/Pin × 100. Precompute: 8500/10000 × 100 = 85
    ctx.push_obligation(ProofObligation::assume("op", "output_power_mw == 8500"));
    ctx.push_obligation(ProofObligation::assume("ip", "input_power_mw == 10000"));
    ctx.push_obligation(ProofObligation::assume("ep", "efficiency_percent == 85")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_85", "efficiency_percent == 85"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: 8500/10000 = 85% efficiency (precomputed)");
}

#[test]
fn soft_start_ramp() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed_ms", "soft_start_ms", "target_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ramp_complete", i32_ty());
    ctx.push_obligation(ProofObligation::assume("em", "elapsed_ms == 15"));
    ctx.push_obligation(ProofObligation::assume("ssm", "soft_start_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "ramp_complete == if elapsed_ms >= soft_start_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ramp_complete == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: 15ms ≥ 10ms soft start → ramp complete");
}

#[test]
fn input_undervoltage_lockout() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_mv", "uvlo_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("uvlo_active", i32_ty());
    // UVLO: regulator shuts down when input drops below threshold
    ctx.push_obligation(ProofObligation::assume("vm", "vin_mv == 2800"));
    ctx.push_obligation(ProofObligation::assume("ut", "uvlo_threshold_mv == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "ua_def",
        "uvlo_active == if vin_mv < uvlo_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "uvlo_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VREG: Vin 2800mV < UVLO 3000mV → shutdown");
}
