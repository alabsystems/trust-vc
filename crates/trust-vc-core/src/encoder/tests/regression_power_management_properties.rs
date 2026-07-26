// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sleep_mode_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("idle_ms", u32_ty());
    ctx.declare_var_typed("sleep_mode", u32_ty());
    // 0=Run, 1=Sleep, 2=Stop, 3=Standby
    // Select based on idle duration
    ctx.push_obligation(ProofObligation::assume("im", "idle_ms == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "sm_def",
        "sleep_mode == if idle_ms < 10 { 0 } else { if idle_ms < 1000 { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_sleep", "sleep_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM: 500ms idle → Sleep mode");
}

#[test]
fn voltage_scaling() {
    let mut ctx = VerificationContext::new();
    for v in &["performance_level", "voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DVFS: lower performance → lower voltage
    // Level 0=max (1200mV), 1=mid (1100mV), 2=low (1000mV)
    ctx.push_obligation(ProofObligation::assume("pl", "performance_level == 1"));
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 1100")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1100", "voltage_mv == 1100"));
    ctx.push_obligation(ProofObligation::assert("above_min", "voltage_mv >= 900")); // safety minimum
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DVFS: level 1 → 1100mV");
}

#[test]
fn wakeup_latency() {
    let mut ctx = VerificationContext::new();
    for v in &["current_mode", "wakeup_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_deadline", i32_ty());
    // Wakeup time depends on sleep depth
    // Sleep: 4us, Stop: 100us, Standby: 5000us
    ctx.push_obligation(ProofObligation::assume("cm", "current_mode == 1")); // Sleep
    ctx.push_obligation(ProofObligation::assume("wu", "wakeup_us == 4")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "md_def",
        "meets_deadline == if wakeup_us <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fast", "wakeup_us == 4"));
    ctx.push_obligation(ProofObligation::assert("ok", "meets_deadline == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM: Sleep wakeup 4us <= 10us deadline");
}

#[test]
fn battery_remaining() {
    let mut ctx = VerificationContext::new();
    for v in &["capacity_mah", "consumed_mah", "remaining_mah"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("low_battery", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "capacity_mah == 3000"));
    ctx.push_obligation(ProofObligation::assume("co", "consumed_mah == 2700"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining_mah == capacity_mah - consumed_mah",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "lb_def",
        "low_battery == if remaining_mah < 600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_300", "remaining_mah == 300"));
    ctx.push_obligation(ProofObligation::assert("yes", "low_battery == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "battery: 3000 - 2700 = 300mAh < 600 → low");
}

#[test]
fn clock_gating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("peripheral_active", u32_ty());
    ctx.declare_var_typed("clock_enabled", i32_ty());
    // Gate clock to inactive peripherals
    ctx.push_obligation(ProofObligation::assume("pa", "peripheral_active == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ce_def",
        "clock_enabled == if peripheral_active == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gated", "clock_enabled == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM: peripheral inactive → clock gated");
}

#[test]
fn thermal_throttle() {
    let mut ctx = VerificationContext::new();
    for v in &["temperature_c", "throttle_threshold_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("throttled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "temperature_c == 95"));
    ctx.push_obligation(ProofObligation::assume("tt", "throttle_threshold_c == 85"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "throttled == if temperature_c > throttle_threshold_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "throttled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM: 95°C > 85°C threshold → throttled");
}

#[test]
fn regulator_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["input_power_mw", "output_power_mw", "loss_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ip", "input_power_mw == 1000"));
    ctx.push_obligation(ProofObligation::assume("op", "output_power_mw == 900"));
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "loss_mw == input_power_mw - output_power_mw",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "loss_mw == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "not_terrible",
        "loss_mw < input_power_mw",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM regulator: 1000 - 900 = 100mW loss (90% eff)");
}

#[test]
fn power_domain_dependency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("core_domain_on", u32_ty());
    ctx.declare_var_typed("io_domain_on", u32_ty());
    ctx.declare_var_typed("config_valid", i32_ty());
    // IO domain requires core domain to be on
    ctx.push_obligation(ProofObligation::assume("cd", "core_domain_on == 1"));
    ctx.push_obligation(ProofObligation::assume("io", "io_domain_on == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "config_valid == if io_domain_on == 0 || core_domain_on == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "config_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM: IO on + core on → valid domain config");
}

#[test]
fn brown_out_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["vdd_mv", "bor_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("brown_out", i32_ty());
    ctx.push_obligation(ProofObligation::assume("v", "vdd_mv == 2500"));
    ctx.push_obligation(ProofObligation::assume("bt", "bor_threshold_mv == 2700"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "brown_out == if vdd_mv < bor_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "brown_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM: VDD 2500mV < 2700mV BOR → brown-out");
}

#[test]
fn retention_ram_sizing() {
    let mut ctx = VerificationContext::new();
    for v in &["total_ram", "retention_ram", "lost_on_sleep"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Only retention RAM preserved during deep sleep
    ctx.push_obligation(ProofObligation::assume("tr", "total_ram == 131072")); // 128KB
    ctx.push_obligation(ProofObligation::assume("rr", "retention_ram == 32768")); // 32KB
    ctx.push_obligation(ProofObligation::assume(
        "los_def",
        "lost_on_sleep == total_ram - retention_ram",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_98304",
        "lost_on_sleep == 98304",
    )); // 96KB
    ctx.push_obligation(ProofObligation::assert(
        "some_retained",
        "retention_ram > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PM: 128KB - 32KB retained = 96KB lost in sleep");
}
