// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn duty_cycle_percentage() {
    let mut ctx = VerificationContext::new();
    for v in &["period_ticks", "on_ticks", "duty_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // duty_pct = on_ticks * 100 / period_ticks — precomputed
    ctx.push_obligation(ProofObligation::assume("pt", "period_ticks == 1000"));
    ctx.push_obligation(ProofObligation::assume("ot", "on_ticks == 750"));
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 75")); // 750/1000*100
    ctx.push_obligation(ProofObligation::assert("is_75", "duty_pct == 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PWM: 750/1000 = 75% duty cycle");
}

#[test]
fn frequency_from_period() {
    let mut ctx = VerificationContext::new();
    for v in &["timer_clock_hz", "period_ticks", "pwm_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tc", "timer_clock_hz == 1000000")); // 1MHz
    ctx.push_obligation(ProofObligation::assume("pt", "period_ticks == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "pf_def",
        "pwm_freq_hz == timer_clock_hz / period_ticks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1000", "pwm_freq_hz == 1000")); // 1kHz
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PWM freq: 1MHz/1000=1kHz");
}

#[test]
fn dead_time_insertion() {
    let mut ctx = VerificationContext::new();
    for v in &["on_ticks", "dead_time_ticks", "effective_on"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ot", "on_ticks == 500"));
    ctx.push_obligation(ProofObligation::assume("dt", "dead_time_ticks == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "effective_on == on_ticks - dead_time_ticks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_490", "effective_on == 490"));
    ctx.push_obligation(ProofObligation::assert(
        "reduced",
        "effective_on < on_ticks",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PWM dead time: 500-10=490 effective on");
}

#[test]
fn complementary_outputs() {
    let mut ctx = VerificationContext::new();
    for v in &["period", "ch_a_on", "ch_b_on"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("complementary", i32_ty());
    // Complementary: ch_b_on = period - ch_a_on
    ctx.push_obligation(ProofObligation::assume("p", "period == 1000"));
    ctx.push_obligation(ProofObligation::assume("ca", "ch_a_on == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "cb_def",
        "ch_b_on == period - ch_a_on",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "complementary == if ch_a_on + ch_b_on == period { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "ch_b_on == 400"));
    ctx.push_obligation(ProofObligation::assert("ok", "complementary == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PWM complementary: 600+400=1000");
}

#[test]
fn center_aligned_peak() {
    let mut ctx = VerificationContext::new();
    for v in &["period", "compare_value", "first_edge", "second_edge"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Center-aligned: count up to period, then down. First edge at compare, second at period*2-compare
    ctx.push_obligation(ProofObligation::assume("p", "period == 1000"));
    ctx.push_obligation(ProofObligation::assume("cv", "compare_value == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "first_edge == compare_value",
    )); // on up-count
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "second_edge == 2 * period - compare_value",
    ));
    ctx.push_obligation(ProofObligation::assert("fe_300", "first_edge == 300"));
    ctx.push_obligation(ProofObligation::assert("se_1700", "second_edge == 1700")); // 2000-300
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PWM center: edges at 300 and 1700");
}

#[test]
fn prescaler_effect() {
    let mut ctx = VerificationContext::new();
    for v in &["base_clock_hz", "prescaler", "timer_clock_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bc", "base_clock_hz == 72000000")); // 72MHz
    ctx.push_obligation(ProofObligation::assume("ps", "prescaler == 72"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "timer_clock_hz == base_clock_hz / prescaler",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1mhz",
        "timer_clock_hz == 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PWM prescaler: 72MHz/72=1MHz");
}

#[test]
fn resolution_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["period_ticks", "resolution_levels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Resolution ≈ period_ticks + 1 levels (0 to period)
    ctx.push_obligation(ProofObligation::assume("pt", "period_ticks == 1023")); // 10-bit
    ctx.push_obligation(ProofObligation::assume(
        "rl_def",
        "resolution_levels == period_ticks + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1024",
        "resolution_levels == 1024",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PWM: 1023+1=1024 levels (10-bit)");
}

#[test]
fn output_compare_match() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "compare_reg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("match_event", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cnt", "counter == 500"));
    ctx.push_obligation(ProofObligation::assume("cr", "compare_reg == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "me_def",
        "match_event == if counter == compare_reg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("match", "match_event == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PWM: counter 500 == compare 500 → match");
}

#[test]
fn pwm_servo_pulse_width() {
    // Servo: 1ms=0°, 1.5ms=90°, 2ms=180° at 50Hz (20ms period)
    let mut ctx = VerificationContext::new();
    for v in &["period_us", "pulse_us", "angle_target"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pu", "period_us == 20000")); // 50Hz
    ctx.push_obligation(ProofObligation::assume("pw", "pulse_us == 1500")); // 90°
    ctx.push_obligation(ProofObligation::assume("at", "angle_target == 90"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_range == if pulse_us >= 1000 && pulse_us <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PWM servo: 1500µs in [1000,2000] → valid");
}

#[test]
fn soft_start_ramp() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "initial_duty",
        "step_size",
        "steps_taken",
        "current_duty",
        "max_duty",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_target", i32_ty());
    ctx.push_obligation(ProofObligation::assume("id", "initial_duty == 0"));
    ctx.push_obligation(ProofObligation::assume("ss", "step_size == 10"));
    ctx.push_obligation(ProofObligation::assume("st", "steps_taken == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "cd_def",
        "current_duty == initial_duty + step_size * steps_taken",
    ));
    ctx.push_obligation(ProofObligation::assume("md", "max_duty == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "at_def",
        "at_target == if current_duty >= max_duty { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "current_duty == 500"));
    ctx.push_obligation(ProofObligation::assert("reached", "at_target == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PWM ramp: 0+10×50=500 → at target");
}
