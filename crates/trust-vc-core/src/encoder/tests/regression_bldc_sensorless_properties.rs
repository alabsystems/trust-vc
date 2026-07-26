// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bemf_zero_crossing() {
    let mut ctx = VerificationContext::new();
    for v in &["bemf_mv", "threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("zc_detected", i32_ty());
    // Back-EMF zero crossing for commutation timing
    ctx.push_obligation(ProofObligation::assume("bm", "bemf_mv == 50"));
    ctx.push_obligation(ProofObligation::assume("tm", "threshold_mv == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "zc_def",
        "zc_detected == if bemf_mv <= threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zc_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLDC sensorless: BEMF 50mV ≤ 100mV threshold → ZC detected",
    );
}

#[test]
fn commutation_step() {
    let mut ctx = VerificationContext::new();
    for v in &["step", "max_steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("step_valid", i32_ty());
    // Six-step commutation: steps 0-5
    ctx.push_obligation(ProofObligation::assume("s", "step == 3"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_steps == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "step_valid == if step <= max_steps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "step_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLDC sensorless: step 3 ≤ 5 → valid commutation step",
    );
}

#[test]
fn startup_ramp() {
    let mut ctx = VerificationContext::new();
    for v in &["ramp_rpm", "min_bemf_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bemf_usable", i32_ty());
    // Open-loop startup ramp until BEMF is detectable
    ctx.push_obligation(ProofObligation::assume("rr", "ramp_rpm == 500"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bemf_rpm == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "bu_def",
        "bemf_usable == if ramp_rpm >= min_bemf_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bemf_usable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC sensorless: 500 RPM ≥ 300 min → BEMF usable");
}

#[test]
fn duty_cycle_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_pct", "max_duty_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_ok", i32_ty());
    // PWM duty cycle for speed control
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 75"));
    ctx.push_obligation(ProofObligation::assume("md", "max_duty_pct == 95"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if duty_pct <= max_duty_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC sensorless: 75% duty ≤ 95% max → OK");
}

#[test]
fn bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vbus_mv", "min_vbus_mv", "max_vbus_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vbus_ok", i32_ty());
    // DC bus voltage range
    ctx.push_obligation(ProofObligation::assume("vm", "vbus_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vbus_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vbus_mv == 48000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vbus_ok == if vbus_mv >= min_vbus_mv && vbus_mv <= max_vbus_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vbus_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC sensorless: 24V bus in [10, 48] → voltage OK");
}

#[test]
fn phase_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // Phase current within motor/driver rating
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 5000")); // 5A
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ma == 10000")); // 10A
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_ma <= max_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC sensorless: 5A phase ≤ 10A max → current OK");
}

#[test]
fn blanking_time() {
    let mut ctx = VerificationContext::new();
    for v in &["blanking_us", "min_blanking_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("blank_ok", i32_ty());
    // Blanking time after commutation to ignore BEMF noise
    ctx.push_obligation(ProofObligation::assume("bu", "blanking_us == 30"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_blanking_us == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "blank_ok == if blanking_us >= min_blanking_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blank_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC sensorless: 30μs blanking ≥ 10μs min → OK");
}

#[test]
fn speed_from_period() {
    let mut ctx = VerificationContext::new();
    for v in &["electrical_period_us", "pole_pairs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rpm", u32_ty());
    // RPM = 60e6 / (period_us × pole_pairs). Precompute: 60000000/(5000×4) = 3000
    ctx.push_obligation(ProofObligation::assume(
        "ep",
        "electrical_period_us == 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("pp", "pole_pairs == 4"));
    ctx.push_obligation(ProofObligation::assume("r", "rpm == 3000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_3000", "rpm == 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLDC sensorless: period 5ms, 4 poles → 3000 RPM (precomputed)",
    );
}

#[test]
fn overcurrent_fault() {
    let mut ctx = VerificationContext::new();
    for v in &["sense_mv", "fault_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("oc_fault", i32_ty());
    // Current sense resistor → voltage → fault
    ctx.push_obligation(ProofObligation::assume("sm", "sense_mv == 600"));
    ctx.push_obligation(ProofObligation::assume("ft", "fault_threshold_mv == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "of_def",
        "oc_fault == if sense_mv >= fault_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "oc_fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLDC sensorless: 600mV sense ≥ 500mV threshold → OC fault",
    );
}

#[test]
fn demagnetization_time() {
    let mut ctx = VerificationContext::new();
    for v in &["demag_us", "max_demag_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("demag_ok", i32_ty());
    // Demagnetization time must complete before next commutation
    ctx.push_obligation(ProofObligation::assume("du", "demag_us == 100"));
    ctx.push_obligation(ProofObligation::assume("md", "max_demag_us == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "demag_ok == if demag_us <= max_demag_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "demag_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC sensorless: 100μs demag ≤ 200μs max → OK");
}
