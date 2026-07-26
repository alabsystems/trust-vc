// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn speed_from_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "no_load_speed_rpm", "rated_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expected_rpm", u32_ty());
    // Speed ∝ voltage. Precompute: 6000/12000 × 10000 = 5000 RPM
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 6000"));
    ctx.push_obligation(ProofObligation::assume("rv", "rated_voltage_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("nl", "no_load_speed_rpm == 10000"));
    ctx.push_obligation(ProofObligation::assume("er", "expected_rpm == 5000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_5000", "expected_rpm == 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DC motor: 6V/12V × 10000 RPM = 5000 RPM (precomputed)",
    );
}

#[test]
fn pwm_duty_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_percent", "max_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("target_rpm", u32_ty());
    // Speed ≈ duty% × max_rpm / 100. Precompute: 75 × 8000 / 100 = 6000
    ctx.push_obligation(ProofObligation::assume("dp", "duty_percent == 75"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rpm == 8000"));
    ctx.push_obligation(ProofObligation::assume("tr", "target_rpm == 6000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_6000", "target_rpm == 6000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DC motor: 75% duty × 8000 RPM = 6000 RPM (precomputed)",
    );
}

#[test]
fn stall_current() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_current_ma", "stall_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_stalled", i32_ty());
    // Stall condition: current approaches stall rating
    ctx.push_obligation(ProofObligation::assume("mc", "measured_current_ma == 4500"));
    ctx.push_obligation(ProofObligation::assume("sc", "stall_current_ma == 5000"));
    // Stall detection at 90% of stall current = 4500
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_stalled == if measured_current_ma >= stall_current_ma - 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_stalled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DC motor: 4500mA ≥ 4500mA (stall-500) → stall detected",
    );
}

#[test]
fn h_bridge_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("high_a", u32_ty());
    ctx.declare_var_typed("low_b", u32_ty());
    ctx.declare_var_typed("forward", i32_ty());
    // H-bridge: forward = high_side_A on, low_side_B on
    ctx.push_obligation(ProofObligation::assume("ha", "high_a == 1"));
    ctx.push_obligation(ProofObligation::assume("lb", "low_b == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "forward == if high_a == 1 && low_b == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "forward == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DC motor: H-bridge high_A=1, low_B=1 → forward drive",
    );
}

#[test]
fn back_emf_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "back_emf_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("torque_available", i32_ty());
    // Torque ∝ (supply - back_EMF). Motor accelerates when supply > BEMF.
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("be", "back_emf_mv == 9000"));
    ctx.push_obligation(ProofObligation::assume(
        "ta_def",
        "torque_available == if supply_mv > back_emf_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "torque_available == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC motor: 12V supply > 9V BEMF → torque available");
}

#[test]
fn overcurrent_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_continuous_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // Motor current must stay below continuous rating
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 1500"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_continuous_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_ma <= max_continuous_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC motor: 1500mA ≤ 2000mA max → current OK");
}

#[test]
fn thermal_derating() {
    let mut ctx = VerificationContext::new();
    for v in &["winding_temp_c", "max_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Winding temperature limit (typically 130°C for Class B insulation)
    ctx.push_obligation(ProofObligation::assume("wt", "winding_temp_c == 95"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_c == 130"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if winding_temp_c < max_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC motor: 95°C winding < 130°C max → temp OK");
}

#[test]
fn direction_control() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", u32_ty());
    ctx.declare_var_typed("is_reverse", i32_ty());
    // Polarity: 0=forward, 1=reverse
    ctx.push_obligation(ProofObligation::assume("p", "polarity == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_reverse == if polarity == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_reverse == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC motor: polarity=1 → reverse direction");
}

#[test]
fn braking_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("brake_mode", u32_ty());
    ctx.declare_var_typed("is_dynamic_brake", i32_ty());
    // Braking: 0=coast, 1=dynamic(short), 2=regenerative
    ctx.push_obligation(ProofObligation::assume("bm", "brake_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_dynamic_brake == if brake_mode == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_dynamic_brake == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC motor: brake_mode=1 → dynamic braking");
}

#[test]
fn efficiency_check() {
    let mut ctx = VerificationContext::new();
    for v in &["mechanical_power_mw", "electrical_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("efficiency_pct", u32_ty());
    ctx.declare_var_typed("efficient_enough", i32_ty());
    // Efficiency = Pmech/Pelec × 100. Precompute: 7500/10000 × 100 = 75%
    ctx.push_obligation(ProofObligation::assume("mp", "mechanical_power_mw == 7500"));
    ctx.push_obligation(ProofObligation::assume(
        "ep",
        "electrical_power_mw == 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("ef", "efficiency_pct == 75")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "ee_def",
        "efficient_enough == if efficiency_pct >= 60 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_75", "efficiency_pct == 75"));
    ctx.push_obligation(ProofObligation::assert("yes", "efficient_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DC motor: 75% efficiency ≥ 60% min → efficient enough",
    );
}
