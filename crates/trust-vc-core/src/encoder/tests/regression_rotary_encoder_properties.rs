// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pulses_per_revolution() {
    let mut ctx = VerificationContext::new();
    for v in &["ppr", "min_ppr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resolution_ok", i32_ty());
    // PPR: pulses per revolution (e.g., 1000, 2000, 4096)
    ctx.push_obligation(ProofObligation::assume("p", "ppr == 2000"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_ppr == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resolution_ok == if ppr >= min_ppr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resolution_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: 2000 PPR ≥ 1000 min → resolution OK");
}

#[test]
fn quadrature_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ppr", "edges_per_pulse"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("counts_per_rev", u32_ty());
    // Quadrature: 4× counting (both edges of A and B channels)
    // CPR = PPR × 4. Precompute: 1000 × 4 = 4000
    ctx.push_obligation(ProofObligation::assume("p", "ppr == 1000"));
    ctx.push_obligation(ProofObligation::assume("ep", "edges_per_pulse == 4"));
    ctx.push_obligation(ProofObligation::assume("cr", "counts_per_rev == 4000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4000", "counts_per_rev == 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: 1000 PPR × 4 = 4000 CPR (precomputed)");
}

#[test]
fn direction_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a_leads_b", u32_ty());
    ctx.declare_var_typed("is_clockwise", i32_ty());
    // Quadrature: A leading B = clockwise (0=B leads A, 1=A leads B)
    ctx.push_obligation(ProofObligation::assume("al", "a_leads_b == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_clockwise == if a_leads_b == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_clockwise == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: A leads B → clockwise rotation");
}

#[test]
fn position_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["old_count", "delta", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Position accumulation
    ctx.push_obligation(ProofObligation::assume("oc", "old_count == 15000"));
    ctx.push_obligation(ProofObligation::assume("d", "delta == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_count == old_count + delta",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15500", "new_count == 15500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: 15000 + 500 = 15500 count position");
}

#[test]
fn max_speed_rpm() {
    let mut ctx = VerificationContext::new();
    for v in &["shaft_rpm", "max_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Encoder max mechanical speed
    ctx.push_obligation(ProofObligation::assume("sr", "shaft_rpm == 5000"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rpm == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if shaft_rpm <= max_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: 5000 RPM ≤ 10000 max → speed OK");
}

#[test]
fn index_pulse() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_index", u32_ty());
    ctx.declare_var_typed("can_home", i32_ty());
    // Z/index channel: one pulse per revolution for absolute reference
    ctx.push_obligation(ProofObligation::assume("hi", "has_index == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ch_def",
        "can_home == if has_index == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_home == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: has index pulse → can home");
}

#[test]
fn output_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["rpm", "ppr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_freq_hz", u32_ty());
    // Output freq = RPM × PPR / 60. Precompute: 3000 × 1000 / 60 = 50000 Hz
    ctx.push_obligation(ProofObligation::assume("r", "rpm == 3000"));
    ctx.push_obligation(ProofObligation::assume("p", "ppr == 1000"));
    ctx.push_obligation(ProofObligation::assume("of", "output_freq_hz == 50000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_50k", "output_freq_hz == 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Encoder: 3000 RPM × 1000 PPR / 60 = 50 kHz (precomputed)",
    );
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_supply_mv", "max_supply_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("supply_ok", i32_ty());
    // Encoder supply: typically 5V or 5-24V
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_supply_mv == 4750"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_supply_mv == 5250"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "supply_ok == if supply_mv >= min_supply_mv && supply_mv <= max_supply_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "supply_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: 5V in [4.75, 5.25] → supply OK");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_mode", u32_ty());
    ctx.declare_var_typed("is_differential", i32_ty());
    // Output: 0=open collector, 1=push-pull (TTL), 2=differential (RS-422)
    ctx.push_obligation(ProofObligation::assume("om", "output_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_differential == if output_mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_differential == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Encoder: output_mode=2 → differential (RS-422)");
}

#[test]
fn position_within_revolution() {
    let mut ctx = VerificationContext::new();
    for v in &["current_count", "counts_per_rev"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_rev", i32_ty());
    // Single-revolution position must be < CPR
    ctx.push_obligation(ProofObligation::assume("cc", "current_count == 3500"));
    ctx.push_obligation(ProofObligation::assume("cr", "counts_per_rev == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "wr_def",
        "within_rev == if current_count < counts_per_rev { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_rev == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Encoder: 3500 count < 4000 CPR → within revolution",
    );
}
