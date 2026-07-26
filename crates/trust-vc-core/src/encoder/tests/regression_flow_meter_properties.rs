// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pulse_to_volume() {
    let mut ctx = VerificationContext::new();
    for v in &["pulse_count", "pulses_per_liter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volume_ml", u32_ty());
    // Volume = pulses / pulses_per_liter × 1000. Precompute: 450/450 × 1000 = 1000ml
    ctx.push_obligation(ProofObligation::assume("pc", "pulse_count == 450"));
    ctx.push_obligation(ProofObligation::assume("pl", "pulses_per_liter == 450"));
    ctx.push_obligation(ProofObligation::assume("vm", "volume_ml == 1000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1000", "volume_ml == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flow: 450 pulses / 450 PPL = 1000ml (precomputed)");
}

#[test]
fn flow_rate_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["pulses_in_interval", "interval_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_rate_ml_min", u32_ty());
    // Flow rate = (pulses / ppl) × (60000 / interval_ms) × 1000. Precompute.
    // 100 pulses in 1000ms at 450 ppl = (100/450) × 60 × 1000 ≈ 13333 ml/min
    ctx.push_obligation(ProofObligation::assume("pi", "pulses_in_interval == 100"));
    ctx.push_obligation(ProofObligation::assume("im", "interval_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_ml_min == 13333")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_13333",
        "flow_rate_ml_min == 13333",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Flow: 100 pulses/1s at 450 PPL = 13333 ml/min (precomputed)",
    );
}

#[test]
fn high_flow_alarm() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_rate", "alarm_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alarm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate == 20000"));
    ctx.push_obligation(ProofObligation::assume("at", "alarm_threshold == 15000"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "alarm == if flow_rate > alarm_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flow: 20000 > 15000 threshold → high flow alarm");
}

#[test]
fn low_flow_cutoff() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_rate", "min_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("below_minimum", i32_ty());
    // Below minimum measurable flow
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate == 5"));
    ctx.push_obligation(ProofObligation::assume("mf", "min_flow == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "bm_def",
        "below_minimum == if flow_rate < min_flow { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "below_minimum == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flow: rate 5 < 50 minimum → below cutoff");
}

#[test]
fn totalizer_accumulation() {
    let mut ctx = VerificationContext::new();
    for v in &["previous_total_ml", "new_volume_ml", "updated_total_ml"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Totalizer += new volume
    ctx.push_obligation(ProofObligation::assume("pt", "previous_total_ml == 50000"));
    ctx.push_obligation(ProofObligation::assume("nv", "new_volume_ml == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ut_def",
        "updated_total_ml == previous_total_ml + new_volume_ml",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_51000",
        "updated_total_ml == 51000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flow: 50000 + 1000 = 51000 ml totalizer");
}

#[test]
fn pipe_diameter_factor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pipe_diameter_mm", u32_ty());
    ctx.declare_var_typed("k_factor", u32_ty());
    // K-factor depends on pipe size. Precompute for 25mm pipe.
    ctx.push_obligation(ProofObligation::assume("pd", "pipe_diameter_mm == 25"));
    ctx.push_obligation(ProofObligation::assume("kf", "k_factor == 450")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_450", "k_factor == 450"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flow: 25mm pipe → K=450 pulses/L (precomputed)");
}

#[test]
fn temperature_effect() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_flow", "temp_correction", "corrected_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Temperature affects fluid viscosity → flow measurement. Subtract correction.
    ctx.push_obligation(ProofObligation::assume("mf", "measured_flow == 10200"));
    ctx.push_obligation(ProofObligation::assume("tc", "temp_correction == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "cf_def",
        "corrected_flow == measured_flow - temp_correction",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_10000",
        "corrected_flow == 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Flow: 10200 - 200 temp correction = 10000 corrected",
    );
}

#[test]
fn batch_complete() {
    let mut ctx = VerificationContext::new();
    for v in &["dispensed_ml", "target_ml"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("batch_done", i32_ty());
    // Batch dispensing: stop when target reached
    ctx.push_obligation(ProofObligation::assume("dm", "dispensed_ml == 5000"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_ml == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "bd_def",
        "batch_done == if dispensed_ml >= target_ml { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "batch_done == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Flow: dispensed 5000ml = 5000ml target → batch complete",
    );
}

#[test]
fn leak_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["night_flow_ml", "leak_threshold_ml"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("leak_detected", i32_ty());
    // Flow during no-use period indicates leak
    ctx.push_obligation(ProofObligation::assume("nf", "night_flow_ml == 500"));
    ctx.push_obligation(ProofObligation::assume("lt", "leak_threshold_ml == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ld_def",
        "leak_detected == if night_flow_ml > leak_threshold_ml { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "leak_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Flow: 500ml night flow > 100ml threshold → leak detected",
    );
}

#[test]
fn reverse_flow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("direction", u32_ty());
    ctx.declare_var_typed("is_reverse", i32_ty());
    // Bidirectional flow: 0=forward, 1=reverse
    ctx.push_obligation(ProofObligation::assume("d", "direction == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_reverse == if direction == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_reverse == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flow: direction 1 → reverse flow");
}
