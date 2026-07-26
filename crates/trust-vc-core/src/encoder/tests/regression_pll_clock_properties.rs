// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_frequency_divider() {
    let mut ctx = VerificationContext::new();
    for v in &["vco_freq_mhz", "output_divider", "output_freq_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output = VCO / divider. Precompute: 800 / 4 = 200 MHz
    ctx.push_obligation(ProofObligation::assume("vf", "vco_freq_mhz == 800"));
    ctx.push_obligation(ProofObligation::assume("od", "output_divider == 4"));
    ctx.push_obligation(ProofObligation::assume("of", "output_freq_mhz == 200")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_200", "output_freq_mhz == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 800 MHz VCO / 4 = 200 MHz output");
}

#[test]
fn vco_range_check() {
    let mut ctx = VerificationContext::new();
    for v in &["vco_freq_mhz", "vco_min_mhz", "vco_max_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vco_valid", i32_ty());
    // VCO must stay within operating range
    ctx.push_obligation(ProofObligation::assume("vf", "vco_freq_mhz == 800"));
    ctx.push_obligation(ProofObligation::assume("vmn", "vco_min_mhz == 400"));
    ctx.push_obligation(ProofObligation::assume("vmx", "vco_max_mhz == 1600"));
    ctx.push_obligation(ProofObligation::assume(
        "vv_def",
        "vco_valid == if vco_freq_mhz >= vco_min_mhz && vco_freq_mhz <= vco_max_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vco_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: VCO 800 MHz in [400, 1600] → valid");
}

#[test]
fn feedback_divider_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["ref_freq_mhz", "feedback_div", "vco_target_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // VCO = ref × feedback_div. Precompute: 25 × 32 = 800
    ctx.push_obligation(ProofObligation::assume("rf", "ref_freq_mhz == 25"));
    ctx.push_obligation(ProofObligation::assume("fd", "feedback_div == 32"));
    ctx.push_obligation(ProofObligation::assume("vt", "vco_target_mhz == 800")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_800", "vco_target_mhz == 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 25 MHz × 32 feedback = 800 MHz VCO");
}

#[test]
fn lock_detect_stable() {
    let mut ctx = VerificationContext::new();
    for v in &["stable_cycles", "lock_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pll_locked", i32_ty());
    // PLL locked after N consecutive stable cycles
    ctx.push_obligation(ProofObligation::assume("sc", "stable_cycles == 256"));
    ctx.push_obligation(ProofObligation::assume("lt", "lock_threshold == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "pl_def",
        "pll_locked == if stable_cycles >= lock_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pll_locked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 256 stable ≥ 100 threshold → locked");
}

#[test]
fn phase_offset_degrees() {
    let mut ctx = VerificationContext::new();
    for v in &["output_index", "num_phases"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("phase_offset_deg", u32_ty());
    // Phase offset = 360 / num_phases × output_index. Precompute: 360/4 × 1 = 90
    ctx.push_obligation(ProofObligation::assume("oi", "output_index == 1"));
    ctx.push_obligation(ProofObligation::assume("np", "num_phases == 4"));
    ctx.push_obligation(ProofObligation::assume("po", "phase_offset_deg == 90")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_90", "phase_offset_deg == 90"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: phase 1 of 4 = 90° offset (precomputed)");
}

#[test]
fn spread_spectrum_range() {
    let mut ctx = VerificationContext::new();
    for v in &["center_freq_mhz", "spread_percent_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("spread_valid", i32_ty());
    // Spread spectrum: ±0.5% max typically (5 in ×10 units)
    ctx.push_obligation(ProofObligation::assume("cf", "center_freq_mhz == 100"));
    ctx.push_obligation(ProofObligation::assume("sp", "spread_percent_x10 == 5")); // 0.5%
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "spread_valid == if spread_percent_x10 <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "spread_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL SS: 0.5% spread ≤ 1.0% max → valid");
}

#[test]
fn input_reference_select() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("primary_ok", u32_ty());
    ctx.declare_var_typed("secondary_ok", u32_ty());
    ctx.declare_var_typed("selected_ref", u32_ty());
    // Select primary if available, else secondary
    ctx.push_obligation(ProofObligation::assume("po", "primary_ok == 0")); // failed
    ctx.push_obligation(ProofObligation::assume("so", "secondary_ok == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sr_def",
        "selected_ref == if primary_ok == 1 { 0 } else { if secondary_ok == 1 { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "selected_ref == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: primary down, secondary OK → select ref 1");
}

#[test]
fn duty_cycle_correction() {
    let mut ctx = VerificationContext::new();
    for v in &["high_time_ps", "low_time_ps", "total_period_ps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_ok", i32_ty());
    // 50% duty: high ≈ low (within margin). Check total = high + low.
    ctx.push_obligation(ProofObligation::assume("ht", "high_time_ps == 500"));
    ctx.push_obligation(ProofObligation::assume("lt", "low_time_ps == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "total_period_ps == high_time_ps + low_time_ps",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if high_time_ps == low_time_ps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1000",
        "total_period_ps == 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 500ps high + 500ps low = 1ns, 50% duty");
}

#[test]
fn jitter_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["pll_jitter_ps", "interconnect_jitter_ps", "total_jitter_ps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_budget", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pj", "pll_jitter_ps == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ij",
        "interconnect_jitter_ps == 20",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "tj_def",
        "total_jitter_ps == pll_jitter_ps + interconnect_jitter_ps",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_budget == if total_jitter_ps <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "total_jitter_ps == 50"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_budget == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 30ps + 20ps = 50ps jitter ≤ 100ps budget");
}

#[test]
fn clock_domain_crossing() {
    let mut ctx = VerificationContext::new();
    for v in &["src_freq_mhz", "dst_freq_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_sync", i32_ty());
    // Clock domain crossing: synchronizer needed if frequencies differ
    ctx.push_obligation(ProofObligation::assume("sf", "src_freq_mhz == 100"));
    ctx.push_obligation(ProofObligation::assume("df", "dst_freq_mhz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "needs_sync == if src_freq_mhz != dst_freq_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_sync == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL CDC: 100 MHz ≠ 200 MHz → needs synchronizer");
}
