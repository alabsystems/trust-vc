// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn differential_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vod_mv", "min_vod_mv", "max_vod_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vod_ok", i32_ty());
    // LVDS differential output voltage: 247-454mV (TIA/EIA-644)
    ctx.push_obligation(ProofObligation::assume("vm", "vod_mv == 350"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vod_mv == 247"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vod_mv == 454"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vod_ok == if vod_mv >= min_vod_mv && vod_mv <= max_vod_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vod_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: Vod 350mV in [247, 454] → compliant");
}

#[test]
fn common_mode_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vcm_mv", "min_vcm_mv", "max_vcm_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vcm_ok", i32_ty());
    // Common-mode output voltage: 1.125-1.375V
    ctx.push_obligation(ProofObligation::assume("vm", "vcm_mv == 1250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vcm_mv == 1125"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vcm_mv == 1375"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vcm_ok == if vcm_mv >= min_vcm_mv && vcm_mv <= max_vcm_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vcm_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: Vcm 1.25V in [1.125, 1.375] → OK");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_mbps", "max_rate_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // LVDS: up to 655 Mbps per pair (TIA/EIA-644)
    ctx.push_obligation(ProofObligation::assume("rm", "rate_mbps == 400"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rate_mbps == 655"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_mbps <= max_rate_mbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: 400 Mbps ≤ 655 Mbps max → rate OK");
}

#[test]
fn termination_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["term_ohms", "target_ohms", "tolerance_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("term_ok", i32_ty());
    // Receiver-end termination: 100Ω ± 10%
    ctx.push_obligation(ProofObligation::assume("to", "term_ohms == 105"));
    ctx.push_obligation(ProofObligation::assume("ta", "target_ohms == 100"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_ohms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "term_ok == if term_ohms >= target_ohms - tolerance_ohms && term_ohms <= target_ohms + tolerance_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "term_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: 105Ω termination in [90, 110] → OK");
}

#[test]
fn receiver_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["input_diff_mv", "threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_signal", i32_ty());
    // Receiver input threshold: ±100mV minimum
    ctx.push_obligation(ProofObligation::assume("id", "input_diff_mv == 200"));
    ctx.push_obligation(ProofObligation::assume("tm", "threshold_mv == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_signal == if input_diff_mv >= threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_signal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LVDS: 200mV differential ≥ 100mV threshold → valid",
    );
}

#[test]
fn cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // LVDS cable: up to 10m typical at full speed
    ctx.push_obligation(ProofObligation::assume("lm", "length_m == 5"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_length_m == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: 5m cable ≤ 10m max → length OK");
}

#[test]
fn pair_count() {
    let mut ctx = VerificationContext::new();
    for v in &["pairs", "max_pairs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pairs_ok", i32_ty());
    // Multi-pair LVDS (e.g., FPD-Link, LVDS serializer/deserializer)
    ctx.push_obligation(ProofObligation::assume("p", "pairs == 4"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pairs == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pairs_ok == if pairs <= max_pairs { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pairs_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: 4 pairs ≤ 8 max → pair count OK");
}

#[test]
fn driver_current() {
    let mut ctx = VerificationContext::new();
    for v in &["driver_ma_x10", "min_ma_x10", "max_ma_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // LVDS driver current: 2.47-4.54mA (×10 scale)
    ctx.push_obligation(ProofObligation::assume("dm", "driver_ma_x10 == 35")); // 3.5mA
    ctx.push_obligation(ProofObligation::assume("mn", "min_ma_x10 == 24")); // 2.4mA
    ctx.push_obligation(ProofObligation::assume("mx", "max_ma_x10 == 45")); // 4.5mA
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if driver_ma_x10 >= min_ma_x10 && driver_ma_x10 <= max_ma_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: 3.5mA driver in [2.4, 4.5] → current OK");
}

#[test]
fn jitter_spec() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ps", "max_jitter_ps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("jitter_ok", i32_ty());
    // Deterministic jitter: must be below eye diagram budget
    ctx.push_obligation(ProofObligation::assume("jp", "jitter_ps == 50"));
    ctx.push_obligation(ProofObligation::assume("mj", "max_jitter_ps == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "jo_def",
        "jitter_ok == if jitter_ps <= max_jitter_ps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "jitter_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: 50ps jitter ≤ 200ps max → OK");
}

#[test]
fn power_per_pair() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "max_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // LVDS low-power: ~1.2mW per differential pair
    ctx.push_obligation(ProofObligation::assume("pm", "power_mw == 1"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_mw == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_mw <= max_power_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDS: 1mW/pair ≤ 5mW max → power OK");
}
