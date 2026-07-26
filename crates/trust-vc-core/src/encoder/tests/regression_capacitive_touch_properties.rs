// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn touch_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["delta_count", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("touched", i32_ty());
    // Touch detected when capacitance delta exceeds threshold
    ctx.push_obligation(ProofObligation::assume("dc", "delta_count == 150"));
    ctx.push_obligation(ProofObligation::assume("th", "threshold == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "touched == if delta_count >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "touched == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: delta 150 ≥ 100 threshold → touched");
}

#[test]
fn baseline_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["current_count", "baseline", "drift_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drift_ok", i32_ty());
    // Baseline drift must stay within limits for reliable detection
    ctx.push_obligation(ProofObligation::assume("cc", "current_count == 1020"));
    ctx.push_obligation(ProofObligation::assume("bl", "baseline == 1000"));
    ctx.push_obligation(ProofObligation::assume("dl", "drift_limit == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "drift_ok == if current_count - baseline <= drift_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: drift 20 ≤ 50 limit → baseline OK");
}

#[test]
fn debounce_count() {
    let mut ctx = VerificationContext::new();
    for v in &["consecutive_touches", "debounce_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("confirmed", i32_ty());
    // Require N consecutive touch readings to confirm
    ctx.push_obligation(ProofObligation::assume("ct", "consecutive_touches == 4"));
    ctx.push_obligation(ProofObligation::assume("dt", "debounce_threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "confirmed == if consecutive_touches >= debounce_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "confirmed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: 4 consecutive ≥ 3 debounce → confirmed");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // Touch controller: 4-32 channels typical
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 12"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_channels == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if channels <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: 12 channels ≤ 32 max → count OK");
}

#[test]
fn scan_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["scan_hz", "min_scan_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Scan rate: fast enough for responsive touch (>50Hz typical)
    ctx.push_obligation(ProofObligation::assume("sh", "scan_hz == 100"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_scan_hz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if scan_hz >= min_scan_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: 100Hz scan ≥ 50Hz min → rate OK");
}

#[test]
fn sensitivity_level() {
    let mut ctx = VerificationContext::new();
    for v in &["sensitivity", "min_sensitivity", "max_sensitivity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sensitivity_ok", i32_ty());
    // Adjustable sensitivity: avoid too sensitive (false triggers) or too low (missed)
    ctx.push_obligation(ProofObligation::assume("s", "sensitivity == 5"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_sensitivity == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_sensitivity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sensitivity_ok == if sensitivity >= min_sensitivity && sensitivity <= max_sensitivity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sensitivity_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: sensitivity 5 in [1, 10] → OK");
}

#[test]
fn proximity_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["proximity_count", "proximity_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hand_near", i32_ty());
    // Proximity mode: detect hand approach before actual touch
    ctx.push_obligation(ProofObligation::assume("pc", "proximity_count == 30"));
    ctx.push_obligation(ProofObligation::assume("pt", "proximity_threshold == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "hn_def",
        "hand_near == if proximity_count >= proximity_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hand_near == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Cap touch: proximity 30 ≥ 20 threshold → hand near",
    );
}

#[test]
fn water_rejection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("water_guard", u32_ty());
    ctx.declare_var_typed("rejection_active", i32_ty());
    // Water/moisture rejection feature: 0=disabled, 1=enabled
    ctx.push_obligation(ProofObligation::assume("wg", "water_guard == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "rejection_active == if water_guard == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rejection_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: water_guard=1 → rejection active");
}

#[test]
fn slider_position() {
    let mut ctx = VerificationContext::new();
    for v in &["position", "max_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Touch slider: interpolated position 0-255
    ctx.push_obligation(ProofObligation::assume("p", "position == 128"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_position == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if position <= max_position { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: slider position 128 ≤ 255 max → valid");
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["active_ua", "max_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Low-power touch: important for battery devices
    ctx.push_obligation(ProofObligation::assume("au", "active_ua == 500"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_ua == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if active_ua <= max_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Cap touch: 500μA active ≤ 1000μA max → power OK");
}
