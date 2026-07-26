// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sensing_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["distance_mm", "rated_distance_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("detected", i32_ty());
    // Inductive proximity: detect metal within sensing range
    ctx.push_obligation(ProofObligation::assume("dm", "distance_mm == 3"));
    ctx.push_obligation(ProofObligation::assume("rd", "rated_distance_mm == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "detected == if distance_mm <= rated_distance_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: 3mm ≤ 5mm rated → target detected");
}

#[test]
fn hysteresis_band() {
    let mut ctx = VerificationContext::new();
    for v in &["operate_distance_mm", "release_distance_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_hysteresis", i32_ty());
    // Hysteresis prevents chatter: release > operate distance
    ctx.push_obligation(ProofObligation::assume("od", "operate_distance_mm == 4"));
    ctx.push_obligation(ProofObligation::assume("rd", "release_distance_mm == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "hh_def",
        "has_hysteresis == if release_distance_mm > operate_distance_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_hysteresis == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Prox: release 5mm > operate 4mm → hysteresis present",
    );
}

#[test]
fn output_type_npn() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_config", u32_ty());
    ctx.declare_var_typed("is_npn", i32_ty());
    // Output: 0=NPN(sinking), 1=PNP(sourcing), 2=push-pull
    ctx.push_obligation(ProofObligation::assume("oc", "output_config == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_npn == if output_config == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_npn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: output_config=0 → NPN sinking");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_v", "min_v", "max_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("supply_ok", i32_ty());
    // Industrial proximity: 10-30V DC typical
    ctx.push_obligation(ProofObligation::assume("sv", "supply_v == 24"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_v == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_v == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "supply_ok == if supply_v >= min_v && supply_v <= max_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "supply_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: 24V in [10, 30] → supply OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["target_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Max switching frequency depends on sensor size
    ctx.push_obligation(ProofObligation::assume("tf", "target_freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_hz == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if target_freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: 1 kHz ≤ 5 kHz max → frequency OK");
}

#[test]
fn correction_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["rated_distance_mm_x10", "correction_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("effective_distance_mm_x10", u32_ty());
    // Non-ferrous metals reduce sensing distance. Precompute: 50×70/100 = 35 (×10 scale)
    ctx.push_obligation(ProofObligation::assume("rd", "rated_distance_mm_x10 == 50")); // 5.0mm
    ctx.push_obligation(ProofObligation::assume("cp", "correction_pct == 70")); // aluminum ~70%
    ctx.push_obligation(ProofObligation::assume(
        "ed",
        "effective_distance_mm_x10 == 35",
    )); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_35",
        "effective_distance_mm_x10 == 35",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Prox: 5mm × 70% aluminum = 3.5mm effective (precomputed)",
    );
}

#[test]
fn ip_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["ip_rating", "min_ip_rating"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("suitable", i32_ty());
    // IP67 = 67, IP68 = 68. Minimum for washdown: IP67
    ctx.push_obligation(ProofObligation::assume("ir", "ip_rating == 67"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_ip_rating == 67"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "suitable == if ip_rating >= min_ip_rating { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "suitable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: IP67 ≥ IP67 min → suitable for washdown");
}

#[test]
fn normally_open_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("contact_type", u32_ty());
    ctx.declare_var_typed("target_present", u32_ty());
    ctx.declare_var_typed("output_active", i32_ty());
    // NO: active when target present. NC: active when target absent.
    ctx.push_obligation(ProofObligation::assume("ct", "contact_type == 0")); // 0=NO
    ctx.push_obligation(ProofObligation::assume("tp", "target_present == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "oa_def",
        "output_active == if contact_type == 0 && target_present == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "output_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: NO + target present → output active");
}

#[test]
fn load_current() {
    let mut ctx = VerificationContext::new();
    for v in &["load_ma", "max_load_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Output load current limit (typically 200mA)
    ctx.push_obligation(ProofObligation::assume("lm", "load_ma == 150"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_ma == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_ma <= max_load_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: 150mA load ≤ 200mA max → load OK");
}

#[test]
fn flush_mounting() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mount_type", u32_ty());
    ctx.declare_var_typed("is_flush", i32_ty());
    // Mount: 0=flush(shielded), 1=non-flush(unshielded)
    ctx.push_obligation(ProofObligation::assume("mt", "mount_type == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "if_def",
        "is_flush == if mount_type == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_flush == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Prox: mount_type=0 → flush (shielded) mount");
}
