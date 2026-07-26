// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn air_gap() {
    let mut ctx = VerificationContext::new();
    for v in &["gap_um", "target_um", "tolerance_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("gap_ok", i32_ty());
    // Air gap between stator and rotor/object (tolerance band)
    ctx.push_obligation(ProofObligation::assume("gu", "gap_um == 510"));
    ctx.push_obligation(ProofObligation::assume("tu", "target_um == 500"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_um == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gap_ok == if gap_um >= target_um - tolerance_um && gap_um <= target_um + tolerance_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 510μm gap in 500±50μm → OK");
}

#[test]
fn force_balance() {
    let mut ctx = VerificationContext::new();
    for v in &["force_mn", "weight_mn", "tolerance_mn"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("balanced", i32_ty());
    // Electromagnetic force must balance gravity (tolerance band)
    ctx.push_obligation(ProofObligation::assume("fm", "force_mn == 9810"));
    ctx.push_obligation(ProofObligation::assume("wm", "weight_mn == 9800")); // ~1kg
    ctx.push_obligation(ProofObligation::assume("tm", "tolerance_mn == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "balanced == if force_mn >= weight_mn - tolerance_mn && force_mn <= weight_mn + tolerance_mn { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "balanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 9810mN force ≈ 9800mN weight → balanced");
}

#[test]
fn position_feedback() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_nm", "max_resolution_nm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Position sensor resolution (lower = better)
    ctx.push_obligation(ProofObligation::assume("rn", "resolution_nm == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resolution_nm == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_nm <= max_resolution_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 100nm resolution ≤ 500nm max → OK");
}

#[test]
fn coil_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("curr_ok", i32_ty());
    // Electromagnet drive current
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ma == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "curr_ok == if current_ma <= max_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "curr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 2A coil current ≤ 5A max → OK");
}

#[test]
fn damping_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["zeta_x100", "min_zeta_x100", "max_zeta_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("zeta_ok", i32_ty());
    // Damping ratio ζ (×100): 0.5-0.9 for good transient response
    ctx.push_obligation(ProofObligation::assume("zx", "zeta_x100 == 70")); // 0.70
    ctx.push_obligation(ProofObligation::assume("mn", "min_zeta_x100 == 50")); // 0.50
    ctx.push_obligation(ProofObligation::assume("mx", "max_zeta_x100 == 90")); // 0.90
    ctx.push_obligation(ProofObligation::assume(
        "zo_def",
        "zeta_ok == if zeta_x100 >= min_zeta_x100 && zeta_x100 <= max_zeta_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zeta_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: ζ=0.70 in [0.50, 0.90] → damping OK");
}

#[test]
fn stiffness() {
    let mut ctx = VerificationContext::new();
    for v in &["k_n_per_m", "min_k"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("k_ok", i32_ty());
    // Magnetic stiffness: N/m
    ctx.push_obligation(ProofObligation::assume("kn", "k_n_per_m == 10000"));
    ctx.push_obligation(ProofObligation::assume("mk", "min_k == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "k_ok == if k_n_per_m >= min_k { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "k_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 10000 N/m stiffness ≥ 5000 min → OK");
}

#[test]
fn levitation_height() {
    let mut ctx = VerificationContext::new();
    for v in &["height_mm", "min_height_mm", "max_height_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("height_ok", i32_ty());
    // Stable levitation height range
    ctx.push_obligation(ProofObligation::assume("hm", "height_mm == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_height_mm == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_height_mm == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "height_ok == if height_mm >= min_height_mm && height_mm <= max_height_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "height_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 10mm height in [5, 25] → OK");
}

#[test]
fn disturbance_rejection() {
    let mut ctx = VerificationContext::new();
    for v in &["rejection_db", "min_rejection_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rej_ok", i32_ty());
    // Disturbance rejection at control bandwidth
    ctx.push_obligation(ProofObligation::assume("rd", "rejection_db == 40"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rejection_db == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rej_ok == if rejection_db >= min_rejection_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rej_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Maglev: 40dB disturbance rejection ≥ 20dB min → OK",
    );
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["power_w", "max_power_w"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Steady-state levitation power
    ctx.push_obligation(ProofObligation::assume("pw", "power_w == 15"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_w == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_w <= max_power_w { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 15W power ≤ 50W max → OK");
}

#[test]
fn controller_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Control loop bandwidth for stable levitation
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 500"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bw_hz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Maglev: 500Hz bandwidth ≥ 100Hz min → OK");
}
