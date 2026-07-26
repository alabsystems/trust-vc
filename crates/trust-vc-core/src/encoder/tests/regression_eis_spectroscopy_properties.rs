// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frequency_sweep_range() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_mhz_x10", "min_freq_x10", "max_freq_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // EIS frequency sweep: 0.01Hz to 1MHz (stored as mHz×10 for low end, Hz for high)
    // Using Hz for simplicity: 100Hz test point
    ctx.push_obligation(ProofObligation::assume("fm", "freq_mhz_x10 == 1000")); // 100Hz
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_x10 == 1")); // 0.1Hz
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_x10 == 10000000")); // 1MHz
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_mhz_x10 >= min_freq_x10 && freq_mhz_x10 <= max_freq_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 100Hz in [0.1Hz, 1MHz] → freq OK");
}

#[test]
fn impedance_magnitude() {
    let mut ctx = VerificationContext::new();
    for v in &["z_mohm", "max_z_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("z_ok", i32_ty());
    // Impedance magnitude in milliohms
    ctx.push_obligation(ProofObligation::assume("zm", "z_mohm == 500"));
    ctx.push_obligation(ProofObligation::assume("mz", "max_z_mohm == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "zo_def",
        "z_ok == if z_mohm <= max_z_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "z_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 500mΩ impedance ≤ 100Ω max → OK");
}

#[test]
fn phase_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_x10", "min_phase_x10", "max_phase_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("phase_ok", i32_ty());
    // Phase angle: 0-90° (×10 for 0.1°, using offset since can be negative in practice)
    // Simplified: positive range 0-900 (0.0° to 90.0°)
    ctx.push_obligation(ProofObligation::assume("px", "phase_x10 == 450")); // 45.0°
    ctx.push_obligation(ProofObligation::assume("mn", "min_phase_x10 == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_phase_x10 == 900"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "phase_ok == if phase_x10 >= min_phase_x10 && phase_x10 <= max_phase_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "phase_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 45.0° phase in [0, 90] → OK");
}

#[test]
fn ac_amplitude() {
    let mut ctx = VerificationContext::new();
    for v in &["ac_mv", "min_ac_mv", "max_ac_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ac_ok", i32_ty());
    // AC perturbation amplitude (small signal for linearity)
    ctx.push_obligation(ProofObligation::assume("am", "ac_mv == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ac_mv == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ac_mv == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "ac_ok == if ac_mv >= min_ac_mv && ac_mv <= max_ac_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ac_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 10mV AC amplitude in [1, 50] → OK");
}

#[test]
fn dc_bias() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_mv", "max_bias_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // DC bias voltage during measurement
    ctx.push_obligation(ProofObligation::assume("bm", "bias_mv == 3700"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_bias_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_mv <= max_bias_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 3.7V DC bias ≤ 5.0V max → OK");
}

#[test]
fn nyquist_point_count() {
    let mut ctx = VerificationContext::new();
    for v in &["points", "min_points"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pts_ok", i32_ty());
    // Points per decade in Nyquist plot
    ctx.push_obligation(ProofObligation::assume("p", "points == 10"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_points == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pts_ok == if points >= min_points { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pts_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 10 pts/decade ≥ 5 min → OK");
}

#[test]
fn warburg_coefficient() {
    let mut ctx = VerificationContext::new();
    for v in &["sigma_x100", "max_sigma_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sigma_ok", i32_ty());
    // Warburg coefficient σ (×100 for 0.01 Ω·s^-1/2)
    ctx.push_obligation(ProofObligation::assume("sx", "sigma_x100 == 500")); // 5.00
    ctx.push_obligation(ProofObligation::assume("ms", "max_sigma_x100 == 2000")); // 20.00
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sigma_ok == if sigma_x100 <= max_sigma_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sigma_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: Warburg σ=5.00 ≤ 20.00 max → OK");
}

#[test]
fn double_layer_capacitance() {
    let mut ctx = VerificationContext::new();
    for v in &["cdl_uf", "min_cdl_uf", "max_cdl_uf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cdl_ok", i32_ty());
    // Double-layer capacitance in μF
    ctx.push_obligation(ProofObligation::assume("cu", "cdl_uf == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cdl_uf == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cdl_uf == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cdl_ok == if cdl_uf >= min_cdl_uf && cdl_uf <= max_cdl_uf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cdl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 50μF Cdl in [1, 1000] → OK");
}

#[test]
fn charge_transfer_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rct_mohm", "max_rct_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rct_ok", i32_ty());
    // Charge transfer resistance in milliohms
    ctx.push_obligation(ProofObligation::assume("rm", "rct_mohm == 200"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rct_mohm == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rct_ok == if rct_mohm <= max_rct_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rct_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 200mΩ Rct ≤ 5000mΩ max → OK");
}

#[test]
fn solution_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rs_mohm", "max_rs_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rs_ok", i32_ty());
    // Electrolyte/solution resistance
    ctx.push_obligation(ProofObligation::assume("rm", "rs_mohm == 50"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rs_mohm == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rs_ok == if rs_mohm <= max_rs_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rs_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS: 50mΩ Rs ≤ 1000mΩ max → OK");
}
