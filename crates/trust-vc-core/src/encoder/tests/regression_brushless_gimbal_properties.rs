// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pole_pairs() {
    let mut ctx = VerificationContext::new();
    for v in &["poles", "min_poles", "max_poles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("poles_ok", i32_ty());
    // Gimbal motors: typically 7-14 pole pairs
    ctx.push_obligation(ProofObligation::assume("p", "poles == 11"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_poles == 7"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_poles == 14"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "poles_ok == if poles >= min_poles && poles <= max_poles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "poles_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 11 pole pairs in [7, 14] → OK");
}

#[test]
fn phase_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["resistance_mohm", "min_r_mohm", "max_r_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("r_ok", i32_ty());
    // Phase resistance in mΩ (low for gimbal efficiency)
    ctx.push_obligation(ProofObligation::assume("rm", "resistance_mohm == 8500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_r_mohm == 2000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_r_mohm == 15000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "r_ok == if resistance_mohm >= min_r_mohm && resistance_mohm <= max_r_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "r_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 8.5Ω in [2.0, 15.0] → resistance OK");
}

#[test]
fn voltage_constant() {
    let mut ctx = VerificationContext::new();
    for v in &["kv_rpm_per_v", "min_kv", "max_kv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("kv_ok", i32_ty());
    // KV rating: RPM per volt (low KV = high torque for gimbals)
    ctx.push_obligation(ProofObligation::assume("kv", "kv_rpm_per_v == 85"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_kv == 30"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_kv == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "kv_ok == if kv_rpm_per_v >= min_kv && kv_rpm_per_v <= max_kv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "kv_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 85 KV in [30, 200] → OK");
}

#[test]
fn control_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["ctrl_hz", "min_ctrl_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ctrl_ok", i32_ty());
    // FOC control loop frequency
    ctx.push_obligation(ProofObligation::assume("ch", "ctrl_hz == 8000"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_ctrl_hz == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ctrl_ok == if ctrl_hz >= min_ctrl_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ctrl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 8kHz FOC control ≥ 4kHz min → OK");
}

#[test]
fn pid_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz", "max_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // PID control bandwidth for stabilization
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw_hz == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw_hz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz && bw_hz <= max_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 100Hz PID bandwidth in [20, 500] → OK");
}

#[test]
fn encoder_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["bits", "min_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Position encoder resolution for FOC commutation
    ctx.push_obligation(ProofObligation::assume("b", "bits == 14"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bits == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if bits >= min_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 14-bit encoder ≥ 12-bit min → OK");
}

#[test]
fn torque_constant() {
    let mut ctx = VerificationContext::new();
    for v in &["kt_mnm_per_a", "min_kt"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("kt_ok", i32_ty());
    // Torque constant: mNm per amp (higher = better for gimbal)
    ctx.push_obligation(ProofObligation::assume("kt", "kt_mnm_per_a == 30"));
    ctx.push_obligation(ProofObligation::assume("mk", "min_kt == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "kt_ok == if kt_mnm_per_a >= min_kt { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "kt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 30 mNm/A torque constant ≥ 10 min → OK");
}

#[test]
fn max_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("curr_ok", i32_ty());
    // Phase current limit
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 800"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "curr_ok == if current_ma <= max_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "curr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 800mA ≤ 2000mA max → current OK");
}

#[test]
fn thermal_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c", "max_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Motor winding temperature limit
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c == 65"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_c == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c <= max_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 65°C ≤ 120°C thermal limit → OK");
}

#[test]
fn vibration_level() {
    let mut ctx = VerificationContext::new();
    for v in &["vib_mg", "max_vib_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vib_ok", i32_ty());
    // Vibration output level (millig for camera stability)
    ctx.push_obligation(ProofObligation::assume("vm", "vib_mg == 5"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_vib_mg == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vib_ok == if vib_mg <= max_vib_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vib_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gimbal: 5mg vibration ≤ 20mg max → OK");
}
