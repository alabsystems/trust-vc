// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn threshold_current() {
    let mut ctx = VerificationContext::new();
    for v in &["ith_ma", "max_ith_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ith_ok", i32_ty());
    // Laser threshold current: onset of lasing
    ctx.push_obligation(ProofObligation::assume("im", "ith_ma == 15"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_ith_ma == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "ith_ok == if ith_ma <= max_ith_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ith_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 15mA threshold ≤ 50mA max → OK");
}

#[test]
fn slope_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["slope_mw_per_ma", "min_slope", "max_slope"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slope_ok", i32_ty());
    // Slope efficiency: mW output per mA above threshold
    ctx.push_obligation(ProofObligation::assume("sm", "slope_mw_per_ma == 3"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_slope == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_slope == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "slope_ok == if slope_mw_per_ma >= min_slope && slope_mw_per_ma <= max_slope { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slope_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 3 mW/mA slope in [1, 10] → OK");
}

#[test]
fn modulation_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_mhz", "min_bw_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Modulation bandwidth for data transmission
    ctx.push_obligation(ProofObligation::assume("bm", "bw_mhz == 2500"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bw_mhz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_mhz >= min_bw_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 2.5GHz bandwidth ≥ 1GHz min → OK");
}

#[test]
fn bias_current() {
    let mut ctx = VerificationContext::new();
    for v in &["ibias_ma", "ith_ma", "max_ibias_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // Bias must exceed threshold and stay below max
    ctx.push_obligation(ProofObligation::assume("ib", "ibias_ma == 25"));
    ctx.push_obligation(ProofObligation::assume("it", "ith_ma == 15"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_ibias_ma == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if ibias_ma >= ith_ma && ibias_ma <= max_ibias_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 25mA bias in [15, 100] → OK");
}

#[test]
fn apc_feedback() {
    let mut ctx = VerificationContext::new();
    for v in &["power_uw", "target_uw", "tolerance_uw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("apc_ok", i32_ty());
    // Automatic Power Control: monitor photodiode feedback
    ctx.push_obligation(ProofObligation::assume("pu", "power_uw == 1020"));
    ctx.push_obligation(ProofObligation::assume("tu", "target_uw == 1000"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_uw == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "apc_ok == if power_uw >= target_uw - tolerance_uw && power_uw <= target_uw + tolerance_uw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "apc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 1.02mW in 1.0mW ± 50μW → APC OK");
}

#[test]
fn temperature_setpoint() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_x10", "target_x10", "tolerance_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // TEC temperature control (×10 for 0.1°C)
    ctx.push_obligation(ProofObligation::assume("tx", "temp_x10 == 252")); // 25.2°C
    ctx.push_obligation(ProofObligation::assume("tt", "target_x10 == 250")); // 25.0°C
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_x10 == 5")); // ±0.5°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_x10 >= target_x10 - tolerance_x10 && temp_x10 <= target_x10 + tolerance_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 25.2°C in 25.0°C ± 0.5 → temp OK");
}

#[test]
fn wavelength() {
    let mut ctx = VerificationContext::new();
    for v in &["wl_nm_x10", "target_nm_x10", "tol_nm_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wl_ok", i32_ty());
    // Wavelength stability (×10 for 0.1nm)
    ctx.push_obligation(ProofObligation::assume("wx", "wl_nm_x10 == 15500")); // 1550.0nm
    ctx.push_obligation(ProofObligation::assume("tw", "target_nm_x10 == 15500"));
    ctx.push_obligation(ProofObligation::assume("tl", "tol_nm_x10 == 10")); // ±1.0nm
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wl_ok == if wl_nm_x10 >= target_nm_x10 - tol_nm_x10 && wl_nm_x10 <= target_nm_x10 + tol_nm_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 1550.0nm in target ± 1.0nm → OK");
}

#[test]
fn extinction_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["er_db_x10", "min_er_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("er_ok", i32_ty());
    // Extinction ratio: ratio of on/off power (×10 for 0.1dB)
    ctx.push_obligation(ProofObligation::assume("ex", "er_db_x10 == 100")); // 10.0dB
    ctx.push_obligation(ProofObligation::assume("me", "min_er_x10 == 60")); // 6.0dB
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "er_ok == if er_db_x10 >= min_er_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "er_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 10.0dB ER ≥ 6.0dB min → OK");
}

#[test]
fn eye_diagram_opening() {
    let mut ctx = VerificationContext::new();
    for v in &["opening_pct", "min_opening_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eye_ok", i32_ty());
    // Eye diagram vertical opening percentage
    ctx.push_obligation(ProofObligation::assume("op", "opening_pct == 80"));
    ctx.push_obligation(ProofObligation::assume("mo", "min_opening_pct == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eye_ok == if opening_pct >= min_opening_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eye_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 80% eye opening ≥ 60% min → OK");
}

#[test]
fn compliance_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vcomp_mv", "min_vcomp_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vcomp_ok", i32_ty());
    // Driver compliance voltage: headroom for laser Vf
    ctx.push_obligation(ProofObligation::assume("vm", "vcomp_mv == 3000"));
    ctx.push_obligation(ProofObligation::assume("mv", "min_vcomp_mv == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vcomp_ok == if vcomp_mv >= min_vcomp_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vcomp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Laser driver: 3.0V compliance ≥ 2.0V min → OK");
}
