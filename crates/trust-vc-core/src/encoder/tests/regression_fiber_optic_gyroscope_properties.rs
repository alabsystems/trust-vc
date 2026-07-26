// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sagnac_scale() {
    let mut ctx = VerificationContext::new();
    for v in &["scale_x1000", "min_scale_x1000", "max_scale_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("scale_ok", i32_ty());
    // Sagnac effect scale factor (×1000 for precision)
    ctx.push_obligation(ProofObligation::assume("sx", "scale_x1000 == 1000")); // 1.000
    ctx.push_obligation(ProofObligation::assume("mn", "min_scale_x1000 == 995")); // 0.995
    ctx.push_obligation(ProofObligation::assume("mx", "max_scale_x1000 == 1005")); // 1.005
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "scale_ok == if scale_x1000 >= min_scale_x1000 && scale_x1000 <= max_scale_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "scale_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: scale factor 1.000 in [0.995, 1.005] → OK");
}

#[test]
fn fiber_coil_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "min_length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // Fiber coil length (longer = more sensitive)
    ctx.push_obligation(ProofObligation::assume("lm", "length_m == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_length_m == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_length_m == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if length_m >= min_length_m && length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 500m fiber coil in [100, 5000] → OK");
}

#[test]
fn source_wavelength() {
    let mut ctx = VerificationContext::new();
    for v in &["wl_nm", "min_wl_nm", "max_wl_nm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wl_ok", i32_ty());
    // SLD source wavelength: typically 830nm or 1550nm
    ctx.push_obligation(ProofObligation::assume("wn", "wl_nm == 1550"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_wl_nm == 800"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_wl_nm == 1600"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wl_ok == if wl_nm >= min_wl_nm && wl_nm <= max_wl_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 1550nm wavelength in [800, 1600] → OK");
}

#[test]
fn bias_stability() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_dph_x100", "max_bias_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // Bias stability: °/h (×100 for 0.01 resolution)
    ctx.push_obligation(ProofObligation::assume("bx", "bias_dph_x100 == 10")); // 0.10°/h
    ctx.push_obligation(ProofObligation::assume("mb", "max_bias_x100 == 100")); // 1.00°/h
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_dph_x100 <= max_bias_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 0.10°/h bias ≤ 1.00°/h max → OK");
}

#[test]
fn angle_random_walk() {
    let mut ctx = VerificationContext::new();
    for v in &["arw_x1000", "max_arw_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("arw_ok", i32_ty());
    // Angle Random Walk: °/√h (×1000 for 0.001 resolution)
    ctx.push_obligation(ProofObligation::assume("ax", "arw_x1000 == 5")); // 0.005°/√h
    ctx.push_obligation(ProofObligation::assume("ma", "max_arw_x1000 == 50")); // 0.050°/√h
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "arw_ok == if arw_x1000 <= max_arw_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "arw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 0.005°/√h ARW ≤ 0.050 max → OK");
}

#[test]
fn fog_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Rate output bandwidth
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 500"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bw_hz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 500Hz bandwidth ≥ 100Hz min → OK");
}

#[test]
fn dynamic_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_dps", "min_range_dps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Input rate dynamic range
    ctx.push_obligation(ProofObligation::assume("rd", "range_dps == 500"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_range_dps == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_dps >= min_range_dps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: ±500°/s range ≥ ±100 min → OK");
}

#[test]
fn scale_factor_nonlinearity() {
    let mut ctx = VerificationContext::new();
    for v in &["nl_ppm", "max_nl_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("nl_ok", i32_ty());
    // Scale factor nonlinearity in ppm
    ctx.push_obligation(ProofObligation::assume("np", "nl_ppm == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_nl_ppm == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "nl_ok == if nl_ppm <= max_nl_ppm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "nl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 50ppm scale nonlinearity ≤ 200 max → OK");
}

#[test]
fn mean_wavelength_stability() {
    let mut ctx = VerificationContext::new();
    for v in &["drift_ppm", "max_drift_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drift_ok", i32_ty());
    // Mean wavelength stability: affects scale factor
    ctx.push_obligation(ProofObligation::assume("dp", "drift_ppm == 10"));
    ctx.push_obligation(ProofObligation::assume("md", "max_drift_ppm == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "drift_ok == if drift_ppm <= max_drift_ppm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 10ppm wavelength drift ≤ 50 max → OK");
}

#[test]
fn modulation_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["mod_khz", "min_mod_khz", "max_mod_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mod_ok", i32_ty());
    // Phase modulation frequency (proper frequency = c/2nL)
    ctx.push_obligation(ProofObligation::assume("mk", "mod_khz == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mod_khz == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mod_khz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mod_ok == if mod_khz >= min_mod_khz && mod_khz <= max_mod_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mod_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FOG: 200kHz modulation in [50, 500] → OK");
}
