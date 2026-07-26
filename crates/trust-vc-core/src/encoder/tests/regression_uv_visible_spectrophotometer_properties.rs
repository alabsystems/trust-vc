// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn wavelength_min_bounded() {
    // UV-Vis minimum wavelength typically 190-200 nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_min_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wl_min_nm == 190"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wl_min_nm >= 190 && wl_min_nm <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: min wavelength 190nm in [190, 200]");
}

#[test]
fn wavelength_max_bounded() {
    // UV-Vis maximum wavelength typically 900-1100 nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_max_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wl_max_nm == 1100"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wl_max_nm >= 900 && wl_max_nm <= 1100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: max wavelength 1100nm in [900, 1100]");
}

#[test]
fn wavelength_accuracy_scaled() {
    // Wavelength accuracy ±0.1 nm → scaled ×10 to integer 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10_nm", u32_ty());
    ctx.declare_var_typed("max_accuracy_x10", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc", "accuracy_x10_nm == 1")); // 0.1 nm
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x10 == 5")); // 0.5 nm max
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if accuracy_x10_nm <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: accuracy 0.1nm (x10=1) <= 0.5nm (x10=5)");
}

#[test]
fn photometric_range_scaled() {
    // Photometric range ±4.000 Abs → scaled ×1000 to 4000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_x1000_abs", u32_ty());
    ctx.declare_var_typed("in_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "range_x1000_abs == 4000")); // 4.000 Abs
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_spec == if range_x1000_abs >= 1000 && range_x1000_abs <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "UV-Vis: photometric range 4.000 Abs (x1000=4000) in [1000, 5000]",
    );
}

#[test]
fn stray_light_scaled() {
    // Stray light 0.01% T → scaled ×100 to 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stray_x100_pct", u32_ty());
    ctx.declare_var_typed("max_stray_x100", u32_ty());
    ctx.declare_var_typed("within_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sl", "stray_x100_pct == 1")); // 0.01% T
    ctx.push_obligation(ProofObligation::assume("ms", "max_stray_x100 == 5")); // 0.05% T max
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if stray_x100_pct <= max_stray_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "UV-Vis: stray light 0.01%T (x100=1) <= 0.05%T (x100=5)",
    );
}

#[test]
fn light_source_type() {
    // Light source: 1=deuterium, 2=tungsten, 3=xenon flash
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "source == 1")); // deuterium
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if source == 1 || source == 2 || source == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: light source deuterium (1) is valid");
}

#[test]
fn beam_type() {
    // Beam type: 1=single, 2=double, 3=split
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("b", "beam == 2")); // double beam
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if beam == 1 || beam == 2 || beam == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: beam type double (2) is valid");
}

#[test]
fn bandwidth_scaled() {
    // Spectral bandwidth 0.5 nm → scaled ×10 to 5
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw_x10_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bw", "bw_x10_nm == 5")); // 0.5 nm
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if bw_x10_nm >= 1 && bw_x10_nm <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: bandwidth 0.5nm (x10=5) in [0.1, 5.0]nm");
}

#[test]
fn scan_speed_bounded() {
    // Scan speed in nm/min, typically 10 to 6000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_nm_min", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sp", "speed_nm_min == 2400"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if speed_nm_min >= 10 && speed_nm_min <= 6000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: scan speed 2400 nm/min in [10, 6000]");
}

#[test]
fn sipper_system_flag() {
    // Sipper system: boolean flag (1=present, 0=absent)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_sipper", i32_ty());
    ctx.declare_var_typed("auto_sampling", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hs", "has_sipper == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "auto_sampling == if has_sipper == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "auto_sampling == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV-Vis: sipper present → auto sampling enabled");
}
