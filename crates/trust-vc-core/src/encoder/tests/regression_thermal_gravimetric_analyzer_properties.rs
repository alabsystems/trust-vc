// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn max_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Max 1500°C. Offset +500 → temp 2000, max 2000
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_offset == 2000")); // 1500°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_offset == 2000")); // 1500°C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_c_offset >= 500 && temp_c_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: 1500°C (offset 2000) within [0, 1500] range");
}

#[test]
fn temperature_accuracy_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "measured_x10",
        "reference_x10",
        "error_x10",
        "tolerance_x10",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accurate", i32_ty());
    // ×10 scaling: 0.1°C precision. 500.0°C = 5000, ref = 5001, error = 1 (0.1°C), tol = 10 (1.0°C)
    ctx.push_obligation(ProofObligation::assume("m", "measured_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assume("r", "reference_x10 == 5001"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "error_x10 == reference_x10 - measured_x10",
    ));
    ctx.push_obligation(ProofObligation::assume("t", "tolerance_x10 == 10")); // 1.0°C
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "accurate == if error_x10 <= tolerance_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "accurate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: temp error 0.1°C <= 1.0°C tolerance");
}

#[test]
fn balance_sensitivity_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "reading_x100",
        "baseline_x100",
        "delta_x100",
        "sensitivity_x100",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("detectable", i32_ty());
    // ×100 scaling: 0.01μg precision. Reading = 100.50μg (10050), baseline = 100.49μg (10049)
    ctx.push_obligation(ProofObligation::assume("rd", "reading_x100 == 10050"));
    ctx.push_obligation(ProofObligation::assume("bl", "baseline_x100 == 10049"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "delta_x100 == reading_x100 - baseline_x100",
    ));
    ctx.push_obligation(ProofObligation::assume("s", "sensitivity_x100 == 1")); // 0.01μg
    ctx.push_obligation(ProofObligation::assume(
        "det_def",
        "detectable == if delta_x100 >= sensitivity_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "detectable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TGA: 0.01μg change detectable at 0.01μg sensitivity",
    );
}

#[test]
fn heating_rate_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_x10", "min_rate_x10", "max_rate_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_rate", i32_ty());
    // ×10 scaling: 0.1°C/min precision. Rate = 10.0°C/min (100), range [1, 1000] (0.1-100.0°C/min)
    ctx.push_obligation(ProofObligation::assume("r", "rate_x10 == 100")); // 10.0°C/min
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate_x10 == 1")); // 0.1°C/min
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate_x10 == 1000")); // 100.0°C/min
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_rate == if rate_x10 >= min_rate_x10 && rate_x10 <= max_rate_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_rate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: 10.0°C/min in [0.1, 100.0] range");
}

#[test]
fn sample_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_mg", "min_mg", "max_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_mass", i32_ty());
    // Sample capacity: 1 to 1000 mg
    ctx.push_obligation(ProofObligation::assume("s", "sample_mg == 25"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mg == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mg == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mass == if sample_mg >= min_mg && sample_mg <= max_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mass == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: 25mg sample in [1, 1000] capacity range");
}

#[test]
fn atmosphere_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atmosphere", u32_ty());
    // 1=nitrogen, 2=air, 3=argon
    ctx.push_obligation(ProofObligation::assume("a", "atmosphere == 1")); // nitrogen
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "atmosphere == 1 || atmosphere == 2 || atmosphere == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: nitrogen (1) is valid atmosphere");
}

#[test]
fn balance_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("balance_type", u32_ty());
    // 1=horizontal, 2=vertical, 3=top-loading
    ctx.push_obligation(ProofObligation::assume("bt", "balance_type == 2")); // vertical
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "balance_type == 1 || balance_type == 2 || balance_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: vertical (2) is valid balance type");
}

#[test]
fn furnace_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("furnace_type", u32_ty());
    // 1=ceramic, 2=platinum, 3=tungsten
    ctx.push_obligation(ProofObligation::assume("ft", "furnace_type == 3")); // tungsten
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "furnace_type == 1 || furnace_type == 2 || furnace_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: tungsten (3) is valid furnace type");
}

#[test]
fn cooling_rate_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["cool_rate_x10", "min_cool_x10", "max_cool_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_cool", i32_ty());
    // ×10 scaling: 0.1°C/min precision. Rate = 5.0°C/min (50), range [1, 500] (0.1-50.0°C/min)
    ctx.push_obligation(ProofObligation::assume("cr", "cool_rate_x10 == 50")); // 5.0°C/min
    ctx.push_obligation(ProofObligation::assume("mn", "min_cool_x10 == 1")); // 0.1°C/min
    ctx.push_obligation(ProofObligation::assume("mx", "max_cool_x10 == 500")); // 50.0°C/min
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cool == if cool_rate_x10 >= min_cool_x10 && cool_rate_x10 <= max_cool_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cool == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: 5.0°C/min cooling in [0.1, 50.0] range");
}

#[test]
fn autosampler_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_autosampler", i32_ty());
    ctx.declare_var_typed("autosampler_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ha", "has_autosampler == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "autosampler_active == if has_autosampler == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "autosampler_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA: autosampler flag enabled → active");
}
