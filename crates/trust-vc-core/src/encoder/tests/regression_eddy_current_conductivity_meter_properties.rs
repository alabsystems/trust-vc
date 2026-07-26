// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_conductivity_range_iacs() {
    // Eddy current conductivity: value 105 %IACS, min 1, max 120
    let mut ctx = VerificationContext::new();
    for v in &["conductivity", "min_cond", "max_cond"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "conductivity == 105"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_cond == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_cond == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if conductivity >= min_cond && conductivity <= max_cond { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 105 %IACS in [1, 120]");
}

#[test]
fn test_frequency_khz_bounded() {
    // Operating frequency: value 60 kHz, min 1, max 500
    let mut ctx = VerificationContext::new();
    for v in &["freq", "min_freq", "max_freq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("f", "freq == 60"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_freq == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_freq == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if freq >= min_freq && freq <= max_freq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: 60 kHz in [1, 500]");
}

#[test]
fn test_accuracy_scaled_x100() {
    // Accuracy scaled x100 (%IACS): value 50 (0.50%), min 5 (0.05%), max 200 (2.00%)
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "min_acc", "max_acc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_acc == 5"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_acc == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if accuracy_x100 >= min_acc && accuracy_x100 <= max_acc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: accuracy 0.50% (50) in [0.05%, 2.00%]",
    );
}

#[test]
fn test_probe_type_disjunction() {
    // Probe type: 1=pencil, 2=surface, 3=eddy current array
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "probe_type == 2")); // surface
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if probe_type == 1 || probe_type == 2 || probe_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: probe type 2 (surface) valid");
}

#[test]
fn test_material_category_disjunction() {
    // Material category: 1=aluminum, 2=copper, 3=titanium, 4=nickel
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "material == 1")); // aluminum
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if material == 1 || material == 2 || material == 3 || material == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: material 1 (aluminum) valid");
}

#[test]
fn test_liftoff_compensation_scaled_x10() {
    // Lift-off compensation scaled x10 (mm): value 20 (2.0mm), min 0, max 100 (10.0mm)
    let mut ctx = VerificationContext::new();
    for v in &["liftoff_x10", "min_lo", "max_lo"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("l", "liftoff_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_lo == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if liftoff_x10 >= min_lo && liftoff_x10 <= max_lo { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: lift-off 2.0mm (20) in [0, 10.0mm]");
}

#[test]
fn test_display_resolution_scaled_x1000() {
    // Display resolution scaled x1000 (%IACS): value 100 (0.100%), min 1 (0.001%), max 1000 (1.000%)
    let mut ctx = VerificationContext::new();
    for v in &["res_x1000", "min_res", "max_res"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "res_x1000 == 100"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_res == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_res == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if res_x1000 >= min_res && res_x1000 <= max_res { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: resolution 0.100% (100) in [0.001%, 1.000%]",
    );
}

#[test]
fn test_communication_interface_disjunction() {
    // Communication: 1=USB, 2=RS-232, 3=Bluetooth
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "comm == 3")); // Bluetooth
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if comm == 1 || comm == 2 || comm == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eddy current: comm 3 (Bluetooth) valid");
}

#[test]
fn test_operating_temp_offset_500() {
    // Operating temperature with +500 offset (°C)
    // 20°C → 520, min -40°C → 460, max 50°C → 550
    let mut ctx = VerificationContext::new();
    for v in &["temp", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "temp == 520"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_temp == 460"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_temp == 550"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp >= min_temp && temp <= max_temp { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: 20C (520) in [-40C (460), 50C (550)]",
    );
}

#[test]
fn test_temperature_compensation_flag() {
    // Temperature compensation: boolean flag (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_comp", i32_ty());
    ctx.declare_var_typed("compensated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "temp_comp == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compensated == if temp_comp == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "compensated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eddy current: temp compensation enabled -> compensated",
    );
}
