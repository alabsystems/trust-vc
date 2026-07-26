// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_mm", "range_min", "range_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Probe range in mm: value 15000 (15m), valid range 100 (0.1m) to 30000 (30m)
    ctx.push_obligation(ProofObligation::assume("mr_val", "range_mm == 15000"));
    ctx.push_obligation(ProofObligation::assume("mr_min", "range_min == 100"));
    ctx.push_obligation(ProofObligation::assume("mr_max", "range_max == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "mr_in_range",
        "range_mm >= range_min && range_mm <= range_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "probe range 15000mm (15m) in valid range [100,30000] (0.1-30m)",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accuracy_ok", i32_ty());
    // Accuracy in mm x100: value 50 means 0.50mm, upper bound 500 means 5.00mm
    ctx.push_obligation(ProofObligation::assume("ac_val", "accuracy_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "max_accuracy == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ac_ok_def",
        "accuracy_ok == if accuracy_x100 <= max_accuracy { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ac_check", "accuracy_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy 50 (0.50mm) within upper bound 500 (5.00mm)",
    );
}

#[test]
fn frequency_band() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_band", u32_ty());
    ctx.declare_var_typed("valid_band", i32_ty());
    // 1=6 GHz, 2=26 GHz, 3=80 GHz, 4=120 GHz
    ctx.push_obligation(ProofObligation::assume("fb_val", "freq_band == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "fb_valid_def",
        "valid_band == if freq_band == 1 || freq_band == 2 || freq_band == 3 || freq_band == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fb_check", "valid_band == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency band 2 (26 GHz) is valid");
}

#[test]
fn antenna_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("antenna", u32_ty());
    ctx.declare_var_typed("valid_antenna", i32_ty());
    // 1=horn, 2=rod, 3=parabolic, 4=planar array
    ctx.push_obligation(ProofObligation::assume("at_val", "antenna == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "at_valid_def",
        "valid_antenna == if antenna == 1 || antenna == 2 || antenna == 3 || antenna == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("at_check", "valid_antenna == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "antenna type 3 (parabolic) is valid");
}

#[test]
fn beam_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["angle_x10", "angle_min", "angle_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Beam angle in degrees x10: value 40 means 4.0 degrees, range 10 (1.0) to 300 (30.0)
    ctx.push_obligation(ProofObligation::assume("ba_val", "angle_x10 == 40"));
    ctx.push_obligation(ProofObligation::assume("ba_min", "angle_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ba_max", "angle_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "ba_in_range",
        "angle_x10 >= angle_min && angle_x10 <= angle_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam angle 40 (4.0 deg) in range [10,300] (1.0-30.0 deg)",
    );
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // 1=4-20mA, 2=4-20mA HART, 3=PROFIBUS PA, 4=Foundation Fieldbus, 5=Modbus RTU
    ctx.push_obligation(ProofObligation::assume("ot_val", "output == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_valid_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 || output == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_check", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 2 (4-20mA HART) is valid");
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: -200C maps to 300, 450C maps to 950. Value 520 means 20C.
    ctx.push_obligation(ProofObligation::assume("pt_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assume("pt_min", "temp_min == 300"));
    ctx.push_obligation(ProofObligation::assume("pt_max", "temp_max == 950"));
    ctx.push_obligation(ProofObligation::assert(
        "pt_in_range",
        "temp >= temp_min && temp <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "process temp 520 (20C) in range [300,950] (-200C to 450C)",
    );
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "press_min", "press_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Process pressure in bar: value 25, valid range 1 to 400
    ctx.push_obligation(ProofObligation::assume("pp_val", "pressure_bar == 25"));
    ctx.push_obligation(ProofObligation::assume("pp_min", "press_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pp_max", "press_max == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "pp_in_range",
        "pressure_bar >= press_min && pressure_bar <= press_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process pressure 25 bar in range [1,400]");
}

#[test]
fn dielectric_constant() {
    let mut ctx = VerificationContext::new();
    for v in &["dk_x100", "dk_min", "dk_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Dielectric constant x100: value 200 means 2.00, range 120 (1.20) to 10000 (100.00)
    ctx.push_obligation(ProofObligation::assume("dk_val", "dk_x100 == 200"));
    ctx.push_obligation(ProofObligation::assume("dk_min_val", "dk_min == 120"));
    ctx.push_obligation(ProofObligation::assume("dk_max_val", "dk_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "dk_in_range",
        "dk_x100 >= dk_min && dk_x100 <= dk_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dielectric constant 200 (2.00) in range [120,10000] (1.20-100.00)",
    );
}

#[test]
fn measurement_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // 1=continuous level, 2=interface, 3=distance
    ctx.push_obligation(ProofObligation::assume("mt_val", "meas_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_valid_def",
        "valid_type == if meas_type == 1 || meas_type == 2 || meas_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mt_check", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement type 1 (continuous level) is valid");
}
