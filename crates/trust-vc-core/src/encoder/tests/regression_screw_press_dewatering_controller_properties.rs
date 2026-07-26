// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn screw_diameter_bounded() {
    // Screw diameter must be within 200-800 mm for standard presses
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "diameter_mm == 350"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if diameter_mm >= 200 && diameter_mm <= 800 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw diameter: 350mm in [200, 800]");
}

#[test]
fn screw_speed_scaled_bounded() {
    // Screw speed in x10 RPM (5 = 0.5 RPM, 30 = 3.0 RPM)
    // Typical range: 1-50 (0.1-5.0 RPM)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "speed_x10 == 15")); // 1.5 RPM
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if speed_x10 >= 1 && speed_x10 <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw speed: 15 (1.5 RPM) in [1, 50]");
}

#[test]
fn throughput_bounded() {
    // Throughput in m^3/h must be within 1-100
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "throughput == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if throughput >= 1 && throughput <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput: 25 m3/h in [1, 100]");
}

#[test]
fn cake_dryness_scaled_bounded() {
    // Cake dryness in x10 % (250 = 25.0%, 400 = 40.0%)
    // Typical range: 150-500 (15.0%-50.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dryness_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "dryness_x10 == 250")); // 25.0%
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dryness_x10 >= 150 && dryness_x10 <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cake dryness: 250 (25.0%) in [150, 500]");
}

#[test]
fn motor_power_bounded() {
    // Motor power in kW must be within 1-50
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "power_kw == 11"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if power_kw >= 1 && power_kw <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power: 11 kW in [1, 50]");
}

#[test]
fn screen_type_valid_disjunction() {
    // Screen type: 1=wedge wire, 2=perforated plate, 3=woven mesh
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screen_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "screen_type == 2")); // perforated plate
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "screen_type == 1 || screen_type == 2 || screen_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screen type: 2 (perforated plate) in {1,2,3}");
}

#[test]
fn sludge_type_valid_disjunction() {
    // Sludge type: 1=municipal, 2=industrial, 3=food processing
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sludge_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "sludge_type == 3")); // food processing
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "sludge_type == 1 || sludge_type == 2 || sludge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sludge type: 3 (food processing) in {1,2,3}");
}

#[test]
fn operating_pressure_scaled_bounded() {
    // Operating pressure in x10 kPa (500 = 50.0 kPa, 2000 = 200.0 kPa)
    // Typical range: 100-3000 (10.0-300.0 kPa)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "pressure_x10 == 500")); // 50.0 kPa
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if pressure_x10 >= 100 && pressure_x10 <= 3000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure: 500 (50.0 kPa) in [100, 3000]");
}

#[test]
fn polymer_dosage_scaled_bounded() {
    // Polymer dosage in x100 kg/ton (250 = 2.50 kg/ton, 800 = 8.00 kg/ton)
    // Typical range: 100-1500 (1.00-15.00 kg/ton)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dosage_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "dosage_x100 == 450")); // 4.50 kg/ton
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dosage_x100 >= 100 && dosage_x100 <= 1500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "polymer dosage: 450 (4.50 kg/ton) in [100, 1500]");
}

#[test]
fn auto_wash_boolean_flag() {
    // Auto-wash enabled: i32 flag (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_wash", i32_ty());
    ctx.declare_var_typed("wash_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("aw", "auto_wash == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume(
        "wa_def",
        "wash_active == if auto_wash == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("active", "wash_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-wash: flag=1 -> active");
}
