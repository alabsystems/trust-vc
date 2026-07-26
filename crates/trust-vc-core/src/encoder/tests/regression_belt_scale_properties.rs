// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_capacity_tonnes_per_hour() {
    let mut ctx = VerificationContext::new();
    for v in &["throughput", "min_throughput", "max_throughput"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Belt scale capacity in tonnes/hour
    ctx.push_obligation(ProofObligation::assume("tp", "throughput == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_throughput == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_throughput == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if throughput >= min_throughput && throughput <= max_throughput { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: 500 t/h in [10, 10000] range");
}

#[test]
fn test_accuracy_class_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // Belt scale accuracy classes: 1=class 0.5, 2=class 1, 3=class 2, 4=class 5
    ctx.push_obligation(ProofObligation::assume("ac", "acc_class == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_class == if acc_class == 1 || acc_class == 2 || acc_class == 3 || acc_class == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: class 1 is valid accuracy class");
}

#[test]
fn test_belt_speed_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_x100", "min_speed_x100", "max_speed_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Belt speed in m/s scaled by 100: 250 = 2.50 m/s
    ctx.push_obligation(ProofObligation::assume("sp", "speed_x100 == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_speed_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_speed_x100 == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if speed_x100 >= min_speed_x100 && speed_x100 <= max_speed_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: 2.50 m/s in [0.50, 8.00] range");
}

#[test]
fn test_belt_width_mm() {
    let mut ctx = VerificationContext::new();
    for v in &["width_mm", "min_width_mm", "max_width_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("width_ok", i32_ty());
    // Conveyor belt width in millimeters
    ctx.push_obligation(ProofObligation::assume("wm", "width_mm == 1200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_width_mm == 300"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_width_mm == 2400"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "width_ok == if width_mm >= min_width_mm && width_mm <= max_width_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "width_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: 1200mm width in [300, 2400] range");
}

#[test]
fn test_idler_count() {
    let mut ctx = VerificationContext::new();
    for v in &["idlers", "min_idlers", "max_idlers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("idler_ok", i32_ty());
    // Weighing idler count
    ctx.push_obligation(ProofObligation::assume("id", "idlers == 2"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_idlers == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_idlers == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "idler_ok == if idlers >= min_idlers && idlers <= max_idlers { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "idler_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: 2 idlers in [1, 8] range");
}

#[test]
fn test_load_cell_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_type", u32_ty());
    ctx.declare_var_typed("valid_cell", i32_ty());
    // Load cell types: 1=strain gauge, 2=piezoelectric, 3=capacitive
    ctx.push_obligation(ProofObligation::assume("ct", "cell_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cell == if cell_type == 1 || cell_type == 2 || cell_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cell == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: strain gauge is valid load cell type");
}

#[test]
fn test_communication_protocol_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("protocol", u32_ty());
    ctx.declare_var_typed("valid_proto", i32_ty());
    // Communication protocols: 1=4-20mA, 2=Profibus, 3=Modbus, 4=Ethernet
    ctx.push_obligation(ProofObligation::assume("pr", "protocol == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_proto == if protocol == 1 || protocol == 2 || protocol == 3 || protocol == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_proto == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Belt scale: Modbus is valid communication protocol",
    );
}

#[test]
fn test_totalizer_resolution_kg() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_kg", "min_resolution_kg", "max_resolution_kg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Totalizer integration resolution in kg
    ctx.push_obligation(ProofObligation::assume("rk", "resolution_kg == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_resolution_kg == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_resolution_kg == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_kg >= min_resolution_kg && resolution_kg <= max_resolution_kg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: 1kg resolution in [0, 100] range");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_off", "min_temp_off", "max_temp_off"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature offset by +500 to avoid negatives:
    // 525 = 25 deg C, 460 = -40 deg C, 585 = 85 deg C
    ctx.push_obligation(ProofObligation::assume("to", "temp_off == 525"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_off == 460"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_off == 585"));
    ctx.push_obligation(ProofObligation::assume(
        "tk_def",
        "temp_ok == if temp_off >= min_temp_off && temp_off <= max_temp_off { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Belt scale: 25 deg C (offset 525) in [-40, 85] range",
    );
}

#[test]
fn test_zero_tracking_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zero_tracking", i32_ty());
    ctx.declare_var_typed("enabled", i32_ty());
    // Zero tracking: automatic zero correction enabled (1) or disabled (0)
    ctx.push_obligation(ProofObligation::assume("zt", "zero_tracking == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "en_def",
        "enabled == if zero_tracking == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belt scale: zero tracking enabled flag is 1");
}
