// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_measurement_range_ppm() {
    // Thermal conductivity measurement range in ppm: value 5000, min 1, max 100000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc_ppm", u32_ty());
    ctx.declare_var_typed("range_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "tc_ppm == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "range_ok == if tc_ppm >= 1 && tc_ppm <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: 5000 ppm in [1, 100000]");
}

#[test]
fn test_accuracy_x10_percent_reading() {
    // Accuracy in tenths of percent of reading: value 10 (1.0%), min 5, max 50
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.declare_var_typed("acc_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "acc_ok == if accuracy_x10 >= 5 && accuracy_x10 <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: accuracy 10 (1.0% reading) in [5, 50]");
}

#[test]
fn test_reference_gas_disjunction() {
    // Reference gas: 1=air, 2=nitrogen, 3=argon
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_gas", u32_ty());
    ctx.declare_var_typed("valid_gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "ref_gas == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vg_def",
        "valid_gas == if ref_gas == 1 || ref_gas == 2 || ref_gas == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_gas == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: reference gas 2 (nitrogen) in {1,2,3}");
}

#[test]
fn test_sample_flow_ml_min() {
    // Sample flow rate in mL/min: value 200, min 50, max 2000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_ml", u32_ty());
    ctx.declare_var_typed("flow_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flow_ml == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "flow_ok == if flow_ml >= 50 && flow_ml <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: sample flow 200 mL/min in [50, 2000]");
}

#[test]
fn test_response_time_t90_seconds() {
    // T90 response time in seconds: value 15, min 1, max 60
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t90_s", u32_ty());
    ctx.declare_var_typed("resp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "t90_s == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "resp_ok == if t90_s >= 1 && t90_s <= 60 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: T90 response 15s in [1, 60]");
}

#[test]
fn test_cell_type_disjunction() {
    // Cell type: 1=filament, 2=thermistor, 3=MEMS
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_type", u32_ty());
    ctx.declare_var_typed("valid_cell", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "cell_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cell == if cell_type == 1 || cell_type == 2 || cell_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_cell == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: cell type 1 (filament) in {1,2,3}");
}

#[test]
fn test_sample_pressure_kpa() {
    // Sample pressure in kPa: value 101, min 50, max 500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_kpa", u32_ty());
    ctx.declare_var_typed("press_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "pressure_kpa == 101"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "press_ok == if pressure_kpa >= 50 && pressure_kpa <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: pressure 101 kPa in [50, 500]");
}

#[test]
fn test_output_type_disjunction() {
    // Output type: 1=4-20mA, 2=RS-485, 3=Modbus, 4=HART
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "output_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: output type 3 (Modbus) in {1,2,3,4}");
}

#[test]
fn test_operating_temp_offset_500() {
    // Operating temperature offset +500: -50C to 80C maps to 450-580, value 520 (20C)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", u32_ty());
    ctx.declare_var_typed("temp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "temp_off == 520"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "temp_ok == if temp_off >= 450 && temp_off <= 580 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: temp offset 520 (20C) in [450, 580]");
}

#[test]
fn test_auto_zero_boolean_flag() {
    // Auto-zero enabled flag (i32: 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_zero", i32_ty());
    ctx.declare_var_typed("drift_corrected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("az", "auto_zero == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dc_def",
        "drift_corrected == if auto_zero == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "drift_corrected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCD: auto-zero flag 1 -> drift corrected");
}
