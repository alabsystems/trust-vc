// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_do_range_ppb() {
    // Dissolved oxygen measurement in ppb: value 8000, min 0, max 50000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("do_ppb", u32_ty());
    ctx.declare_var_typed("range_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "do_ppb == 8000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "range_ok == if do_ppb >= 0 && do_ppb <= 50000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: 8000 ppb in [0, 50000]");
}

#[test]
fn test_accuracy_x10_percent() {
    // Accuracy in tenths of percent: value 10 (1.0%), min 5, max 50
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
    expect_verified(&result, "DO: accuracy 10 (1.0%) in [5, 50]");
}

#[test]
fn test_sensor_type_disjunction() {
    // Sensor type: 1=optical luminescence, 2=galvanic, 3=polarographic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "sensor_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DO: sensor type 1 (optical luminescence) in {1,2,3}",
    );
}

#[test]
fn test_response_time_t90_seconds() {
    // T90 response time in seconds: value 60, min 10, max 300
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t90_s", u32_ty());
    ctx.declare_var_typed("resp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "t90_s == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "resp_ok == if t90_s >= 10 && t90_s <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: T90 response 60s in [10, 300]");
}

#[test]
fn test_sample_temp_offset_500() {
    // Sample temperature offset +500 in degrees C: value 525 (25C), min 460 (-40C), max 560 (60C)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", u32_ty());
    ctx.declare_var_typed("temp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "temp_off == 525"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "temp_ok == if temp_off >= 460 && temp_off <= 560 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: temp offset 525 (25C) in [460, 560]");
}

#[test]
fn test_pressure_compensation_kpa() {
    // Barometric pressure compensation in kPa: value 101, min 80, max 120
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_kpa", u32_ty());
    ctx.declare_var_typed("press_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "pressure_kpa == 101"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "press_ok == if pressure_kpa >= 80 && pressure_kpa <= 120 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: pressure 101 kPa in [80, 120]");
}

#[test]
fn test_output_type_disjunction() {
    // Output type: 1=4-20mA, 2=Modbus, 3=HART
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "output_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output_type == 1 || output_type == 2 || output_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: output type 1 (4-20mA) in {1,2,3}");
}

#[test]
fn test_calibration_interval_days() {
    // Calibration/maintenance interval in days: value 30, min 7, max 365
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal_days", u32_ty());
    ctx.declare_var_typed("cal_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "cal_days == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "cal_ok == if cal_days >= 7 && cal_days <= 365 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "cal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: calibration interval 30 days in [7, 365]");
}

#[test]
fn test_salinity_compensation_x10_ppt() {
    // Salinity compensation in tenths of ppt: value 0 (freshwater), min 0, max 400
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("salinity_x10", u32_ty());
    ctx.declare_var_typed("sal_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "salinity_x10 == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "sal_ok == if salinity_x10 >= 0 && salinity_x10 <= 400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "sal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: salinity 0 (freshwater) in [0, 400]");
}

#[test]
fn test_auto_cleaning_boolean_flag() {
    // Auto-cleaning enabled flag (i32: 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_clean", i32_ty());
    ctx.declare_var_typed("maintenance_reduced", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac", "auto_clean == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mr_def",
        "maintenance_reduced == if auto_clean == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "maintenance_reduced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DO: auto-cleaning flag 1 -> maintenance reduced");
}
