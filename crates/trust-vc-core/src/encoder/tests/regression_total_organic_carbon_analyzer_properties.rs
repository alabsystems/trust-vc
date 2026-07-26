// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_measurement_range_ppb() {
    // TOC measurement range in ppb: value 50000, min 1, max 100000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range", u32_ty());
    ctx.declare_var_typed("range_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "range == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "range_ok == if range >= 1 && range <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: range 50000 ppb in [1, 100000]");
}

#[test]
fn test_detection_limit_ppb() {
    // Detection limit in ppb: value 2, min 1, max 50
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit", u32_ty());
    ctx.declare_var_typed("limit_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "limit == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "limit_ok == if limit >= 1 && limit <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "limit_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: detection limit 2 ppb in [1, 50]");
}

#[test]
fn test_accuracy_x10_percent() {
    // Accuracy in tenths of percent: value 20 (2.0%), min 5, max 50
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.declare_var_typed("acc_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "acc_ok == if accuracy_x10 >= 5 && accuracy_x10 <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: accuracy 20 (2.0%) in [5, 50]");
}

#[test]
fn test_oxidation_method_disjunction() {
    // Oxidation method: 1=UV persulfate, 2=combustion, 3=UV only
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ox_method", u32_ty());
    ctx.declare_var_typed("valid_ox", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "ox_method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_ox == if ox_method == 1 || ox_method == 2 || ox_method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_ox == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOC: oxidation method 1 (UV persulfate) in {1,2,3}",
    );
}

#[test]
fn test_detection_method_disjunction() {
    // Detection method: 1=NDIR, 2=conductivity, 3=membrane conductivity
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_method", u32_ty());
    ctx.declare_var_typed("valid_det", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "det_method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_det == if det_method == 1 || det_method == 2 || det_method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_det == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: detection method 1 (NDIR) in {1,2,3}");
}

#[test]
fn test_sample_volume_ml() {
    // Sample volume in mL: value 50, min 1, max 500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", u32_ty());
    ctx.declare_var_typed("vol_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "volume == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "vol_ok == if volume >= 1 && volume <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "vol_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: sample volume 50 mL in [1, 500]");
}

#[test]
fn test_response_time_min() {
    // Response time in minutes: value 5, min 1, max 30
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response", u32_ty());
    ctx.declare_var_typed("resp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "response == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "resp_ok == if response >= 1 && response <= 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: response time 5 min in [1, 30]");
}

#[test]
fn test_communication_protocol_disjunction() {
    // Communication: 1=4-20mA, 2=Modbus, 3=Profibus, 4=Ethernet
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "comm == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_comm == if comm == 1 || comm == 2 || comm == 3 || comm == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: communication 2 (Modbus) in {1,2,3,4}");
}

#[test]
fn test_operating_temp_offset_500() {
    // Operating temperature offset +500 in degrees C: value 520 (20C), min 495 (-5C), max 545 (45C)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", u32_ty());
    ctx.declare_var_typed("temp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "temp_off == 520"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "temp_ok == if temp_off >= 495 && temp_off <= 545 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TOC: temp offset 520 (20C) in [495, 545]");
}

#[test]
fn test_auto_calibration_boolean_flag() {
    // Auto-calibration enabled flag (i32: 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_cal", i32_ty());
    ctx.declare_var_typed("cal_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac", "auto_cal == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "cal_active == if auto_cal == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "cal_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOC: auto-calibration flag 1 -> calibration active",
    );
}
