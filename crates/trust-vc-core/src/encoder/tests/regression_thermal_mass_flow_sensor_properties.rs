// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_full_scale_sccm() {
    let mut ctx = VerificationContext::new();
    for v in &["sccm", "sccm_min", "sccm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Full scale flow capacity in sccm: value 1000, valid range 1 to 500000
    ctx.push_obligation(ProofObligation::assume("fs_val", "sccm == 1000"));
    ctx.push_obligation(ProofObligation::assume("fs_min", "sccm_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fs_max", "sccm_max == 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "fs_in_range",
        "sccm >= sccm_min && sccm <= sccm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "full scale 1000 sccm in range [1,500000]");
}

#[test]
fn test_accuracy_x100() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x100", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy as x100 %: value 100 (1.00%), valid range 25 (0.25%) to 300 (3.00%)
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "acc_min == 25"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "acc_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "acc_x100 >= acc_min && acc_x100 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy 100 (1.00%) in range [25,300] (0.25%-3.00%)",
    );
}

#[test]
fn test_repeatability_x100() {
    let mut ctx = VerificationContext::new();
    for v in &["rep_x100", "rep_min", "rep_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Repeatability as x100 %: value 25 (0.25%), valid range 5 (0.05%) to 100 (1.00%)
    ctx.push_obligation(ProofObligation::assume("rp_val", "rep_x100 == 25"));
    ctx.push_obligation(ProofObligation::assume("rp_min", "rep_min == 5"));
    ctx.push_obligation(ProofObligation::assume("rp_max", "rep_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "rp_in_range",
        "rep_x100 >= rep_min && rep_x100 <= rep_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "repeatability 25 (0.25%) in range [5,100] (0.05%-1.00%)",
    );
}

#[test]
fn test_response_time_ms() {
    let mut ctx = VerificationContext::new();
    for v in &["t63_ms", "t63_min", "t63_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time T63 in ms: value 500, valid range 10 to 5000
    ctx.push_obligation(ProofObligation::assume("rt_val", "t63_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "t63_min == 10"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "t63_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "t63_ms >= t63_min && t63_ms <= t63_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 500 ms (T63) in range [10,5000]");
}

#[test]
fn test_gas_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", u32_ty());
    ctx.declare_var_typed("valid_gas", i32_ty());
    // 1=air, 2=N2, 3=O2, 4=Ar, 5=CO2
    ctx.push_obligation(ProofObligation::assume("gt_val", "gas == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "gt_valid_def",
        "valid_gas == if gas == 1 || gas == 2 || gas == 3 || gas == 4 || gas == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gt_check", "valid_gas == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas type 1 (air) is valid");
}

#[test]
fn test_sensor_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("element", u32_ty());
    ctx.declare_var_typed("valid_element", i32_ty());
    // 1=MEMS, 2=capillary, 3=inline
    ctx.push_obligation(ProofObligation::assume("se_val", "element == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "se_valid_def",
        "valid_element == if element == 1 || element == 2 || element == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("se_check", "valid_element == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor element 1 (MEMS) is valid");
}

#[test]
fn test_output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // 1=4-20mA, 2=0-5V, 3=RS485, 4=digital
    ctx.push_obligation(ProofObligation::assume("ot_val", "output == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_valid_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_check", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 1 (4-20mA) is valid");
}

#[test]
fn test_operating_pressure_kpa() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_kpa", "press_min", "press_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating pressure max in kPa: value 1000, valid range 100 to 10000
    ctx.push_obligation(ProofObligation::assume("op_val", "pressure_kpa == 1000"));
    ctx.push_obligation(ProofObligation::assume("op_min", "press_min == 100"));
    ctx.push_obligation(ProofObligation::assume("op_max", "press_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "op_in_range",
        "pressure_kpa >= press_min && pressure_kpa <= press_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating pressure 1000 kPa in range [100,10000]");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_off", "temp_off_min", "temp_off_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temp offset +500: value 525 (25C), min 460 (-40C), max 600 (100C)
    ctx.push_obligation(ProofObligation::assume("to_val", "temp_off == 525"));
    ctx.push_obligation(ProofObligation::assume("to_min", "temp_off_min == 460"));
    ctx.push_obligation(ProofObligation::assume("to_max", "temp_off_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "to_in_range",
        "temp_off >= temp_off_min && temp_off <= temp_off_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 525 (25C) in range [460,600] (-40C to 100C)",
    );
}

#[test]
fn test_bidirectional_flow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bidir", i32_ty());
    ctx.declare_var_typed("supports_reverse", i32_ty());
    // Boolean flag: 1=bidirectional, 0=unidirectional
    ctx.push_obligation(ProofObligation::assume("bf_val", "bidir == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sr_def",
        "supports_reverse == if bidir == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sr_check", "supports_reverse == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bidirectional flow flag 1 → supports reverse flow");
}
