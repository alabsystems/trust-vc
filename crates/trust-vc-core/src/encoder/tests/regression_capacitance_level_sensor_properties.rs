// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_probe_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", u32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "length == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "length >= 100 && length <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Capacitance level: 2000mm probe in [100, 6000]");
}

#[test]
fn test_measurement_range_x10_pf_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "range_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "range_x10 >= 10 && range_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Capacitance level: 50.0 pF range in [1.0, 1000.0]");
}

#[test]
fn test_medium_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("medium", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "medium == 1 || medium == 2 || medium == 3 || medium == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "medium == 1 || medium == 2 || medium == 3 || medium == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitance level: medium type in {liquid, granular, powder, slurry}",
    );
}

#[test]
fn test_probe_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitance level: probe material in {stainless steel, PTFE coated, ceramic}",
    );
}

#[test]
fn test_process_pressure_kpa_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "pressure == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pressure >= 0 && pressure <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Capacitance level: 1000 kPa pressure in [0, 4000]");
}

#[test]
fn test_accuracy_x100_percent_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "accuracy_x100 >= 5 && accuracy_x100 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitance level: 0.50% accuracy in [0.05%, 2.00%]",
    );
}

#[test]
fn test_output_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "output == 1 || output == 2 || output == 3 || output == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "output == 1 || output == 2 || output == 3 || output == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitance level: output type in {4-20mA, HART, relay, Modbus}",
    );
}

#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    // 40 deg C stored as 540 (offset +500), range -40 to 200 deg C → 460 to 700
    ctx.push_obligation(ProofObligation::assume("val", "temp == 540"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "temp >= 460 && temp <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitance level: 40 deg C (offset 540) in [460, 700]",
    );
}

#[test]
fn test_ip_rating_non_sequential_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "ip == 65 || ip == 67 || ip == 68",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "ip == 65 || ip == 67 || ip == 68",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Capacitance level: IP rating in {65, 67, 68}");
}

#[test]
fn test_empty_calibration_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "calibrated",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Capacitance level: empty calibration flag enabled");
}
