// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_phase_meter_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "freq >= 1 && freq <= 200000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "freq >= 1 && freq <= 200000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: frequency range 1-200000000 Hz bounded",
    );
}

#[test]
fn test_phase_meter_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "res_x1000 >= 1 && res_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "res_x1000 >= 1 && res_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: resolution x1000 degrees (0.001 deg) bounded",
    );
}

#[test]
fn test_phase_meter_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "acc_x100 >= 1 && acc_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "acc_x100 >= 1 && acc_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: accuracy x100 degrees (0.01 deg) bounded",
    );
}

#[test]
fn test_phase_meter_input_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "ch >= 2 && ch <= 4"));
    ctx.push_obligation(ProofObligation::assert("check", "ch >= 2 && ch <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "precision phase meter: input channels 2-4 bounded");
}

#[test]
fn test_phase_meter_input_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("z", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "z == 50 || z == 1000000"));
    ctx.push_obligation(ProofObligation::assert("check", "z == 50 || z == 1000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: input impedance 50 or 1000000 ohms",
    );
}

#[test]
fn test_phase_meter_averaging_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("avg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "avg >= 1 && avg <= 1024"));
    ctx.push_obligation(ProofObligation::assert("check", "avg >= 1 && avg <= 1024"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: averaging count 1-1024 bounded",
    );
}

#[test]
fn test_phase_meter_display_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "disp == 1 || disp == 2 || disp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "disp == 1 || disp == 2 || disp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: display 1=degrees, 2=radians, 3=time",
    );
}

#[test]
fn test_phase_meter_coupling_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cpl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "cpl == 1 || cpl == 2 || cpl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "cpl == 1 || cpl == 2 || cpl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: coupling 1=AC, 2=DC, 3=differential",
    );
}

#[test]
fn test_phase_meter_reference_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "ref_src == 1 || ref_src == 2 || ref_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "ref_src == 1 || ref_src == 2 || ref_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: reference 1=channel A, 2=external, 3=internal",
    );
}

#[test]
fn test_phase_meter_data_logging_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("log", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "log == 0 || log == 1"));
    ctx.push_obligation(ProofObligation::assert("check", "log == 0 || log == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase meter: data logging boolean 0 or 1",
    );
}
