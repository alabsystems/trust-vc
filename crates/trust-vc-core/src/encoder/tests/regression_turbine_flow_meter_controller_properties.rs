//! Turbine flow meter controller property regression tests.
//!
//! These tests verify bounded-range and enumeration properties for turbine
//! flow meter controller parameters: pipe size, flow range, accuracy,
//! repeatability, pressure rating, operating temperature, blade material,
//! bearing type, output signal, and bidirectional flag.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_turbine_meter_pipe_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pipe", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pipe_lo", "pipe >= 6"));
    ctx.push_obligation(ProofObligation::assume("pipe_hi", "pipe <= 600"));
    ctx.push_obligation(ProofObligation::assert(
        "pipe_bounded",
        "pipe >= 6 && pipe <= 600",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipe size 6-600mm should verify as bounded");
}

#[test]
fn test_turbine_meter_flow_range_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_lo", "flow_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assume("flow_hi", "flow_x10 <= 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 100000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow range x10 (0.1 L/min precision) should verify as bounded",
    );
}

#[test]
fn test_turbine_meter_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_lo", "acc_x100 >= 5"));
    ctx.push_obligation(ProofObligation::assume("acc_hi", "acc_x100 <= 200"));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x100 >= 5 && acc_x100 <= 200",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x100 (0.01% precision) should verify as bounded",
    );
}

#[test]
fn test_turbine_meter_repeatability_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rep_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rep_lo", "rep_x1000 >= 1"));
    ctx.push_obligation(ProofObligation::assume("rep_hi", "rep_x1000 <= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "rep_bounded",
        "rep_x1000 >= 1 && rep_x1000 <= 100",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "repeatability x1000 (0.001% precision) should verify as bounded",
    );
}

#[test]
fn test_turbine_meter_pressure_rating_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press", i32_ty());
    ctx.push_obligation(ProofObligation::assume("press_lo", "press >= 150"));
    ctx.push_obligation(ProofObligation::assume("press_hi", "press <= 6000"));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press >= 150 && press <= 6000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pressure rating 150-6000 psi should verify as bounded",
    );
}

#[test]
fn test_turbine_meter_operating_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_lo", "temp >= 460"));
    ctx.push_obligation(ProofObligation::assume("temp_hi", "temp <= 750"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 460 && temp <= 750",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp offset +500 (-40C to 250C -> 460 to 750) should verify as bounded",
    );
}

#[test]
fn test_turbine_meter_blade_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_enum",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade material (1=stainless, 2=Hastelloy, 3=titanium) should verify",
    );
}

#[test]
fn test_turbine_meter_bearing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("brg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "brg_enum",
        "brg == 1 || brg == 2 || brg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "brg_valid",
        "brg == 1 || brg == 2 || brg == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type (1=ball, 2=sleeve, 3=ceramic) should verify",
    );
}

#[test]
fn test_turbine_meter_output_signal_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sig", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sig_enum",
        "sig == 1 || sig == 2 || sig == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sig_valid",
        "sig == 1 || sig == 2 || sig == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output signal (1=pulse, 2=4-20mA, 3=frequency) should verify",
    );
}

#[test]
fn test_turbine_meter_bidirectional_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bidir", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bidir_bool",
        "bidir == 0 || bidir == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bidir_valid",
        "bidir == 0 || bidir == 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bidirectional flow flag (0 or 1) should verify");
}
