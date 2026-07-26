// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_strain_gauge_amp_gain_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain", i32_ty());
    ctx.push_obligation(ProofObligation::assume("gain_val", "gain == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "gain_bounded",
        "gain >= 1 && gain <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "strain gauge amp gain 1000 in [1, 10000]");
}

#[test]
fn test_strain_gauge_amp_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bw_val", "bw == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bw_bounded",
        "bw >= 10 && bw <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strain gauge amp bandwidth 5000 Hz in [10, 100000]",
    );
}

#[test]
fn test_strain_gauge_amp_excitation_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "excitation_val",
        "excitation == 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "excitation_bounded",
        "excitation >= 1000 && excitation <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strain gauge amp excitation 5000 mV (5V) in [1000, 15000]",
    );
}

#[test]
fn test_strain_gauge_amp_bridge_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bridge_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bt_val", "bridge_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_bridge",
        "bridge_type == 1 || bridge_type == 2 || bridge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strain gauge amp bridge type 3 (full) in {1=quarter,2=half,3=full}",
    );
}

#[test]
fn test_strain_gauge_amp_input_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume("channels_val", "channels == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "channels_bounded",
        "channels >= 1 && channels <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "strain gauge amp input channels 8 in [1, 64]");
}

#[test]
fn test_strain_gauge_amp_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_val",
        "accuracy_x100 == 5",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_bounded",
        "accuracy_x100 >= 1 && accuracy_x100 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "strain gauge amp accuracy 5 (0.05% FS) in [1, 50]");
}

#[test]
fn test_strain_gauge_amp_adc_resolution_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bits_val", "bits == 24"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_bits",
        "bits == 16 || bits == 20 || bits == 24 || bits == 32",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strain gauge amp ADC resolution 24 in {16, 20, 24, 32}",
    );
}

#[test]
fn test_strain_gauge_amp_output_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot_val", "output_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_output",
        "output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strain gauge amp output type 2 (USB) in {1=analog,2=USB,3=Ethernet,4=fieldbus}",
    );
}

#[test]
fn test_strain_gauge_amp_operating_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 460 && temp <= 585",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strain gauge amp temp 520 (20C offset+500) in [460 (-40C), 585 (85C)]",
    );
}

#[test]
fn test_strain_gauge_amp_shunt_calibration_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("shunt_cal_enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sce_def",
        "shunt_cal_enabled == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("enabled", "shunt_cal_enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strain gauge amp shunt calibration flag=1 → enabled",
    );
}
