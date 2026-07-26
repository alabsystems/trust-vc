// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_arpes_photon_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "photon_energy_range",
        "energy >= 5 && energy <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "photon_energy_valid",
        "energy >= 5 && energy <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "photon energy in eV must be bounded [5, 2000]");
}

#[test]
fn test_arpes_energy_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_res_range",
        "res_x1000 >= 1 && res_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_res_valid",
        "res_x1000 >= 1 && res_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy resolution x1000 in meV must be bounded [1, 500]",
    );
}

#[test]
fn test_arpes_angular_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angular_res_range",
        "angle_x100 >= 1 && angle_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angular_res_valid",
        "angle_x100 >= 1 && angle_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "angular resolution x100 in 0.01 degrees must be bounded [1, 100]",
    );
}

#[test]
fn test_arpes_sample_temperature_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_offset_range",
        "temp_off >= 496 && temp_off <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_offset_valid",
        "temp_off >= 496 && temp_off <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample temperature offset +500 must be bounded [496, 1500] representing -4K to 1000K",
    );
}

#[test]
fn test_arpes_detector_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_channels_range",
        "channels >= 100 && channels <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_channels_valid",
        "channels >= 100 && channels <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector channels must be bounded [100, 10000]");
}

#[test]
fn test_arpes_light_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "light_source_enum",
        "src == 1 || src == 2 || src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "light_source_valid",
        "src == 1 || src == 2 || src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "light source must be 1=helium-lamp, 2=synchrotron, or 3=laser",
    );
}

#[test]
fn test_arpes_analyzer_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "analyzer_type_enum",
        "at == 1 || at == 2 || at == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analyzer_type_valid",
        "at == 1 || at == 2 || at == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer type must be 1=hemispherical, 2=cylindrical-mirror, or 3=time-of-flight",
    );
}

#[test]
fn test_arpes_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "measurement_mode_enum",
        "mm == 1 || mm == 2 || mm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "measurement_mode_valid",
        "mm == 1 || mm == 2 || mm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode must be 1=angle-mode, 2=transmission, or 3=spin-resolved",
    );
}

#[test]
fn test_arpes_auto_sample_alignment_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "alignment_flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "alignment_flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto sample alignment flag must be boolean 0 or 1");
}

#[test]
fn test_arpes_pass_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pass_energy_range",
        "pass >= 1 && pass <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pass_energy_valid",
        "pass >= 1 && pass <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pass energy in eV must be bounded [1, 500]");
}
