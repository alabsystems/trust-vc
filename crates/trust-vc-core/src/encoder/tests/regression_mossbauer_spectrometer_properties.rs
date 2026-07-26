// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_mossbauer_spec_velocity_range_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "velocity_range",
        "velocity_x100 >= 100 && velocity_x100 <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "velocity_bounded",
        "velocity_x100 >= 100 && velocity_x100 <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Doppler velocity x100 must be between 100 and 15000 (1.00-150.00 mm/s)",
    );
}

#[test]
fn test_mossbauer_spec_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "channel_range",
        "channels >= 256 && channels <= 4096",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "channel_bounded",
        "channels >= 256 && channels <= 4096",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count must be between 256 and 4096");
}

#[test]
fn test_mossbauer_spec_source_activity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("activity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "activity_range",
        "activity >= 5 && activity <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "activity_bounded",
        "activity >= 5 && activity <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "source activity must be between 5 and 100 mCi");
}

#[test]
fn test_mossbauer_spec_collection_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_sec", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_range",
        "time_sec >= 1 && time_sec <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_bounded",
        "time_sec >= 1 && time_sec <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collection time must be between 1 and 10000 seconds",
    );
}

#[test]
fn test_mossbauer_spec_energy_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution_x10 >= 1 && resolution_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_bounded",
        "resolution_x10 >= 1 && resolution_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy resolution x10 must be between 1 and 100 (0.1-10.0 eV)",
    );
}

#[test]
fn test_mossbauer_spec_temperature_range_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset500", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_offset500 >= 0 && temp_offset500 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_offset500 >= 0 && temp_offset500 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature offset+500 must be between 0 and 1500 (representing -500 to 1000 K)",
    );
}

#[test]
fn test_mossbauer_spec_source_isotope_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("isotope", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "isotope_range",
        "isotope >= 1 && isotope <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "isotope_valid",
        "isotope >= 1 && isotope <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "source isotope must be 1=Co-57, 2=Fe-57, or 3=Sn-119",
    );
}

#[test]
fn test_mossbauer_spec_geometry_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geometry", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "geometry_range",
        "geometry >= 1 && geometry <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "geometry_valid",
        "geometry >= 1 && geometry <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geometry must be 1=transmission, 2=backscatter, or 3=conversion-electron",
    );
}

#[test]
fn test_mossbauer_spec_drive_waveform_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "waveform_range",
        "waveform >= 1 && waveform <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "waveform_valid",
        "waveform >= 1 && waveform <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive waveform must be 1=constant-acceleration, 2=sinusoidal, or 3=constant-velocity",
    );
}

#[test]
fn test_mossbauer_spec_auto_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_cal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cal_range",
        "auto_cal >= 0 && auto_cal <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cal_valid",
        "auto_cal >= 0 && auto_cal <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto-calibration flag must be 0=disabled or 1=enabled",
    );
}
