// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_ch", "max_ch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch_val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_ch == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_ch == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "channels_in_range",
        "channels >= min_ch && channels <= max_ch",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 4 channels in [1, 16] range");
}

#[test]
fn test_wavelength_range_pm() {
    let mut ctx = VerificationContext::new();
    for v in &["center_wl", "min_wl", "max_wl"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Wavelength in picometers: 1550.000nm = 1550000pm
    ctx.push_obligation(ProofObligation::assume("cw_val", "center_wl == 1550000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_wl == 1510000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_wl == 1590000"));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_in_range",
        "center_wl >= min_wl && center_wl <= max_wl",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FBG: 1550.000nm center wavelength in [1510, 1590] nm range",
    );
}

#[test]
fn test_resolution_pm() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution", "min_res", "max_res"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Resolution in picometers
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution == 1"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_res == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_res == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_in_range",
        "resolution >= min_res && resolution <= max_res",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 1pm resolution in [1, 100] pm range");
}

#[test]
fn test_scan_rate_hz() {
    let mut ctx = VerificationContext::new();
    for v in &["scan_rate", "min_rate", "max_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sr_val", "scan_rate == 1000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_rate == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_rate == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "scan_rate_in_range",
        "scan_rate >= min_rate && scan_rate <= max_rate",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 1000 Hz scan rate in [1, 10000] Hz range");
}

#[test]
fn test_sensor_count_per_channel() {
    let mut ctx = VerificationContext::new();
    for v in &["sensors", "min_sensors", "max_sensors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Multiplexed gratings per channel
    ctx.push_obligation(ProofObligation::assume("s_val", "sensors == 16"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_sensors == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_sensors == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "sensors_in_range",
        "sensors >= min_sensors && sensors <= max_sensors",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 16 sensors per channel in [1, 100] range");
}

#[test]
fn test_measurement_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_type", u32_ty());
    // 1=strain, 2=temperature, 3=pressure
    ctx.push_obligation(ProofObligation::assume("mt_val", "meas_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "meas_type == 1 || meas_type == 2 || meas_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FBG: measurement type 1 (strain) is valid 3-way disjunction",
    );
}

#[test]
fn test_light_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("light_src", u32_ty());
    // 1=swept laser, 2=broadband ASE, 3=tunable filter
    ctx.push_obligation(ProofObligation::assume("ls_val", "light_src == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source",
        "light_src == 1 || light_src == 2 || light_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FBG: light source 2 (broadband ASE) is valid 3-way disjunction",
    );
}

#[test]
fn test_strain_range_microstrain() {
    let mut ctx = VerificationContext::new();
    for v in &["strain_ue", "min_strain", "max_strain"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Microstrain range
    ctx.push_obligation(ProofObligation::assume("s_val", "strain_ue == 5000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_strain == 100"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_strain == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "strain_in_range",
        "strain_ue >= min_strain && strain_ue <= max_strain",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 5000 microstrain in [100, 30000] range");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Temperature with +500 offset: 25C = 525, -240C = 260, 300C = 800
    ctx.push_obligation(ProofObligation::assume("t_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_temp == 260"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_temp == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp_offset >= min_temp && temp_offset <= max_temp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FBG: 25C (offset 525) in [-240C, 300C] (offset [260, 800])",
    );
}

#[test]
fn test_dynamic_measurement_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_flag", i32_ty());
    ctx.declare_var_typed("scan_rate", u32_ty());
    ctx.declare_var_typed("effective_rate", u32_ty());
    // Dynamic mode doubles the scan rate; static mode uses base rate
    ctx.push_obligation(ProofObligation::assume("df_val", "dynamic_flag == 1"));
    ctx.push_obligation(ProofObligation::assume("sr_val", "scan_rate == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "effective_rate == if dynamic_flag == 1 { scan_rate + scan_rate } else { scan_rate }",
    ));
    ctx.push_obligation(ProofObligation::assert("doubled", "effective_rate == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FBG: dynamic mode doubles scan rate 1000 -> 2000 Hz",
    );
}
