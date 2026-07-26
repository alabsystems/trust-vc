// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn wavelength() {
    let mut ctx = VerificationContext::new();
    for v in &["wavelength_pm", "min_wl_pm", "max_wl_pm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wl_ok", i32_ty());
    // Bragg wavelength in picometers (1550.000 nm = 1550000 pm)
    ctx.push_obligation(ProofObligation::assume("wp", "wavelength_pm == 1550000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_wl_pm == 800000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_wl_pm == 1600000"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wl_ok == if wavelength_pm >= min_wl_pm && wavelength_pm <= max_wl_pm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 1550nm wavelength in [800, 1600] nm range");
}

#[test]
fn strain_range() {
    let mut ctx = VerificationContext::new();
    for v in &["microstrain", "max_microstrain"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("strain_ok", i32_ty());
    // Microstrain (με) measurement range
    ctx.push_obligation(ProofObligation::assume("ms", "microstrain == 5000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_microstrain == 15000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "strain_ok == if microstrain <= max_microstrain { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "strain_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 5000 με strain within 15000 με max");
}

#[test]
fn temperature_range() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Temperature offset +500: -40°C=460, 20°C=520, 300°C=800
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 20°C (offset 520) in [-40, 300]°C range");
}

#[test]
fn reflectivity() {
    let mut ctx = VerificationContext::new();
    for v in &["refl_x10", "min_refl_x10", "max_refl_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("refl_ok", i32_ty());
    // Grating reflectivity percentage (×10): 90.0% = 900
    ctx.push_obligation(ProofObligation::assume("rx", "refl_x10 == 900"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_refl_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_refl_x10 == 999"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "refl_ok == if refl_x10 >= min_refl_x10 && refl_x10 <= max_refl_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "refl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 90.0% reflectivity in [10.0, 99.9]%");
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_pm", "min_bw_pm", "max_bw_pm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // 3dB bandwidth in picometers
    ctx.push_obligation(ProofObligation::assume("bp", "bw_pm == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw_pm == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw_pm == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_pm >= min_bw_pm && bw_pm <= max_bw_pm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 200pm 3dB bandwidth in [50, 1000] pm");
}

#[test]
fn grating_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_mm", "min_len_mm", "max_len_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // Physical grating length in mm
    ctx.push_obligation(ProofObligation::assume("lm", "length_mm == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_len_mm == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_len_mm == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if length_mm >= min_len_mm && length_mm <= max_len_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 10mm grating length in [1, 100] mm");
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor", u32_ty());
    ctx.declare_var_typed("valid_sensor", i32_ty());
    // Sensor types: 1=strain, 2=temperature, 3=pressure, 4=acceleration
    ctx.push_obligation(ProofObligation::assume("s", "sensor == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_sensor == if sensor == 1 || sensor == 2 || sensor == 3 || sensor == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_sensor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: strain (1) is valid sensor type");
}

#[test]
fn multiplexing_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sensors", "min_sensors", "max_sensors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mux_ok", i32_ty());
    // WDM multiplexed sensors per fiber
    ctx.push_obligation(ProofObligation::assume("sc", "sensors == 16"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_sensors == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_sensors == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mux_ok == if sensors >= min_sensors && sensors <= max_sensors { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mux_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 16 WDM sensors in [1, 100] per fiber");
}

#[test]
fn strain_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["res_x10", "max_res_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Microstrain resolution (×10): 1.0 με = 10
    ctx.push_obligation(ProofObligation::assume("rx", "res_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_res_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if res_x10 <= max_res_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 1.0 με resolution within 10.0 με max");
}

#[test]
fn interrogation_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_hz", "min_rate_hz", "max_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Interrogation measurement rate in Hz
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate_hz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_hz >= min_rate_hz && rate_hz <= max_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FBG: 1000 Hz interrogation in [1, 10000] Hz");
}
