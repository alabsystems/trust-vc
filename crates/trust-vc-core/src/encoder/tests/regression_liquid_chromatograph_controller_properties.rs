use super::*;

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

/// Max pressure in bar: bounded [200, 1500], concrete value 400.
#[test]
fn test_max_pressure_bar_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure_bar", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mp_val", "max_pressure_bar == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "max_pressure_bar >= 200 && max_pressure_bar <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max pressure 400 bar within valid range [200, 1500]",
    );
}

/// Flow rate scaled x100 in mL/min: 50 represents 0.50 mL/min, bounded [1, 1000].
#[test]
fn test_flow_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fr_val", "flow_rate_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_rate_x100 >= 1 && flow_rate_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate 0.50 mL/min (x100=50) within valid range [1, 1000]",
    );
}

/// Column length in mm: bounded [30, 300], concrete value 150.
#[test]
fn test_column_length_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("column_length_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cl_val", "column_length_mm == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "length_bounded",
        "column_length_mm >= 30 && column_length_mm <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column length 150 mm within valid range [30, 300]");
}

/// Column inner diameter scaled x100 in mm: 460 represents 4.60 mm, bounded [21, 5000].
#[test]
fn test_column_diameter_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col_diameter_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cd_val",
        "col_diameter_x100 == 460",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_bounded",
        "col_diameter_x100 >= 21 && col_diameter_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "column diameter 4.60 mm (x100=460) within valid range [21, 5000]",
    );
}

/// Detector wavelength in nm: bounded [190, 900], concrete value 254.
#[test]
fn test_wavelength_range_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_val", "wavelength_nm == 254"));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_bounded",
        "wavelength_nm >= 190 && wavelength_nm <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength 254 nm within valid range [190, 900]");
}

/// Detector type: 3-way disjunction (1=UV-Vis, 2=fluorescence, 3=refractive index).
#[test]
fn test_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dt_val", "detector_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_detector",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fluorescence (2) is a valid detector type");
}

/// Pump type: 3-way disjunction (1=binary, 2=quaternary, 3=isocratic).
#[test]
fn test_pump_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pt_val", "pump_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_pump",
        "pump_type == 1 || pump_type == 2 || pump_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "binary (1) is a valid pump type");
}

/// Injection volume scaled x10 in uL: 50 represents 5.0 uL, bounded [1, 1000].
#[test]
fn test_injection_volume_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_volume_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("iv_val", "inj_volume_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "volume_bounded",
        "inj_volume_x10 >= 1 && inj_volume_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "injection volume 5.0 uL (x10=50) within valid range [1, 1000]",
    );
}

/// Sample capacity (number of vial positions): bounded [1, 384], concrete value 96.
#[test]
fn test_sample_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_capacity", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sc_val", "sample_capacity == 96"));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_bounded",
        "sample_capacity >= 1 && sample_capacity <= 384",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample capacity 96 vials within valid range [1, 384]",
    );
}

/// Column thermostat: boolean flag (i32, 1=enabled, 0=disabled).
#[test]
fn test_column_thermostat_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thermostat_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tf_val", "thermostat_flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "thermostat_on",
        "if thermostat_flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column thermostat flag=1 evaluates to enabled");
}
