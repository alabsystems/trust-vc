// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_microfluidic_evap_channel_width_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch_width_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cw_a",
        "ch_width_um >= 10 && ch_width_um <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cw_c",
        "ch_width_um >= 10 && ch_width_um <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel width in [10, 5000] um");
}

#[test]
fn test_microfluidic_evap_flow_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "flow_x100 >= 1 && flow_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "flow_x100 >= 1 && flow_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x100 in [1, 100000] representing 0.01-1000.00 uL/min",
    );
}

#[test]
fn test_microfluidic_evap_heater_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heater_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ht_a",
        "heater_temp >= 30 && heater_temp <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ht_c",
        "heater_temp >= 30 && heater_temp <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heater temperature in [30, 300] C");
}

#[test]
fn test_microfluidic_evap_channel_depth_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch_depth_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cd_a",
        "ch_depth_um >= 5 && ch_depth_um <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cd_c",
        "ch_depth_um >= 5 && ch_depth_um <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel depth in [5, 1000] um");
}

#[test]
fn test_microfluidic_evap_concentration_factor_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cf_a",
        "conc_x10 >= 10 && conc_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cf_c",
        "conc_x10 >= 10 && conc_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "concentration factor x10 in [10, 10000] representing 1.0-1000.0x",
    );
}

#[test]
fn test_microfluidic_evap_vapor_pressure_kpa_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vp_a",
        "vp_x10 >= 1 && vp_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vp_c",
        "vp_x10 >= 1 && vp_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vapor pressure x10 in [1, 10000] representing 0.1-1000.0 kPa",
    );
}

#[test]
fn test_microfluidic_evap_substrate_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("substrate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sb_a",
        "substrate == 1 || substrate == 2 || substrate == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sb_c",
        "substrate == 1 || substrate == 2 || substrate == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "substrate: PDMS, glass, or silicon");
}

#[test]
fn test_microfluidic_evap_heating_method_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hm_a",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hm_c",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating: resistive thin film, Peltier, or IR laser",
    );
}

#[test]
fn test_microfluidic_evap_geometry_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geometry", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gm_a",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gm_c",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geometry: serpentine, parallel channels, or radial",
    );
}

#[test]
fn test_microfluidic_evap_vacuum_assist_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_assist", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "va_a",
        "vac_assist == 0 || vac_assist == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "va_c",
        "vac_assist == 0 || vac_assist == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum assist flag is boolean");
}
