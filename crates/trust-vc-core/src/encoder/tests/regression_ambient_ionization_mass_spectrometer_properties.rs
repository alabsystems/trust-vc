// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ambient_ion_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mass_lower", "mass >= 50"));
    ctx.push_obligation(ProofObligation::assume("mass_upper", "mass <= 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "mass_bounded",
        "mass >= 50 && mass <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range bounded 50-100000 amu");
}

#[test]
fn test_ambient_ion_ms_capillary_voltage_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("volt_lower", "voltage_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assume("volt_upper", "voltage_x10 <= 60"));
    ctx.push_obligation(ProofObligation::assert(
        "volt_bounded",
        "voltage_x10 >= 5 && voltage_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capillary voltage x10 bounded 0.5-6.0 kV");
}

#[test]
fn test_ambient_ion_ms_gas_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_lower", "flow_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assume("flow_upper", "flow_x10 <= 200"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas flow x10 bounded 0.1-20.0 L/min");
}

#[test]
fn test_ambient_ion_ms_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolving", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_lower", "resolving >= 1000"));
    ctx.push_obligation(ProofObligation::assume("res_upper", "resolving <= 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "resolving >= 1000 && resolving <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution bounded 1000-500000");
}

#[test]
fn test_ambient_ion_ms_source_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_lower", "temp_off >= 120"));
    ctx.push_obligation(ProofObligation::assume("temp_upper", "temp_off <= 600"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 120 && temp_off <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "source temp offset+100 bounded 120-600 representing 20-500 C",
    );
}

#[test]
fn test_ambient_ion_ms_ionization_technique_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tech", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tech_range",
        "tech == 1 || tech == 2 || tech == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tech_valid",
        "tech == 1 || tech == 2 || tech == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization technique three-way 1=DART 2=DESI 3=ASAP",
    );
}

#[test]
fn test_ambient_ion_ms_analyzer_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_range",
        "at == 1 || at == 2 || at == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_valid",
        "at == 1 || at == 2 || at == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer type three-way 1=TOF 2=orbitrap 3=triple-quad",
    );
}

#[test]
fn test_ambient_ion_ms_gas_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gt_range",
        "gt == 1 || gt == 2 || gt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gt_valid",
        "gt == 1 || gt == 2 || gt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas type three-way 1=helium 2=nitrogen 3=argon");
}

#[test]
fn test_ambient_ion_ms_auto_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto calibration boolean flag 0 or 1");
}

#[test]
fn test_ambient_ion_ms_scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_lower", "speed >= 100"));
    ctx.push_obligation(ProofObligation::assume("speed_upper", "speed <= 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 100 && speed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed bounded 100-100000 amu/sec");
}
