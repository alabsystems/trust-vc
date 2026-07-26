// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_esi_ms_spray_voltage_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spray_voltage_range",
        "voltage_x100 >= 50 && voltage_x100 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spray_voltage_check",
        "voltage_x100 >= 50 && voltage_x100 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray voltage x100 in [50, 600] representing 0.5-6.0 kV",
    );
}

#[test]
fn test_esi_ms_capillary_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capillary_temp_range",
        "cap_temp >= 200 && cap_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capillary_temp_check",
        "cap_temp >= 200 && cap_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capillary temperature offset+100 in [200, 500]");
}

#[test]
fn test_esi_ms_sheath_gas_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sheath_gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sheath_gas_range",
        "sheath_gas >= 1 && sheath_gas <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sheath_gas_check",
        "sheath_gas >= 1 && sheath_gas <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sheath gas flow in [1, 80] arbitrary units");
}

#[test]
fn test_esi_ms_auxiliary_gas_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("aux_gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aux_gas_range",
        "aux_gas >= 0 && aux_gas <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aux_gas_check",
        "aux_gas >= 0 && aux_gas <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auxiliary gas flow in [0, 60] arbitrary units");
}

#[test]
fn test_esi_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mz >= 50 && mz <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_range_check",
        "mz >= 50 && mz <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass-to-charge ratio in [50, 6000] m/z");
}

#[test]
fn test_esi_ms_cone_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cone_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cone_voltage_range",
        "cone_v >= 5 && cone_v <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cone_voltage_check",
        "cone_v >= 5 && cone_v <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cone voltage in [5, 200] V");
}

#[test]
fn test_esi_ms_ionization_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "polarity_valid",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "polarity_check",
        "polarity >= 1 && polarity <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization polarity: 1=positive 2=negative 3=alternating",
    );
}

#[test]
fn test_esi_ms_scan_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "scan_mode_valid",
        "scan == 1 || scan == 2 || scan == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scan_mode_check",
        "scan >= 1 && scan <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan mode: 1=full-scan 2=SIM 3=MRM");
}

#[test]
fn test_esi_ms_desolvation_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("desolv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "desolv_method_valid",
        "desolv == 1 || desolv == 2 || desolv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "desolv_method_check",
        "desolv >= 1 && desolv <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "desolvation: 1=heated-capillary 2=curtain-gas 3=counter-current",
    );
}

#[test]
fn test_esi_ms_auto_tune_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_check",
        "flag >= 0 && flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-tune flag is 0 or 1");
}
