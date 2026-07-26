// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_eesi_ms_spray_voltage_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sv_a",
        "spray_x100 >= 10 && spray_x100 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sv_c",
        "spray_x100 >= 10 && spray_x100 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EESI spray voltage x100 in [10, 600] representing 0.10-6.00 kV",
    );
}

#[test]
fn test_eesi_ms_extraction_solvent_flow_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ef_a",
        "flow_x100 >= 1 && flow_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ef_c",
        "flow_x100 >= 1 && flow_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "extraction flow x100 in [1, 50000] representing 0.01-500.00 uL/min",
    );
}

#[test]
fn test_eesi_ms_sample_flow_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sf_a",
        "sample_x100 >= 1 && sample_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sf_c",
        "sample_x100 >= 1 && sample_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample flow x100 in [1, 100000] representing 0.01-1000.00 uL/min",
    );
}

#[test]
fn test_eesi_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mz_a", "mz >= 50 && mz <= 4000"));
    ctx.push_obligation(ProofObligation::assert("mz_c", "mz >= 50 && mz <= 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EESI mass range in [50, 4000] m/z");
}

#[test]
fn test_eesi_ms_collision_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_deg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ca_a",
        "angle_deg >= 10 && angle_deg <= 180",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ca_c",
        "angle_deg >= 10 && angle_deg <= 180",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "collision angle in [10, 180] degrees");
}

#[test]
fn test_eesi_ms_desolvation_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("desolv_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "desolv_temp >= 150 && desolv_temp <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "desolv_temp >= 150 && desolv_temp <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "desolvation temp offset+100 in [150, 600] representing 50-500 C",
    );
}

#[test]
fn test_eesi_ms_extraction_solvent_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solvent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sol_a",
        "solvent == 1 || solvent == 2 || solvent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sol_c",
        "solvent >= 1 && solvent <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "extraction solvent 3-way (methanol-water/acetonitrile-water/ethanol-water)",
    );
}

#[test]
fn test_eesi_ms_sample_phase_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ph_a",
        "phase == 1 || phase == 2 || phase == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("ph_c", "phase >= 1 && phase <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample phase 3-way (liquid/aerosol/solid-surface)");
}

#[test]
fn test_eesi_ms_ionization_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pol_a",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pol_c",
        "polarity >= 1 && polarity <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization polarity 3-way (positive/negative/alternating)",
    );
}

#[test]
fn test_eesi_ms_real_time_monitoring_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real-time monitoring flag is boolean (0 or 1)");
}
