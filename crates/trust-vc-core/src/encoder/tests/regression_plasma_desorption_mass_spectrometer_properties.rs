// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_plasma_desorption_ms_mass_range_amu() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range_a",
        "mass >= 100 && mass <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_range_c",
        "mass >= 1 && mass <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PDMS mass range [100, 100000] amu implies wider bound",
    );
}

#[test]
fn test_plasma_desorption_ms_accelerating_voltage_kv() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range_a",
        "voltage >= 5 && voltage <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_range_c",
        "voltage >= 1 && voltage <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accelerating voltage [5, 30] kV implies wider bound",
    );
}

#[test]
fn test_plasma_desorption_ms_fission_fragment_energy_mev() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range_a",
        "energy >= 50 && energy <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_range_c",
        "energy >= 1 && energy <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fission fragment energy [50, 200] MeV implies wider bound",
    );
}

#[test]
fn test_plasma_desorption_ms_flight_tube_length_cm() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "length_range_a",
        "length >= 50 && length <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "length_range_c",
        "length >= 1 && length <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flight tube length [50, 300] cm implies wider bound",
    );
}

#[test]
fn test_plasma_desorption_ms_source_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_off_range_a",
        "temp_off >= 80 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_off_range_c",
        "temp_off + 100 >= 180 && temp_off + 100 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "source temperature offset +100 degC stays in expected range",
    );
}

#[test]
fn test_plasma_desorption_ms_collection_time_seconds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_range_a",
        "time >= 60 && time <= 86400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_range_c",
        "time >= 1 && time <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collection time [60, 86400] seconds implies wider bound",
    );
}

#[test]
fn test_plasma_desorption_ms_fission_source_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_type_a",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_type_c",
        "source >= 1 && source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fission source (1=Cf252, 2=Am241, 3=Pu238) implies [1, 3]",
    );
}

#[test]
fn test_plasma_desorption_ms_detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_type_a",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_type_c",
        "detector >= 1 && detector <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector (1=MCP, 2=channeltron, 3=electron-multiplier) implies [1, 3]",
    );
}

#[test]
fn test_plasma_desorption_ms_sample_preparation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prep", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "prep_type_a",
        "prep == 1 || prep == 2 || prep == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "prep_type_c",
        "prep >= 1 && prep <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample prep (1=electrospray, 2=spin-coating, 3=adsorption) implies [1, 3]",
    );
}

#[test]
fn test_plasma_desorption_ms_auto_time_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_cal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_cal_flag_a",
        "auto_cal == 0 || auto_cal == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_cal_flag_c",
        "auto_cal >= 0 && auto_cal <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto time calibration boolean flag implies [0, 1]");
}
