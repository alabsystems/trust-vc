// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Mass range in atomic mass units (amu). Valid LC-MS instruments measure
/// ions between 1 and 100,000 amu. Assume a peptide at 3000 amu.
#[test]
fn test_lcms_mass_range_amu() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_bound",
        "mass >= 1 && mass <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("mass_val", "mass == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "mass_in_range",
        "mass >= 1 && mass <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "peptide at 3000 amu within LC-MS mass range");
}

/// Mass resolution (resolving power). Instruments range from 100 to
/// 1,000,000 resolving power. Assume a high-resolution Q-TOF at 30,000.
#[test]
fn test_lcms_mass_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_bound",
        "resolution >= 100 && resolution <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "res_in_range",
        "resolution >= 100 && resolution <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q-TOF resolution 30000 within valid range");
}

/// Scan speed in amu per second. Valid range 100 to 100,000 amu/sec.
/// Assume a fast scan at 20,000 amu/sec.
#[test]
fn test_lcms_scan_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_bound",
        "scan_speed >= 100 && scan_speed <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "scan_speed == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_in_range",
        "scan_speed >= 100 && scan_speed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed 20000 amu/sec within valid range");
}

/// Flow rate scaled by 100 (integer encoding of mL/min). 50 represents
/// 0.50 mL/min. Valid range 1 to 5000 (0.01 to 50.00 mL/min).
#[test]
fn test_lcms_flow_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_bound",
        "flow_rate >= 1 && flow_rate <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_rate == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_range",
        "flow_rate >= 1 && flow_rate <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate 0.50 mL/min (encoded 50) within valid range",
    );
}

/// Column temperature with +100 offset to avoid negative integers.
/// 140 represents 40 degrees C. Valid range 100 to 400 (0 to 300 C).
#[test]
fn test_lcms_column_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_bound",
        "col_temp >= 100 && col_temp <= 400",
    ));
    ctx.push_obligation(ProofObligation::assume("temp_val", "col_temp == 140"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "col_temp >= 100 && col_temp <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column temp 40C (encoded 140) within valid range");
}

/// Maximum system pressure scaled by 10 (integer encoding of bar).
/// 12000 represents 1200.0 bar. Valid range 100 to 20000 (10.0 to 2000.0 bar).
#[test]
fn test_lcms_max_pressure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_bound",
        "pressure >= 100 && pressure <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 12000"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_in_range",
        "pressure >= 100 && pressure <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pressure 1200.0 bar (encoded 12000) within valid range",
    );
}

/// Ionization source type: 1=ESI (electrospray), 2=APCI (atmospheric
/// pressure chemical ionization), 3=APPI (atmospheric pressure
/// photoionization). Assume ESI (most common for LC-MS).
#[test]
fn test_lcms_ionization_source() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ion_src_val", "ion_src == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source",
        "ion_src == 1 || ion_src == 2 || ion_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ESI (1) is a valid ionization source");
}

/// Mass analyzer type: 1=single-quadrupole, 2=triple-quadrupole,
/// 3=Q-TOF (quadrupole time-of-flight). Assume triple-quad for MRM.
#[test]
fn test_lcms_mass_analyzer() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("analyzer_val", "analyzer == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_analyzer",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "triple-quad (2) is a valid mass analyzer");
}

/// Mobile phase mode: 1=reversed-phase, 2=normal-phase, 3=HILIC
/// (hydrophilic interaction liquid chromatography). Assume reversed-phase.
#[test]
fn test_lcms_mobile_phase() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase", i32_ty());
    ctx.push_obligation(ProofObligation::assume("phase_val", "phase == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_phase",
        "phase == 1 || phase == 2 || phase == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reversed-phase (1) is a valid mobile phase mode");
}

/// Automatic source switching flag. When enabled (1), the instrument
/// can alternate between positive and negative ionization within a
/// single run. Assert that if the flag is 1, the active-source
/// indicator evaluates to 1.
#[test]
fn test_lcms_auto_source_switching() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "switching_active",
        "(if flag == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto source switching enabled when flag is 1");
}
