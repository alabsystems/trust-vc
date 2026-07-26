// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ICP-MS (Inductively Coupled Plasma Mass Spectrometer) property regression tests.
//!
//! These tests verify bounded instrument parameters, enumerated component
//! selections, and boolean configuration flags for an ICP-MS model encoded
//! as integer constraints.

use super::*;

/// Mass range in atomic mass units (amu). Valid: 1..=300.
#[test]
fn test_icpms_mass_range_amu() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_amu", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mass_lower", "mass_amu >= 1"));
    ctx.push_obligation(ProofObligation::assume("mass_upper", "mass_amu <= 300"));
    ctx.push_obligation(ProofObligation::assume("mass_val", "mass_amu == 260"));
    ctx.push_obligation(ProofObligation::assert(
        "mass_in_range",
        "mass_amu >= 1 && mass_amu <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass 260 amu is within ICP-MS range 1..=300");
}

/// Detection limit in units of x1000 ppt (1 unit = 0.001 ppt). Valid: 1..=10000.
#[test]
fn test_icpms_detection_limit_ppt() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("det_lower", "det_limit >= 1"));
    ctx.push_obligation(ProofObligation::assume("det_upper", "det_limit <= 10000"));
    ctx.push_obligation(ProofObligation::assume("det_val", "det_limit == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "det_in_range",
        "det_limit >= 1 && det_limit <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit 10 (0.010 ppt) is within range 1..=10000",
    );
}

/// Linear dynamic range in orders of magnitude. Valid: 5..=12.
#[test]
fn test_icpms_linear_dynamic_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dyn_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dyn_lower", "dyn_range >= 5"));
    ctx.push_obligation(ProofObligation::assume("dyn_upper", "dyn_range <= 12"));
    ctx.push_obligation(ProofObligation::assume("dyn_val", "dyn_range == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "dyn_in_range",
        "dyn_range >= 5 && dyn_range <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "9 orders of magnitude is within dynamic range 5..=12",
    );
}

/// Plasma RF power in watts. Valid: 500..=2000.
#[test]
fn test_icpms_plasma_rf_power() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rf_power", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rf_lower", "rf_power >= 500"));
    ctx.push_obligation(ProofObligation::assume("rf_upper", "rf_power <= 2000"));
    ctx.push_obligation(ProofObligation::assume("rf_val", "rf_power == 1600"));
    ctx.push_obligation(ProofObligation::assert(
        "rf_in_range",
        "rf_power >= 500 && rf_power <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1600 W RF power is within plasma range 500..=2000");
}

/// Nebulizer gas flow in units of x100 L/min (100 = 1.00 L/min). Valid: 10..=200.
#[test]
fn test_icpms_nebulizer_flow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("neb_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("neb_lower", "neb_flow >= 10"));
    ctx.push_obligation(ProofObligation::assume("neb_upper", "neb_flow <= 200"));
    ctx.push_obligation(ProofObligation::assume("neb_val", "neb_flow == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "neb_in_range",
        "neb_flow >= 10 && neb_flow <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nebulizer flow 100 (1.00 L/min) is within range 10..=200",
    );
}

/// Number of isotopes monitored simultaneously. Valid: 1..=100.
#[test]
fn test_icpms_isotope_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("isotopes", i32_ty());
    ctx.push_obligation(ProofObligation::assume("iso_lower", "isotopes >= 1"));
    ctx.push_obligation(ProofObligation::assume("iso_upper", "isotopes <= 100"));
    ctx.push_obligation(ProofObligation::assume("iso_val", "isotopes == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "iso_in_range",
        "isotopes >= 1 && isotopes <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "monitoring 30 isotopes is within range 1..=100");
}

/// Mass analyzer type: 1=quadrupole, 2=magnetic-sector, 3=TOF.
#[test]
fn test_icpms_mass_analyzer_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("analyzer_val", "analyzer == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "analyzer_valid",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "quadrupole (1) is a valid mass analyzer type");
}

/// Interference removal mode: 1=collision-cell, 2=reaction-cell, 3=high-resolution.
#[test]
fn test_icpms_interference_removal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("removal", i32_ty());
    ctx.push_obligation(ProofObligation::assume("removal_val", "removal == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "removal_valid",
        "removal == 1 || removal == 2 || removal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collision-cell (1) is a valid interference removal mode",
    );
}

/// Sample introduction method: 1=pneumatic-nebulizer, 2=laser-ablation, 3=electrothermal-vaporization.
#[test]
fn test_icpms_sample_introduction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("intro", i32_ty());
    ctx.push_obligation(ProofObligation::assume("intro_val", "intro == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "intro_valid",
        "intro == 1 || intro == 2 || intro == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pneumatic-nebulizer (1) is a valid sample introduction method",
    );
}

/// Automatic internal standard correction: boolean flag (0 or 1).
/// When flag==1, correction is applied and result should be 1.
#[test]
fn test_icpms_internal_standard_correction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "correction_applied",
        "(if flag == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "internal standard correction is applied when flag==1",
    );
}
