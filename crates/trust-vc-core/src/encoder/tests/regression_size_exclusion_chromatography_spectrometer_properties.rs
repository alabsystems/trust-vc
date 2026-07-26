// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Size exclusion chromatography (SEC/GPC) spectrometer property verification.
// Integer-scaled fixed-point representations avoid floating-point in the SMT domain.

#[test]
fn test_sec_column_length_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col_len", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "col_range",
        "col_len >= 100 && col_len <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("col_val", "col_len == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "col_bound",
        "col_len >= 100 && col_len <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column length 300 mm within [100, 1000]");
}

#[test]
fn test_sec_particle_size_bounded() {
    // Particle size in units of 0.1 um: 50 = 5.0 um
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("particle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "particle_range",
        "particle >= 10 && particle <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("particle_val", "particle == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "particle_bound",
        "particle >= 10 && particle <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "particle size 5.0 um (50) within [10, 500]");
}

#[test]
fn test_sec_flow_rate_bounded() {
    // Flow rate in units of 0.01 mL/min: 100 = 1.00 mL/min
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow >= 1 && flow <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bound",
        "flow >= 1 && flow <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 1.00 mL/min (100) within [1, 5000]");
}

#[test]
fn test_sec_max_molecular_weight_kda_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mw_range",
        "mw >= 1 && mw <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("mw_val", "mw == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "mw_bound",
        "mw >= 1 && mw <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max molecular weight 2000 kDa within [1, 50000]");
}

#[test]
fn test_sec_resolution_factor_bounded() {
    // Resolution factor scaled x100: 150 = 1.50
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res >= 10 && res <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("res_val", "res == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "res_bound",
        "res >= 10 && res <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution factor 1.50 (150) within [10, 500]");
}

#[test]
fn test_sec_injection_volume_bounded() {
    // Injection volume in units of 0.1 uL: 1000 = 100.0 uL
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_vol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inj_range",
        "inj_vol >= 1 && inj_vol <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("inj_val", "inj_vol == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "inj_bound",
        "inj_vol >= 1 && inj_vol <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "injection volume 100.0 uL (1000) within [1, 50000]",
    );
}

#[test]
fn test_sec_column_packing_material() {
    // 1=silica, 2=polystyrene-DVB, 3=agarose
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("packing", i32_ty());
    ctx.push_obligation(ProofObligation::assume("packing_val", "packing == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "packing_valid",
        "packing == 1 || packing == 2 || packing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "polystyrene-DVB (2) is a valid packing material");
}

#[test]
fn test_sec_detection_method() {
    // 1=refractive-index, 2=UV, 3=light-scattering
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume("detector_val", "detector == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractive-index (1) is a valid detection method");
}

#[test]
fn test_sec_calibration_type() {
    // 1=conventional, 2=universal, 3=absolute-mw
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cal_val", "cal == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "cal_valid",
        "cal == 1 || cal == 2 || cal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conventional (1) is a valid calibration type");
}

#[test]
fn test_sec_automatic_column_switching() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_switch", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_switch == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "switch_active",
        "(if auto_switch == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic column switching enabled when flag is 1");
}
