// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Ionic liquid compressor controller – property-based regression tests
// ---------------------------------------------------------------------------

/// Discharge pressure in bar — bounded range.
#[test]
fn test_ionic_liquid_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "pressure >= 1 && pressure <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "pressure >= 1 && pressure <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionic liquid compressor discharge pressure bounded",
    );
}

/// Flow rate at ×10 m3/min — bounded range.
#[test]
fn test_ionic_liquid_compressor_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionic liquid compressor flow rate x10 bounded");
}

/// Liquid viscosity at ×100 mPa·s — bounded range.
#[test]
fn test_ionic_liquid_compressor_viscosity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("visc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lv_a",
        "visc_x100 >= 10 && visc_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lv_c",
        "visc_x100 >= 10 && visc_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionic liquid compressor viscosity x100 bounded");
}

/// Discharge temperature with offset +100 °C — bounded range.
#[test]
fn test_ionic_liquid_compressor_discharge_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "temp_off >= 50 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "temp_off >= 50 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionic liquid compressor discharge temperature offset bounded",
    );
}

/// Compression ratio at ×10 — bounded range.
#[test]
fn test_ionic_liquid_compressor_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cr_a",
        "ratio_x10 >= 10 && ratio_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cr_c",
        "ratio_x10 >= 10 && ratio_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionic liquid compressor compression ratio x10 bounded",
    );
}

/// Motor power in kW — bounded range.
#[test]
fn test_ionic_liquid_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mp_a",
        "power >= 1 && power <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mp_c",
        "power >= 1 && power <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionic liquid compressor motor power bounded");
}

/// Ionic liquid type — 3-way disjunction.
#[test]
fn test_ionic_liquid_compressor_liquid_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liquid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "il_a",
        "liquid == 1 || liquid == 2 || liquid == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "il_c",
        "liquid == 1 || liquid == 2 || liquid == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionic liquid compressor liquid type three-way disjunction",
    );
}

/// Sealing method — 3-way disjunction.
#[test]
fn test_ionic_liquid_compressor_sealing_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionic liquid compressor sealing method three-way disjunction",
    );
}

/// Cooling system — 3-way disjunction.
#[test]
fn test_ionic_liquid_compressor_cooling_system_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cs_a",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cs_c",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionic liquid compressor cooling system three-way disjunction",
    );
}

/// Automatic liquid level control — boolean flag.
#[test]
fn test_ionic_liquid_compressor_auto_liquid_level_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("lc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionic liquid compressor auto liquid level control flag",
    );
}
