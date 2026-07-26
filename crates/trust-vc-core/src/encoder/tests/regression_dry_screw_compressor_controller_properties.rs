// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Dry (oil-free) screw compressor controller – property-based regression tests
// ---------------------------------------------------------------------------

/// Discharge pressure in bar — bounded range.
#[test]
fn test_dry_screw_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "pressure >= 2 && pressure <= 40",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "pressure >= 2 && pressure <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dry screw compressor discharge pressure bounded");
}

/// Inlet temperature with offset +100 °C — bounded range.
#[test]
fn test_dry_screw_compressor_inlet_temperature_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "it_a",
        "temp_off >= 60 && temp_off <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "it_c",
        "temp_off >= 60 && temp_off <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dry screw compressor inlet temperature offset bounded",
    );
}

/// Rotor speed in RPM — bounded range.
#[test]
fn test_dry_screw_compressor_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rs_a",
        "speed >= 1000 && speed <= 25000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rs_c",
        "speed >= 1000 && speed <= 25000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dry screw compressor rotor speed bounded");
}

/// Volume flow at ×10 m3/min — bounded range.
#[test]
fn test_dry_screw_compressor_volume_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vf_a",
        "flow_x10 >= 10 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vf_c",
        "flow_x10 >= 10 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dry screw compressor volume flow x10 bounded");
}

/// Bearing temperature with offset +100 °C — bounded range.
#[test]
fn test_dry_screw_compressor_bearing_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bt_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bt_a",
        "bt_off >= 100 && bt_off <= 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bt_c",
        "bt_off >= 100 && bt_off <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dry screw compressor bearing temperature offset bounded",
    );
}

/// Cooling method — 3-way disjunction.
#[test]
fn test_dry_screw_compressor_cooling_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "cm == 1 || cm == 2 || cm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "cm == 1 || cm == 2 || cm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dry screw compressor cooling method three-way disjunction",
    );
}

/// Seal type — 3-way disjunction.
#[test]
fn test_dry_screw_compressor_seal_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("st", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "st == 1 || st == 2 || st == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "st == 1 || st == 2 || st == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dry screw compressor seal type three-way disjunction",
    );
}

/// Stage count — 3-way disjunction.
#[test]
fn test_dry_screw_compressor_stage_count_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sc_a",
        "sc == 1 || sc == 2 || sc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sc_c",
        "sc == 1 || sc == 2 || sc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dry screw compressor stage count three-way disjunction",
    );
}

/// Automatic anti-surge control — boolean flag.
#[test]
fn test_dry_screw_compressor_auto_anti_surge_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("as_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("as_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dry screw compressor auto anti-surge flag");
}

/// Compression ratio at ×10 — bounded range.
#[test]
fn test_dry_screw_compressor_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cr_a",
        "ratio_x10 >= 15 && ratio_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cr_c",
        "ratio_x10 >= 15 && ratio_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dry screw compressor compression ratio x10 bounded",
    );
}
