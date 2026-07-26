// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_transformer_power_mva() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mva", "min_mva", "max_mva"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Transformer rated power in MVA
    ctx.push_obligation(ProofObligation::assume("pm", "power_mva == 80"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mva == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mva == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_mva >= min_mva && power_mva <= max_mva { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EAF: 80 MVA transformer power in [1, 500] -> OK");
}

#[test]
fn test_electrode_diameter_mm() {
    let mut ctx = VerificationContext::new();
    for v in &["diameter_mm", "min_dia", "max_dia"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dia_ok", i32_ty());
    // Graphite electrode diameter in mm
    ctx.push_obligation(ProofObligation::assume("dm", "diameter_mm == 600"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_dia == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_dia == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dia_ok == if diameter_mm >= min_dia && diameter_mm <= max_dia { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dia_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EAF: 600mm electrode diameter in [100, 800] -> OK");
}

#[test]
fn test_furnace_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("furnace_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Furnace types: 1=AC three-phase, 2=DC single-electrode, 3=DC twin-electrode
    ctx.push_obligation(ProofObligation::assume("ft", "furnace_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if furnace_type == 1 || furnace_type == 2 || furnace_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EAF: AC three-phase is valid furnace type (3-way)");
}

#[test]
fn test_tap_to_tap_time_min() {
    let mut ctx = VerificationContext::new();
    for v in &["tap_time", "min_time", "max_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("time_ok", i32_ty());
    // Tap-to-tap time in minutes
    ctx.push_obligation(ProofObligation::assume("tt", "tap_time == 55"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_time == 30"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_time == 180"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "time_ok == if tap_time >= min_time && tap_time <= max_time { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "time_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EAF: 55 min tap-to-tap time in [30, 180] -> OK");
}

#[test]
fn test_electrode_regulation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reg_type", u32_ty());
    ctx.declare_var_typed("valid_reg", i32_ty());
    // Regulation types: 1=hydraulic, 2=electromechanical, 3=servo
    ctx.push_obligation(ProofObligation::assume("rt", "reg_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_reg == if reg_type == 1 || reg_type == 2 || reg_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_reg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EAF: servo is valid electrode regulation (3-way)");
}

#[test]
fn test_steel_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Steel tapping temperature in degrees Celsius (all positive, no offset needed)
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c == 1620"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp == 1500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp == 1700"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c >= min_temp && temp_c <= max_temp { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EAF: 1620C steel temperature in [1500, 1700] -> OK",
    );
}

#[test]
fn test_charge_weight_tonnes() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_t", "min_charge", "max_charge"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("charge_ok", i32_ty());
    // Charge weight in metric tonnes
    ctx.push_obligation(ProofObligation::assume("ct", "charge_t == 120"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_charge == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_charge == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "charge_ok == if charge_t >= min_charge && charge_t <= max_charge { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "charge_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EAF: 120t charge weight in [1, 300] -> OK");
}

#[test]
fn test_power_factor_x100() {
    let mut ctx = VerificationContext::new();
    for v in &["pf_x100", "min_pf", "max_pf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pf_ok", i32_ty());
    // Power factor scaled by 100 (0.85 -> 85)
    ctx.push_obligation(ProofObligation::assume("pf", "pf_x100 == 85"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pf == 70"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pf == 99"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pf_ok == if pf_x100 >= min_pf && pf_x100 <= max_pf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EAF: 0.85 power factor (x100=85) in [70, 99] -> OK",
    );
}

#[test]
fn test_slag_door_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("door_type", u32_ty());
    ctx.declare_var_typed("valid_door", i32_ty());
    // Slag door types: 1=manual, 2=hydraulic, 3=eccentric bottom tap (EBT)
    ctx.push_obligation(ProofObligation::assume("dt", "door_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_door == if door_type == 1 || door_type == 2 || door_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_door == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EAF: hydraulic is valid slag door type (3-way)");
}

#[test]
fn test_fume_extraction_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fume_extract", i32_ty());
    ctx.declare_var_typed("extract_active", i32_ty());
    // Fume extraction system as boolean flag (i32: 1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("fe", "fume_extract == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "extract_active == if fume_extract == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "extract_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EAF: fume extraction enabled -> active (boolean flag)",
    );
}
