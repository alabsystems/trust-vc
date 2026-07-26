// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn clamping_force_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_kn", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "force_range",
        "force_kn >= 100 && force_kn <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "force_nonneg",
        "force_kn >= 100 && force_kn <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "clamping force in [100, 100000] kN should be bounded",
    );
}

#[test]
fn injection_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure_bar >= 500 && pressure_bar <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bound",
        "pressure_bar >= 500 && pressure_bar <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "injection pressure in [500, 3000] bar should be bounded",
    );
}

#[test]
fn barrel_temperature_offset_bounded() {
    // Barrel temperature: real range 100-400°C, offset +500 → [600, 900]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("barrel_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "barrel_temp_range",
        "barrel_temp >= 600 && barrel_temp <= 900",
    ));
    // Verify the offset encoding preserves the bound
    ctx.push_obligation(ProofObligation::assert(
        "barrel_above_min",
        "barrel_temp >= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "barrel_below_max",
        "barrel_temp <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "barrel temp offset [600, 900] (100-400C + 500) should be bounded",
    );
}

#[test]
fn machine_type_three_way_disjunction() {
    // 1=hydraulic, 2=electric, 3=hybrid
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("machine_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "machine_type_valid",
        "machine_type == 1 || machine_type == 2 || machine_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "machine_type_positive",
        "machine_type >= 1 && machine_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "machine type disjunction {1,2,3} implies range [1,3]",
    );
}

#[test]
fn screw_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screw_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "screw_range",
        "screw_mm >= 14 && screw_mm <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "screw_bound",
        "screw_mm >= 14 && screw_mm <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw diameter in [14, 200] mm should be bounded");
}

#[test]
fn shot_weight_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shot_g", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shot_range",
        "shot_g >= 1 && shot_g <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shot_bound",
        "shot_g >= 1 && shot_g <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shot weight in [1, 50000] g should be bounded");
}

#[test]
fn cycle_time_scaled_bounded() {
    // Cycle time in tenths of a second: 12.5s → 125, range [30, 3000] (3s to 300s)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_tenths", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cycle_range",
        "cycle_tenths >= 30 && cycle_tenths <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cycle_bound",
        "cycle_tenths >= 30 && cycle_tenths <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cycle time (x10 s) in [30, 3000] should be bounded",
    );
}

#[test]
fn mold_temperature_offset_bounded() {
    // Mold temperature: real range 20-200°C, offset +500 → [520, 700]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mold_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mold_temp_range",
        "mold_temp >= 520 && mold_temp <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mold_above_min",
        "mold_temp >= 520",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mold_below_max",
        "mold_temp <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mold temp offset [520, 700] (20-200C + 500) should be bounded",
    );
}

#[test]
fn plasticizing_type_three_way_disjunction() {
    // 1=reciprocating screw, 2=plunger, 3=preplasticizing
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plast_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "plast_type_valid",
        "plast_type == 1 || plast_type == 2 || plast_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "plast_type_positive",
        "plast_type >= 1 && plast_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plasticizing type disjunction {1,2,3} implies range [1,3]",
    );
}

#[test]
fn safety_gate_interlock_boolean_flag() {
    // Boolean flag encoded as i32: 0=gate open (unsafe), 1=gate closed (safe)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gate_closed", i32_ty());
    ctx.declare_var_typed("injection_allowed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gate_is_bool",
        "gate_closed == 0 || gate_closed == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "interlock_def",
        "injection_allowed == if gate_closed == 1 { 1 } else { 0 }",
    ));
    // When gate is closed, injection is allowed
    ctx.push_obligation(ProofObligation::assume("gate_val", "gate_closed == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "injection_enabled",
        "injection_allowed == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "safety gate interlock: gate closed implies injection allowed",
    );
}
