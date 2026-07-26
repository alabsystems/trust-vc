// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial vacuum degasser property verification.
// Encodes key parameters of an industrial vacuum degasser system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Vessel volume (L) — bounded [100, 50000], value 5000.
#[test]
fn test_vessel_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_volume_l", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_val",
        "vessel_volume_l == 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("vol_min", "vessel_volume_l >= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_max",
        "vessel_volume_l <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume 5000 L in [100, 50000]");
}

/// Test 2: Vacuum level (Pa) — bounded [10, 5000], value 500.
#[test]
fn test_vacuum_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_pa", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_pa == 500"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_pa >= 10"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_pa <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 500 Pa in [10, 5000]");
}

/// Test 3: Flow rate (L/min) — bounded [10, 2000], value 200.
#[test]
fn test_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_lmin", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_lmin == 200"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow_lmin >= 10"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow_lmin <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 200 L/min in [10, 2000]");
}

/// Test 4: Degasser type — 3-way disjunction.
/// 1=spray, 2=packed column, 3=membrane. Value 2 (packed column).
#[test]
fn test_degasser_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("degasser_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("deg_val", "degasser_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_degasser",
        "degasser_type == 1 || degasser_type == 2 || degasser_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "degasser type 2 (packed column) is valid 3-way disjunction",
    );
}

/// Test 5: Dissolved gas — 3-way disjunction.
/// 1=O2, 2=CO2, 3=N2. Value 1 (O2).
#[test]
fn test_dissolved_gas_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dissolved_gas", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gas_val", "dissolved_gas == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_gas",
        "dissolved_gas == 1 || dissolved_gas == 2 || dissolved_gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dissolved gas 1 (O2) is valid 3-way disjunction");
}

/// Test 6: Removal efficiency (x10 %) — bounded [900, 999].
/// 995 represents 99.5%. Value 995.
#[test]
fn test_removal_efficiency_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("eff_val", "eff_x10 == 995"));
    ctx.push_obligation(ProofObligation::assert("eff_min", "eff_x10 >= 900"));
    ctx.push_obligation(ProofObligation::assert("eff_max", "eff_x10 <= 999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "removal efficiency 99.5% (995 x10) in [900, 999]");
}

/// Test 7: Pump type — 3-way disjunction.
/// 1=liquid ring, 2=rotary vane, 3=dry screw. Value 3 (dry screw).
#[test]
fn test_pump_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pump_val", "pump_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_pump",
        "pump_type == 1 || pump_type == 2 || pump_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pump type 3 (dry screw) is valid 3-way disjunction",
    );
}

/// Test 8: Process temperature (deg C) — bounded [20, 150], value 80.
/// All positive range, no offset needed.
#[test]
fn test_process_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("proc_temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "proc_temp_c == 80"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "proc_temp_c >= 20"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "proc_temp_c <= 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process temp 80 C in [20, 150]");
}

/// Test 9: Material — 3-way disjunction.
/// 1=SS304, 2=SS316, 3=duplex. Value 2 (SS316).
#[test]
fn test_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "vessel_material == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "vessel_material == 1 || vessel_material == 2 || vessel_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material 2 (SS316) is valid 3-way disjunction");
}

/// Test 10: Level control — boolean flag using i32 with if/else pattern.
/// Flag 1 = level control enabled, control_active = 1.
#[test]
fn test_level_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("level_ctrl_flag", i32_ty());
    ctx.declare_var_typed("control_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "level_ctrl_flag == 0 || level_ctrl_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "level_ctrl_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_def",
        "control_active == if level_ctrl_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "control_enabled",
        "control_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "level control flag enables control");
}
