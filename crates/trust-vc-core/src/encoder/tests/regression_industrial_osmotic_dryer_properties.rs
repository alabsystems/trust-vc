// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Solution concentration (x100 %) — bounded [500, 9500].
/// 500 represents 5.00%, 9500 represents 95.00%. Value 4000.
#[test]
fn test_osmotic_dryer_solution_concentration_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conc_a",
        "conc_x100 >= 500 && conc_x100 <= 9500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conc_c",
        "conc_x100 >= 500 && conc_x100 <= 9500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solution concentration x100 in [500, 9500] representing 5.00-95.00%",
    );
}

/// Test 2: Immersion time (seconds) — bounded [60, 86400].
/// 3600 represents 1 hour. Value 3600.
#[test]
fn test_osmotic_dryer_immersion_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("immersion_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "imm_a",
        "immersion_s >= 60 && immersion_s <= 86400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "imm_c",
        "immersion_s >= 60 && immersion_s <= 86400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "immersion time in [60, 86400] seconds");
}

/// Test 3: Solution temperature offset +100 (deg C) — bounded [120, 180].
/// 120 represents 20 C, 150 represents 50 C, 180 represents 80 C.
#[test]
fn test_osmotic_dryer_solution_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sol_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stemp_a",
        "sol_temp >= 120 && sol_temp <= 180",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stemp_c",
        "sol_temp >= 120 && sol_temp <= 180",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solution temp offset+100 in [120, 180] representing 20-80 C",
    );
}

/// Test 4: Agitation speed (RPM) — bounded [0, 500].
#[test]
fn test_osmotic_dryer_agitation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("agit_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "agit_a",
        "agit_rpm >= 0 && agit_rpm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "agit_c",
        "agit_rpm >= 0 && agit_rpm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "agitation speed in [0, 500] RPM");
}

/// Test 5: Product-to-solution ratio (x100) — bounded [10, 500].
/// 10 represents 0.10, 100 represents 1.00. Value 100.
#[test]
fn test_osmotic_dryer_product_solution_ratio_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_a",
        "ratio_x100 >= 10 && ratio_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_c",
        "ratio_x100 >= 10 && ratio_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product-to-solution ratio x100 in [10, 500] representing 0.10-5.00",
    );
}

/// Test 6: Water activity target (x10000) — bounded [8000, 9900].
/// 9500 represents 0.9500 aw. Value 9500.
#[test]
fn test_osmotic_dryer_water_activity_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("aw_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aw_a",
        "aw_x10000 >= 8000 && aw_x10000 <= 9900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aw_c",
        "aw_x10000 >= 8000 && aw_x10000 <= 9900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "water activity target x10000 in [8000, 9900] representing 0.80-0.99 aw",
    );
}

/// Test 7: Osmotic agent type — 3-way disjunction.
/// 1=sucrose, 2=NaCl, 3=glycerol.
#[test]
fn test_osmotic_dryer_osmotic_agent_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("agent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "agent_a",
        "agent == 1 || agent == 2 || agent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "agent_c",
        "agent >= 1 && agent <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "osmotic agent 3-way (sucrose/NaCl/glycerol)");
}

/// Test 8: Process mode — 3-way disjunction.
/// 1=batch, 2=semi-continuous, 3=continuous.
#[test]
fn test_osmotic_dryer_process_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_a",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("mode_c", "mode >= 1 && mode <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "process mode 3-way (batch/semi-continuous/continuous)",
    );
}

/// Test 9: Solution recycling strategy — 3-way disjunction.
/// 1=discard, 2=reconcentrate, 3=reuse-direct.
#[test]
fn test_osmotic_dryer_solution_recycling_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("recycle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "recycle_a",
        "recycle == 1 || recycle == 2 || recycle == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "recycle_c",
        "recycle >= 1 && recycle <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solution recycling 3-way (discard/reconcentrate/reuse-direct)",
    );
}

/// Test 10: Vacuum assist flag — boolean.
/// 0=disabled, 1=enabled.
#[test]
fn test_osmotic_dryer_vacuum_assist_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum assist flag is boolean (0 or 1)");
}
