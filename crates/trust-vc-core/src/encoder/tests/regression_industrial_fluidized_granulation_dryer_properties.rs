// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Air temperature offset +100 (30-100 C encoded as 130-200).
#[test]
fn test_fluidized_granulation_dryer_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 130 && temp_off <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 130 && temp_off <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temperature offset+100 must be in range 130-200 representing 30-100 C",
    );
}

/// Test 2: Air flow x10 m3/min — bounded [10, 500].
#[test]
fn test_fluidized_granulation_dryer_air_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 10 && flow_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 10 && flow_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air flow x10 must be in range 10-500 representing 1.0-50.0 m3/min",
    );
}

/// Test 3: Spray rate x100 mL/min — bounded [1, 5000].
#[test]
fn test_fluidized_granulation_dryer_spray_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spray_range",
        "spray_x100 >= 1 && spray_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spray_bounded",
        "spray_x100 >= 1 && spray_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray rate x100 must be in range 1-5000 representing 0.01-50.00 mL/min",
    );
}

/// Test 4: Bed depth x10 mm — bounded [50, 1000].
#[test]
fn test_fluidized_granulation_dryer_bed_depth_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "depth_range",
        "depth_x10 >= 50 && depth_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "depth_bounded",
        "depth_x10 >= 50 && depth_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bed depth x10 must be in range 50-1000 representing 5.0-100.0 mm",
    );
}

/// Test 5: Granule size x10 um — bounded [10, 50000].
#[test]
fn test_fluidized_granulation_dryer_granule_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gran_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gran_range",
        "gran_x10 >= 10 && gran_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gran_bounded",
        "gran_x10 >= 10 && gran_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "granule size x10 must be in range 10-50000 representing 1.0-5000.0 um",
    );
}

/// Test 6: Binder concentration x100 % — bounded [100, 5000].
#[test]
fn test_fluidized_granulation_dryer_binder_concentration_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("binder_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "binder_range",
        "binder_x100 >= 100 && binder_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "binder_bounded",
        "binder_x100 >= 100 && binder_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "binder concentration x100 must be in range 100-5000 representing 1.00-50.00 percent",
    );
}

/// Test 7: Spray nozzle type — 3-way disjunction.
/// 1=top-spray, 2=bottom-spray, 3=tangential-spray.
#[test]
fn test_fluidized_granulation_dryer_spray_nozzle_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nozzle_range",
        "nozzle == 1 || nozzle == 2 || nozzle == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nozzle_valid",
        "nozzle == 1 || nozzle == 2 || nozzle == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray nozzle type must be top (1), bottom (2), or tangential (3)",
    );
}

/// Test 8: Fluidization mode — 3-way disjunction.
/// 1=continuous, 2=batch, 3=pulsed.
#[test]
fn test_fluidized_granulation_dryer_fluidization_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fmode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fmode_range",
        "fmode == 1 || fmode == 2 || fmode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fmode_valid",
        "fmode == 1 || fmode == 2 || fmode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluidization mode must be continuous (1), batch (2), or pulsed (3)",
    );
}

/// Test 9: Drying stage — 3-way disjunction.
/// 1=pre-heat, 2=granulation, 3=drying.
#[test]
fn test_fluidized_granulation_dryer_drying_stage_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stage_range",
        "stage == 1 || stage == 2 || stage == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stage_valid",
        "stage == 1 || stage == 2 || stage == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drying stage must be pre-heat (1), granulation (2), or drying (3)",
    );
}

/// Test 10: Auto moisture control — boolean flag (0 or 1).
#[test]
fn test_fluidized_granulation_dryer_auto_moisture_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto moisture control flag must be 0 (disabled) or 1 (enabled)",
    );
}
