// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial fluid bed granulator property verification.
// Encodes key parameters of a fluid bed granulation system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Bed capacity (kg) — batch size bounded [1, 5000], value 500.
#[test]
fn test_bed_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 500"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "cap >= 1"));
    ctx.push_obligation(ProofObligation::assert("cap_max", "cap <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed capacity 500 kg in [1, 5000]");
}

/// Test 2: Process air flow (x10 m3/h) — 1000.0 m3/h = 10000, bounded [100, 50000], value 10000.
#[test]
fn test_air_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("air_val", "air_x10 == 10000"));
    ctx.push_obligation(ProofObligation::assert("air_min", "air_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("air_max", "air_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow 1000.0 m3/h (10000 x10) in [100, 50000]");
}

/// Test 3: Inlet air temperature (offset +100 for sub-zero) — 280 C = 380, bounded [100, 600], value 380.
#[test]
fn test_inlet_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 380"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp >= 100"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet temp 280 C (offset 380) in [100, 600]");
}

/// Test 4: Binder spray rate (x100 mL/min) — 50.00 mL/min = 5000, bounded [10, 10000], value 5000.
#[test]
fn test_spray_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spray_val", "spray_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assert("spray_min", "spray_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("spray_max", "spray_x100 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray rate 50.00 mL/min (5000 x100) in [10, 10000]",
    );
}

/// Test 5: Product moisture content (x10 %) — 2.5% = 25, bounded [1, 100], value 25.
#[test]
fn test_product_moisture_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moist_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("moist_val", "moist_x10 == 25"));
    ctx.push_obligation(ProofObligation::assert("moist_min", "moist_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("moist_max", "moist_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product moisture 2.5% (25 x10) in [1, 100]");
}

/// Test 6: Nozzle atomization pressure (x10 bar) — 3.0 bar = 30, bounded [5, 60], value 30.
#[test]
fn test_nozzle_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noz_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("noz_val", "noz_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("noz_min", "noz_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("noz_max", "noz_x10 <= 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle pressure 3.0 bar (30 x10) in [5, 60]");
}

/// Test 7: Process mode — 3-way disjunction.
/// 1=top-spray, 2=bottom-spray, 3=tangential-spray. Value 1 (top-spray).
#[test]
fn test_process_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "process mode 1 (top-spray) is valid 3-way disjunction",
    );
}

/// Test 8: Filter type — 3-way disjunction.
/// 1=bag, 2=cartridge, 3=stainless-mesh. Value 2 (cartridge).
#[test]
fn test_filter_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter", u32_ty());
    ctx.push_obligation(ProofObligation::assume("filt_val", "filter == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_filter",
        "filter == 1 || filter == 2 || filter == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "filter type 2 (cartridge) is valid 3-way disjunction",
    );
}

/// Test 9: Bowl material — 3-way disjunction.
/// 1=stainless-304, 2=stainless-316L, 3=hastelloy. Value 2 (stainless-316L).
#[test]
fn test_bowl_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bowl_mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bowl_val", "bowl_mat == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_bowl",
        "bowl_mat == 1 || bowl_mat == 2 || bowl_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bowl material 2 (stainless-316L) is valid 3-way disjunction",
    );
}

/// Test 10: Explosion-proof rating — boolean flag using i32 with if/else pattern.
/// Flag 1 = unit is explosion-proof rated, assert rating active.
#[test]
fn test_explosion_proof_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exproof", i32_ty());
    ctx.declare_var_typed("rating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "exproof == 0 || exproof == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "exproof == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rating_def",
        "rating == if exproof == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rating_active", "rating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "explosion-proof flag triggers rating active");
}
