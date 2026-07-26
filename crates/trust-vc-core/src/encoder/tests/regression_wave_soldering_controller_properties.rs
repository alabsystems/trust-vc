// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Wave soldering controller property verification.
// Encodes key parameters of a wave soldering machine and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Solder pot temperature (deg C) — bounded [200, 300], value 255.
/// All values positive so no offset needed.
#[test]
fn test_solder_pot_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pot_temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pt_val", "pot_temp_c == 255"));
    ctx.push_obligation(ProofObligation::assert("pt_min", "pot_temp_c >= 200"));
    ctx.push_obligation(ProofObligation::assert("pt_max", "pot_temp_c <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solder pot temp 255 C in [200, 300]");
}

/// Test 2: Conveyor speed (x10 mm/s) — 120.0 mm/s = 1200, bounded [100, 3000], value 1200.
#[test]
fn test_conveyor_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cs_val", "speed_x10 == 1200"));
    ctx.push_obligation(ProofObligation::assert("cs_min", "speed_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("cs_max", "speed_x10 <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "conveyor speed 120.0 mm/s (1200 x10) in [100, 3000]",
    );
}

/// Test 3: Solder type — 3-way disjunction.
/// 1=Sn63Pb37, 2=SAC305, 3=SN100C. Value 2 (SAC305).
#[test]
fn test_solder_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solder_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("st_val", "solder_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_solder_type",
        "solder_type == 1 || solder_type == 2 || solder_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solder type 2 (SAC305) is valid 3-way disjunction");
}

/// Test 4: Preheat zone count — bounded [1, 6], value 3.
#[test]
fn test_preheat_zone_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("preheat_zones", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pz_val", "preheat_zones == 3"));
    ctx.push_obligation(ProofObligation::assert("pz_min", "preheat_zones >= 1"));
    ctx.push_obligation(ProofObligation::assert("pz_max", "preheat_zones <= 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "preheat zone count 3 in [1, 6]");
}

/// Test 5: Preheat temperature (deg C) — offset +500, bounded [550, 700].
/// Real range: 50 C to 200 C. Value 150 C → 650 with offset.
#[test]
fn test_preheat_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("preheat_temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pht_range",
        "preheat_temp_off >= 550 && preheat_temp_off <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pht_lower",
        "preheat_temp_off >= 550",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pht_upper",
        "preheat_temp_off <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "preheat temp (offset +500) in [550, 700] implies bounds",
    );
}

/// Test 6: Wave type — 3-way disjunction.
/// 1=lambda, 2=chip, 3=dual. Value 3 (dual).
#[test]
fn test_wave_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wave_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wt_val", "wave_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_wave_type",
        "wave_type == 1 || wave_type == 2 || wave_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wave type 3 (dual) is valid 3-way disjunction");
}

/// Test 7: Flux type — 3-way disjunction.
/// 1=rosin, 2=no-clean, 3=water-soluble. Value 1 (rosin).
#[test]
fn test_flux_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flux_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ft_val", "flux_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_flux_type",
        "flux_type == 1 || flux_type == 2 || flux_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flux type 1 (rosin) is valid 3-way disjunction");
}

/// Test 8: Board width max (mm) — bounded [50, 500], value 300.
#[test]
fn test_board_width_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("board_width_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bw_val", "board_width_mm == 300"));
    ctx.push_obligation(ProofObligation::assert("bw_min", "board_width_mm >= 50"));
    ctx.push_obligation(ProofObligation::assert("bw_max", "board_width_mm <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "board width 300 mm in [50, 500]");
}

/// Test 9: Nitrogen atmosphere — boolean flag using i32.
/// Flag 1 = inert gas blanket enabled, which activates N2 flow (n2_flow_active = 1).
#[test]
fn test_nitrogen_atmosphere_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n2_flag", i32_ty());
    ctx.declare_var_typed("n2_flow_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "n2_flag == 0 || n2_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "n2_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "flow_def",
        "n2_flow_active == if n2_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "n2_flow_triggered",
        "n2_flow_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nitrogen atmosphere flag enables N2 flow");
}

/// Test 10: Dross removal — boolean flag using i32.
/// Flag 1 = automatic dross skimmer enabled, which activates skimmer (skimmer_active = 1).
#[test]
fn test_dross_removal_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dross_flag", i32_ty());
    ctx.declare_var_typed("skimmer_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "dross_flag == 0 || dross_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "dross_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "skimmer_def",
        "skimmer_active == if dross_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "skimmer_triggered",
        "skimmer_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dross removal flag activates skimmer");
}
