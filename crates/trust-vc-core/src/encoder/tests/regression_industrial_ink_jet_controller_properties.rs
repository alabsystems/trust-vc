// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial ink jet controller property verification.
// Encodes key parameters of an industrial ink jet printing system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Print speed (m/min) — line speed bounded [1, 500], value 120.
#[test]
fn test_print_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("print_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "print_speed == 120"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "print_speed >= 1"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "print_speed <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "print speed 120 m/min in [1, 500]");
}

/// Test 2: Resolution (DPI) — print resolution bounded [50, 1200], value 600.
#[test]
fn test_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution == 600"));
    ctx.push_obligation(ProofObligation::assert("res_min", "resolution >= 50"));
    ctx.push_obligation(ProofObligation::assert("res_max", "resolution <= 1200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 600 DPI in [50, 1200]");
}

/// Test 3: Ink type — 4-way disjunction.
/// 1=solvent, 2=UV curable, 3=water-based, 4=thermal. Value 2 (UV curable).
#[test]
fn test_ink_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ink_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ink_val", "ink_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ink",
        "ink_type == 1 || ink_type == 2 || ink_type == 3 || ink_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ink type 2 (UV curable) is valid 4-way disjunction",
    );
}

/// Test 4: Nozzle count — number of active nozzles bounded [1, 256], value 128.
#[test]
fn test_nozzle_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("nozzle_val", "nozzle_count == 128"));
    ctx.push_obligation(ProofObligation::assert("nozzle_min", "nozzle_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("nozzle_max", "nozzle_count <= 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle count 128 in [1, 256]");
}

/// Test 5: Drop volume (pL) — ink drop volume bounded [1, 200], value 35.
#[test]
fn test_drop_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drop_volume", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drop_val", "drop_volume == 35"));
    ctx.push_obligation(ProofObligation::assert("drop_min", "drop_volume >= 1"));
    ctx.push_obligation(ProofObligation::assert("drop_max", "drop_volume <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drop volume 35 pL in [1, 200]");
}

/// Test 6: Print head temperature offset +500 (deg C) — bounded [480, 600], value 520.
/// 520 represents 20°C (520 - 500), 480 represents -20°C, 600 represents 100°C.
#[test]
fn test_print_head_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "head_temp_offset == 520",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "head_temp_offset >= 480",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "head_temp_offset <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "print head temp 20 C (offset 520) in [480, 600]");
}

/// Test 7: Communication interface — 3-way disjunction.
/// 1=Ethernet, 2=RS-232, 3=USB. Value 1 (Ethernet).
#[test]
fn test_communication_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_iface", u32_ty());
    ctx.push_obligation(ProofObligation::assume("comm_val", "comm_iface == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm",
        "comm_iface == 1 || comm_iface == 2 || comm_iface == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "communication 1 (Ethernet) is valid 3-way disjunction",
    );
}

/// Test 8: Substrate type — 4-way disjunction.
/// 1=paper, 2=plastic, 3=metal, 4=glass. Value 3 (metal).
#[test]
fn test_substrate_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("substrate", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sub_val", "substrate == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_substrate",
        "substrate == 1 || substrate == 2 || substrate == 3 || substrate == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "substrate type 3 (metal) is valid 4-way disjunction",
    );
}

/// Test 9: Line count — number of print lines per pass bounded [1, 10], value 4.
#[test]
fn test_line_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("line_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("line_val", "line_count == 4"));
    ctx.push_obligation(ProofObligation::assert("line_min", "line_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("line_max", "line_count <= 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "line count 4 in [1, 10]");
}

/// Test 10: Auto-purge — boolean flag using i32 with if/else pattern.
/// Flag 1 = auto-purge enabled, triggers purge cycle interval of 60 seconds.
#[test]
fn test_auto_purge_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_purge", i32_ty());
    ctx.declare_var_typed("purge_interval", u32_ty());
    ctx.declare_var_typed("effective_interval", u32_ty());
    ctx.declare_var_typed("no_purge", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_purge == 1"));
    ctx.push_obligation(ProofObligation::assume("no_purge_val", "no_purge == 9999"));
    ctx.push_obligation(ProofObligation::assume("purge_val", "purge_interval == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "interval_def",
        "effective_interval == if auto_purge == 1 { purge_interval } else { no_purge }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "purge_limits_interval",
        "effective_interval <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-purge flag limits interval to 60 seconds");
}
