// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_tube_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume("kv_range", "kv >= 5 && kv <= 60"));
    ctx.push_obligation(ProofObligation::assume("kv_val", "kv == 50"));
    ctx.push_obligation(ProofObligation::assert("kv_is_50", "kv == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "X-ray tube voltage should be 50 kV");
}

#[test]
fn test_tube_current_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_range",
        "curr_x10 >= 1 && curr_x10 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assume("curr_val", "curr_x10 == 10000"));
    ctx.push_obligation(ProofObligation::assert("curr_is_1a", "curr_x10 == 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube current x10 should be 10000 (1000.0 mA = 1A)");
}

#[test]
fn test_element_range_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("z_min", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "z_min_range",
        "z_min >= 4 && z_min <= 11",
    ));
    ctx.push_obligation(ProofObligation::assume("z_min_val", "z_min == 5"));
    ctx.push_obligation(ProofObligation::assert("z_min_is_boron", "z_min == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min detectable atomic number should be 5 (Boron)");
}

#[test]
fn test_element_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("z_max", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "z_max_range",
        "z_max >= 82 && z_max <= 92",
    ));
    ctx.push_obligation(ProofObligation::assume("z_max_val", "z_max == 92"));
    ctx.push_obligation(ProofObligation::assert("z_max_is_uranium", "z_max == 92"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max detectable atomic number should be 92 (Uranium)",
    );
}

#[test]
fn test_detection_limit_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lod_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lod_range",
        "lod_x100 >= 1 && lod_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("lod_val", "lod_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert("lod_is_010ppm", "lod_x100 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit x100 should be 10 (0.10 ppm)");
}

#[test]
fn test_spot_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_range",
        "spot_x10 >= 10 && spot_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("spot_val", "spot_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert("spot_is_25um", "spot_x10 == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "analysis spot size x10 should be 250 (25.0 um)");
}

#[test]
fn test_excitation_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "src_valid",
        "src == 1 || src == 2 || src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "src_in_range",
        "src >= 1 && src <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation source (1=rhodium, 2=molybdenum, 3=palladium) should be in [1,3]",
    );
}

#[test]
fn test_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_valid",
        "det == 1 || det == 2 || det == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_in_range",
        "det >= 1 && det <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type (1=SDD, 2=proportional, 3=scintillation) should be in [1,3]",
    );
}

#[test]
fn test_analysis_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_in_range",
        "mode >= 1 && mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis mode (1=WDXRF, 2=EDXRF, 3=TXRF) should be in [1,3]",
    );
}

#[test]
fn test_vacuum_chamber_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_true", "vac == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_one",
        "if vac == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vacuum chamber flag should evaluate to 1 when enabled",
    );
}
