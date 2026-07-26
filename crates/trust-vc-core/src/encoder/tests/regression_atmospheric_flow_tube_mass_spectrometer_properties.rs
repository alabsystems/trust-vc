// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_aft_tube_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_p_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tp_a",
        "tube_p_x10 >= 5 && tube_p_x10 <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tp_c",
        "tube_p_x10 >= 5 && tube_p_x10 <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tube pressure x10 in [5, 20] representing 0.5-2.0 Torr",
    );
}

#[test]
fn test_aft_carrier_gas_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_a",
        "gas_flow >= 100 && gas_flow <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_c",
        "gas_flow >= 100 && gas_flow <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "carrier gas flow in [100, 50000] sccm");
}

#[test]
fn test_aft_tube_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tt_a",
        "tube_temp >= 200 && tube_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tt_c",
        "tube_temp >= 200 && tube_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube temperature in [200, 500] K");
}

#[test]
fn test_aft_reaction_time_ms_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rxn_ms", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_a",
        "rxn_ms >= 1 && rxn_ms <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rt_c",
        "rxn_ms >= 1 && rxn_ms <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reaction time in [1, 1000] ms");
}

#[test]
fn test_aft_tube_diameter_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_dia_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "td_a",
        "tube_dia_mm >= 10 && tube_dia_mm <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "td_c",
        "tube_dia_mm >= 10 && tube_dia_mm <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube diameter in [10, 200] mm");
}

#[test]
fn test_aft_reynolds_number_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("re_num", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rn_a",
        "re_num >= 1 && re_num <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rn_c",
        "re_num >= 1 && re_num <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Reynolds number in [1, 10000] (laminar to transitional)",
    );
}

#[test]
fn test_aft_ion_source_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "is_a",
        "ion_src == 1 || ion_src == 2 || ion_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_c",
        "ion_src == 1 || ion_src == 2 || ion_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ion source: electron impact, microwave discharge, or H-atom lamp",
    );
}

#[test]
fn test_aft_detection_method_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detect", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dm_a",
        "detect == 1 || detect == 2 || detect == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dm_c",
        "detect == 1 || detect == 2 || detect == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection: quadrupole MS, channel electron multiplier, or LIF",
    );
}

#[test]
fn test_aft_wall_coating_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wall_coat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wc_a",
        "wall_coat == 1 || wall_coat == 2 || wall_coat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wc_c",
        "wall_coat == 1 || wall_coat == 2 || wall_coat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wall coating: halocarbon wax, Teflon, or boric acid",
    );
}

#[test]
fn test_aft_movable_injector_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("movable_inj", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mi_a",
        "movable_inj == 0 || movable_inj == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mi_c",
        "movable_inj == 0 || movable_inj == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "movable injector flag is boolean");
}
