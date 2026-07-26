// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bag_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bags", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bag_range",
        "bags >= 10 && bags <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "bags >= 10"));
    ctx.push_obligation(ProofObligation::assert("upper", "bags <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bag count in [10, 5000] implies bounds hold");
}

#[test]
fn air_to_cloth_ratio_bounded() {
    // Air-to-cloth ratio scaled ×100: 1.50 → 150, range [50, 500]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio_x100 >= 50 && ratio_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "ratio_x100 >= 50"));
    ctx.push_obligation(ProofObligation::assert("upper", "ratio_x100 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air-to-cloth ratio (×100) in [50, 500] implies bounds",
    );
}

#[test]
fn cleaning_type_three_way_disjunction() {
    // 1=pulse jet, 2=reverse air, 3=shaker
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cleaning", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_cleaning",
        "cleaning == 1 || cleaning == 2 || cleaning == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "cleaning >= 1 && cleaning <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cleaning type {1,2,3} implies [1,3] bounds");
}

#[test]
fn differential_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_range",
        "dp >= 200 && dp <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "dp >= 200"));
    ctx.push_obligation(ProofObligation::assert("upper", "dp <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "differential pressure (Pa) in [200, 3000] implies bounds",
    );
}

#[test]
fn pulse_duration_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_ms", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pulse_range",
        "pulse_ms >= 50 && pulse_ms <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "pulse_ms >= 50"));
    ctx.push_obligation(ProofObligation::assert("upper", "pulse_ms <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse duration (ms) in [50, 500] implies bounds");
}

#[test]
fn bag_material_four_way_disjunction() {
    // 1=polyester, 2=Nomex, 3=PTFE, 4=fiberglass
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_material",
        "material == 1 || material == 2 || material == 3 || material == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "material >= 1 && material <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bag material {1,2,3,4} implies [1,4] bounds");
}

#[test]
fn gas_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_vol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_range",
        "gas_vol >= 1000 && gas_vol <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "gas_vol >= 1000"));
    ctx.push_obligation(ProofObligation::assert("upper", "gas_vol <= 500000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas volume (m³/h) in [1000, 500000] implies bounds",
    );
}

#[test]
fn emission_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emission", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "emission_range",
        "emission >= 1 && emission <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "emission >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "emission <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "emission limit (mg/m³) in [1, 50] implies bounds");
}

#[test]
fn operating_temp_offset_bounded() {
    // Temperature offset +500: 20°C → 520. Valid range [450, 800] (i.e. -50°C to 300°C).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 450 && temp_off <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "temp_off >= 450"));
    ctx.push_obligation(ProofObligation::assert("upper", "temp_off <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp (offset +500) in [450, 800] implies bounds",
    );
}

#[test]
fn bag_leak_detect_boolean_flag() {
    // Boolean flag encoded as i32: 0=no leak, 1=leak detected
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_flag", i32_ty());
    ctx.declare_var_typed("alarm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "leak_flag == 0 || leak_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm == if leak_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "alarm_matches_flag",
        "alarm == leak_flag",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bag leak detect flag propagates to alarm correctly",
    );
}
