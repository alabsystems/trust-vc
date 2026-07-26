// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_vacuum_belt_dryer_belt_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_bounds",
        "area >= 1 && area <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_check",
        "area >= 1 && area <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt area should be bounded between 1 and 50 m^2");
}

#[test]
fn test_vacuum_belt_dryer_belt_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spd_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_bounds",
        "spd_x100 >= 1 && spd_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "spd_x100 >= 1 && spd_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt speed x100 should be bounded between 1 and 500",
    );
}

#[test]
fn test_vacuum_belt_dryer_vacuum_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vacuum_bounds",
        "vac_x10 >= 1 && vac_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vacuum_check",
        "vac_x10 >= 1 && vac_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vacuum x10 should be bounded between 1 and 1000 mbar",
    );
}

#[test]
fn test_vacuum_belt_dryer_heating_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_bounds",
        "temp >= 530 && temp <= 650",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_check",
        "temp >= 530 && temp <= 650",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating temp offset+500 should be bounded between 530 and 650",
    );
}

#[test]
fn test_vacuum_belt_dryer_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "throughput_bounds",
        "tp >= 10 && tp <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "throughput_check",
        "tp >= 10 && tp <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "throughput should be bounded between 10 and 5000 kg/h",
    );
}

#[test]
fn test_vacuum_belt_dryer_residence_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "residence_bounds",
        "rt >= 5 && rt <= 120",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "residence_check",
        "rt >= 5 && rt <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "residence time should be bounded between 5 and 120 min",
    );
}

#[test]
fn test_vacuum_belt_dryer_heating_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heating_method",
        "heat == 1 || heat == 2 || heat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heating_check",
        "heat == 1 || heat == 2 || heat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method should be conduction, radiation, or microwave",
    );
}

#[test]
fn test_vacuum_belt_dryer_feed_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_type",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_check",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed type should be liquid, paste, or granular");
}

#[test]
fn test_vacuum_belt_dryer_condenser_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "condenser_type",
        "cond == 1 || cond == 2 || cond == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "condenser_check",
        "cond == 1 || cond == 2 || cond == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condenser type should be shell-tube, plate, or spray",
    );
}

#[test]
fn test_vacuum_belt_dryer_cip_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cip", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cip_boolean",
        "cip == 0 || cip == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("cip_check", "cip == 0 || cip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CIP flag should be 0 or 1");
}
