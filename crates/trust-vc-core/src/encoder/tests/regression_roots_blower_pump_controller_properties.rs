// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression tests: roots blower vacuum pump controller property verification

use super::*;

#[test]
fn test_roots_blower_pumping_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pumping_speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pumping_speed_x10 >= 100 && pumping_speed_x10 <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "pumping_speed_x10 == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pumping_speed_x10 >= 100 && pumping_speed_x10 <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pumping speed x10 value 50000 (meaning 5000.0 m3/h) within 100-500000 range",
    );
}

#[test]
fn test_roots_blower_max_differential_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diff_press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "diff_press_x10 >= 10 && diff_press_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "diff_press_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "diff_press_x10 >= 10 && diff_press_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max differential pressure x10 value 1000 (meaning 100.0 mbar) within 10-10000 range",
    );
}

#[test]
fn test_roots_blower_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rotor_rpm >= 500 && rotor_rpm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rotor_rpm == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rotor_rpm >= 500 && rotor_rpm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed 3000 RPM within 500-5000 RPM range");
}

#[test]
fn test_roots_blower_ultimate_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ult_press_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ult_press_x100 >= 1 && ult_press_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "ult_press_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "ult_press_x100 >= 1 && ult_press_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ultimate pressure x100 value 10 (meaning 0.10 mbar) within 1-10000 range",
    );
}

#[test]
fn test_roots_blower_number_of_lobes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lobes", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "lobes >= 2 && lobes <= 4"));
    ctx.push_obligation(ProofObligation::assume("val", "lobes == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "lobes >= 2 && lobes <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of lobes 3 within 2-4 range");
}

#[test]
fn test_roots_blower_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "motor_kw >= 1 && motor_kw <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "motor_kw == 75"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "motor_kw >= 1 && motor_kw <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 75 kW within 1-500 kW range");
}

#[test]
fn test_roots_blower_lobe_profile_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lobe_profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "lobe_profile == 1 || lobe_profile == 2 || lobe_profile == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "lobe_profile == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "lobe_profile == 1 || lobe_profile == 2 || lobe_profile == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lobe profile is standard(1), twisted(2), or claw(3)",
    );
}

#[test]
fn test_roots_blower_sealing_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sealing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "sealing == 1 || sealing == 2 || sealing == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sealing == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "sealing == 1 || sealing == 2 || sealing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sealing method is clearance(1), oil-sealed(2), or gas-purge(3)",
    );
}

#[test]
fn test_roots_blower_cooling_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "cooling == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling type is air(1), water(2), or oil-circulation(3)",
    );
}

#[test]
fn test_roots_blower_automatic_bypass_valve_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bypass_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "bypass_flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "bypass_active",
        "if bypass_flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic bypass valve flag set implies conditional evaluates to 1",
    );
}
