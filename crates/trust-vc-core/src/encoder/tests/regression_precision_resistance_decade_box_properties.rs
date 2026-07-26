// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_decade_box_max_resistance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("r_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a",
        "r_max >= 1 && r_max <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "c",
        "r_max >= 1 && r_max <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "decade box: max resistance 1-100000000 ohms bounded",
    );
}

#[test]
fn test_decade_box_min_step_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("step_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a",
        "step_x100 >= 1 && step_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "c",
        "step_x100 >= 1 && step_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decade box: min step x100 ohms bounded");
}

#[test]
fn test_decade_box_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a",
        "acc_x10000 >= 1 && acc_x10000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "c",
        "acc_x10000 >= 1 && acc_x10000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decade box: accuracy x10000 percent bounded");
}

#[test]
fn test_decade_box_decades_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "dec >= 3 && dec <= 9"));
    ctx.push_obligation(ProofObligation::assert("c", "dec >= 3 && dec <= 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decade box: decade count 3-9 bounded");
}

#[test]
fn test_decade_box_power_rating_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a",
        "pwr_x10 >= 1 && pwr_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "c",
        "pwr_x10 >= 1 && pwr_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decade box: power rating x10 watts bounded");
}

#[test]
fn test_decade_box_temp_coeff_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "tc_x10 >= 1 && tc_x10 <= 200"));
    ctx.push_obligation(ProofObligation::assert("c", "tc_x10 >= 1 && tc_x10 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decade box: temp coefficient x10 ppm bounded");
}

#[test]
fn test_decade_box_switch_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a",
        "sw == 1 || sw == 2 || sw == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "c",
        "sw == 1 || sw == 2 || sw == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decade box: switch type rotary/pushbutton/relay");
}

#[test]
fn test_decade_box_resistor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a",
        "rt == 1 || rt == 2 || rt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "c",
        "rt == 1 || rt == 2 || rt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "decade box: resistor type wirewound/metal film/foil",
    );
}

#[test]
fn test_decade_box_connection_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "c",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "decade box: connection 2-terminal/4-terminal/guarded",
    );
}

#[test]
fn test_decade_box_programmable_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prog", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "prog == 0 || prog == 1"));
    ctx.push_obligation(ProofObligation::assert("c", "prog == 0 || prog == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decade box: programmable boolean flag");
}
