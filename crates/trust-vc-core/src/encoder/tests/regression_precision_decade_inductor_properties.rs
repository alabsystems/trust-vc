// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Maximum inductance in millihenries, bounded [1, 100000], value 10000 mH.
#[test]
fn max_inductance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_mh", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_mh >= 1 && max_mh <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "max_mh == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "max_mh >= 1 && max_mh <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "maximum inductance 10000 mH within [1, 100000]");
}

/// Number of decade selector dials, bounded [3, 7], value 6.
#[test]
fn decades_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dials", u8_ty());
    ctx.push_obligation(ProofObligation::assume("range", "dials >= 3 && dials <= 7"));
    ctx.push_obligation(ProofObligation::assume("val", "dials == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dials >= 3 && dials <= 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "6 decade dials within [3, 7]");
}

/// Accuracy as percentage x100 (0.10% = 10), bounded [1, 500], value 10.
#[test]
fn accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "acc >= 1 && acc <= 500"));
    ctx.push_obligation(ProofObligation::assume("val", "acc == 10"));
    ctx.push_obligation(ProofObligation::assert("bounded", "acc >= 1 && acc <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 10 (0.10%) within [1, 500]");
}

/// Minimum quality factor Q, bounded [1, 500], value 50.
#[test]
fn q_factor_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("q", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "q >= 1 && q <= 500"));
    ctx.push_obligation(ProofObligation::assume("val", "q == 50"));
    ctx.push_obligation(ProofObligation::assert("bounded", "q >= 1 && q <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "quality factor 50 within [1, 500]");
}

/// Maximum operating frequency in kHz, bounded [1, 10000], value 1000.
#[test]
fn max_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_khz >= 1 && freq_khz <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_khz == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_khz >= 1 && freq_khz <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max frequency 1000 kHz within [1, 10000]");
}

/// DC series resistance x100 ohms (0.50 ohm = 50), bounded [1, 10000], value 50.
#[test]
fn dc_resistance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rdc", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "rdc >= 1 && rdc <= 10000"));
    ctx.push_obligation(ProofObligation::assume("val", "rdc == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rdc >= 1 && rdc <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC resistance 50 (0.50 ohm) within [1, 10000]");
}

/// Core material: 1=ferrite, 2=iron-powder, 3=air-core.
#[test]
fn core_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "v == 1 || v == 2 || v == 3"));
    ctx.push_obligation(ProofObligation::assert("bounded", "v >= 1 && v <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "core material enum {ferrite, iron-powder, air-core} within [1, 3]",
    );
}

/// Winding type: 1=toroidal, 2=solenoid, 3=multilayer.
#[test]
fn winding_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "v == 1 || v == 2 || v == 3"));
    ctx.push_obligation(ProofObligation::assert("bounded", "v >= 1 && v <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "winding type enum {toroidal, solenoid, multilayer} within [1, 3]",
    );
}

/// Shielding type: 1=magnetic, 2=electrostatic, 3=none.
#[test]
fn shielding_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "v == 1 || v == 2 || v == 3"));
    ctx.push_obligation(ProofObligation::assert("bounded", "v >= 1 && v <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shielding enum {magnetic, electrostatic, none} within [1, 3]",
    );
}

/// Four-terminal (Kelvin) connection: boolean flag as i32 (1=true, 0=false).
#[test]
fn four_terminal_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "boolean",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "four-terminal Kelvin connection flag is true");
}
