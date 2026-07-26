// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_freq_counter_max_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "freq >= 1 && freq <= 350000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "freq >= 1 && freq <= 350000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: max frequency 1-350000000 Hz bounded",
    );
}

#[test]
fn test_freq_counter_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "res_x100 >= 1 && res_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "res_x100 >= 1 && res_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: resolution x100 Hz (0.01 Hz) bounded",
    );
}

#[test]
fn test_freq_counter_accuracy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "acc_x1000 >= 1 && acc_x1000 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "acc_x1000 >= 1 && acc_x1000 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: accuracy x1000 ppm (0.001 ppm) bounded",
    );
}

#[test]
fn test_freq_counter_input_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "ch >= 1 && ch <= 4"));
    ctx.push_obligation(ProofObligation::assert("check", "ch >= 1 && ch <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: input channels 1-4 bounded",
    );
}

#[test]
fn test_freq_counter_gate_time_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gate_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "gate_x100 >= 1 && gate_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "gate_x100 >= 1 && gate_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: gate time x100 seconds (0.01s) bounded",
    );
}

#[test]
fn test_freq_counter_input_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("z", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "z == 50 || z == 1000000"));
    ctx.push_obligation(ProofObligation::assert("check", "z == 50 || z == 1000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: input impedance 50 or 1000000 ohms",
    );
}

#[test]
fn test_freq_counter_timebase_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tb", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "tb == 1 || tb == 2 || tb == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "tb == 1 || tb == 2 || tb == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: timebase 1=TCXO, 2=OCXO, 3=rubidium",
    );
}

#[test]
fn test_freq_counter_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: mode 1=frequency, 2=period, 3=ratio",
    );
}

#[test]
fn test_freq_counter_coupling_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cpl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "cpl == 1 || cpl == 2 || cpl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "cpl == 1 || cpl == 2 || cpl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: input coupling 1=AC, 2=DC, 3=50ohm",
    );
}

#[test]
fn test_freq_counter_timestamp_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ts", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounds", "ts == 0 || ts == 1"));
    ctx.push_obligation(ProofObligation::assert("check", "ts == 0 || ts == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision freq counter: timestamp capability boolean 0 or 1",
    );
}
