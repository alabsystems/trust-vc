// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn clock_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["clk_khz", "min_clk_khz", "max_clk_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("clk_ok", i32_ty());
    // External clock sets filter cutoff
    ctx.push_obligation(ProofObligation::assume("ck", "clk_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_clk_khz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_clk_khz == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "clk_ok == if clk_khz >= min_clk_khz && clk_khz <= max_clk_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "clk_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 100kHz clock in [10, 5000] → OK");
}

#[test]
fn cutoff_ratio() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio", u32_ty());
    ctx.declare_var_typed("valid_ratio", i32_ty());
    // Clock-to-cutoff ratio: standard values
    ctx.push_obligation(ProofObligation::assume("r", "ratio == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_ratio == if ratio == 50 || ratio == 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ratio == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 100:1 is a valid clock-to-cutoff ratio");
}

#[test]
fn passband_ripple() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_x100", "max_ripple_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ripple_ok", i32_ty());
    // Passband ripple in dB (×100 for 0.01dB)
    ctx.push_obligation(ProofObligation::assume("rx", "ripple_x100 == 50")); // 0.50dB
    ctx.push_obligation(ProofObligation::assume("mr", "max_ripple_x100 == 100")); // 1.00dB
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ripple_ok == if ripple_x100 <= max_ripple_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ripple_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 0.50dB ripple ≤ 1.00dB max → OK");
}

#[test]
fn stopband_attenuation() {
    let mut ctx = VerificationContext::new();
    for v in &["atten_db", "min_atten_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("atten_ok", i32_ty());
    // Stopband attenuation (higher = better)
    ctx.push_obligation(ProofObligation::assume("ad", "atten_db == 60"));
    ctx.push_obligation(ProofObligation::assume("ma", "min_atten_db == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "atten_ok == if atten_db >= min_atten_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "atten_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 60dB stopband ≥ 40dB min → OK");
}

#[test]
fn filter_order() {
    let mut ctx = VerificationContext::new();
    for v in &["order", "min_order", "max_order"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("order_ok", i32_ty());
    // Filter order (2-8 typical for SC filters)
    ctx.push_obligation(ProofObligation::assume("o", "order == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_order == 2"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_order == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "order_ok == if order >= min_order && order <= max_order { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "order_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 4th order in [2, 8] → OK");
}

#[test]
fn sampling_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["fs_over_fc", "min_ratio"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ratio_ok", i32_ty());
    // Nyquist: clock must be well above cutoff
    ctx.push_obligation(ProofObligation::assume("ff", "fs_over_fc == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_ratio == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ratio_ok == if fs_over_fc >= min_ratio { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ratio_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 100:1 sampling ratio ≥ 50 min → OK");
}

#[test]
fn capacitor_ratio_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Capacitor matching accuracy: % (×100 for 0.01%)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x100 == 10")); // 0.10%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 0.10% cap accuracy ≤ 0.50% max → OK");
}

#[test]
fn charge_injection() {
    let mut ctx = VerificationContext::new();
    for v in &["injection_pc", "max_injection_pc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("inj_ok", i32_ty());
    // Switch charge injection: picocoulombs
    ctx.push_obligation(ProofObligation::assume("ip", "injection_pc == 5"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_injection_pc == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "inj_ok == if injection_pc <= max_injection_pc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "inj_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 5pC charge injection ≤ 20pC max → OK");
}

#[test]
fn settling_time() {
    let mut ctx = VerificationContext::new();
    for v in &["settle_us", "max_settle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("settle_ok", i32_ty());
    // Output settling time to specified accuracy
    ctx.push_obligation(ProofObligation::assume("su", "settle_us == 100"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_settle_us == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "settle_ok == if settle_us <= max_settle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "settle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 100μs settling ≤ 500μs max → OK");
}

#[test]
fn cmrr() {
    let mut ctx = VerificationContext::new();
    for v in &["cmrr_db", "min_cmrr_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cmrr_ok", i32_ty());
    // Common-Mode Rejection Ratio (higher = better)
    ctx.push_obligation(ProofObligation::assume("cd", "cmrr_db == 80"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cmrr_db == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cmrr_ok == if cmrr_db >= min_cmrr_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cmrr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC filter: 80dB CMRR ≥ 60dB min → OK");
}
