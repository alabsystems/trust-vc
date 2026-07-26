// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_mhz", "min_freq_mhz", "max_freq_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Output frequency in MHz
    ctx.push_obligation(ProofObligation::assume("fm", "freq_mhz == 2400"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_mhz == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_mhz == 6000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_mhz >= min_freq_mhz && freq_mhz <= max_freq_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 2400 MHz in [100, 6000] → OK");
}

#[test]
fn reference_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["ref_khz", "min_ref_khz", "max_ref_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ref_ok", i32_ty());
    // Reference input frequency in kHz
    ctx.push_obligation(ProofObligation::assume("rk", "ref_khz == 10000")); // 10 MHz
    ctx.push_obligation(ProofObligation::assume("mn", "min_ref_khz == 1000")); // 1 MHz
    ctx.push_obligation(ProofObligation::assume("mx", "max_ref_khz == 250000")); // 250 MHz
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ref_ok == if ref_khz >= min_ref_khz && ref_khz <= max_ref_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ref_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 10 MHz ref in [1, 250] MHz → OK");
}

#[test]
fn phase_noise() {
    let mut ctx = VerificationContext::new();
    for v in &["noise_offset", "max_noise_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("noise_ok", i32_ty());
    // Phase noise in dBc/Hz at 10kHz offset (using offset +200 for negative values)
    // -100 dBc/Hz → offset = 100, -120 → offset = 80
    ctx.push_obligation(ProofObligation::assume("no", "noise_offset == 100")); // -100 dBc/Hz
    ctx.push_obligation(ProofObligation::assume("mn", "max_noise_offset == 120")); // max = -80 dBc/Hz
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "noise_ok == if noise_offset <= max_noise_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "noise_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: -100 dBc/Hz noise ≤ -80 dBc/Hz max → OK");
}

#[test]
fn loop_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_khz", "min_bw_khz", "max_bw_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Loop filter bandwidth in kHz
    ctx.push_obligation(ProofObligation::assume("bk", "bw_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw_khz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_khz >= min_bw_khz && bw_khz <= max_bw_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 100 kHz bandwidth in [1, 1000] → OK");
}

#[test]
fn charge_pump_current() {
    let mut ctx = VerificationContext::new();
    for v in &["cp_ua", "max_cp_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cp_ok", i32_ty());
    // Charge pump current in μA
    ctx.push_obligation(ProofObligation::assume("cu", "cp_ua == 5000")); // 5 mA
    ctx.push_obligation(ProofObligation::assume("mc", "max_cp_ua == 15000")); // 15 mA
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cp_ok == if cp_ua <= max_cp_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 5mA charge pump ≤ 15mA max → OK");
}

#[test]
fn lock_detect_time() {
    let mut ctx = VerificationContext::new();
    for v in &["lock_us", "max_lock_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lock_ok", i32_ty());
    // Lock acquisition time in μs
    ctx.push_obligation(ProofObligation::assume("lu", "lock_us == 50"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_lock_us == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lock_ok == if lock_us <= max_lock_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lock_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: 50μs lock time ≤ 500μs max → OK");
}

#[test]
fn divider_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["n_divider", "min_n", "max_n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("div_ok", i32_ty());
    // Integer-N divider ratio
    ctx.push_obligation(ProofObligation::assume("nd", "n_divider == 240"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_n == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_n == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "div_ok == if n_divider >= min_n && n_divider <= max_n { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "div_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: N=240 divider in [1, 65535] → OK");
}

#[test]
fn pll_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pll_arch", u32_ty());
    ctx.declare_var_typed("valid_arch", i32_ty());
    // PLL architectures: 1=integer-N, 2=fractional-N, 3=all-digital, 4=analog
    ctx.push_obligation(ProofObligation::assume("pa", "pll_arch == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_arch == if pll_arch == 1 || pll_arch == 2 || pll_arch == 3 || pll_arch == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_arch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: fractional-N is valid architecture");
}

#[test]
fn vco_tuning_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vco_min_mhz", "vco_max_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vco_ok", i32_ty());
    // VCO must have positive tuning range
    ctx.push_obligation(ProofObligation::assume("vn", "vco_min_mhz == 2000"));
    ctx.push_obligation(ProofObligation::assume("vx", "vco_max_mhz == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vco_ok == if vco_max_mhz > vco_min_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vco_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: VCO [2000, 4000] MHz has positive range");
}

#[test]
fn spur_level() {
    let mut ctx = VerificationContext::new();
    for v in &["spur_offset", "max_spur_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("spur_ok", i32_ty());
    // Reference spur level (offset +100 for negative dBc)
    // -60 dBc → offset = 40, -80 dBc → offset = 20
    ctx.push_obligation(ProofObligation::assume("so", "spur_offset == 30")); // -70 dBc
    ctx.push_obligation(ProofObligation::assume("ms", "max_spur_offset == 50")); // -50 dBc max
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "spur_ok == if spur_offset <= max_spur_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "spur_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL: -70 dBc spur ≤ -50 dBc max → OK");
}
