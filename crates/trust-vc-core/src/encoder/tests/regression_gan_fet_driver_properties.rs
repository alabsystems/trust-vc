// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gate_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["mv", "mv_min", "mv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gate drive voltage in mV: value 5500 (5.5V), valid range 4500-7000 (GaN needs precise 5-6V)
    ctx.push_obligation(ProofObligation::assume("gv_val", "mv == 5500"));
    ctx.push_obligation(ProofObligation::assume("gv_min", "mv_min == 4500"));
    ctx.push_obligation(ProofObligation::assume("gv_max", "mv_max == 7000"));
    ctx.push_obligation(ProofObligation::assert(
        "gv_in_range",
        "mv >= mv_min && mv <= mv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gate voltage 5500 mV in range [4500,7000]");
}

#[test]
fn blocking_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bv", u32_ty());
    ctx.declare_var_typed("valid_bv", i32_ty());
    // Non-sequential GaN voltage classes: 100, 200, 650
    ctx.push_obligation(ProofObligation::assume("bk_val", "bv == 650"));
    ctx.push_obligation(ProofObligation::assume(
        "bk_def",
        "valid_bv == if bv == 100 || bv == 200 || bv == 650 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bk_chk", "valid_bv == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blocking voltage 650 V is valid GaN class");
}

#[test]
fn rise_time() {
    let mut ctx = VerificationContext::new();
    for v in &["ns", "ns_min", "ns_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Rise time in ns: value 5 (much faster than Si/SiC), valid range 1-50
    ctx.push_obligation(ProofObligation::assume("rt_val", "ns == 5"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "ns_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "ns_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "ns >= ns_min && ns <= ns_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rise time 5 ns in range [1,50]");
}

#[test]
fn fall_time() {
    let mut ctx = VerificationContext::new();
    for v in &["ns", "ns_min", "ns_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Fall time in ns: value 4, valid range 1-50
    ctx.push_obligation(ProofObligation::assume("ft_val", "ns == 4"));
    ctx.push_obligation(ProofObligation::assume("ft_min", "ns_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ft_max", "ns_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "ft_in_range",
        "ns >= ns_min && ns <= ns_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fall time 4 ns in range [1,50]");
}

#[test]
fn dead_time() {
    let mut ctx = VerificationContext::new();
    for v in &["ns", "ns_min", "ns_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Dead time in ns: value 20, valid range 1-100
    ctx.push_obligation(ProofObligation::assume("dt_val", "ns == 20"));
    ctx.push_obligation(ProofObligation::assume("dt_min", "ns_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dt_max", "ns_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "dt_in_range",
        "ns >= ns_min && ns <= ns_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dead time 20 ns in range [1,100]");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["khz", "khz_min", "khz_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Switching frequency in kHz: value 1000, valid range 100-10000 (GaN excels at high freq)
    ctx.push_obligation(ProofObligation::assume("sf_val", "khz == 1000"));
    ctx.push_obligation(ProofObligation::assume("sf_min", "khz_min == 100"));
    ctx.push_obligation(ProofObligation::assume("sf_max", "khz_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "sf_in_range",
        "khz >= khz_min && khz <= khz_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switching frequency 1000 kHz in range [100,10000]");
}

#[test]
fn bootstrap_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["mv", "mv_min", "mv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bootstrap voltage in mV: value 5200, valid range 4000-8000
    ctx.push_obligation(ProofObligation::assume("bs_val", "mv == 5200"));
    ctx.push_obligation(ProofObligation::assume("bs_min", "mv_min == 4000"));
    ctx.push_obligation(ProofObligation::assume("bs_max", "mv_max == 8000"));
    ctx.push_obligation(ProofObligation::assert(
        "bs_in_range",
        "mv >= mv_min && mv <= mv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bootstrap voltage 5200 mV in range [4000,8000]");
}

#[test]
fn undervoltage_lockout() {
    let mut ctx = VerificationContext::new();
    for v in &["mv", "mv_min", "mv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Undervoltage lockout threshold in mV: value 3800, valid range 3000-5000
    ctx.push_obligation(ProofObligation::assume("ul_val", "mv == 3800"));
    ctx.push_obligation(ProofObligation::assume("ul_min", "mv_min == 3000"));
    ctx.push_obligation(ProofObligation::assume("ul_max", "mv_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "ul_in_range",
        "mv >= mv_min && mv <= mv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "undervoltage lockout 3800 mV in range [3000,5000]");
}

#[test]
fn driver_topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // 1=half-bridge, 2=full-bridge, 3=high-side only
    ctx.push_obligation(ProofObligation::assume("tp_val", "topo == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tp_chk", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "driver topology 1 (half-bridge) is valid");
}

#[test]
fn integrated_fet() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("integrated", i32_ty());
    // Boolean flag: 1=integrated GaN+driver, 0=discrete driver
    ctx.push_obligation(ProofObligation::assume("if_val", "integrated == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "if_chk",
        "integrated == 0 || integrated == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "integrated FET flag 1 is valid boolean");
}
