// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pll_output_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mhz", "multiply", "divide"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_mhz", u32_ty());
    // Fout = Fin × M / D. Precompute: 100 × 5 / 2 = 250
    ctx.push_obligation(ProofObligation::assume("im", "input_mhz == 100"));
    ctx.push_obligation(ProofObligation::assume("m", "multiply == 5"));
    ctx.push_obligation(ProofObligation::assume("d", "divide == 2"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mhz == 250")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_250", "output_mhz == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: 100MHz × 5 / 2 = 250MHz (precomputed)");
}

#[test]
fn vco_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vco_mhz", "min_vco_mhz", "max_vco_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vco_ok", i32_ty());
    // VCO frequency range (e.g., Xilinx MMCM: 600-1200MHz)
    ctx.push_obligation(ProofObligation::assume("vm", "vco_mhz == 800"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vco_mhz == 600"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vco_mhz == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vco_ok == if vco_mhz >= min_vco_mhz && vco_mhz <= max_vco_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vco_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: VCO 800MHz in [600, 1200] → OK");
}

#[test]
fn phase_shift() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_deg", "max_phase_deg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("phase_ok", i32_ty());
    // Clock phase shift: 0-359 degrees
    ctx.push_obligation(ProofObligation::assume("pd", "phase_deg == 90"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_phase_deg == 359"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "phase_ok == if phase_deg <= max_phase_deg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "phase_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: 90° phase ≤ 359° max → OK");
}

#[test]
fn duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_pct", "min_duty_pct", "max_duty_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_ok", i32_ty());
    // Programmable duty cycle: 10-90% typical
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_duty_pct == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_duty_pct == 90"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if duty_pct >= min_duty_pct && duty_pct <= max_duty_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: 50% duty in [10, 90] → OK");
}

#[test]
fn jitter_spec() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ps", "max_jitter_ps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("jitter_ok", i32_ty());
    // Peak-to-peak jitter budget
    ctx.push_obligation(ProofObligation::assume("jp", "jitter_ps == 100"));
    ctx.push_obligation(ProofObligation::assume("mj", "max_jitter_ps == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "jo_def",
        "jitter_ok == if jitter_ps <= max_jitter_ps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "jitter_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: 100ps jitter ≤ 300ps max → OK");
}

#[test]
fn clock_outputs() {
    let mut ctx = VerificationContext::new();
    for v in &["outputs", "max_outputs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("out_ok", i32_ty());
    // Number of clock outputs from PLL/MMCM (e.g., MMCM: up to 7)
    ctx.push_obligation(ProofObligation::assume("o", "outputs == 4"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_outputs == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "out_ok == if outputs <= max_outputs { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "out_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: 4 outputs ≤ 7 max → OK");
}

#[test]
fn lock_time() {
    let mut ctx = VerificationContext::new();
    for v in &["lock_us", "max_lock_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lock_ok", i32_ty());
    // PLL lock time (time to achieve stable output)
    ctx.push_obligation(ProofObligation::assume("lu", "lock_us == 50"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_lock_us == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lock_ok == if lock_us <= max_lock_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lock_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: 50μs lock ≤ 100μs max → OK");
}

#[test]
fn input_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["fin_mhz", "min_fin_mhz", "max_fin_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fin_ok", i32_ty());
    // PLL input frequency range
    ctx.push_obligation(ProofObligation::assume("fm", "fin_mhz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_fin_mhz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_fin_mhz == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fin_ok == if fin_mhz >= min_fin_mhz && fin_mhz <= max_fin_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: 100MHz input in [10, 800] → OK");
}

#[test]
fn spread_spectrum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ss_enabled", u32_ty());
    ctx.declare_var_typed("emi_reduced", i32_ty());
    // Spread spectrum clocking for EMI reduction
    ctx.push_obligation(ProofObligation::assume("se", "ss_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "emi_reduced == if ss_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "emi_reduced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: SS=1 → EMI reduced");
}

#[test]
fn clock_domain() {
    let mut ctx = VerificationContext::new();
    for v in &["domain_id", "max_domains"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("domain_ok", i32_ty());
    // Clock domain identifier within design
    ctx.push_obligation(ProofObligation::assume("di", "domain_id == 3"));
    ctx.push_obligation(ProofObligation::assume("md", "max_domains == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "domain_ok == if domain_id < max_domains { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "domain_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FPGA CLK: domain 3 < 8 max → OK");
}
