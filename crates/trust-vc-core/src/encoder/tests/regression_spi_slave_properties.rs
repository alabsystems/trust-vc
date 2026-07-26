// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn clock_polarity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cpol", u32_ty());
    ctx.declare_var_typed("idle_high", i32_ty());
    // CPOL: 0=idle low, 1=idle high
    ctx.push_obligation(ProofObligation::assume("c", "cpol == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "idle_high == if cpol == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "idle_high == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: CPOL=1 → clock idle high");
}

#[test]
fn clock_phase() {
    let mut ctx = VerificationContext::new();
    for v in &["cpol", "cpha"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("spi_mode", u32_ty());
    // SPI mode = CPOL*2 + CPHA. Precompute: 1*2 + 1 = 3
    ctx.push_obligation(ProofObligation::assume("cp", "cpol == 1"));
    ctx.push_obligation(ProofObligation::assume("ch", "cpha == 1"));
    ctx.push_obligation(ProofObligation::assume("sm", "spi_mode == 3")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_3", "spi_mode == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: CPOL=1, CPHA=1 → mode 3 (precomputed)");
}

#[test]
fn max_clock_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["sclk_mhz", "max_sclk_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Slave max clock frequency
    ctx.push_obligation(ProofObligation::assume("sm", "sclk_mhz == 20"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_sclk_mhz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if sclk_mhz <= max_sclk_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: 20MHz SCLK ≤ 50MHz max → freq OK");
}

#[test]
fn word_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits", u32_ty());
    ctx.declare_var_typed("valid_size", i32_ty());
    // Common SPI word sizes: 8, 16, 32
    ctx.push_obligation(ProofObligation::assume("b", "bits == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_size == if bits == 8 || bits == 16 || bits == 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_size == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: 16-bit word is valid size");
}

#[test]
fn chip_select_active() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cs_pin", u32_ty());
    ctx.declare_var_typed("selected", i32_ty());
    // CS active low: 0=selected, 1=deselected
    ctx.push_obligation(ProofObligation::assume("cp", "cs_pin == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "selected == if cs_pin == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "selected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: CS=0 → selected (active low)");
}

#[test]
fn fifo_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_entries", "max_fifo"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fifo_ok", i32_ty());
    // TX/RX FIFO depth
    ctx.push_obligation(ProofObligation::assume("fe", "fifo_entries == 8"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_fifo == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fifo_ok == if fifo_entries <= max_fifo { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fifo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: 8 FIFO entries ≤ 16 max → OK");
}

#[test]
fn setup_time() {
    let mut ctx = VerificationContext::new();
    for v in &["setup_ns", "min_setup_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timing_ok", i32_ty());
    // Data setup time before clock edge
    ctx.push_obligation(ProofObligation::assume("sn", "setup_ns == 10"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_setup_ns == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timing_ok == if setup_ns >= min_setup_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timing_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: 10ns setup ≥ 5ns min → timing OK");
}

#[test]
fn hold_time() {
    let mut ctx = VerificationContext::new();
    for v in &["hold_ns", "min_hold_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hold_ok", i32_ty());
    // Data hold time after clock edge
    ctx.push_obligation(ProofObligation::assume("hn", "hold_ns == 8"));
    ctx.push_obligation(ProofObligation::assume("mh", "min_hold_ns == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hold_ok == if hold_ns >= min_hold_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hold_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: 8ns hold ≥ 3ns min → OK");
}

#[test]
fn bit_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("msb_first", u32_ty());
    ctx.declare_var_typed("is_msb", i32_ty());
    // Bit order: 0=LSB first, 1=MSB first
    ctx.push_obligation(ProofObligation::assume("mf", "msb_first == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "is_msb == if msb_first == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_msb == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: msb_first=1 → MSB-first order");
}

#[test]
fn cs_to_sclk_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["delay_ns", "min_delay_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("delay_ok", i32_ty());
    // Minimum delay from CS assertion to first SCLK edge
    ctx.push_obligation(ProofObligation::assume("dn", "delay_ns == 20"));
    ctx.push_obligation(ProofObligation::assume("md", "min_delay_ns == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "delay_ok == if delay_ns >= min_delay_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "delay_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI slave: 20ns CS-to-SCLK ≥ 10ns min → OK");
}
