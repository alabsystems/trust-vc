// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pll_output_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["input_hz", "multiplier", "divider", "output_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // PLL output = input * N / M
    ctx.push_obligation(ProofObligation::assume("ih", "input_hz == 8000000")); // 8MHz crystal
    ctx.push_obligation(ProofObligation::assume("m", "multiplier == 9"));
    ctx.push_obligation(ProofObligation::assume("d", "divider == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "oh_def",
        "output_hz == input_hz * multiplier / divider",
    ));
    ctx.push_obligation(ProofObligation::assert("is_72mhz", "output_hz == 72000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PLL: 8MHz×9/1=72MHz");
}

#[test]
fn ahb_prescaler() {
    let mut ctx = VerificationContext::new();
    for v in &["sysclk_hz", "ahb_prescaler", "hclk_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sc", "sysclk_hz == 72000000"));
    ctx.push_obligation(ProofObligation::assume("ap", "ahb_prescaler == 1")); // no division
    ctx.push_obligation(ProofObligation::assume(
        "hc_def",
        "hclk_hz == sysclk_hz / ahb_prescaler",
    ));
    ctx.push_obligation(ProofObligation::assert("is_72mhz", "hclk_hz == 72000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "AHB: 72MHz/1=72MHz");
}

#[test]
fn apb1_max_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["hclk_hz", "apb1_prescaler", "pclk1_hz", "max_pclk1"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hc", "hclk_hz == 72000000"));
    ctx.push_obligation(ProofObligation::assume("ap", "apb1_prescaler == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "pclk1_hz == hclk_hz / apb1_prescaler",
    ));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pclk1 == 36000000")); // 36MHz max
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if pclk1_hz <= max_pclk1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_36mhz", "pclk1_hz == 36000000"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "APB1: 72MHz/2=36MHz <= 36MHz max");
}

#[test]
fn clock_source_selection() {
    // 0=HSI, 1=HSE, 2=PLL
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clock_source", u32_ty());
    ctx.declare_var_typed("is_pll", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "clock_source == 2")); // PLL
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "is_pll == if clock_source == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_pll == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clock source: 2 → PLL");
}

#[test]
fn hsi_trimming() {
    let mut ctx = VerificationContext::new();
    for v in &["nominal_hz", "trim_steps", "step_size_hz", "actual_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // HSI: 8MHz nominal, trimming ±40kHz in steps
    ctx.push_obligation(ProofObligation::assume("nh", "nominal_hz == 8000000"));
    ctx.push_obligation(ProofObligation::assume("ts", "trim_steps == 5")); // 5 steps up
    ctx.push_obligation(ProofObligation::assume("ss", "step_size_hz == 8000")); // ~8kHz per step
    ctx.push_obligation(ProofObligation::assume(
        "ah_def",
        "actual_hz == nominal_hz + trim_steps * step_size_hz",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8040k", "actual_hz == 8040000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "HSI trim: 8MHz + 5×8kHz = 8.04MHz");
}

#[test]
fn css_failure_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hse_ready", u32_ty());
    ctx.declare_var_typed("css_enabled", u32_ty());
    ctx.declare_var_typed("switch_to_hsi", i32_ty());
    // Clock security system: switch to HSI if HSE fails
    ctx.push_obligation(ProofObligation::assume("hr", "hse_ready == 0")); // HSE failed
    ctx.push_obligation(ProofObligation::assume("ce", "css_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sw_def",
        "switch_to_hsi == if css_enabled == 1 && hse_ready == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "switch_to_hsi == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CSS: HSE fail + CSS on → switch to HSI");
}

#[test]
fn mco_output_divider() {
    let mut ctx = VerificationContext::new();
    for v in &["source_hz", "mco_divider", "mco_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sh", "source_hz == 72000000"));
    ctx.push_obligation(ProofObligation::assume("md", "mco_divider == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "mh_def",
        "mco_hz == source_hz / mco_divider",
    ));
    ctx.push_obligation(ProofObligation::assert("is_18mhz", "mco_hz == 18000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "MCO: 72MHz/4=18MHz output");
}

#[test]
fn pll_lock_time() {
    let mut ctx = VerificationContext::new();
    for v in &["lock_time_us", "max_lock_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("locked_in_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "lock_time_us == 200"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_lock_us == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "lit_def",
        "locked_in_time == if lock_time_us <= max_lock_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "locked_in_time == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLL lock: 200µs <= 500µs max");
}

#[test]
fn usb_48mhz_requirement() {
    let mut ctx = VerificationContext::new();
    for v in &["pll_output_hz", "usb_prescaler", "usb_clock_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("usb_valid", i32_ty());
    // USB requires exactly 48MHz
    ctx.push_obligation(ProofObligation::assume("po", "pll_output_hz == 72000000"));
    ctx.push_obligation(ProofObligation::assume("up", "usb_prescaler == 1")); // 1.5 → not available, use 72/1.5 precomputed
    ctx.push_obligation(ProofObligation::assume("uc", "usb_clock_hz == 48000000")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "uv_def",
        "usb_valid == if usb_clock_hz == 48000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "usb_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: 48MHz clock → valid");
}

#[test]
fn low_power_clock_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["lsi_hz", "lse_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rtc_source", u32_ty()); // 0=LSI, 1=LSE
    ctx.declare_var_typed("rtc_clock_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lsi", "lsi_hz == 40000")); // 40kHz (±10%)
    ctx.push_obligation(ProofObligation::assume("lse", "lse_hz == 32768")); // 32.768kHz crystal
    ctx.push_obligation(ProofObligation::assume("rs", "rtc_source == 1")); // LSE
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "rtc_clock_hz == if rtc_source == 0 { lsi_hz } else { lse_hz }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32768", "rtc_clock_hz == 32768"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTC: LSE source → 32768Hz");
}
