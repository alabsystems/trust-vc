// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pin_direction_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("direction_reg", u32_ty()); // bit=1 means output
    ctx.declare_var_typed("pin_number", u32_ty());
    ctx.declare_var_typed("is_output", i32_ty());
    // Pin 3: check bit 3 (value 8)
    ctx.push_obligation(ProofObligation::assume("dr", "direction_reg == 8")); // only pin 3 is output
    ctx.push_obligation(ProofObligation::assume("pn", "pin_number == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "is_output == if direction_reg & 8 == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "GPIO: dir_reg & 8 == 8 → pin 3 output");
}

#[test]
fn output_data_register_set() {
    let mut ctx = VerificationContext::new();
    for v in &["old_odr", "set_mask", "new_odr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Set bits: new = old | mask
    ctx.push_obligation(ProofObligation::assume("oo", "old_odr == 0"));
    ctx.push_obligation(ProofObligation::assume("sm", "set_mask == 5")); // pins 0 and 2
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "new_odr == old_odr | set_mask",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "new_odr == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "GPIO ODR: 0 | 5 = 5");
}

#[test]
fn input_data_register_read() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("idr", u32_ty());
    ctx.declare_var_typed("pin_mask", u32_ty());
    ctx.declare_var_typed("pin_value", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "idr == 255")); // all 8 low pins high
    ctx.push_obligation(ProofObligation::assume("pm", "pin_mask == 4")); // pin 2
    ctx.push_obligation(ProofObligation::assume(
        "pv_def",
        "pin_value == if idr & pin_mask == pin_mask { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("high", "pin_value == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "GPIO IDR: 255 & 4 == 4 → pin 2 high");
}

#[test]
fn alternate_function_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["af_number", "max_af"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Typical: 16 alternate functions (AF0-AF15)
    ctx.push_obligation(ProofObligation::assume("an", "af_number == 7")); // AF7 = USART
    ctx.push_obligation(ProofObligation::assume("ma", "max_af == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if af_number <= max_af { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPIO AF: 7 <= 15 → valid");
}

#[test]
fn pull_up_pull_down_config() {
    // 0=no pull, 1=pull-up, 2=pull-down
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pupd_config", u32_ty());
    ctx.declare_var_typed("has_pull", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "pupd_config == 1")); // pull-up
    ctx.push_obligation(ProofObligation::assume(
        "hp_def",
        "has_pull == if pupd_config > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_pull == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPIO: pull-up config (1) → has pull");
}

#[test]
fn output_speed_selection() {
    // 0=low, 1=medium, 2=high, 3=very high
    let mut ctx = VerificationContext::new();
    for v in &["speed_setting", "max_freq_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ss", "speed_setting == 3")); // very high
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_mhz == 100")); // 100MHz
    ctx.push_obligation(ProofObligation::assert("is_3", "speed_setting == 3"));
    ctx.push_obligation(ProofObligation::assert("fast", "max_freq_mhz > 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPIO speed: setting 3 → 100MHz");
}

#[test]
fn open_drain_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty()); // 0=push-pull, 1=open-drain
    ctx.declare_var_typed("output_value", u32_ty());
    ctx.declare_var_typed("pin_driven_low", i32_ty());
    // Open drain: can only drive low, high-Z when output=1
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 1")); // open-drain
    ctx.push_obligation(ProofObligation::assume("ov", "output_value == 0")); // driving low
    ctx.push_obligation(ProofObligation::assume(
        "pdl_def",
        "pin_driven_low == if output_type == 1 && output_value == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pin_driven_low == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPIO: open-drain + output=0 → driven low");
}

#[test]
fn port_wide_write() {
    let mut ctx = VerificationContext::new();
    for v in &["port_width_bits", "write_value", "max_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pw", "port_width_bits == 16"));
    ctx.push_obligation(ProofObligation::assume("wv", "write_value == 43690")); // 0xAAAA
    ctx.push_obligation(ProofObligation::assume("mv", "max_value == 65535")); // 2^16-1
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if write_value <= max_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPIO: 0xAAAA <= 0xFFFF → fits 16-bit port");
}

#[test]
fn external_interrupt_line() {
    let mut ctx = VerificationContext::new();
    for v in &["pin_number", "exti_line"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // EXTI line matches pin number (0-15)
    ctx.push_obligation(ProofObligation::assume("pn", "pin_number == 5"));
    ctx.push_obligation(ProofObligation::assume("el_def", "exti_line == pin_number"));
    ctx.push_obligation(ProofObligation::assert("is_5", "exti_line == 5"));
    ctx.push_obligation(ProofObligation::assert("valid", "exti_line <= 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPIO EXTI: pin 5 → line 5");
}

#[test]
fn lock_bit_sequence() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lock_key", u32_ty());
    ctx.declare_var_typed("expected_key", u32_ty());
    ctx.declare_var_typed("locked", i32_ty());
    // GPIO lock requires specific key sequence
    ctx.push_obligation(ProofObligation::assume("lk", "lock_key == 65536")); // bit 16 = LCKK
    ctx.push_obligation(ProofObligation::assume("ek", "expected_key == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "locked == if lock_key == expected_key { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "locked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPIO lock: key 65536 matches → locked");
}
