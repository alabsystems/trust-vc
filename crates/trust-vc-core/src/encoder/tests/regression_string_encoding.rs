// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ascii_a_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ch_val", "ch == 65"));
    ctx.push_obligation(ProofObligation::assert("is_uppercase_a", "ch == 65"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ASCII 'A' = 65");
}

#[test]
fn ascii_lowercase_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["upper", "lower"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("upper_val", "upper == 65"));
    ctx.push_obligation(ProofObligation::assume("lower_def", "lower == upper + 32"));
    ctx.push_obligation(ProofObligation::assert("is_97", "lower == 97"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "'A' + 32 = 'a' (97)");
}

#[test]
fn digit_to_value() {
    // '0' = 48, so digit value = char - 48
    let mut ctx = VerificationContext::new();
    for v in &["ch", "digit_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch_val", "ch == 53"));
    ctx.push_obligation(ProofObligation::assume("digit_def", "digit_val == ch - 48"));
    ctx.push_obligation(ProofObligation::assert("is_5", "digit_val == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "'5' (53) - '0' (48) = 5");
}

#[test]
fn value_to_digit() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "ch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val_val", "val == 7"));
    ctx.push_obligation(ProofObligation::assume("ch_def", "ch == val + 48"));
    ctx.push_obligation(ProofObligation::assert("is_55", "ch == 55"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 + '0' (48) = '7' (55)");
}

#[test]
fn utf8_single_byte_ascii() {
    // ASCII characters (0-127) encode as a single byte in UTF-8
    let mut ctx = VerificationContext::new();
    for v in &["codepoint", "bytes_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 65"));
    ctx.push_obligation(ProofObligation::assume(
        "bytes_def",
        "bytes_needed == if codepoint <= 127 { 1 } else { if codepoint <= 2047 { 2 } else { if codepoint <= 65535 { 3 } else { 4 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("one_byte", "bytes_needed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ASCII 'A' needs 1 UTF-8 byte");
}

#[test]
fn utf8_two_byte_range() {
    let mut ctx = VerificationContext::new();
    for v in &["codepoint", "bytes_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // é = U+00E9 = 233
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 233"));
    ctx.push_obligation(ProofObligation::assume(
        "bytes_def",
        "bytes_needed == if codepoint <= 127 { 1 } else { if codepoint <= 2047 { 2 } else { if codepoint <= 65535 { 3 } else { 4 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("two_bytes", "bytes_needed == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "U+00E9 (é) needs 2 UTF-8 bytes");
}

#[test]
fn string_length_from_bytes() {
    // ASCII string length = byte length
    let mut ctx = VerificationContext::new();
    for v in &["byte_len", "char_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bl", "byte_len == 5"));
    // All ASCII: char_len == byte_len
    ctx.push_obligation(ProofObligation::assume("cl_def", "char_len == byte_len"));
    ctx.push_obligation(ProofObligation::assert("is_5", "char_len == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ASCII string: char_len == byte_len");
}

#[test]
fn hex_digit_a_to_value() {
    // Hex 'A' = 65, value = 10
    let mut ctx = VerificationContext::new();
    for v in &["ch", "val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch_val", "ch == 65"));
    // hex digit A-F: value = ch - 55
    ctx.push_obligation(ProofObligation::assume("val_def", "val == ch - 55"));
    ctx.push_obligation(ProofObligation::assert("is_10", "val == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "'A' (65) as hex = 10");
}

#[test]
fn two_hex_digits_to_byte() {
    // "3F" → 63: hi_nibble * 16 + lo_nibble
    let mut ctx = VerificationContext::new();
    for v in &["hi_char", "lo_char", "hi_val", "lo_val", "byte_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hi_ch", "hi_char == 51"));
    ctx.push_obligation(ProofObligation::assume("lo_ch", "lo_char == 70"));
    // '3' = 51, digit value = 51 - 48 = 3
    ctx.push_obligation(ProofObligation::assume("hi_def", "hi_val == hi_char - 48"));
    // 'F' = 70, hex value = 70 - 55 = 15
    ctx.push_obligation(ProofObligation::assume("lo_def", "lo_val == lo_char - 55"));
    ctx.push_obligation(ProofObligation::assume(
        "byte_def",
        "byte_val == hi_val * 16 + lo_val",
    ));
    ctx.push_obligation(ProofObligation::assert("is_63", "byte_val == 63"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "hex '3F' = 3*16 + 15 = 63");
}

#[test]
fn base64_group_size() {
    // Base64: 3 bytes → 4 characters
    let mut ctx = VerificationContext::new();
    for v in &["input_bytes", "output_chars"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("input", "input_bytes == 9"));
    // groups of 3 → groups of 4
    ctx.push_obligation(ProofObligation::assume(
        "output_def",
        "output_chars == (input_bytes / 3) * 4",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "output_chars == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "9 bytes → 12 base64 chars");
}
