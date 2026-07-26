// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ascii_is_single_byte() {
    // ASCII (0-127) encoded as single byte
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("codepoint", u32_ty());
    ctx.declare_var_typed("bytes_needed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 65")); // 'A'
    ctx.push_obligation(ProofObligation::assume(
        "bn_def",
        "bytes_needed == if codepoint < 128 { 1 } else { if codepoint < 2048 { 2 } else { if codepoint < 65536 { 3 } else { 4 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "bytes_needed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "'A' (65) needs 1 byte");
}

#[test]
fn two_byte_range() {
    // U+0080 to U+07FF: 2 bytes
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("codepoint", u32_ty());
    ctx.declare_var_typed("bytes_needed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 233")); // 'é'
    ctx.push_obligation(ProofObligation::assume(
        "bn_def",
        "bytes_needed == if codepoint < 128 { 1 } else { if codepoint < 2048 { 2 } else { if codepoint < 65536 { 3 } else { 4 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "bytes_needed == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "'é' (233) needs 2 bytes");
}

#[test]
fn three_byte_range() {
    // U+0800 to U+FFFF: 3 bytes
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("codepoint", u32_ty());
    ctx.declare_var_typed("bytes_needed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 8364")); // '€' U+20AC
    ctx.push_obligation(ProofObligation::assume(
        "bn_def",
        "bytes_needed == if codepoint < 128 { 1 } else { if codepoint < 2048 { 2 } else { if codepoint < 65536 { 3 } else { 4 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "bytes_needed == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "'€' (8364) needs 3 bytes");
}

#[test]
fn four_byte_range() {
    // U+10000 to U+10FFFF: 4 bytes
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("codepoint", u32_ty());
    ctx.declare_var_typed("bytes_needed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 128512")); // U+1F600
    ctx.push_obligation(ProofObligation::assume(
        "bn_def",
        "bytes_needed == if codepoint < 128 { 1 } else { if codepoint < 2048 { 2 } else { if codepoint < 65536 { 3 } else { 4 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "bytes_needed == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "U+1F600 (128512) needs 4 bytes");
}

#[test]
fn continuation_byte_marker() {
    // Continuation bytes start with 10xxxxxx (0x80-0xBF)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("byte_val", u32_ty());
    ctx.declare_var_typed("is_continuation", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bv", "byte_val == 160")); // 0xA0 = 10100000
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_continuation == if byte_val >= 128 && byte_val < 192 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_cont", "is_continuation == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0xA0 is continuation byte");
}

#[test]
fn lead_byte_two_byte_marker() {
    // 2-byte lead: 110xxxxx (0xC0-0xDF)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("byte_val", u32_ty());
    ctx.declare_var_typed("is_2byte_lead", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bv", "byte_val == 195")); // 0xC3
    ctx.push_obligation(ProofObligation::assume(
        "il_def",
        "is_2byte_lead == if byte_val >= 192 && byte_val < 224 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_lead", "is_2byte_lead == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0xC3 is 2-byte lead");
}

#[test]
fn max_codepoint() {
    // Maximum Unicode codepoint: U+10FFFF = 1114111
    let mut ctx = VerificationContext::new();
    for v in &["codepoint", "max_unicode"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 1114111"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_unicode == 1114111"));
    ctx.push_obligation(ProofObligation::assert(
        "at_max",
        "codepoint <= max_unicode",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "U+10FFFF is max codepoint");
}

#[test]
fn surrogate_range_excluded() {
    // UTF-8 excludes surrogate range: U+D800 to U+DFFF
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("codepoint", u32_ty());
    ctx.declare_var_typed("is_surrogate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "codepoint == 55296")); // U+D800
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_surrogate == if codepoint >= 55296 && codepoint <= 57343 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("surrogate", "is_surrogate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "U+D800 is in surrogate range");
}

#[test]
fn string_length_in_bytes() {
    // "Hello" = 5 ASCII chars = 5 bytes
    let mut ctx = VerificationContext::new();
    for v in &["char_count", "byte_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cc", "char_count == 5"));
    // All ASCII, so bytes = chars
    ctx.push_obligation(ProofObligation::assume(
        "bc_def",
        "byte_count == char_count",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "byte_count == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 ASCII chars = 5 bytes");
}

#[test]
fn overlong_encoding_detection() {
    // Overlong: using more bytes than needed (e.g., 2 bytes for ASCII)
    // The byte value for an overlong NUL would be C0 80
    let mut ctx = VerificationContext::new();
    for v in &["lead_byte", "min_for_2byte"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_overlong", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lb", "lead_byte == 192")); // 0xC0
    ctx.push_obligation(ProofObligation::assume("min", "min_for_2byte == 194")); // 0xC2
    ctx.push_obligation(ProofObligation::assume(
        "ol_def",
        "is_overlong == if lead_byte < min_for_2byte { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("overlong", "is_overlong == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0xC0 < 0xC2 → overlong encoding");
}
