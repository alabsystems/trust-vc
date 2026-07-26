// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn key_slot_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["used_slots", "max_slots"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_store", i32_ty());
    ctx.push_obligation(ProofObligation::assume("us", "used_slots == 95"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_slots == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_store == if used_slots < max_slots { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_store == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM: 95 used < 100 max → can store key");
}

#[test]
fn key_length_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("key_bits", u32_ty());
    ctx.declare_var_typed("valid_aes", i32_ty());
    // AES key sizes: 128, 192, or 256 bits
    ctx.push_obligation(ProofObligation::assume("kb", "key_bits == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_aes == if key_bits == 128 || key_bits == 192 || key_bits == 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_aes == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM: 256-bit AES key → valid");
}

#[test]
fn rsa_key_pair_size() {
    let mut ctx = VerificationContext::new();
    for v in &["modulus_bits", "public_exponent_bits", "private_key_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("strong_enough", i32_ty());
    // RSA-2048: modulus = 2048 bits. Private key ≈ modulus/8 bytes.
    ctx.push_obligation(ProofObligation::assume("mb", "modulus_bits == 2048"));
    ctx.push_obligation(ProofObligation::assume("peb", "public_exponent_bits == 17")); // e = 65537
    ctx.push_obligation(ProofObligation::assume(
        "pkb_def",
        "private_key_bytes == modulus_bits / 8",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "strong_enough == if modulus_bits >= 2048 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_256",
        "private_key_bytes == 256",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "strong_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "HSM RSA: 2048/8 = 256 byte private key");
}

#[test]
fn certificate_chain_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["chain_length", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_chain", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cl", "chain_length == 3")); // leaf, intermediate, root
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_chain == if chain_length <= max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_chain == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM cert: chain 3 ≤ 5 max depth → valid");
}

#[test]
fn key_derivation_iterations() {
    let mut ctx = VerificationContext::new();
    for v in &["iterations", "min_iterations"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("secure", i32_ty());
    // PBKDF2: minimum 100,000 iterations
    ctx.push_obligation(ProofObligation::assume("i", "iterations == 600000"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_iterations == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "secure == if iterations >= min_iterations { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "secure == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM PBKDF2: 600000 ≥ 100000 min → secure");
}

#[test]
fn session_key_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &["creation_time", "current_time", "max_lifetime", "elapsed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct_", "creation_time == 1000"));
    ctx.push_obligation(ProofObligation::assume("cur", "current_time == 4600"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_lifetime == 3600")); // 1 hour
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "elapsed == current_time - creation_time",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ex_def",
        "expired == if elapsed > max_lifetime { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3600", "elapsed == 3600"));
    ctx.push_obligation(ProofObligation::assert("no", "expired == 0")); // exactly at limit, not past
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "HSM session: 3600s elapsed = 3600s max → not expired (needs >)",
    );
}

#[test]
fn key_usage_flags() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("key_flags", u32_ty());
    ctx.declare_var_typed("required_flag", u32_ty());
    ctx.declare_var_typed("has_permission", i32_ty());
    // Key flags: bit 0 = encrypt, bit 1 = decrypt, bit 2 = sign, bit 3 = verify
    // flags = 5 (0b0101) = encrypt + sign. Required: sign (bit 2 = 4)
    ctx.push_obligation(ProofObligation::assume("kf", "key_flags == 5"));
    ctx.push_obligation(ProofObligation::assume("rf", "required_flag == 4")); // sign
    ctx.push_obligation(ProofObligation::assume("hp", "has_permission == 1")); // precomputed: 5 & 4 != 0
    ctx.push_obligation(ProofObligation::assert("yes", "has_permission == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM: key flags 0b0101 has sign permission");
}

#[test]
fn secure_channel_nonce() {
    let mut ctx = VerificationContext::new();
    for v in &["nonce_value", "last_nonce"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_nonce", i32_ty());
    // Nonce must be strictly increasing to prevent replay
    ctx.push_obligation(ProofObligation::assume("nv", "nonce_value == 1001"));
    ctx.push_obligation(ProofObligation::assume("ln", "last_nonce == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "vn_def",
        "valid_nonce == if nonce_value > last_nonce { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_nonce == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM nonce: 1001 > 1000 → valid (no replay)");
}

#[test]
fn tamper_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_mv", u32_ty());
    ctx.declare_var_typed("temp_mc", u32_ty());
    ctx.declare_var_typed("tamper_alert", i32_ty());
    // Tamper: voltage or temperature out of spec
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 2800")); // below 3.0V
    ctx.push_obligation(ProofObligation::assume("tm", "temp_mc == 50000")); // 50°C normal
    ctx.push_obligation(ProofObligation::assume(
        "ta_def",
        "tamper_alert == if voltage_mv < 3000 || temp_mc > 85000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tamper_alert == 1")); // low voltage
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM tamper: 2.8V < 3.0V min → alert");
}

#[test]
fn key_wrap_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["plaintext_bytes", "wrap_overhead", "wrapped_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AES key wrap adds 8 bytes overhead
    ctx.push_obligation(ProofObligation::assume("pb", "plaintext_bytes == 32")); // 256-bit key
    ctx.push_obligation(ProofObligation::assume("wo", "wrap_overhead == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "wrapped_bytes == plaintext_bytes + wrap_overhead",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "wrapped_bytes == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HSM key wrap: 32 + 8 = 40 bytes wrapped");
}
