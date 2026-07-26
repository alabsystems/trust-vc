// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn lease_duration_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["lease_time", "max_lease", "min_lease"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "lease_time == 3600")); // 1 hour
    ctx.push_obligation(ProofObligation::assume("ml", "max_lease == 86400")); // 24 hours
    ctx.push_obligation(ProofObligation::assume("mnl", "min_lease == 300")); // 5 minutes
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if lease_time >= min_lease && lease_time <= max_lease { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DHCP: 300 <= 3600 <= 86400");
}

#[test]
fn address_pool_depletion() {
    let mut ctx = VerificationContext::new();
    for v in &["pool_size", "leased", "available"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "pool_size == 254")); // /24 minus network + broadcast
    ctx.push_obligation(ProofObligation::assume("l", "leased == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "available == pool_size - leased",
    ));
    ctx.push_obligation(ProofObligation::assert("is_54", "available == 54"));
    ctx.push_obligation(ProofObligation::assert("has_addresses", "available > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DHCP pool: 254 - 200 = 54 available");
}

#[test]
fn renewal_at_half_lease() {
    let mut ctx = VerificationContext::new();
    for v in &["lease_time", "t1_timer"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lt", "lease_time == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "t1_def",
        "t1_timer == lease_time / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1800", "t1_timer == 1800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DHCP T1: 3600/2 = 1800 (renew at half)");
}

#[test]
fn rebind_at_seven_eighths() {
    let mut ctx = VerificationContext::new();
    for v in &["lease_time", "t2_timer"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // T2 = lease * 7/8 = lease * 875 / 1000 (integer approx)
    ctx.push_obligation(ProofObligation::assume("lt", "lease_time == 8000"));
    ctx.push_obligation(ProofObligation::assume(
        "t2_def",
        "t2_timer == lease_time * 875 / 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7000", "t2_timer == 7000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DHCP T2: 8000*875/1000 = 7000 (rebind at 7/8)");
}

#[test]
fn subnet_mask_host_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["prefix_length", "host_bits", "max_hosts"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pl", "prefix_length == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "hb_def",
        "host_bits == 32 - prefix_length",
    ));
    // 2^8 - 2 = 254 hosts (minus network and broadcast)
    ctx.push_obligation(ProofObligation::assume("mh", "max_hosts == 254")); // hardcoded for /24
    ctx.push_obligation(ProofObligation::assert("hb_8", "host_bits == 8"));
    ctx.push_obligation(ProofObligation::assert("mh_254", "max_hosts == 254"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "/24: 8 host bits, 254 max hosts");
}

#[test]
fn lease_expiry_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["lease_start", "lease_duration", "current_time", "lease_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ls", "lease_start == 1000"));
    ctx.push_obligation(ProofObligation::assume("ld", "lease_duration == 3600"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "le_def",
        "lease_end == lease_start + lease_duration",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "expired == if current_time >= lease_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("le_4600", "lease_end == 4600"));
    ctx.push_obligation(ProofObligation::assert("yes", "expired == 1")); // 5000 >= 4600
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DHCP: 1000+3600=4600, 5000>=4600 → expired");
}

#[test]
fn offer_reserves_address() {
    let mut ctx = VerificationContext::new();
    for v in &["available_before", "available_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ab", "available_before == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "available_after == available_before - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_99", "available_after == 99"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "available_after < available_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DHCP offer: 100 → 99 available");
}

#[test]
fn decline_returns_address() {
    let mut ctx = VerificationContext::new();
    for v in &["available_before", "available_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ab", "available_before == 99"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "available_after == available_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "available_after == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "increased",
        "available_after > available_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DHCP decline: 99 → 100 available");
}

#[test]
fn relay_agent_hop_count() {
    let mut ctx = VerificationContext::new();
    for v in &["hops", "max_hops"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_forward", i32_ty());
    ctx.push_obligation(ProofObligation::assume("h", "hops == 3"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_hops == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "should_forward == if hops < max_hops { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "should_forward == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "relay: hops=3 < max=16 → forward");
}

#[test]
fn option_field_total_length() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "option_count",
        "avg_option_size",
        "total_options_size",
        "max_options",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oc", "option_count == 5"));
    ctx.push_obligation(ProofObligation::assume("aos", "avg_option_size == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "tos_def",
        "total_options_size == option_count * avg_option_size",
    ));
    ctx.push_obligation(ProofObligation::assume("mo", "max_options == 312")); // DHCP option field max
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if total_options_size <= max_options { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "total_options_size == 50"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DHCP options: 5×10=50 <= 312 max");
}
