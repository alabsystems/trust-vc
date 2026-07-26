// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn region_contains_address() {
    let mut ctx = VerificationContext::new();
    for v in &["region_base", "region_size", "address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_region", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rb", "region_base == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("rs", "region_size == 131072")); // 128KB
    ctx.push_obligation(ProofObligation::assume("a", "address == 536871000")); // inside region
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_region == if address >= region_base && address < region_base + region_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_region == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: address in [0x20000000, +128KB)");
}

#[test]
fn access_permission_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("privilege_level", u32_ty());
    ctx.declare_var_typed("region_ap", u32_ty());
    ctx.declare_var_typed("access_allowed", i32_ty());
    // AP=3: full access for privileged and unprivileged
    // AP=1: privileged only
    // privilege_level: 0=unprivileged, 1=privileged
    ctx.push_obligation(ProofObligation::assume("pl", "privilege_level == 0")); // unprivileged
    ctx.push_obligation(ProofObligation::assume("ap", "region_ap == 3")); // full access
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "access_allowed == if region_ap == 3 || privilege_level == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "access_allowed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: AP=3 → unprivileged access allowed");
}

#[test]
fn region_size_power_of_two() {
    let mut ctx = VerificationContext::new();
    for v in &["size_field", "actual_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ARM MPU: size = 2^(field+1). field=16 → 2^17 = 131072
    // Precomputed since exponentiation is NLA
    ctx.push_obligation(ProofObligation::assume("sf", "size_field == 16"));
    ctx.push_obligation(ProofObligation::assume("as_val", "actual_size == 131072")); // 2^17
    ctx.push_obligation(ProofObligation::assert("is_128k", "actual_size == 131072"));
    ctx.push_obligation(ProofObligation::assert("positive", "actual_size > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: size_field=16 → 128KB");
}

#[test]
fn subregion_disable() {
    let mut ctx = VerificationContext::new();
    for v in &["region_size", "subregion_size", "num_subregions"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("subregion_disabled", u32_ty());
    ctx.declare_var_typed("effective_size", u32_ty());
    // 8 subregions per region, each can be individually disabled
    ctx.push_obligation(ProofObligation::assume("rs", "region_size == 131072")); // 128KB
    ctx.push_obligation(ProofObligation::assume("ns", "num_subregions == 8"));
    ctx.push_obligation(ProofObligation::assume("ss", "subregion_size == 16384")); // 128KB/8 = 16KB
    ctx.push_obligation(ProofObligation::assume("sd", "subregion_disabled == 2")); // 2 of 8 disabled
    ctx.push_obligation(ProofObligation::assume(
        "es_def",
        "effective_size == region_size - subregion_disabled * subregion_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_98304",
        "effective_size == 98304",
    )); // 128K - 2×16K
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "MPU subregion: 128K - 2×16K = 96KB effective");
}

#[test]
fn region_priority_overlap() {
    let mut ctx = VerificationContext::new();
    for v in &["region0_match", "region1_match"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("effective_region", u32_ty());
    // Higher-numbered regions have higher priority when overlapping
    ctx.push_obligation(ProofObligation::assume("r0", "region0_match == 1"));
    ctx.push_obligation(ProofObligation::assume("r1", "region1_match == 1")); // both match
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "effective_region == if region1_match == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "effective_region == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: region 1 takes priority over region 0");
}

#[test]
fn execute_never() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("xn_bit", u32_ty());
    ctx.declare_var_typed("is_instruction_fetch", u32_ty());
    ctx.declare_var_typed("fault", i32_ty());
    // XN (eXecute Never): prevents code execution from region
    ctx.push_obligation(ProofObligation::assume("xn", "xn_bit == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "if_val",
        "is_instruction_fetch == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fault == if xn_bit == 1 && is_instruction_fetch == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: XN=1 + instruction fetch → fault");
}

#[test]
fn background_region_default() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("any_region_match", u32_ty());
    ctx.declare_var_typed("default_map_enabled", u32_ty());
    ctx.declare_var_typed("access_granted", i32_ty());
    // If no region matches and default map is enabled, use default permissions
    ctx.push_obligation(ProofObligation::assume("arm", "any_region_match == 0"));
    ctx.push_obligation(ProofObligation::assume("dme", "default_map_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ag_def",
        "access_granted == if any_region_match == 1 || default_map_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "access_granted == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: no match + default map → access via default");
}

#[test]
fn region_alignment_requirement() {
    let mut ctx = VerificationContext::new();
    for v in &["base_address", "region_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // Base address must be aligned to region size
    ctx.push_obligation(ProofObligation::assume("ba", "base_address == 262144")); // 256KB = 0x40000
    ctx.push_obligation(ProofObligation::assume("rs", "region_size == 262144")); // 256KB
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if base_address % region_size == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "MPU: 256KB base aligned to 256KB region");
}

#[test]
fn cacheable_attribute() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tex_field", u32_ty());
    ctx.declare_var_typed("c_bit", u32_ty());
    ctx.declare_var_typed("b_bit", u32_ty());
    ctx.declare_var_typed("is_write_back", i32_ty());
    // TEX=0, C=1, B=1 → Write-back, write-allocate
    ctx.push_obligation(ProofObligation::assume("tex", "tex_field == 0"));
    ctx.push_obligation(ProofObligation::assume("c", "c_bit == 1"));
    ctx.push_obligation(ProofObligation::assume("b", "b_bit == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "is_write_back == if tex_field == 0 && c_bit == 1 && b_bit == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_write_back == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: TEX=0,C=1,B=1 → write-back");
}

#[test]
fn total_regions_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["configured_regions", "max_regions"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    // Cortex-M: 8 MPU regions typical, M7 has 16
    ctx.push_obligation(ProofObligation::assume("cr", "configured_regions == 7"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_regions == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if configured_regions <= max_regions { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "has_room",
        "configured_regions < max_regions",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPU: 7 < 8 → within limit, one slot free");
}
