// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn safety_integrity_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sil", u32_ty());
    ctx.declare_var_typed("valid_sil", i32_ty());
    // SIL 1-4 per IEC 61508; this system is SIL 3
    ctx.push_obligation(ProofObligation::assume("sil_val", "sil == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_def",
        "valid_sil == if sil >= 1 && sil <= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sil_valid", "valid_sil == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: SIL 3 is within valid range 1-4");
}

#[test]
fn proof_test_interval() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interval_months", u32_ty());
    ctx.declare_var_typed("valid_interval", i32_ty());
    // Proof test interval: 12 months, must be in 1-120
    ctx.push_obligation(ProofObligation::assume("iv", "interval_months == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_interval == if interval_months >= 1 && interval_months <= 120 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "interval_ok",
        "valid_interval == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SIS: 12-month proof test interval within 1-120 range",
    );
}

#[test]
fn safe_failure_fraction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sff_x10", u32_ty());
    ctx.declare_var_typed("min_sff_x10", u32_ty());
    ctx.declare_var_typed("sff_ok", i32_ty());
    // SFF 92.0% (stored as 920), minimum 60.0% (600) for SIL 3
    ctx.push_obligation(ProofObligation::assume("sff", "sff_x10 == 920"));
    ctx.push_obligation(ProofObligation::assume("min", "min_sff_x10 == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "sff_ok == if sff_x10 >= min_sff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sff_sufficient", "sff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: SFF 92.0% >= 60.0% minimum for SIL 3");
}

#[test]
fn hardware_fault_tolerance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hft", u32_ty());
    ctx.declare_var_typed("valid_hft", i32_ty());
    // HFT: 0, 1, or 2 per IEC 61508; this system uses HFT=1
    ctx.push_obligation(ProofObligation::assume("hft_val", "hft == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vh_def",
        "valid_hft == if hft == 0 || hft == 1 || hft == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("hft_valid", "valid_hft == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: HFT 1 is valid (0, 1, or 2)");
}

#[test]
fn diagnostic_coverage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dc_x10", u32_ty());
    ctx.declare_var_typed("min_dc_x10", u32_ty());
    ctx.declare_var_typed("dc_ok", i32_ty());
    // DC 90.0% (stored as 900), minimum 60.0% (600) per IEC 61508
    ctx.push_obligation(ProofObligation::assume("dc", "dc_x10 == 900"));
    ctx.push_obligation(ProofObligation::assume("min", "min_dc_x10 == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "dc_ok == if dc_x10 >= min_dc_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dc_sufficient", "dc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: DC 90.0% >= 60.0% minimum");
}

#[test]
fn architecture_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("arch", u32_ty());
    ctx.declare_var_typed("valid_arch", i32_ty());
    // Architecture: 1=1oo1, 2=1oo2, 3=2oo2, 4=2oo3, 5=1oo1D
    ctx.push_obligation(ProofObligation::assume("arch_val", "arch == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_arch == if arch == 1 || arch == 2 || arch == 3 || arch == 4 || arch == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("arch_valid", "valid_arch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: architecture 2oo3 (4) is valid voting type");
}

#[test]
fn demand_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Demand mode: 1=low demand, 2=high demand, 3=continuous
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mode_valid", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: low demand mode (1) is valid demand mode");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_ms", u32_ty());
    ctx.declare_var_typed("max_response_ms", u32_ty());
    ctx.declare_var_typed("response_ok", i32_ty());
    // Safety function response time: 500ms, max allowable 5000ms
    ctx.push_obligation(ProofObligation::assume("rt", "response_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_response_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "response_ok == if response_ms <= max_response_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "response_sufficient",
        "response_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: 500ms response <= 5000ms max allowable");
}

#[test]
fn common_cause_beta() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beta_x100", u32_ty());
    ctx.declare_var_typed("max_beta_x100", u32_ty());
    ctx.declare_var_typed("beta_ok", i32_ty());
    // Beta factor 5.00% (stored as 500), max 10.00% (1000)
    ctx.push_obligation(ProofObligation::assume("bv", "beta_x100 == 500"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_beta_x100 == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "beta_ok == if beta_x100 <= max_beta_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("beta_acceptable", "beta_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: beta factor 5.00% <= 10.00% maximum");
}

#[test]
fn mission_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mission_years", u32_ty());
    ctx.declare_var_typed("valid_mission", i32_ty());
    // Mission/useful life: 20 years, valid range 5-30
    ctx.push_obligation(ProofObligation::assume("mt", "mission_years == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mission == if mission_years >= 5 && mission_years <= 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mission_valid",
        "valid_mission == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIS: 20-year mission time within 5-30 year range");
}
