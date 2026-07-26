// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn resistance_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ohms", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // Pt100=100, Pt500=500, Pt1000=1000, Pt2000=2000 ohms per IEC 60751
    ctx.push_obligation(ProofObligation::assume("rc_val", "ohms == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_valid_def",
        "valid_class == if ohms == 100 || ohms == 500 || ohms == 1000 || ohms == 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rc_check", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resistance class 1000 (Pt1000) is valid");
}

#[test]
fn tolerance_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tol", u32_ty());
    ctx.declare_var_typed("valid_tol", i32_ty());
    // 1=Class AA, 2=Class A, 3=Class B, 4=Class C per IEC 60751
    ctx.push_obligation(ProofObligation::assume("tc_val", "tol == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_valid_def",
        "valid_tol == if tol == 1 || tol == 2 || tol == 3 || tol == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tc_check", "valid_tol == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tolerance class 2 (Class A) is valid");
}

#[test]
fn wire_config() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wires", u32_ty());
    ctx.declare_var_typed("valid_wire", i32_ty());
    // 1=2-wire, 2=3-wire, 3=4-wire, 4=smart
    ctx.push_obligation(ProofObligation::assume("wc_val", "wires == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "wc_valid_def",
        "valid_wire == if wires == 1 || wires == 2 || wires == 3 || wires == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wc_check", "valid_wire == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wire config 3 (4-wire) is valid");
}

#[test]
fn temp_range_low() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_low_off", "tl_min", "tl_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Low temp with +500 offset: -200C -> 300, valid range 100 to 500
    ctx.push_obligation(ProofObligation::assume("tl_val", "temp_low_off == 300"));
    ctx.push_obligation(ProofObligation::assume("tl_lo", "tl_min == 100"));
    ctx.push_obligation(ProofObligation::assume("tl_hi", "tl_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "tl_in_range",
        "temp_low_off >= tl_min && temp_low_off <= tl_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temp range low 300 (-200C offset) in range [100,500]",
    );
}

#[test]
fn temp_range_high() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_hi_off", "th_min", "th_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // High temp with +500 offset: up to 850C -> 1350, valid range 500 to 1400
    ctx.push_obligation(ProofObligation::assume("th_val", "temp_hi_off == 1350"));
    ctx.push_obligation(ProofObligation::assume("th_lo", "th_min == 500"));
    ctx.push_obligation(ProofObligation::assume("th_hi", "th_max == 1400"));
    ctx.push_obligation(ProofObligation::assert(
        "th_in_range",
        "temp_hi_off >= th_min && temp_hi_off <= th_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temp range high 1350 (850C offset) in range [500,1400]",
    );
}

#[test]
fn alpha_coefficient() {
    let mut ctx = VerificationContext::new();
    for v in &["alpha_x1000", "al_min", "al_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Alpha coefficient x1000: IEC 60751 specifies 0.003851/K -> 3851 (x1e6), use x1000: 3.851 -> 3851
    ctx.push_obligation(ProofObligation::assume("al_val", "alpha_x1000 == 3851"));
    ctx.push_obligation(ProofObligation::assume("al_lo", "al_min == 3800"));
    ctx.push_obligation(ProofObligation::assume("al_hi", "al_max == 3950"));
    ctx.push_obligation(ProofObligation::assert(
        "al_in_range",
        "alpha_x1000 >= al_min && alpha_x1000 <= al_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "alpha coefficient 3851 (0.003851/K x1e6) in range [3800,3950]",
    );
}

#[test]
fn self_heating() {
    let mut ctx = VerificationContext::new();
    for v in &["heat_x100", "sh_min", "sh_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Self-heating in x100 mW: 0.50 mW -> 50, valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("sh_val", "heat_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("sh_lo", "sh_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sh_hi", "sh_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "sh_in_range",
        "heat_x100 >= sh_min && heat_x100 <= sh_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-heating 50 (0.50 mW) in range [1,500]");
}

#[test]
fn sheath_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sheath", u32_ty());
    ctx.declare_var_typed("valid_sheath", i32_ty());
    // 1=stainless steel 316, 2=Inconel 600, 3=ceramic, 4=quartz
    ctx.push_obligation(ProofObligation::assume("sm_val", "sheath == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sm_valid_def",
        "valid_sheath == if sheath == 1 || sheath == 2 || sheath == 3 || sheath == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sm_check", "valid_sheath == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sheath material 1 (stainless steel 316) is valid");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["t63_x10", "rt_min", "rt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time T63 in x10 seconds: 0.5s -> 5, valid range 1 to 600
    ctx.push_obligation(ProofObligation::assume("rt_val", "t63_x10 == 5"));
    ctx.push_obligation(ProofObligation::assume("rt_lo", "rt_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rt_hi", "rt_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "t63_x10 >= rt_min && t63_x10 <= rt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 5 (0.5s T63) in range [1,600]");
}

#[test]
fn insulation_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["ins_mohm", "ir_min", "ir_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Insulation resistance in megaohms at test voltage, valid range 10 to 10000
    ctx.push_obligation(ProofObligation::assume("ir_val", "ins_mohm == 100"));
    ctx.push_obligation(ProofObligation::assume("ir_lo", "ir_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ir_hi", "ir_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "ir_in_range",
        "ins_mohm >= ir_min && ins_mohm <= ir_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "insulation resistance 100 MOhm in range [10,10000]",
    );
}
