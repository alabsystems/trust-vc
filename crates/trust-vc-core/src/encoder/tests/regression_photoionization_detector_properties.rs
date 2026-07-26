// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn lamp_energy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ev10", u32_ty());
    ctx.declare_var_typed("valid_ev", i32_ty());
    // Lamp energy x10 eV: 4-way non-sequential (97=9.7, 106=10.6, 117=11.7, 126=12.6 eV)
    ctx.push_obligation(ProofObligation::assume("le_val", "ev10 == 106"));
    ctx.push_obligation(ProofObligation::assume(
        "le_valid_def",
        "valid_ev == if ev10 == 97 || ev10 == 106 || ev10 == 117 || ev10 == 126 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("le_check", "valid_ev == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lamp energy 10.6 eV (106 x10) is valid");
}

#[test]
fn detection_range() {
    let mut ctx = VerificationContext::new();
    for v in &["ppb", "ppb_min", "ppb_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Detection range in ppb: value 500, valid range 1 to 20000000 (1 ppb to 20000 ppm)
    ctx.push_obligation(ProofObligation::assume("dr_val", "ppb == 500"));
    ctx.push_obligation(ProofObligation::assume("dr_min", "ppb_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dr_max", "ppb_max == 20000000"));
    ctx.push_obligation(ProofObligation::assert(
        "dr_in_range",
        "ppb >= ppb_min && ppb <= ppb_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection range 500 ppb in range [1,20000000]");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["res", "res_min", "res_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Resolution in ppb: value 10, valid range 1 to 100
    ctx.push_obligation(ProofObligation::assume("rs_val", "res == 10"));
    ctx.push_obligation(ProofObligation::assume("rs_min", "res_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rs_max", "res_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "rs_in_range",
        "res >= res_min && res <= res_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 10 ppb in range [1,100]");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["t90", "t90_min", "t90_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time T90 x10 seconds: value 20 (2.0s), valid range 5 to 300
    ctx.push_obligation(ProofObligation::assume("rt_val", "t90 == 20"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "t90_min == 5"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "t90_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "t90 >= t90_min && t90 <= t90_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time T90 2.0s (20 x10) in range [5,300]");
}

#[test]
fn correction_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["cf", "cf_min", "cf_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Correction factor x100 relative to isobutylene: value 100 (1.00), valid range 10 to 10000
    ctx.push_obligation(ProofObligation::assume("cf_val", "cf == 100"));
    ctx.push_obligation(ProofObligation::assume("cf_min", "cf_min == 10"));
    ctx.push_obligation(ProofObligation::assume("cf_max", "cf_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "cf_in_range",
        "cf >= cf_min && cf <= cf_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "correction factor 1.00 (100 x100) in range [10,10000]",
    );
}

#[test]
fn humidity_range() {
    let mut ctx = VerificationContext::new();
    for v in &["rh10", "rh10_min", "rh10_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Humidity x10 %RH: value 500 (50.0%), valid range 0 to 999 (0-99.9%)
    ctx.push_obligation(ProofObligation::assume("hr_val", "rh10 == 500"));
    ctx.push_obligation(ProofObligation::assume("hr_min", "rh10_min == 0"));
    ctx.push_obligation(ProofObligation::assume("hr_max", "rh10_max == 999"));
    ctx.push_obligation(ProofObligation::assert(
        "hr_in_range",
        "rh10 >= rh10_min && rh10 <= rh10_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "humidity 50.0% RH (500 x10) in range [0,999]");
}

#[test]
fn operating_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature offset +500: value 520 (20C), valid range 480 to 550 (-20C to 50C)
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assume("ot_min", "temp_min == 480"));
    ctx.push_obligation(ProofObligation::assume("ot_max", "temp_max == 550"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "temp >= temp_min && temp <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 20C (520 offset+500) in range [480,550]",
    );
}

#[test]
fn lamp_lifetime() {
    let mut ctx = VerificationContext::new();
    for v in &["hrs", "hrs_min", "hrs_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Lamp lifetime in hours: value 6000, valid range 100 to 30000
    ctx.push_obligation(ProofObligation::assume("ll_val", "hrs == 6000"));
    ctx.push_obligation(ProofObligation::assume("ll_min", "hrs_min == 100"));
    ctx.push_obligation(ProofObligation::assume("ll_max", "hrs_max == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "ll_in_range",
        "hrs >= hrs_min && hrs <= hrs_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lamp lifetime 6000 hours in range [100,30000]");
}

#[test]
fn intrinsic_safety() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rating", u32_ty());
    ctx.declare_var_typed("valid_rating", i32_ty());
    // 1=no rating, 2=ATEX Ex ia, 3=UL Class I Div 1
    ctx.push_obligation(ProofObligation::assume("is_val", "rating == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "is_valid_def",
        "valid_rating == if rating == 1 || rating == 2 || rating == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_check", "valid_rating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "intrinsic safety rating 2 (ATEX Ex ia) is valid");
}

#[test]
fn data_logging() {
    let mut ctx = VerificationContext::new();
    for v in &["pts", "pts_min", "pts_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Data logging capacity in data points: value 50000, valid range 1 to 1000000
    ctx.push_obligation(ProofObligation::assume("dl_val", "pts == 50000"));
    ctx.push_obligation(ProofObligation::assume("dl_min", "pts_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dl_max", "pts_max == 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "dl_in_range",
        "pts >= pts_min && pts <= pts_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data logging 50000 points in range [1,1000000]");
}
