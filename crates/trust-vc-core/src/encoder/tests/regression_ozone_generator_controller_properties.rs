// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ozone_output() {
    let mut ctx = VerificationContext::new();
    for v in &["oo_val", "oo_min", "oo_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Ozone output in g/h: value 250, valid range 1 to 5000
    ctx.push_obligation(ProofObligation::assume("oo_val", "oo_val == 250"));
    ctx.push_obligation(ProofObligation::assume("oo_min", "oo_min == 1"));
    ctx.push_obligation(ProofObligation::assume("oo_max", "oo_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "oo_in_range",
        "oo_val >= oo_min && oo_val <= oo_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ozone output 250 g/h in range [1,5000]");
}

#[test]
fn concentration() {
    let mut ctx = VerificationContext::new();
    for v in &["cn_val", "cn_min", "cn_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Ozone concentration in ppm: value 50, valid range 1 to 300
    ctx.push_obligation(ProofObligation::assume("cn_val", "cn_val == 50"));
    ctx.push_obligation(ProofObligation::assume("cn_min", "cn_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cn_max", "cn_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "cn_in_range",
        "cn_val >= cn_min && cn_val <= cn_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ozone concentration 50 ppm in range [1,300]");
}

#[test]
fn feed_gas() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fg_type", u32_ty());
    ctx.declare_var_typed("valid_fg", i32_ty());
    // Feed gas types: 1=dry air, 2=oxygen, 3=ambient air
    ctx.push_obligation(ProofObligation::assume("fg_val", "fg_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "fg_def",
        "valid_fg == if fg_type == 1 || fg_type == 2 || fg_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fg_chk", "valid_fg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed gas type 2 (oxygen) is valid ozone feed gas");
}

#[test]
fn generator_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gt_type", u32_ty());
    ctx.declare_var_typed("valid_gt", i32_ty());
    // Generator types: 1=corona discharge, 2=UV, 3=electrolytic
    ctx.push_obligation(ProofObligation::assume("gt_val", "gt_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "gt_def",
        "valid_gt == if gt_type == 1 || gt_type == 2 || gt_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gt_chk", "valid_gt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "generator type 1 (corona discharge) is valid ozone generator type",
    );
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["pw_val", "pw_min", "pw_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Power consumption in W: value 1500, valid range 10 to 50000
    ctx.push_obligation(ProofObligation::assume("pw_val", "pw_val == 1500"));
    ctx.push_obligation(ProofObligation::assume("pw_min", "pw_min == 10"));
    ctx.push_obligation(ProofObligation::assume("pw_max", "pw_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "pw_in_range",
        "pw_val >= pw_min && pw_val <= pw_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power consumption 1500 W in range [10,50000]");
}

#[test]
fn cooling_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cm_type", u32_ty());
    ctx.declare_var_typed("valid_cm", i32_ty());
    // Cooling methods: 1=air-cooled, 2=water-cooled, 3=oil-cooled
    ctx.push_obligation(ProofObligation::assume("cm_val", "cm_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "valid_cm == if cm_type == 1 || cm_type == 2 || cm_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "valid_cm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling method 2 (water-cooled) is valid ozone generator cooling",
    );
}

#[test]
fn flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["fr_val", "fr_min", "fr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gas flow rate in L/min: value 100, valid range 1 to 1000
    ctx.push_obligation(ProofObligation::assume("fr_val", "fr_val == 100"));
    ctx.push_obligation(ProofObligation::assume("fr_min", "fr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fr_max", "fr_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "fr_in_range",
        "fr_val >= fr_min && fr_val <= fr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 100 L/min in range [1,1000]");
}

#[test]
fn destruct_unit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("du_flag", i32_ty());
    ctx.declare_var_typed("valid_du", i32_ty());
    // Destruct unit: 1=integrated, 0=external
    ctx.push_obligation(ProofObligation::assume("du_val", "du_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "du_def",
        "valid_du == if du_flag == 0 || du_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("du_chk", "valid_du == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "destruct unit flag 1 (integrated) is valid ozone destruct setting",
    );
}

#[test]
fn contact_time() {
    let mut ctx = VerificationContext::new();
    for v in &["ct_val", "ct_min", "ct_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Contact time in seconds: value 300, valid range 1 to 3600
    ctx.push_obligation(ProofObligation::assume("ct_val", "ct_val == 300"));
    ctx.push_obligation(ProofObligation::assume("ct_min", "ct_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ct_max", "ct_max == 3600"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_in_range",
        "ct_val >= ct_min && ct_val <= ct_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "contact time 300 seconds in range [1,3600]");
}

#[test]
fn residual_monitor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rm_flag", i32_ty());
    ctx.declare_var_typed("valid_rm", i32_ty());
    // Residual monitor: 1=installed, 0=not installed
    ctx.push_obligation(ProofObligation::assume("rm_val", "rm_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rm_def",
        "valid_rm == if rm_flag == 0 || rm_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rm_chk", "valid_rm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "residual monitor flag 1 (installed) is valid ozone monitor setting",
    );
}
