// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn capacity_mg() {
    let mut ctx = VerificationContext::new();
    for v in &["cap", "cap_min", "cap_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Maximum capacity in milligrams: value 5000000 (5 kg), valid range 1000 (1g) to 100000000 (100kg)
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 5000000"));
    ctx.push_obligation(ProofObligation::assume("cap_lo", "cap_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("cap_hi", "cap_max == 100000000"));
    ctx.push_obligation(ProofObligation::assert(
        "cap_in_range",
        "cap >= cap_min && cap <= cap_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity 5000000 mg (5 kg) in range [1000,100000000]",
    );
}

#[test]
fn readability_x1000() {
    let mut ctx = VerificationContext::new();
    for v in &["rdbl", "rdbl_min", "rdbl_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Readability as x1000 mg (e.g., 0.001 mg = 1), valid range 1 to 10000
    ctx.push_obligation(ProofObligation::assume("rd_val", "rdbl == 10"));
    ctx.push_obligation(ProofObligation::assume("rd_lo", "rdbl_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rd_hi", "rdbl_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "rd_in_range",
        "rdbl >= rdbl_min && rdbl <= rdbl_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "readability 10 (0.01 mg) in range [1,10000]");
}

#[test]
fn accuracy_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_cls", u32_ty());
    ctx.declare_var_typed("valid_cls", i32_ty());
    // Accuracy class: 1=class I (special), 2=class II (high), 3=class III (medium), 4=class IIII (ordinary)
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_cls == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "valid_cls == if acc_cls == 1 || acc_cls == 2 || acc_cls == 3 || acc_cls == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ac_chk", "valid_cls == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy class 2 (class II high) is valid class");
}

#[test]
fn weighing_technology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tech", u32_ty());
    ctx.declare_var_typed("valid_tech", i32_ty());
    // Weighing technology: 1=electromagnetic force compensation, 2=strain gauge, 3=tuning fork
    ctx.push_obligation(ProofObligation::assume("wt_val", "tech == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "wt_def",
        "valid_tech == if tech == 1 || tech == 2 || tech == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wt_chk", "valid_tech == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "weighing technology 1 (electromagnetic force compensation) is valid",
    );
}

#[test]
fn pan_size_mm() {
    let mut ctx = VerificationContext::new();
    for v in &["pan", "pan_min", "pan_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Weighing pan diameter in mm: value 120, valid range 50 to 500
    ctx.push_obligation(ProofObligation::assume("ps_val", "pan == 120"));
    ctx.push_obligation(ProofObligation::assume("ps_lo", "pan_min == 50"));
    ctx.push_obligation(ProofObligation::assume("ps_hi", "pan_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "ps_in_range",
        "pan >= pan_min && pan <= pan_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pan size 120 mm in range [50,500]");
}

#[test]
fn stabilization_time_x10() {
    let mut ctx = VerificationContext::new();
    for v in &["stab", "stab_min", "stab_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Stabilization time as x10 seconds (e.g., 1.5s = 15), valid range 5 to 100
    ctx.push_obligation(ProofObligation::assume("st_val", "stab == 15"));
    ctx.push_obligation(ProofObligation::assume("st_lo", "stab_min == 5"));
    ctx.push_obligation(ProofObligation::assume("st_hi", "stab_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "st_in_range",
        "stab >= stab_min && stab <= stab_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stabilization time 15 (1.5s) in range [5,100]");
}

#[test]
fn communication_interface() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // Communication interface: 1=RS-232, 2=USB, 3=Ethernet, 4=Bluetooth
    ctx.push_obligation(ProofObligation::assume("ci_val", "comm == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ci_def",
        "valid_comm == if comm == 1 || comm == 2 || comm == 3 || comm == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ci_chk", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication 2 (USB) is valid interface");
}

#[test]
fn repeatability_x1000() {
    let mut ctx = VerificationContext::new();
    for v in &["rpt", "rpt_min", "rpt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Repeatability as x1000 mg (e.g., 0.002 mg = 2), valid range 1 to 1000
    ctx.push_obligation(ProofObligation::assume("rp_val", "rpt == 2"));
    ctx.push_obligation(ProofObligation::assume("rp_lo", "rpt_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rp_hi", "rpt_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "rp_in_range",
        "rpt >= rpt_min && rpt <= rpt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repeatability 2 (0.002 mg) in range [1,1000]");
}

#[test]
fn operating_temperature_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature with +500 offset (e.g., 20C = 520), valid range 450 (-50+500) to 580 (80+500)
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assume("ot_lo", "temp_min == 450"));
    ctx.push_obligation(ProofObligation::assume("ot_hi", "temp_max == 580"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "temp >= temp_min && temp <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 520 (20C offset+500) in range [450,580]",
    );
}

#[test]
fn internal_calibration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_ical", i32_ty());
    ctx.declare_var_typed("valid_flag", i32_ty());
    // Internal calibration: boolean flag encoded as i32 (0=no, 1=yes)
    ctx.push_obligation(ProofObligation::assume("ic_val", "has_ical == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "valid_flag == if has_ical == 0 || has_ical == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ic_chk", "valid_flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "internal calibration flag 1 (yes) is valid boolean",
    );
}
