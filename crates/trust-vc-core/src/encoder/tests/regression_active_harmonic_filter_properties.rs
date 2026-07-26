// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rated_current() {
    let mut ctx = VerificationContext::new();
    for v in &["rc_val", "rc_min", "rc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Rated current in A: value 200, valid range 25 to 600
    ctx.push_obligation(ProofObligation::assume("rc_val", "rc_val == 200"));
    ctx.push_obligation(ProofObligation::assume("rc_min", "rc_min == 25"));
    ctx.push_obligation(ProofObligation::assume("rc_max", "rc_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "rc_in_range",
        "rc_val >= rc_min && rc_val <= rc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rated current 200 A in range [25,600]");
}

#[test]
fn harmonic_order() {
    let mut ctx = VerificationContext::new();
    for v in &["ho_val", "ho_min", "ho_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Max compensated harmonic order: value 25, valid range 2 to 50
    ctx.push_obligation(ProofObligation::assume("ho_val", "ho_val == 25"));
    ctx.push_obligation(ProofObligation::assume("ho_min", "ho_min == 2"));
    ctx.push_obligation(ProofObligation::assume("ho_max", "ho_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "ho_in_range",
        "ho_val >= ho_min && ho_val <= ho_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "harmonic order 25 in range [2,50]");
}

#[test]
fn correction_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["cs_val", "cs_min", "cs_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Correction speed in us response time: value 500, valid range 100 to 50000
    ctx.push_obligation(ProofObligation::assume("cs_val", "cs_val == 500"));
    ctx.push_obligation(ProofObligation::assume("cs_min", "cs_min == 100"));
    ctx.push_obligation(ProofObligation::assume("cs_max", "cs_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "cs_in_range",
        "cs_val >= cs_min && cs_val <= cs_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "correction speed 500 us in range [100,50000]");
}

#[test]
fn voltage_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vc_type", u32_ty());
    ctx.declare_var_typed("valid_vc", i32_ty());
    // Voltage class: 208 V, 480 V, 690 V
    ctx.push_obligation(ProofObligation::assume("vc_val", "vc_type == 480"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_vc == if vc_type == 208 || vc_type == 480 || vc_type == 690 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vc_chk", "valid_vc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage class 480 V is valid AHF voltage class");
}

#[test]
fn topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tp_type", u32_ty());
    ctx.declare_var_typed("valid_tp", i32_ty());
    // Topology: 1=shunt, 2=series, 3=hybrid
    ctx.push_obligation(ProofObligation::assume("tp_val", "tp_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "valid_tp == if tp_type == 1 || tp_type == 2 || tp_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tp_chk", "valid_tp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "topology 1 (shunt) is valid AHF topology");
}

#[test]
fn thd_reduction() {
    let mut ctx = VerificationContext::new();
    for v in &["td_val", "td_min", "td_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // THD reduction target x10 %: value 50 (5.0%), valid range 10 to 200
    ctx.push_obligation(ProofObligation::assume("td_val", "td_val == 50"));
    ctx.push_obligation(ProofObligation::assume("td_min", "td_min == 10"));
    ctx.push_obligation(ProofObligation::assume("td_max", "td_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "td_in_range",
        "td_val >= td_min && td_val <= td_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "THD reduction 50 (5.0%) in range [10,200]");
}

#[test]
fn phase_config() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pc_type", u32_ty());
    ctx.declare_var_typed("valid_pc", i32_ty());
    // Phase config: 1=single-phase, 2=three-phase 3-wire, 3=three-phase 4-wire
    ctx.push_obligation(ProofObligation::assume("pc_val", "pc_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "valid_pc == if pc_type == 1 || pc_type == 2 || pc_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pc_chk", "valid_pc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phase config 3 (three-phase 4-wire) is valid AHF phase config",
    );
}

#[test]
fn ct_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["cr_val", "cr_min", "cr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // CT ratio primary amps: value 400, valid range 50 to 5000
    ctx.push_obligation(ProofObligation::assume("cr_val", "cr_val == 400"));
    ctx.push_obligation(ProofObligation::assume("cr_min", "cr_min == 50"));
    ctx.push_obligation(ProofObligation::assume("cr_max", "cr_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "cr_in_range",
        "cr_val >= cr_min && cr_val <= cr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT ratio 400 primary amps in range [50,5000]");
}

#[test]
fn communication() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cm_type", u32_ty());
    ctx.declare_var_typed("valid_cm", i32_ty());
    // Communication: 1=Modbus RTU, 2=Modbus TCP, 3=PROFINET, 4=Ethernet/IP
    ctx.push_obligation(ProofObligation::assume("cm_val", "cm_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "valid_cm == if cm_type == 1 || cm_type == 2 || cm_type == 3 || cm_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "valid_cm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "communication 2 (Modbus TCP) is valid AHF communication protocol",
    );
}

#[test]
fn power_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["pf_val", "pf_min", "pf_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Power factor x100: value 95 (0.95), valid range 80 to 100
    ctx.push_obligation(ProofObligation::assume("pf_val", "pf_val == 95"));
    ctx.push_obligation(ProofObligation::assume("pf_min", "pf_min == 80"));
    ctx.push_obligation(ProofObligation::assume("pf_max", "pf_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "pf_in_range",
        "pf_val >= pf_min && pf_val <= pf_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power factor 95 (0.95) in range [80,100]");
}
