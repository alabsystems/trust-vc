// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn drain_source_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vds_v", "max_vds_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vds_ok", i32_ty());
    // Maximum drain-source voltage
    ctx.push_obligation(ProofObligation::assume("vv", "vds_v == 60"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_vds_v == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vds_ok == if vds_v <= max_vds_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vds_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 60V VDS ≤ 100V max → OK");
}

#[test]
fn on_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rds_on_mohm", "max_rds_on_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rds_ok", i32_ty());
    // RDS(on) in milliohms
    ctx.push_obligation(ProofObligation::assume("rm", "rds_on_mohm == 5")); // 5mΩ
    ctx.push_obligation(ProofObligation::assume("mr", "max_rds_on_mohm == 20")); // 20mΩ
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rds_ok == if rds_on_mohm <= max_rds_on_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rds_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 5mΩ RDS(on) ≤ 20mΩ max → OK");
}

#[test]
fn gate_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["vgs_th_mv", "min_vgs_th_mv", "max_vgs_th_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vgs_ok", i32_ty());
    // Gate threshold voltage in millivolts
    ctx.push_obligation(ProofObligation::assume("vm", "vgs_th_mv == 2000")); // 2.0V
    ctx.push_obligation(ProofObligation::assume("mn", "min_vgs_th_mv == 1000")); // 1.0V
    ctx.push_obligation(ProofObligation::assume("mx", "max_vgs_th_mv == 4000")); // 4.0V
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vgs_ok == if vgs_th_mv >= min_vgs_th_mv && vgs_th_mv <= max_vgs_th_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vgs_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 2.0V VGS(th) in [1.0, 4.0] → OK");
}

#[test]
fn continuous_drain_current() {
    let mut ctx = VerificationContext::new();
    for v in &["id_a", "max_id_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_ok", i32_ty());
    // Continuous drain current at 25°C
    ctx.push_obligation(ProofObligation::assume("ia", "id_a == 30"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_id_a == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "id_ok == if id_a <= max_id_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 30A drain ≤ 100A max → OK");
}

#[test]
fn gate_charge() {
    let mut ctx = VerificationContext::new();
    for v in &["qg_nc", "max_qg_nc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("qg_ok", i32_ty());
    // Total gate charge in nanocoulombs
    ctx.push_obligation(ProofObligation::assume("qn", "qg_nc == 40"));
    ctx.push_obligation(ProofObligation::assume("mq", "max_qg_nc == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "qo_def",
        "qg_ok == if qg_nc <= max_qg_nc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "qg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 40nC gate charge ≤ 150nC max → OK");
}

#[test]
fn thermal_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rth_x10", "max_rth_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rth_ok", i32_ty());
    // Junction-to-case thermal resistance (°C/W ×10)
    ctx.push_obligation(ProofObligation::assume("rx", "rth_x10 == 8")); // 0.8 °C/W
    ctx.push_obligation(ProofObligation::assume("mr", "max_rth_x10 == 20")); // 2.0 °C/W
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rth_ok == if rth_x10 <= max_rth_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 0.8°C/W Rth ≤ 2.0 max → OK");
}

#[test]
fn package_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("package", u32_ty());
    ctx.declare_var_typed("valid_pkg", i32_ty());
    // Packages: 1=TO-220, 2=D2PAK, 3=DPAK, 4=SO-8, 5=QFN
    ctx.push_obligation(ProofObligation::assume("p", "package == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_pkg == if package == 1 || package == 2 || package == 3 || package == 4 || package == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_pkg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: TO-220 is valid package type");
}

#[test]
fn switching_time() {
    let mut ctx = VerificationContext::new();
    for v in &["turn_on_ns", "max_turn_on_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ton_ok", i32_ty());
    // Turn-on switching time
    ctx.push_obligation(ProofObligation::assume("tn", "turn_on_ns == 20"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_turn_on_ns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "ton_ok == if turn_on_ns <= max_turn_on_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ton_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 20ns turn-on ≤ 100ns max → OK");
}

#[test]
fn body_diode_recovery() {
    let mut ctx = VerificationContext::new();
    for v in &["trr_ns", "max_trr_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trr_ok", i32_ty());
    // Body diode reverse recovery time
    ctx.push_obligation(ProofObligation::assume("tn", "trr_ns == 30"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_trr_ns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "trr_ok == if trr_ns <= max_trr_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 30ns body diode trr ≤ 100ns max → OK");
}

#[test]
fn junction_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["tj_c", "max_tj_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tj_ok", i32_ty());
    // Maximum junction temperature
    ctx.push_obligation(ProofObligation::assume("tc", "tj_c == 125"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tj_c == 175"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tj_ok == if tj_c <= max_tj_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tj_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MOSFET: 125°C junction ≤ 175°C max → OK");
}
