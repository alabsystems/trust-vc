// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn breakdown_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["bv_v", "min_bv_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bv_ok", i32_ty());
    // SiC MOSFET breakdown voltage
    ctx.push_obligation(ProofObligation::assume("bv", "bv_v == 1200"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bv_v == 650"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bv_ok == if bv_v >= min_bv_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bv_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 1200V breakdown ≥ 650V min → OK");
}

#[test]
fn on_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rds_on_mohm", "max_rds_on_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rds_ok", i32_ty());
    // RDS(on) — much lower than Si at high voltage
    ctx.push_obligation(ProofObligation::assume("rm", "rds_on_mohm == 25")); // 25mΩ
    ctx.push_obligation(ProofObligation::assume("mr", "max_rds_on_mohm == 80")); // 80mΩ
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rds_ok == if rds_on_mohm <= max_rds_on_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rds_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 25mΩ RDS(on) ≤ 80mΩ max → OK");
}

#[test]
fn junction_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["tj_c", "max_tj_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tj_ok", i32_ty());
    // SiC: higher max Tj than Si (up to 200°C)
    ctx.push_obligation(ProofObligation::assume("tc", "tj_c == 175"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tj_c == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tj_ok == if tj_c <= max_tj_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tj_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 175°C junction ≤ 200°C max → OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // SiC enables higher switching frequencies
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 100kHz switching in [10, 500] → OK");
}

#[test]
fn gate_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vgs_v", "min_vgs_v", "max_vgs_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vgs_ok", i32_ty());
    // Gate-source voltage drive range
    ctx.push_obligation(ProofObligation::assume("vv", "vgs_v == 18"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vgs_v == 15"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vgs_v == 22"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vgs_ok == if vgs_v >= min_vgs_v && vgs_v <= max_vgs_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vgs_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 18V VGS in [15, 22] → OK");
}

#[test]
fn reverse_recovery() {
    let mut ctx = VerificationContext::new();
    for v in &["trr_ns", "max_trr_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trr_ok", i32_ty());
    // Body diode recovery time (SiC: nearly zero)
    ctx.push_obligation(ProofObligation::assume("tn", "trr_ns == 15"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_trr_ns == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "trr_ok == if trr_ns <= max_trr_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 15ns body diode trr ≤ 50ns max → OK");
}

#[test]
fn thermal_conductivity() {
    let mut ctx = VerificationContext::new();
    for v in &["k_x10", "min_k_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("k_ok", i32_ty());
    // SiC thermal conductivity W/(m·K) (×10, SiC ≈ 4.9 vs Si ≈ 1.5)
    ctx.push_obligation(ProofObligation::assume("kx", "k_x10 == 49")); // 4.9 W/(m·K)
    ctx.push_obligation(ProofObligation::assume("mk", "min_k_x10 == 30")); // 3.0
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "k_ok == if k_x10 >= min_k_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "k_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 4.9 W/(m·K) thermal ≥ 3.0 min → OK");
}

#[test]
fn device_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dev_type", u32_ty());
    ctx.declare_var_typed("valid_dev", i32_ty());
    // SiC device types: 1=MOSFET, 2=Schottky diode, 3=JFET, 4=module (half-bridge)
    ctx.push_obligation(ProofObligation::assume("dt", "dev_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dev == if dev_type == 1 || dev_type == 2 || dev_type == 3 || dev_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dev == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: MOSFET is valid device type");
}

#[test]
fn gate_charge() {
    let mut ctx = VerificationContext::new();
    for v in &["qg_nc", "max_qg_nc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("qg_ok", i32_ty());
    // Total gate charge in nC (SiC: lower than Si)
    ctx.push_obligation(ProofObligation::assume("qn", "qg_nc == 60"));
    ctx.push_obligation(ProofObligation::assume("mq", "max_qg_nc == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "qo_def",
        "qg_ok == if qg_nc <= max_qg_nc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "qg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 60nC gate charge ≤ 200nC max → OK");
}

#[test]
fn drain_current() {
    let mut ctx = VerificationContext::new();
    for v in &["id_a", "max_id_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_ok", i32_ty());
    // Continuous drain current
    ctx.push_obligation(ProofObligation::assume("ia", "id_a == 40"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_id_a == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "id_ok == if id_a <= max_id_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SiC: 40A drain ≤ 100A max → OK");
}
