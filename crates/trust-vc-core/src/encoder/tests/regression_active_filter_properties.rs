// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn thd_reduction() {
    let mut ctx = VerificationContext::new();
    for v in &["thd_pct_x10", "max_thd_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("thd_ok", i32_ty());
    // Total harmonic distortion after filtering (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("tx", "thd_pct_x10 == 30")); // 3.0%
    ctx.push_obligation(ProofObligation::assume("mt", "max_thd_x10 == 50")); // 5.0% (IEEE 519)
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "thd_ok == if thd_pct_x10 <= max_thd_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: 3.0% THD ≤ 5.0% limit → OK");
}

#[test]
fn compensation_order() {
    let mut ctx = VerificationContext::new();
    for v in &["max_harmonic", "min_harmonic"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("harm_ok", i32_ty());
    // Maximum harmonic order compensated
    ctx.push_obligation(ProofObligation::assume("mh", "max_harmonic == 25"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_harmonic == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "harm_ok == if max_harmonic >= min_harmonic { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "harm_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Active filter: compensates up to 25th harmonic ≥ 13 min → OK",
    );
}

#[test]
fn rated_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_a", "max_current_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cur_ok", i32_ty());
    // Rated compensation current
    ctx.push_obligation(ProofObligation::assume("ca", "current_a == 50"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_a == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cur_ok == if current_a <= max_current_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cur_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: 50A rated ≤ 300A max → OK");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_us", "max_resp_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Dynamic response time in microseconds
    ctx.push_obligation(ProofObligation::assume("ru", "resp_us == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resp_us == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_us <= max_resp_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: 100μs response ≤ 500μs max → OK");
}

#[test]
fn power_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["pf_x100", "min_pf_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pf_ok", i32_ty());
    // Power factor correction target (×100, 1.00 = unity)
    ctx.push_obligation(ProofObligation::assume("px", "pf_x100 == 98")); // 0.98
    ctx.push_obligation(ProofObligation::assume("mp", "min_pf_x100 == 95")); // 0.95
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pf_ok == if pf_x100 >= min_pf_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: PF 0.98 ≥ 0.95 min → OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["sw_khz", "min_sw_khz", "max_sw_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sw_ok", i32_ty());
    // Inverter switching frequency
    ctx.push_obligation(ProofObligation::assume("sk", "sw_khz == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_sw_khz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_sw_khz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sw_ok == if sw_khz >= min_sw_khz && sw_khz <= max_sw_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: 20kHz switching in [10, 50] → OK");
}

#[test]
fn topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // Topologies: 1=shunt, 2=series, 3=hybrid, 4=UPQC
    ctx.push_obligation(ProofObligation::assume("t", "topo == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 || topo == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: shunt is valid topology");
}

#[test]
fn dc_bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vdc_v", "min_vdc_v", "max_vdc_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vdc_ok", i32_ty());
    // DC bus voltage
    ctx.push_obligation(ProofObligation::assume("vv", "vdc_v == 700"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vdc_v == 600"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vdc_v == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vdc_ok == if vdc_v >= min_vdc_v && vdc_v <= max_vdc_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vdc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: 700V DC bus in [600, 800] → OK");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "min_eff_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Overall efficiency (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ex", "eff_x10 == 970")); // 97.0%
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_x10 == 950")); // 95.0%
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_x10 >= min_eff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: 97.0% efficiency ≥ 95.0% min → OK");
}

#[test]
fn reactive_power() {
    let mut ctx = VerificationContext::new();
    for v in &["kvar", "max_kvar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("var_ok", i32_ty());
    // Reactive power compensation capacity in kVAR
    ctx.push_obligation(ProofObligation::assume("kv", "kvar == 100"));
    ctx.push_obligation(ProofObligation::assume("mk", "max_kvar == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "var_ok == if kvar <= max_kvar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "var_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Active filter: 100 kVAR ≤ 500 max → OK");
}
