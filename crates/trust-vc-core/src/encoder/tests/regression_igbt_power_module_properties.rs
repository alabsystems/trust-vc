// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn voltage_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vclass", u32_ty());
    ctx.declare_var_typed("valid_vclass", i32_ty());
    // Non-sequential voltage classes in V: 600, 1200, 1700, 3300, 6500
    ctx.push_obligation(ProofObligation::assume("vc_val", "vclass == 1700"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_valid_def",
        "valid_vclass == if vclass == 600 || vclass == 1200 || vclass == 1700 || vclass == 3300 || vclass == 6500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vc_check", "valid_vclass == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage class 1700 V is valid");
}

#[test]
fn current_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["amps", "amps_min", "amps_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Current rating in A (amperes): value 450, valid range 10 to 3600
    ctx.push_obligation(ProofObligation::assume("cr_val", "amps == 450"));
    ctx.push_obligation(ProofObligation::assume("cr_min", "amps_min == 10"));
    ctx.push_obligation(ProofObligation::assume("cr_max", "amps_max == 3600"));
    ctx.push_obligation(ProofObligation::assert(
        "cr_in_range",
        "amps >= amps_min && amps <= amps_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current rating 450 A in range [10,3600]");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "freq_min", "freq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Switching frequency in kHz: value 20, valid range 1 to 100
    ctx.push_obligation(ProofObligation::assume("sf_val", "freq_khz == 20"));
    ctx.push_obligation(ProofObligation::assume("sf_min", "freq_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sf_max", "freq_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "sf_in_range",
        "freq_khz >= freq_min && freq_khz <= freq_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switching frequency 20 kHz in range [1,100]");
}

#[test]
fn module_topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // 1=half-bridge, 2=full-bridge/H-bridge, 3=six-pack/3-phase, 4=chopper
    ctx.push_obligation(ProofObligation::assume("mt_val", "topo == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_valid_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 || topo == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mt_check", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "module topology 3 (six-pack/3-phase) is valid");
}

#[test]
fn thermal_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rth", "rth_min", "rth_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Thermal resistance in units of 0.01 C/W (e.g., 0.05 C/W -> 5): value 5, valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("tr_val", "rth == 5"));
    ctx.push_obligation(ProofObligation::assume("tr_min", "rth_min == 1"));
    ctx.push_obligation(ProofObligation::assume("tr_max", "rth_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "tr_in_range",
        "rth >= rth_min && rth <= rth_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal resistance 5 (0.05 C/W) in range [1,500]");
}

#[test]
fn gate_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vge_mv", "vge_min", "vge_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gate-emitter voltage in mV: value 15000 (15V), valid range 10000 to 20000
    ctx.push_obligation(ProofObligation::assume("gv_val", "vge_mv == 15000"));
    ctx.push_obligation(ProofObligation::assume("gv_min", "vge_min == 10000"));
    ctx.push_obligation(ProofObligation::assume("gv_max", "vge_max == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "gv_in_range",
        "vge_mv >= vge_min && vge_mv <= vge_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gate voltage 15000 mV (15V) in range [10000,20000]",
    );
}

#[test]
fn turn_on_time() {
    let mut ctx = VerificationContext::new();
    for v in &["ton_ns", "ton_min", "ton_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Turn-on time in ns: value 500, valid range 50 to 5000
    ctx.push_obligation(ProofObligation::assume("to_val", "ton_ns == 500"));
    ctx.push_obligation(ProofObligation::assume("to_min", "ton_min == 50"));
    ctx.push_obligation(ProofObligation::assume("to_max", "ton_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "to_in_range",
        "ton_ns >= ton_min && ton_ns <= ton_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turn-on time 500 ns in range [50,5000]");
}

#[test]
fn turn_off_time() {
    let mut ctx = VerificationContext::new();
    for v in &["toff_ns", "toff_min", "toff_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Turn-off time in ns: value 1200, valid range 50 to 10000
    ctx.push_obligation(ProofObligation::assume("tf_val", "toff_ns == 1200"));
    ctx.push_obligation(ProofObligation::assume("tf_min", "toff_min == 50"));
    ctx.push_obligation(ProofObligation::assume("tf_max", "toff_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "tf_in_range",
        "toff_ns >= toff_min && toff_ns <= toff_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turn-off time 1200 ns in range [50,10000]");
}

#[test]
fn package_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pkg", u32_ty());
    ctx.declare_var_typed("valid_pkg", i32_ty());
    // 1=TO-247, 2=EconoPACK, 3=PrimePACK, 4=HiPak, 5=press-pack
    ctx.push_obligation(ProofObligation::assume("pt_val", "pkg == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_valid_def",
        "valid_pkg == if pkg == 1 || pkg == 2 || pkg == 3 || pkg == 4 || pkg == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pt_check", "valid_pkg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "package type 2 (EconoPACK) is valid");
}

#[test]
fn junction_temp_max() {
    let mut ctx = VerificationContext::new();
    for v in &["tj_max", "tj_min", "tj_ceil"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Maximum junction temperature in C: value 175, valid range 125 to 200
    ctx.push_obligation(ProofObligation::assume("jt_val", "tj_max == 175"));
    ctx.push_obligation(ProofObligation::assume("jt_min", "tj_min == 125"));
    ctx.push_obligation(ProofObligation::assume("jt_ceil", "tj_ceil == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "jt_in_range",
        "tj_max >= tj_min && tj_max <= tj_ceil",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "junction temp max 175 C in range [125,200]");
}
