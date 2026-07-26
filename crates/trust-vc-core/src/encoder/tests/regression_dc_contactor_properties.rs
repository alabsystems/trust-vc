// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rated_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_v", "max_voltage_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Rated DC voltage
    ctx.push_obligation(ProofObligation::assume("vv", "voltage_v == 800"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_voltage_v == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_v <= max_voltage_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 800V DC ≤ 1500V max → OK");
}

#[test]
fn rated_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_a", "max_current_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cur_ok", i32_ty());
    // Continuous rated current
    ctx.push_obligation(ProofObligation::assume("ca", "current_a == 200"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_a == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cur_ok == if current_a <= max_current_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cur_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 200A ≤ 600A max → OK");
}

#[test]
fn arc_quenching() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", u32_ty());
    ctx.declare_var_typed("valid_method", i32_ty());
    // Arc quenching: 1=magnetic blowout, 2=gas chamber, 3=vacuum, 4=hybrid
    ctx.push_obligation(ProofObligation::assume("m", "method == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_method == if method == 1 || method == 2 || method == 3 || method == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_method == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: gas chamber is valid arc quenching");
}

#[test]
fn contact_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["res_uohm", "max_res_uohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Contact resistance in microohms
    ctx.push_obligation(ProofObligation::assume("ru", "res_uohm == 50"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_res_uohm == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if res_uohm <= max_res_uohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Contactor: 50μΩ contact resistance ≤ 200μΩ max → OK",
    );
}

#[test]
fn operate_time() {
    let mut ctx = VerificationContext::new();
    for v in &["close_ms", "max_close_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("close_ok", i32_ty());
    // Closing (operate) time
    ctx.push_obligation(ProofObligation::assume("cm", "close_ms == 15"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_close_ms == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "close_ok == if close_ms <= max_close_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "close_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 15ms close time ≤ 50ms max → OK");
}

#[test]
fn release_time() {
    let mut ctx = VerificationContext::new();
    for v in &["release_ms", "max_release_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rel_ok", i32_ty());
    // Opening (release) time
    ctx.push_obligation(ProofObligation::assume("rm", "release_ms == 5"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_release_ms == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rel_ok == if release_ms <= max_release_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 5ms release ≤ 20ms max → OK");
}

#[test]
fn endurance_cycles() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles_k", "min_cycles_k"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cyc_ok", i32_ty());
    // Electrical endurance in thousands of cycles
    ctx.push_obligation(ProofObligation::assume("ck", "cycles_k == 100")); // 100k cycles
    ctx.push_obligation(ProofObligation::assume("mc", "min_cycles_k == 50")); // 50k
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cyc_ok == if cycles_k >= min_cycles_k { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cyc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 100k cycles ≥ 50k min → OK");
}

#[test]
fn coil_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["coil_v", "min_coil_v", "max_coil_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("coil_ok", i32_ty());
    // Coil operating voltage range
    ctx.push_obligation(ProofObligation::assume("cv", "coil_v == 24"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_coil_v == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_coil_v == 28"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "coil_ok == if coil_v >= min_coil_v && coil_v <= max_coil_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "coil_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 24V coil in [20, 28] → OK");
}

#[test]
fn dielectric_strength() {
    let mut ctx = VerificationContext::new();
    for v in &["test_kv", "min_test_kv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("diel_ok", i32_ty());
    // Dielectric withstand voltage in kV
    ctx.push_obligation(ProofObligation::assume("tk", "test_kv == 4"));
    ctx.push_obligation(ProofObligation::assume("mt", "min_test_kv == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "diel_ok == if test_kv >= min_test_kv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "diel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 4kV dielectric ≥ 2kV min → OK");
}

#[test]
fn pole_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("poles", u32_ty());
    ctx.declare_var_typed("valid_poles", i32_ty());
    // Standard pole configurations
    ctx.push_obligation(ProofObligation::assume("p", "poles == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_poles == if poles == 1 || poles == 2 || poles == 3 || poles == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_poles == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Contactor: 2-pole is valid configuration");
}
