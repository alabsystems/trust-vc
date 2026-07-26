// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn power_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["rating_va", "min_rating_va", "max_rating_va"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rating_ok", i32_ty());
    // UPS power rating in VA (10 kVA)
    ctx.push_obligation(ProofObligation::assume("rv", "rating_va == 10000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rating_va == 500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rating_va == 500000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rating_ok == if rating_va >= min_rating_va && rating_va <= max_rating_va { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rating_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: 10 kVA rating in [500, 500000] VA range");
}

#[test]
fn topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // UPS topologies: 1=standby (offline), 2=line-interactive, 3=double-conversion (online), 4=delta conversion
    ctx.push_obligation(ProofObligation::assume("tp", "topo == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 || topo == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: double-conversion (online) is valid topology");
}

#[test]
fn input_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("input_v", u32_ty());
    ctx.declare_var_typed("valid_input", i32_ty());
    // Nominal input voltage: 120/208/230/480 V
    ctx.push_obligation(ProofObligation::assume("iv", "input_v == 208"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_input == if input_v == 120 || input_v == 208 || input_v == 230 || input_v == 480 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_input == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: 208V is valid nominal input voltage");
}

#[test]
fn output_voltage_regulation() {
    let mut ctx = VerificationContext::new();
    for v in &["tolerance_x10", "max_tolerance_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tol_ok", i32_ty());
    // Output voltage tolerance x10 (%), 20 = 2.0%, max 50 = 5.0%
    ctx.push_obligation(ProofObligation::assume("tx", "tolerance_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tolerance_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tol_ok == if tolerance_x10 <= max_tolerance_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tol_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: 2.0% output tolerance <= 5.0% max");
}

#[test]
fn transfer_time() {
    let mut ctx = VerificationContext::new();
    for v in &["xfer_ms", "max_xfer_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("xfer_ok", i32_ty());
    // Transfer to battery time in ms (online = 0ms)
    ctx.push_obligation(ProofObligation::assume("xm", "xfer_ms == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_xfer_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "xo_def",
        "xfer_ok == if xfer_ms <= max_xfer_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "xfer_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: 0ms transfer (online) <= 10ms max");
}

#[test]
fn battery_runtime() {
    let mut ctx = VerificationContext::new();
    for v in &["runtime_min", "min_runtime_min", "max_runtime_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("runtime_ok", i32_ty());
    // Battery runtime at full load in minutes
    ctx.push_obligation(ProofObligation::assume("rm", "runtime_min == 15"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_runtime_min == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_runtime_min == 480"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "runtime_ok == if runtime_min >= min_runtime_min && runtime_min <= max_runtime_min { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "runtime_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: 15 min runtime in [5, 480] range");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "min_eff_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // UPS efficiency x10 (%), 950 = 95.0%, min 850 = 85.0%
    ctx.push_obligation(ProofObligation::assume("ex", "eff_x10 == 950"));
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_x10 == 850"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_x10 >= min_eff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: 95.0% efficiency >= 85.0% min");
}

#[test]
fn battery_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batt_type", u32_ty());
    ctx.declare_var_typed("valid_batt", i32_ty());
    // Battery types: 1=VRLA (sealed lead-acid), 2=lithium-ion, 3=nickel-cadmium
    ctx.push_obligation(ProofObligation::assume("bt", "batt_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_batt == if batt_type == 1 || batt_type == 2 || batt_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_batt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "UPS: VRLA (sealed lead-acid) is valid battery type",
    );
}

#[test]
fn phase_configuration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_cfg", u32_ty());
    ctx.declare_var_typed("valid_phase", i32_ty());
    // Phase configurations: 1=single-phase, 2=three-phase, 3=split-phase
    ctx.push_obligation(ProofObligation::assume("pc", "phase_cfg == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_phase == if phase_cfg == 1 || phase_cfg == 2 || phase_cfg == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_phase == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: three-phase is valid phase configuration");
}

#[test]
fn overload_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["overload_x10", "min_overload_x10", "max_overload_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overload_ok", i32_ty());
    // Overload capacity x10 (%), 1100 = 110.0%, range [1000, 1500] = [100%, 150%]
    ctx.push_obligation(ProofObligation::assume("ox", "overload_x10 == 1100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_overload_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_overload_x10 == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "overload_ok == if overload_x10 >= min_overload_x10 && overload_x10 <= max_overload_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "overload_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UPS: 110.0% overload in [100%, 150%] range");
}
