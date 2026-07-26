// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn probe_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_mm", "min_length_mm", "max_length_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // Probe length in mm
    ctx.push_obligation(ProofObligation::assume("lm", "length_mm == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_length_mm == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_length_mm == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if length_mm >= min_length_mm && length_mm <= max_length_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 500mm probe in [100, 3000] → OK");
}

#[test]
fn dielectric_constant() {
    let mut ctx = VerificationContext::new();
    for v in &["dk_x10", "min_dk_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dk_ok", i32_ty());
    // Dielectric constant of media (×10, water≈80.0, oil≈2.0)
    ctx.push_obligation(ProofObligation::assume("dx", "dk_x10 == 800")); // 80.0 (water)
    ctx.push_obligation(ProofObligation::assume("md", "min_dk_x10 == 15")); // 1.5
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dk_ok == if dk_x10 >= min_dk_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dk_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: water Dk 80.0 ≥ 1.5 min → OK");
}

#[test]
fn measurement_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "max_accuracy_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy as % of span (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x10 == 5")); // 0.5%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x10 == 20")); // 2.0%
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 0.5% accuracy ≤ 2.0% max → OK");
}

#[test]
fn output_signal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output types: 1=4-20mA, 2=0-10V, 3=relay, 4=HART, 5=IO-Link
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 || output_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 4-20mA is valid output type");
}

#[test]
fn switching_point() {
    let mut ctx = VerificationContext::new();
    for v in &["switch_pct", "min_switch_pct", "max_switch_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sw_ok", i32_ty());
    // Switching point as % of probe length
    ctx.push_obligation(ProofObligation::assume("sp", "switch_pct == 75"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_switch_pct == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_switch_pct == 95"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sw_ok == if switch_pct >= min_switch_pct && switch_pct <= max_switch_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 75% switch point in [5, 95] → OK");
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature: -40°C to +150°C (offset +500)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 580")); // 80°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460")); // -40°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 650")); // 150°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 80°C process temp in [-40, 150] → OK");
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "max_pressure_bar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Process pressure rating
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 16"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar <= max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 16 bar ≤ 40 max → OK");
}

#[test]
fn dead_band() {
    let mut ctx = VerificationContext::new();
    for v in &["deadband_mm", "max_deadband_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("db_ok", i32_ty());
    // Dead band (non-sensing zone at top of probe)
    ctx.push_obligation(ProofObligation::assume("dm", "deadband_mm == 30"));
    ctx.push_obligation(ProofObligation::assume("md", "max_deadband_mm == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "db_ok == if deadband_mm <= max_deadband_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "db_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 30mm dead band ≤ 100mm max → OK");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_ms", "max_resp_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Measurement response time
    ctx.push_obligation(ProofObligation::assume("rm", "resp_ms == 200"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resp_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_ms <= max_resp_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 200ms response ≤ 1000ms max → OK");
}

#[test]
fn capacitance_range() {
    let mut ctx = VerificationContext::new();
    for v in &["cap_pf", "min_cap_pf", "max_cap_pf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Probe capacitance in picofarads
    ctx.push_obligation(ProofObligation::assume("cp", "cap_pf == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cap_pf == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cap_pf == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if cap_pf >= min_cap_pf && cap_pf <= max_cap_pf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Level: 50 pF capacitance in [5, 500] → OK");
}
