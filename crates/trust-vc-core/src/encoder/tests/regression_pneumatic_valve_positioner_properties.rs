// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn supply_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_kpa", "min_pressure_kpa", "max_pressure_kpa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Air supply pressure in kPa: 400 kPa (4 bar), range 140-700 (1.4-7 bar)
    ctx.push_obligation(ProofObligation::assume("pk", "pressure_kpa == 400"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure_kpa == 140"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure_kpa == 700"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_kpa >= min_pressure_kpa && pressure_kpa <= max_pressure_kpa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Positioner: 4 bar supply in [1.4, 7] bar -> OK");
}

#[test]
fn signal_input() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sig_type", u32_ty());
    ctx.declare_var_typed("valid_sig", i32_ty());
    // Signal input types: 1=4-20mA, 2=0-10V, 3=HART, 4=Foundation Fieldbus
    ctx.push_obligation(ProofObligation::assume("st", "sig_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_sig == if sig_type == 1 || sig_type == 2 || sig_type == 3 || sig_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_sig == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Positioner: 4-20mA is valid signal input");
}

#[test]
fn travel_range() {
    let mut ctx = VerificationContext::new();
    for v in &["travel_mm", "min_travel_mm", "max_travel_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("travel_ok", i32_ty());
    // Valve travel in mm: value 50, range 5-300
    ctx.push_obligation(ProofObligation::assume("tm", "travel_mm == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_travel_mm == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_travel_mm == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "travel_ok == if travel_mm >= min_travel_mm && travel_mm <= max_travel_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "travel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Positioner: 50mm travel in [5, 300] -> OK");
}

#[test]
fn linearity() {
    let mut ctx = VerificationContext::new();
    for v in &["linearity_x100", "max_linearity_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lin_ok", i32_ty());
    // Linearity x100 (% of span): value 50 (0.50%), max 200 (2.00%)
    ctx.push_obligation(ProofObligation::assume("lx", "linearity_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_linearity_x100 == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lin_ok == if linearity_x100 <= max_linearity_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Positioner: 0.50% linearity <= 2.00% max -> OK");
}

#[test]
fn dead_band() {
    let mut ctx = VerificationContext::new();
    for v in &["dead_band_x100", "max_dead_band_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("db_ok", i32_ty());
    // Dead band x100 (%): value 10 (0.10%), max 100 (1.00%)
    ctx.push_obligation(ProofObligation::assume("dx", "dead_band_x100 == 10"));
    ctx.push_obligation(ProofObligation::assume("md", "max_dead_band_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "db_ok == if dead_band_x100 <= max_dead_band_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "db_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Positioner: 0.10% dead band <= 1.00% max -> OK");
}

#[test]
fn action_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("action", u32_ty());
    ctx.declare_var_typed("valid_action", i32_ty());
    // Action types: 1=direct (air-to-open), 2=reverse (air-to-close), 3=double-acting, 4=split-range
    ctx.push_obligation(ProofObligation::assume("ac", "action == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_action == if action == 1 || action == 2 || action == 3 || action == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_action == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Positioner: reverse (air-to-close) is valid action",
    );
}

#[test]
fn fail_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fmode", u32_ty());
    ctx.declare_var_typed("valid_fmode", i32_ty());
    // Fail modes: 1=fail-open, 2=fail-closed, 3=fail-in-place (lock)
    ctx.push_obligation(ProofObligation::assume("fm", "fmode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fmode == if fmode == 1 || fmode == 2 || fmode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_fmode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Positioner: fail-in-place (lock) is valid fail mode",
    );
}

#[test]
fn flow_characteristic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_char", u32_ty());
    ctx.declare_var_typed("valid_flow", i32_ty());
    // Flow characteristics: 1=linear, 2=equal-percentage, 3=quick-opening
    ctx.push_obligation(ProofObligation::assume("fc", "flow_char == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vfc_def",
        "valid_flow == if flow_char == 1 || flow_char == 2 || flow_char == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_flow == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Positioner: equal-percentage is valid flow characteristic",
    );
}

#[test]
fn step_response() {
    let mut ctx = VerificationContext::new();
    for v in &["t63_x10", "max_t63_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Step response time T63 in seconds x10: value 10 (1.0s), max 50 (5.0s)
    ctx.push_obligation(ProofObligation::assume("tx", "t63_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_t63_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if t63_x10 <= max_t63_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Positioner: 1.0s T63 response <= 5.0s max -> OK");
}

#[test]
fn feedback_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fb_type", u32_ty());
    ctx.declare_var_typed("valid_fb", i32_ty());
    // Feedback types: 1=potentiometer, 2=LVDT, 3=Hall effect
    ctx.push_obligation(ProofObligation::assume("ft", "fb_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vfb_def",
        "valid_fb == if fb_type == 1 || fb_type == 2 || fb_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_fb == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Positioner: LVDT is valid feedback type");
}
