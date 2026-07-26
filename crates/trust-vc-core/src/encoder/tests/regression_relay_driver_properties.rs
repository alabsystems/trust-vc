// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn coil_voltage_match() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "rated_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_match", i32_ty());
    // Relay coil rated voltage (e.g., 12V relay)
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("rv", "rated_voltage_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "voltage_match == if supply_mv == rated_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Relay: supply 12V = rated 12V → voltage match");
}

#[test]
fn contact_current_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["load_current_ma", "max_contact_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_rating", i32_ty());
    // Contact rating: max switching current
    ctx.push_obligation(ProofObligation::assume("lc", "load_current_ma == 5000")); // 5A
    ctx.push_obligation(ProofObligation::assume("mc", "max_contact_ma == 10000")); // 10A
    ctx.push_obligation(ProofObligation::assume(
        "wr_def",
        "within_rating == if load_current_ma <= max_contact_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_rating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Relay: 5A load ≤ 10A rating → within contact rating",
    );
}

#[test]
fn coil_power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["coil_voltage_mv", "coil_resistance_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_mw", u32_ty());
    // P = V²/R. Precompute: 12000² / 400 / 1000 = 360 mW
    ctx.push_obligation(ProofObligation::assume("cv", "coil_voltage_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("cr", "coil_resistance_ohms == 400"));
    ctx.push_obligation(ProofObligation::assume("pw", "power_mw == 360")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_360", "power_mw == 360"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Relay: 12V²/400Ω = 360mW coil power (precomputed)");
}

#[test]
fn bounce_time() {
    let mut ctx = VerificationContext::new();
    for v in &["bounce_ms", "debounce_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("debounced", i32_ty());
    // Contact bounce: typically 1-5ms. Debounce timer must exceed.
    ctx.push_obligation(ProofObligation::assume("bm", "bounce_ms == 3"));
    ctx.push_obligation(ProofObligation::assume("dm", "debounce_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "debounced == if debounce_ms > bounce_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "debounced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Relay: 10ms debounce > 3ms bounce → debounced");
}

#[test]
fn mechanical_life() {
    let mut ctx = VerificationContext::new();
    for v in &["operations", "rated_operations"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_life", i32_ty());
    // Mechanical life: typically 10M operations
    ctx.push_obligation(ProofObligation::assume("op", "operations == 5000000")); // 5M
    ctx.push_obligation(ProofObligation::assume(
        "ro",
        "rated_operations == 10000000",
    )); // 10M
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_life == if operations < rated_operations { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_life == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Relay: 5M ops < 10M rated → within mechanical life",
    );
}

#[test]
fn driver_transistor_saturation() {
    let mut ctx = VerificationContext::new();
    for v in &["base_current_ua", "min_base_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("saturated", i32_ty());
    // NPN driver: base current must ensure saturation
    ctx.push_obligation(ProofObligation::assume("bc", "base_current_ua == 500"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_base_ua == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "saturated == if base_current_ua >= min_base_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "saturated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Relay: 500μA base ≥ 300μA min → transistor saturated",
    );
}

#[test]
fn snubber_sizing() {
    let mut ctx = VerificationContext::new();
    for v in &["snubber_voltage_v", "spike_voltage_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("protected", i32_ty());
    // RC snubber across contacts to suppress arcing
    ctx.push_obligation(ProofObligation::assume("sv", "snubber_voltage_v == 300"));
    ctx.push_obligation(ProofObligation::assume("spv", "spike_voltage_v == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "protected == if snubber_voltage_v >= spike_voltage_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "protected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Relay: snubber 300V ≥ 250V spike → protected");
}

#[test]
fn operate_time() {
    let mut ctx = VerificationContext::new();
    for v in &["operate_ms", "max_operate_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fast_enough", i32_ty());
    // Operate time: energize to contact close
    ctx.push_obligation(ProofObligation::assume("om", "operate_ms == 8"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_operate_ms == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "fast_enough == if operate_ms <= max_operate_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fast_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Relay: 8ms operate ≤ 15ms max → fast enough");
}

#[test]
fn contact_form() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("form", u32_ty());
    ctx.declare_var_typed("has_nc_contact", i32_ty());
    // Form A (SPST-NO)=0, Form B (SPST-NC)=1, Form C (SPDT)=2
    ctx.push_obligation(ProofObligation::assume("f", "form == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "hn_def",
        "has_nc_contact == if form >= 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_nc_contact == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Relay: Form C (2) ≥ 1 → has NC contact");
}

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["working_voltage_v", "isolation_rating_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("safe", i32_ty());
    // Coil-to-contact isolation
    ctx.push_obligation(ProofObligation::assume("wv", "working_voltage_v == 240"));
    ctx.push_obligation(ProofObligation::assume("ir", "isolation_rating_v == 2500"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "safe == if working_voltage_v <= isolation_rating_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Relay: 240V working ≤ 2500V isolation → safe");
}
