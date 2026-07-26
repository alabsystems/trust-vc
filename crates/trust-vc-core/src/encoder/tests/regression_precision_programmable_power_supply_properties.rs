// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: precision programmable power supply properties

use super::*;

#[test]
fn test_voltage_range_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "voltage_x1000 >= 1 && voltage_x1000 <= 600000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "voltage_x1000 == 60000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "voltage_x1000 >= 1 && voltage_x1000 <= 600000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage range x1000 bounded at 60.000V");
}

#[test]
fn test_current_range_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "current_x1000 >= 1 && current_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "current_x1000 == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "current_x1000 >= 1 && current_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current range x1000 bounded at 10.000A");
}

#[test]
fn test_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_watts", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "power_watts >= 1 && power_watts <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "power_watts == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "power_watts >= 1 && power_watts <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power bounded at 600W");
}

#[test]
fn test_voltage_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "accuracy_x10000 >= 1 && accuracy_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x10000 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "accuracy_x10000 >= 1 && accuracy_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage accuracy x10000 bounded at 0.0010%");
}

#[test]
fn test_ripple_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ripple_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ripple_x1000 >= 1 && ripple_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "ripple_x1000 == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "ripple_x1000 >= 1 && ripple_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ripple x1000 bounded at 0.005 mVpp");
}

#[test]
fn test_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 8",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 1 && channels <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output channels bounded at 4");
}

#[test]
fn test_regulation_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reg_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "reg_mode == 1 || reg_mode == 2 || reg_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "reg_mode >= 1 && reg_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "regulation mode disjunction CV/CC/CP");
}

#[test]
fn test_interface_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iface", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "iface == 1 || iface == 2 || iface == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "iface >= 1 && iface <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "interface disjunction GPIB/USB/LAN");
}

#[test]
fn test_output_topology_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topology", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "topology == 1 || topology == 2 || topology == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "topology >= 1 && topology <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output topology disjunction linear/switching/hybrid",
    );
}

#[test]
fn test_ovp_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ovp_enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_set", "ovp_enabled == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "is_enabled",
        "if ovp_enabled == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "over-voltage protection flag enabled");
}
