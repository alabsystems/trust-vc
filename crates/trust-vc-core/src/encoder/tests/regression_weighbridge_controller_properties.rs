// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn max_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["kg", "kg_min", "kg_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Maximum weighbridge capacity in kg: value 60000, valid range 1000 to 200000
    ctx.push_obligation(ProofObligation::assume("mc_val", "kg == 60000"));
    ctx.push_obligation(ProofObligation::assume("mc_min", "kg_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("mc_max", "kg_max == 200000"));
    ctx.push_obligation(ProofObligation::assert(
        "mc_in_range",
        "kg >= kg_min && kg <= kg_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "weighbridge capacity 60000 kg in range [1000,200000]",
    );
}

#[test]
fn scale_division() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("div_g", u32_ty());
    ctx.declare_var_typed("valid_div", i32_ty());
    // Scale division (smallest increment) in grams: 1=10g, 2=20g, 3=50g, 4=100g
    ctx.push_obligation(ProofObligation::assume("sd_val", "div_g == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "valid_div == if div_g == 1 || div_g == 2 || div_g == 3 || div_g == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sd_chk", "valid_div == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scale division 3 (50g) is valid increment");
}

#[test]
fn accuracy_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_cls", u32_ty());
    ctx.declare_var_typed("valid_cls", i32_ty());
    // Accuracy class: 1=OIML III, 2=OIML IIII, 3=non-trade
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_cls == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "valid_cls == if acc_cls == 1 || acc_cls == 2 || acc_cls == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ac_chk", "valid_cls == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy class 1 (OIML III) is valid class");
}

#[test]
fn platform_count() {
    let mut ctx = VerificationContext::new();
    for v in &["plat", "plat_min", "plat_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of weighing platforms: value 2, valid range 1 to 4
    ctx.push_obligation(ProofObligation::assume("pc_val", "plat == 2"));
    ctx.push_obligation(ProofObligation::assume("pc_min", "plat_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pc_max", "plat_max == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "pc_in_range",
        "plat >= plat_min && plat <= plat_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "platform count 2 in range [1,4]");
}

#[test]
fn load_cell_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cells", "cells_min", "cells_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of load cells: value 8, valid range 1 to 16
    ctx.push_obligation(ProofObligation::assume("lc_val", "cells == 8"));
    ctx.push_obligation(ProofObligation::assume("lc_min", "cells_min == 1"));
    ctx.push_obligation(ProofObligation::assume("lc_max", "cells_max == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "lc_in_range",
        "cells >= cells_min && cells <= cells_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load cell count 8 in range [1,16]");
}

#[test]
fn excitation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["mv", "mv_min", "mv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Excitation voltage in mV: value 10000 (10V), valid range 5000 to 15000
    ctx.push_obligation(ProofObligation::assume("ev_val", "mv == 10000"));
    ctx.push_obligation(ProofObligation::assume("ev_min", "mv_min == 5000"));
    ctx.push_obligation(ProofObligation::assume("ev_max", "mv_max == 15000"));
    ctx.push_obligation(ProofObligation::assert(
        "ev_in_range",
        "mv >= mv_min && mv <= mv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation voltage 10000 mV (10V) in range [5000,15000]",
    );
}

#[test]
fn adc_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["bits", "bits_min", "bits_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ADC resolution in bits: value 24, valid range 16 to 24
    ctx.push_obligation(ProofObligation::assume("ar_val", "bits == 24"));
    ctx.push_obligation(ProofObligation::assume("ar_min", "bits_min == 16"));
    ctx.push_obligation(ProofObligation::assume("ar_max", "bits_max == 24"));
    ctx.push_obligation(ProofObligation::assert(
        "ar_in_range",
        "bits >= bits_min && bits <= bits_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC resolution 24 bits in range [16,24]");
}

#[test]
fn communication() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // Communication interface: 1=RS-232, 2=RS-485, 3=Ethernet, 4=fieldbus
    ctx.push_obligation(ProofObligation::assume("cm_val", "comm == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "valid_comm == if comm == 1 || comm == 2 || comm == 3 || comm == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication 3 (Ethernet) is valid interface");
}

#[test]
fn zero_range() {
    let mut ctx = VerificationContext::new();
    for v in &["zr_x10", "zr_min", "zr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Zero range as x10 percent of capacity (e.g., 2.0% = 20), valid range 10 to 100
    ctx.push_obligation(ProofObligation::assume("zr_val", "zr_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("zr_lo", "zr_min == 10"));
    ctx.push_obligation(ProofObligation::assume("zr_hi", "zr_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "zr_in_range",
        "zr_x10 >= zr_min && zr_x10 <= zr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zero range 2.0% capacity in range [1.0%,10.0%]");
}

#[test]
fn tare_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tare", u32_ty());
    ctx.declare_var_typed("valid_tare", i32_ty());
    // Tare mode: 1=semi-automatic, 2=automatic, 3=preset
    ctx.push_obligation(ProofObligation::assume("tm_val", "tare == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_def",
        "valid_tare == if tare == 1 || tare == 2 || tare == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tm_chk", "valid_tare == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tare mode 2 (automatic) is valid mode");
}
