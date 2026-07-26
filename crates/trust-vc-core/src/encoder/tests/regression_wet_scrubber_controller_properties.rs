// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn gas_flow_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["flow", "flow_min", "flow_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gas flow rate in m³/h: value 10000, valid range 500 to 100000
    ctx.push_obligation(ProofObligation::assume("gf_val", "flow == 10000"));
    ctx.push_obligation(ProofObligation::assume("gf_min", "flow_min == 500"));
    ctx.push_obligation(ProofObligation::assume("gf_max", "flow_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "gf_in_range",
        "flow >= flow_min && flow <= flow_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas flow 10000 m3/h in range [500,100000]");
}

#[test]
fn liquid_rate_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["liquid", "liq_min", "liq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Liquid recirculation rate in L/min: value 500, valid range 50 to 5000
    ctx.push_obligation(ProofObligation::assume("lr_val", "liquid == 500"));
    ctx.push_obligation(ProofObligation::assume("lr_min", "liq_min == 50"));
    ctx.push_obligation(ProofObligation::assume("lr_max", "liq_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "lr_in_range",
        "liquid >= liq_min && liquid <= liq_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid rate 500 L/min in range [50,5000]");
}

#[test]
fn scrubber_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scrub_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // 1=packed bed, 2=spray tower, 3=Venturi
    ctx.push_obligation(ProofObligation::assume("st_val", "scrub_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "valid_type == if scrub_type == 1 || scrub_type == 2 || scrub_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_chk", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scrubber type 1 (packed bed) is valid");
}

#[test]
fn removal_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "eff_min", "eff_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Removal efficiency x10 %: value 980 (98.0%), valid range 800 to 999
    ctx.push_obligation(ProofObligation::assume("re_val", "eff_x10 == 980"));
    ctx.push_obligation(ProofObligation::assume("re_min", "eff_min == 800"));
    ctx.push_obligation(ProofObligation::assume("re_max", "eff_max == 999"));
    ctx.push_obligation(ProofObligation::assert(
        "re_in_range",
        "eff_x10 >= eff_min && eff_x10 <= eff_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "removal efficiency 98.0% in range [80.0,99.9]");
}

#[test]
fn pressure_drop_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["dp", "dp_min", "dp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pressure drop in Pa: value 2500, valid range 100 to 10000
    ctx.push_obligation(ProofObligation::assume("pd_val", "dp == 2500"));
    ctx.push_obligation(ProofObligation::assume("pd_min", "dp_min == 100"));
    ctx.push_obligation(ProofObligation::assume("pd_max", "dp_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "pd_in_range",
        "dp >= dp_min && dp <= dp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure drop 2500 Pa in range [100,10000]");
}

#[test]
fn ph_setpoint_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["ph_x10", "ph_min", "ph_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // pH setpoint x10: value 70 (7.0), valid range 20 to 130
    ctx.push_obligation(ProofObligation::assume("ph_val", "ph_x10 == 70"));
    ctx.push_obligation(ProofObligation::assume("ph_lo", "ph_min == 20"));
    ctx.push_obligation(ProofObligation::assume("ph_hi", "ph_max == 130"));
    ctx.push_obligation(ProofObligation::assert(
        "ph_in_range",
        "ph_x10 >= ph_min && ph_x10 <= ph_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH setpoint 7.0 (x10=70) in range [2.0,13.0]");
}

#[test]
fn reagent_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reagent", u32_ty());
    ctx.declare_var_typed("valid_reagent", i32_ty());
    // 1=NaOH, 2=lime, 3=Na2CO3
    ctx.push_obligation(ProofObligation::assume("rg_val", "reagent == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rg_def",
        "valid_reagent == if reagent == 1 || reagent == 2 || reagent == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rg_chk", "valid_reagent == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reagent type 1 (NaOH) is valid");
}

#[test]
fn packing_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("packing", u32_ty());
    ctx.declare_var_typed("valid_packing", i32_ty());
    // 1=polypropylene, 2=ceramic, 3=metal
    ctx.push_obligation(ProofObligation::assume("pm_val", "packing == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "pm_def",
        "valid_packing == if packing == 1 || packing == 2 || packing == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pm_chk", "valid_packing == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "packing material 2 (ceramic) is valid");
}

#[test]
fn blowdown_interval_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["blowdown", "bd_min", "bd_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Blowdown interval in minutes: value 60, valid range 5 to 480
    ctx.push_obligation(ProofObligation::assume("bd_val", "blowdown == 60"));
    ctx.push_obligation(ProofObligation::assume("bd_lo", "bd_min == 5"));
    ctx.push_obligation(ProofObligation::assume("bd_hi", "bd_max == 480"));
    ctx.push_obligation(ProofObligation::assert(
        "bd_in_range",
        "blowdown >= bd_min && blowdown <= bd_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blowdown interval 60 min in range [5,480]");
}

#[test]
fn mist_eliminator_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    // Mist eliminator installed: boolean flag, 1=yes
    ctx.push_obligation(ProofObligation::assume("me_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "me_def",
        "result == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("me_chk", "result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mist eliminator flag 1 (installed) confirms active",
    );
}
