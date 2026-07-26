// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn system_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure", "min_pressure", "max_pressure"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // System operating pressure in bar
    ctx.push_obligation(ProofObligation::assume("pv", "pressure == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure == 700"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure >= min_pressure && pressure <= max_pressure { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: 250 bar system pressure in [50, 700] range");
}

#[test]
fn flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow", "min_flow", "max_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Flow rate in L/min
    ctx.push_obligation(ProofObligation::assume("fv", "flow == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow >= min_flow && flow <= max_flow { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: 100 L/min flow rate in [5, 500] range");
}

#[test]
fn reservoir_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["capacity", "min_capacity", "max_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Reservoir capacity in liters
    ctx.push_obligation(ProofObligation::assume("cv", "capacity == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_capacity == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_capacity == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if capacity >= min_capacity && capacity <= max_capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: 200 L reservoir capacity in [20, 2000] range");
}

#[test]
fn pump_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump", u32_ty());
    ctx.declare_var_typed("valid_pump", i32_ty());
    // Pump types: 1=gear, 2=vane, 3=piston
    ctx.push_obligation(ProofObligation::assume("pv", "pump == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_pump == if pump == 1 || pump == 2 || pump == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_pump == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: piston is valid pump type");
}

#[test]
fn motor_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power", "min_power", "max_power"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pwr_ok", i32_ty());
    // Motor power in kW
    ctx.push_obligation(ProofObligation::assume("pv", "power == 37"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_power == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_power == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pwr_ok == if power >= min_power && power <= max_power { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pwr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: 37 kW motor power in [1, 200] range");
}

#[test]
fn oil_viscosity() {
    let mut ctx = VerificationContext::new();
    for v in &["visc_x10", "min_visc_x10", "max_visc_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("visc_ok", i32_ty());
    // Oil viscosity x10 (cSt): 460 = 46.0 cSt, range [100, 1000] = [10.0, 100.0] cSt
    ctx.push_obligation(ProofObligation::assume("vv", "visc_x10 == 460"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_visc_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_visc_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "visc_ok == if visc_x10 >= min_visc_x10 && visc_x10 <= max_visc_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "visc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "HPU: 46.0 cSt oil viscosity in [10.0, 100.0] range",
    );
}

#[test]
fn filtration_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["filter", "min_filter", "max_filter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("filt_ok", i32_ty());
    // Filtration rating in micrometers
    ctx.push_obligation(ProofObligation::assume("fv", "filter == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_filter == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_filter == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "filt_ok == if filter >= min_filter && filter <= max_filter { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "filt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: 10 um filtration rating in [1, 100] range");
}

#[test]
fn cooling_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", u32_ty());
    ctx.declare_var_typed("valid_cooling", i32_ty());
    // Cooling types: 1=air, 2=water, 3=none
    ctx.push_obligation(ProofObligation::assume("cv", "cooling == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cooling == if cooling == 1 || cooling == 2 || cooling == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cooling == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: water cooling is valid cooling type");
}

#[test]
fn oil_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Oil temperature offset +500: 550 = 50 deg C, range [480, 580] = [-20, 80] deg C
    ctx.push_obligation(ProofObligation::assume("tv", "temp == 550"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp == 480"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp == 580"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp >= min_temp && temp <= max_temp { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "HPU: 50 deg C oil temp in [-20, 80] range (offset +500)",
    );
}

#[test]
fn level_switch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("level_active", i32_ty());
    // Level switch: boolean flag (1=active, 0=inactive)
    ctx.push_obligation(ProofObligation::assume("fv", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "la_def",
        "level_active == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "level_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HPU: level switch flag=1 -> active");
}
