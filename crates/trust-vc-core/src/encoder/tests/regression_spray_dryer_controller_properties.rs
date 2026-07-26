// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn evaporation_rate_bounded() {
    // Evaporation rate in kg/h, bounded [10, 50000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "evap_range",
        "evap_rate >= 10 && evap_rate <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "evap_rate >= 10"));
    ctx.push_obligation(ProofObligation::assert("upper", "evap_rate <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "evaporation rate (kg/h) in [10, 50000] implies bounds",
    );
}

#[test]
fn inlet_air_temp_bounded() {
    // Inlet air temperature in °C, bounded [100, 500] (all positive, no offset)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_range",
        "inlet_temp >= 100 && inlet_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "inlet_temp >= 100"));
    ctx.push_obligation(ProofObligation::assert("upper", "inlet_temp <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet air temp (°C) in [100, 500] implies bounds");
}

#[test]
fn outlet_air_temp_offset_bounded() {
    // Outlet air temperature with offset +500: 30°C → 530, 200°C → 700
    // Bounded [530, 700] (i.e. 30°C to 200°C)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("outlet_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "outlet_range",
        "outlet_off >= 530 && outlet_off <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "outlet_off >= 530"));
    ctx.push_obligation(ProofObligation::assert("upper", "outlet_off <= 700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "outlet air temp (offset +500) in [530, 700] implies bounds",
    );
}

#[test]
fn atomizer_type_three_way_disjunction() {
    // 1=rotary, 2=pressure nozzle, 3=two-fluid nozzle
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atomizer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_atomizer",
        "atomizer == 1 || atomizer == 2 || atomizer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "atomizer >= 1 && atomizer <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atomizer type {1=rotary,2=pressure,3=two-fluid} implies [1,3] bounds",
    );
}

#[test]
fn chamber_diameter_bounded() {
    // Chamber diameter in mm, bounded [500, 20000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_range",
        "diameter >= 500 && diameter <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "diameter >= 500"));
    ctx.push_obligation(ProofObligation::assert("upper", "diameter <= 20000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chamber diameter (mm) in [500, 20000] implies bounds",
    );
}

#[test]
fn feed_concentration_scaled_bounded() {
    // Feed concentration scaled ×10: 30.0% → 300, bounded [50, 700] (5.0%-70.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conc_range",
        "conc_x10 >= 50 && conc_x10 <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "conc_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("upper", "conc_x10 <= 700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "feed concentration (×10 %) in [50, 700] implies bounds",
    );
}

#[test]
fn air_flow_bounded() {
    // Air flow rate in m³/h, bounded [100, 100000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "air_flow >= 100 && air_flow <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "air_flow >= 100"));
    ctx.push_obligation(ProofObligation::assert("upper", "air_flow <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow (m³/h) in [100, 100000] implies bounds");
}

#[test]
fn cyclone_efficiency_scaled_bounded() {
    // Cyclone efficiency scaled ×10: 98.5% → 985, bounded [900, 999] (90.0%-99.9%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "eff_x10 >= 900 && eff_x10 <= 999",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "eff_x10 >= 900"));
    ctx.push_obligation(ProofObligation::assert("upper", "eff_x10 <= 999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cyclone efficiency (×10 %) in [900, 999] implies bounds",
    );
}

#[test]
fn powder_collection_three_way_disjunction() {
    // 1=cyclone, 2=baghouse, 3=electrostatic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_collector",
        "collector == 1 || collector == 2 || collector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "collector >= 1 && collector <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "powder collection {1=cyclone,2=baghouse,3=electrostatic} implies [1,3] bounds",
    );
}

#[test]
fn explosion_vent_boolean_flag() {
    // Boolean flag encoded as i32: 0=vent closed, 1=vent open
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vent_flag", i32_ty());
    ctx.declare_var_typed("safety_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "vent_flag == 0 || vent_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "safety_def",
        "safety_active == if vent_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "safety_matches_vent",
        "safety_active == vent_flag",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "explosion vent flag propagates to safety status correctly",
    );
}
