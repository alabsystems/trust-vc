// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Pan diameter in mm, valid range 300-2000.
#[test]
fn pan_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "diameter >= 300 && diameter <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "diameter == 1200"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "diameter >= 300 && diameter <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pan diameter 1200mm within 300-2000mm range");
}

/// Batch size in x10 kg (scaled integer), valid range 10-10000 representing 1.0-1000.0 kg.
#[test]
fn batch_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "batch >= 10 && batch <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "batch == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "batch >= 10 && batch <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "batch size 300.0kg (x10=3000) within 1.0-1000.0kg range",
    );
}

/// Spray rate in x10 mL/min (scaled integer), valid range 10-5000 representing 1.0-500.0 mL/min.
#[test]
fn spray_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spray_rate >= 10 && spray_rate <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spray_rate == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spray_rate >= 10 && spray_rate <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray rate 50.0mL/min (x10=500) within 1.0-500.0mL/min range",
    );
}

/// Pan speed in x10 RPM (scaled integer), valid range 10-200 representing 1.0-20.0 RPM.
#[test]
fn pan_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pan_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pan_speed >= 10 && pan_speed <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "pan_speed == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pan_speed >= 10 && pan_speed <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pan speed 8.0RPM (x10=80) within 1.0-20.0RPM range",
    );
}

/// Inlet air temperature as offset+100 in degrees C, valid range 120-500 representing 20-400C.
#[test]
fn inlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "inlet_temp >= 120 && inlet_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "inlet_temp == 380"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "inlet_temp >= 120 && inlet_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet air temp 280C (offset+100=380) within 20-400C range",
    );
}

/// Exhaust temperature as offset+100 in degrees C, valid range 110-300 representing 10-200C.
#[test]
fn exhaust_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exhaust_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "exhaust_temp >= 110 && exhaust_temp <= 300",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "exhaust_temp == 180"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "exhaust_temp >= 110 && exhaust_temp <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "exhaust temp 80C (offset+100=180) within 10-200C range",
    );
}

/// Coating type: 1=sugar, 2=film, 3=enteric.
#[test]
fn coating_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "coating == 1 || coating == 2 || coating == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "coating == 1 || coating == 2 || coating == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "coating type is one of sugar(1), film(2), enteric(3)",
    );
}

/// Pan shape: 1=conventional, 2=perforated, 3=side-vented.
#[test]
fn pan_shape_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shape", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "shape == 1 || shape == 2 || shape == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "shape == 1 || shape == 2 || shape == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pan shape is one of conventional(1), perforated(2), side-vented(3)",
    );
}

/// Spray system: 1=air-spray, 2=airless, 3=electrostatic.
#[test]
fn spray_system_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_sys", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "spray_sys == 1 || spray_sys == 2 || spray_sys == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "spray_sys == 1 || spray_sys == 2 || spray_sys == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray system is one of air-spray(1), airless(2), electrostatic(3)",
    );
}

/// Automatic weight gain monitoring flag: i32 boolean (0 or 1).
/// When flag==1, the if-then-else evaluates to 1.
#[test]
fn automatic_weight_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "weight_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic weight monitoring active when flag is 1");
}
