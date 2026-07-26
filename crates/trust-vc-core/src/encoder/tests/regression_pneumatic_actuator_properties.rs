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
    // Supply air pressure in kPa
    ctx.push_obligation(ProofObligation::assume("pk", "pressure_kpa == 600")); // 6 bar
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure_kpa == 400")); // 4 bar
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure_kpa == 1000")); // 10 bar
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_kpa >= min_pressure_kpa && pressure_kpa <= max_pressure_kpa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: 6 bar supply in [4, 10] → OK");
}

#[test]
fn bore_diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bore_mm", u32_ty());
    ctx.declare_var_typed("valid_bore", i32_ty());
    // Standard bore sizes in mm
    ctx.push_obligation(ProofObligation::assume("bm", "bore_mm == 63"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_bore == if bore_mm == 32 || bore_mm == 40 || bore_mm == 50 || bore_mm == 63 || bore_mm == 80 || bore_mm == 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_bore == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: 63mm is valid bore size");
}

#[test]
fn stroke_length() {
    let mut ctx = VerificationContext::new();
    for v in &["stroke_mm", "max_stroke_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stroke_ok", i32_ty());
    // Piston stroke in mm
    ctx.push_obligation(ProofObligation::assume("sm", "stroke_mm == 200"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_stroke_mm == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stroke_ok == if stroke_mm >= 1 && stroke_mm <= max_stroke_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stroke_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: 200mm stroke in [1, 2000] → OK");
}

#[test]
fn actuator_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("act_type", u32_ty());
    ctx.declare_var_typed("valid_act", i32_ty());
    // Types: 1=single-acting, 2=double-acting, 3=rotary, 4=rodless, 5=guided
    ctx.push_obligation(ProofObligation::assume("at", "act_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_act == if act_type == 1 || act_type == 2 || act_type == 3 || act_type == 4 || act_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_act == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: double-acting is valid type");
}

#[test]
fn cycling_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles_min", "max_cycles_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cyc_ok", i32_ty());
    // Cycles per minute
    ctx.push_obligation(ProofObligation::assume("cm", "cycles_min == 60"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycles_min == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cyc_ok == if cycles_min <= max_cycles_min { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cyc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: 60 cycles/min ≤ 300 max → OK");
}

#[test]
fn piston_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_mm_s", "max_speed_mm_s"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("spd_ok", i32_ty());
    // Piston speed in mm/s
    ctx.push_obligation(ProofObligation::assume("ss", "speed_mm_s == 500"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_speed_mm_s == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "spd_ok == if speed_mm_s <= max_speed_mm_s { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "spd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: 500mm/s piston speed ≤ 3000 max → OK");
}

#[test]
fn cushioning() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cushion", u32_ty());
    ctx.declare_var_typed("valid_cushion", i32_ty());
    // End-of-stroke cushioning: 1=none, 2=rubber bumper, 3=adjustable pneumatic
    ctx.push_obligation(ProofObligation::assume("c", "cushion == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cushion == if cushion == 1 || cushion == 2 || cushion == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cushion == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pneumatic: adjustable pneumatic cushioning is valid",
    );
}

#[test]
fn port_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port", u32_ty());
    ctx.declare_var_typed("valid_port", i32_ty());
    // Port thread sizes (encoded): 1=M5, 2=G1/8, 3=G1/4, 4=G3/8, 5=G1/2
    ctx.push_obligation(ProofObligation::assume("p", "port == 3")); // G1/4
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_port == if port == 1 || port == 2 || port == 3 || port == 4 || port == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_port == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: G1/4 is valid port size");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature (offset +500): -20°C to +80°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 480")); // -20°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 580")); // 80°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: 20°C in [-20, 80] → OK");
}

#[test]
fn endurance_cycles() {
    let mut ctx = VerificationContext::new();
    for v in &["life_million", "min_life_million"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("life_ok", i32_ty());
    // Mechanical lifetime in millions of cycles
    ctx.push_obligation(ProofObligation::assume("lm", "life_million == 30"));
    ctx.push_obligation(ProofObligation::assume("ml", "min_life_million == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if life_million >= min_life_million { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pneumatic: 30M cycles ≥ 10M min → OK");
}
