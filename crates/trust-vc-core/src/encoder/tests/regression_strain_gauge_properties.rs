// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gauge_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["delta_r_x1000", "r_nominal_x1000", "strain_ue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("gauge_factor_x100", u32_ty());
    // GF = (ΔR/R) / ε. Precompute: (2/1000) / (1000/1000000) × 100 = 200 (GF=2.0)
    ctx.push_obligation(ProofObligation::assume("dr", "delta_r_x1000 == 2")); // ΔR/R = 0.002
    ctx.push_obligation(ProofObligation::assume("rn", "r_nominal_x1000 == 1000")); // reference
    ctx.push_obligation(ProofObligation::assume("se", "strain_ue == 1000")); // 1000 microstrain
    ctx.push_obligation(ProofObligation::assume("gf", "gauge_factor_x100 == 200")); // precomputed GF=2.0
    ctx.push_obligation(ProofObligation::assert(
        "is_200",
        "gauge_factor_x100 == 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Strain gauge: GF = 2.0 (precomputed from ΔR/R / ε)",
    );
}

#[test]
fn bridge_output() {
    let mut ctx = VerificationContext::new();
    for v in &["excitation_mv", "strain_ue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_uv", u32_ty());
    // Quarter bridge: Vout ≈ Vex × GF × ε / 4. Precompute: 5000 × 2 × 1000 / 4000000 × 1000000 = 2500μV
    ctx.push_obligation(ProofObligation::assume("em", "excitation_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("se", "strain_ue == 1000"));
    ctx.push_obligation(ProofObligation::assume("ou", "output_uv == 2500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2500", "output_uv == 2500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Strain gauge: 5V × GF2 × 1000με / 4 = 2500μV (precomputed)",
    );
}

#[test]
fn resistance_match() {
    let mut ctx = VerificationContext::new();
    for v in &["gauge_ohms", "nominal_ohms", "tolerance_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("match_ok", i32_ty());
    // Nominal resistance: 120Ω or 350Ω ± tolerance
    ctx.push_obligation(ProofObligation::assume("go", "gauge_ohms == 121"));
    ctx.push_obligation(ProofObligation::assume("no", "nominal_ohms == 120"));
    ctx.push_obligation(ProofObligation::assume("to", "tolerance_ohms == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "match_ok == if gauge_ohms >= nominal_ohms - tolerance_ohms && gauge_ohms <= nominal_ohms + tolerance_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "match_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Strain gauge: 121Ω in [118, 122] → resistance match",
    );
}

#[test]
fn thermal_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_coeff_ppm", "max_temp_coeff_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("compensated", i32_ty());
    // Self-temperature-compensated gauges: low apparent strain from temp
    ctx.push_obligation(ProofObligation::assume("tc", "temp_coeff_ppm == 5"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_coeff_ppm == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compensated == if temp_coeff_ppm <= max_temp_coeff_ppm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "compensated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Strain gauge: 5 ppm/°C ≤ 10 max → temp compensated",
    );
}

#[test]
fn bridge_configuration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("active_arms", u32_ty());
    ctx.declare_var_typed("is_full_bridge", i32_ty());
    // Bridge types: 1=quarter, 2=half, 4=full
    ctx.push_obligation(ProofObligation::assume("aa", "active_arms == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "if_def",
        "is_full_bridge == if active_arms == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_full_bridge == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Strain gauge: 4 active arms → full bridge");
}

#[test]
fn fatigue_life() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_count", "rated_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_life", i32_ty());
    // Fatigue life at ±1500 microstrain: typically 10^7+ cycles
    ctx.push_obligation(ProofObligation::assume("cc", "cycle_count == 5000000"));
    ctx.push_obligation(ProofObligation::assume("rc", "rated_cycles == 10000000"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_life == if cycle_count < rated_cycles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_life == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Strain gauge: 5M cycles < 10M rated → within life");
}

#[test]
fn lead_wire_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["lead_ohms_x10", "max_lead_ohms_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lead_ok", i32_ty());
    // 3-wire compensation: lead resistance should be small vs gauge
    ctx.push_obligation(ProofObligation::assume("lo", "lead_ohms_x10 == 5")); // 0.5Ω
    ctx.push_obligation(ProofObligation::assume("ml", "max_lead_ohms_x10 == 20")); // 2.0Ω
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lead_ok == if lead_ohms_x10 <= max_lead_ohms_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lead_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Strain gauge: 0.5Ω lead ≤ 2.0Ω max → lead OK");
}

#[test]
fn max_strain() {
    let mut ctx = VerificationContext::new();
    for v in &["applied_ue", "max_ue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("strain_ok", i32_ty());
    // Max measurable strain: typically ±3000-5000 microstrain
    ctx.push_obligation(ProofObligation::assume("au", "applied_ue == 2000"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_ue == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "strain_ok == if applied_ue <= max_ue { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "strain_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Strain gauge: 2000με ≤ 5000με max → strain OK");
}

#[test]
fn amplifier_gain() {
    let mut ctx = VerificationContext::new();
    for v in &["input_uv", "gain"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_mv", u32_ty());
    // Instrumentation amp gain. Precompute: 2500μV × 1000 / 1000 = 2500mV
    ctx.push_obligation(ProofObligation::assume("iu", "input_uv == 2500"));
    ctx.push_obligation(ProofObligation::assume("g", "gain == 1000"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 2500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2500", "output_mv == 2500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Strain gauge: 2500μV × 1000 gain = 2500mV (precomputed)",
    );
}

#[test]
fn installation_surface() {
    let mut ctx = VerificationContext::new();
    for v in &["surface_roughness_um", "max_roughness_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("surface_ok", i32_ty());
    // Bonding surface must be smooth for accurate strain transfer
    ctx.push_obligation(ProofObligation::assume("sr", "surface_roughness_um == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_roughness_um == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "surface_ok == if surface_roughness_um <= max_roughness_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "surface_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Strain gauge: 3μm roughness ≤ 10μm max → surface OK",
    );
}
