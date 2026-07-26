// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache 2.0 License.
//
// Regression tests: magnetic sector mass spectrometer properties.

use super::*;

#[test]
fn test_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_amu", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_amu >= 500 && max_amu <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "max_amu == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "max_amu >= 500 && max_amu <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range bounded within 500-10000 amu");
}

#[test]
fn test_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolving_power", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resolving_power >= 1000 && resolving_power <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resolving_power == 60000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "resolving_power >= 1000 && resolving_power <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolving power bounded within 1000-100000");
}

#[test]
fn test_sensitivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counts_per_fg", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "counts_per_fg >= 1 && counts_per_fg <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "counts_per_fg == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "counts_per_fg >= 1 && counts_per_fg <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity bounded within 1-10000 counts/fg");
}

#[test]
fn test_accelerating_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kv", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "kv >= 1 && kv <= 10"));
    ctx.push_obligation(ProofObligation::assume("val", "kv == 8"));
    ctx.push_obligation(ProofObligation::assert("bounded", "kv >= 1 && kv <= 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accelerating voltage bounded within 1-10 kV");
}

#[test]
fn test_magnet_radius_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("radius_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "radius_x10 >= 100 && radius_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "radius_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "radius_x10 >= 100 && radius_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnet radius x10 bounded within 100-1000 (50.0 cm)",
    );
}

#[test]
fn test_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decades", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "decades >= 5 && decades <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "decades == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "decades >= 5 && decades <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range bounded within 5-12 decades");
}

#[test]
fn test_geometry_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geometry", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geometry is single-focusing, double-focusing, or Nier-Johnson",
    );
}

#[test]
fn test_source_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "source type is EI, FAB, or TIMS");
}

#[test]
fn test_collector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "collector == 1 || collector == 2 || collector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "collector == 1 || collector == 2 || collector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collector type is single, multi-collector, or focal-plane",
    );
}

#[test]
fn test_high_resolution_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_high_res", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "high resolution flag implies conditional evaluates to 1",
    );
}
