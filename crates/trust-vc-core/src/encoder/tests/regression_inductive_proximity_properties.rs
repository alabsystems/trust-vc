// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sensing_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["distance_mm_x10", "rated_sn_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dist_ok", i32_ty());
    // Rated sensing distance Sn (×10 for 0.1mm)
    ctx.push_obligation(ProofObligation::assume("dx", "distance_mm_x10 == 40")); // 4.0mm
    ctx.push_obligation(ProofObligation::assume("rs", "rated_sn_x10 == 50")); // 5.0mm
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dist_ok == if distance_mm_x10 <= rated_sn_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dist_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: 4.0mm distance ≤ 5.0mm Sn → OK");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("out_type", u32_ty());
    ctx.declare_var_typed("valid_out", i32_ty());
    // Output types: 1=NPN-NO, 2=NPN-NC, 3=PNP-NO, 4=PNP-NC, 5=push-pull
    ctx.push_obligation(ProofObligation::assume("ot", "out_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_out == if out_type == 1 || out_type == 2 || out_type == 3 || out_type == 4 || out_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: PNP-NO is valid output type");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Maximum switching frequency
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 2000"));
    ctx.push_obligation(ProofObligation::assume("mf", "min_freq_hz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: 2000Hz switching ≥ 500Hz min → OK");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_supply_mv", "max_supply_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sup_ok", i32_ty());
    // DC supply voltage range (10-30V typical)
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 24000")); // 24V
    ctx.push_obligation(ProofObligation::assume("mn", "min_supply_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_supply_mv == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sup_ok == if supply_mv >= min_supply_mv && supply_mv <= max_supply_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sup_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: 24V supply in [10, 30] → OK");
}

#[test]
fn correction_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["cf_x100", "min_cf_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cf_ok", i32_ty());
    // Material correction factor (×100, steel=1.00, aluminum≈0.40)
    ctx.push_obligation(ProofObligation::assume("cx", "cf_x100 == 100")); // 1.00 (steel)
    ctx.push_obligation(ProofObligation::assume("mc", "min_cf_x100 == 30")); // 0.30
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cf_ok == if cf_x100 >= min_cf_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: steel CF 1.00 ≥ 0.30 min → OK");
}

#[test]
fn repeat_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["repeat_um", "max_repeat_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rep_ok", i32_ty());
    // Repeat accuracy in micrometers
    ctx.push_obligation(ProofObligation::assume("ru", "repeat_um == 10"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_repeat_um == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rep_ok == if repeat_um <= max_repeat_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rep_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: 10μm repeat accuracy ≤ 50μm max → OK");
}

#[test]
fn housing_diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.declare_var_typed("valid_dia", i32_ty());
    // Standard housing sizes in mm
    ctx.push_obligation(ProofObligation::assume("dm", "diameter_mm == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dia == if diameter_mm == 4 || diameter_mm == 8 || diameter_mm == 12 || diameter_mm == 18 || diameter_mm == 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dia == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: M12 is valid housing size");
}

#[test]
fn protection_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["ip_rating", "min_ip_rating"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ip_ok", i32_ty());
    // IP rating: 67 = IP67, 68 = IP68, 69 = IP69K
    ctx.push_obligation(ProofObligation::assume("ir", "ip_rating == 67"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_ip_rating == 67"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "ip_ok == if ip_rating >= min_ip_rating { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ip_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: IP67 ≥ IP67 min → OK");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temp: -25°C to +70°C (offset +500 → 475 to 570)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525")); // 25°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 475")); // -25°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 570")); // 70°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: 25°C in [-25, 70] → temp OK");
}

#[test]
fn current_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cur_ok", i32_ty());
    // Quiescent current draw
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 8"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ma == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cur_ok == if current_ma <= max_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cur_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inductive: 8mA current ≤ 15mA max → OK");
}
