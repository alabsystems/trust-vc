// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tube_voltage_within_operating_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_kv", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("kv", "tube_kv == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if tube_kv >= 10 && tube_kv <= 60 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: tube voltage 40kV within 10-60kV range");
}

#[test]
fn tube_current_scaled_precision() {
    // Current in ×10 units: 25 = 2.5 mA
    let mut ctx = VerificationContext::new();
    for v in &["current_x10", "min_x10", "max_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "current_x10 == 25")); // 2.5 mA
    ctx.push_obligation(ProofObligation::assume("lo", "min_x10 == 1")); // 0.1 mA
    ctx.push_obligation(ProofObligation::assume("hi", "max_x10 == 500")); // 50.0 mA
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if current_x10 >= min_x10 && current_x10 <= max_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "XRF: tube current 2.5mA (×10=25) within 0.1-50.0mA",
    );
}

#[test]
fn element_atomic_number_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atomic_num", u32_ty());
    ctx.declare_var_typed("detectable", i32_ty());
    // Iron (Fe) = 26, within beryllium (4) to uranium (92)
    ctx.push_obligation(ProofObligation::assume("z", "atomic_num == 26"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "detectable == if atomic_num >= 4 && atomic_num <= 92 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "detectable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: Fe (Z=26) within detectable range 4-92");
}

#[test]
fn detection_limit_scaled_ppm() {
    // Detection limit in ×10 units: 5 = 0.5 ppm
    let mut ctx = VerificationContext::new();
    for v in &["det_limit_x10", "concentration_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("above_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dl", "det_limit_x10 == 5")); // 0.5 ppm
    ctx.push_obligation(ProofObligation::assume("conc", "concentration_x10 == 120")); // 12.0 ppm
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "above_limit == if concentration_x10 >= det_limit_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "above_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "XRF: 12.0ppm (×10=120) above detection limit 0.5ppm (×10=5)",
    );
}

#[test]
fn measurement_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_time_s", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "meas_time_s == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if meas_time_s >= 5 && meas_time_s <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: measurement time 60s within 5-300s range");
}

#[test]
fn excitation_source_valid() {
    // 1=rhodium, 2=silver, 3=molybdenum
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "source == 2")); // silver anode
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "XRF: excitation source silver (2) is valid {Rh,Ag,Mo}",
    );
}

#[test]
fn detector_type_valid() {
    // 1=SDD, 2=proportional counter, 3=scintillation
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "detector == 1")); // SDD
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: detector SDD (1) is valid {SDD,PC,scint}");
}

#[test]
fn analysis_mode_valid() {
    // 1=WDXRF, 2=EDXRF, 3=TXRF
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "mode == 3")); // TXRF
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: analysis mode TXRF (3) is valid {WD,ED,TX}");
}

#[test]
fn sample_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if capacity >= 1 && capacity <= 48 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: sample capacity 24 within 1-48 range");
}

#[test]
fn helium_purge_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("he_purge", i32_ty());
    ctx.declare_var_typed("light_element_mode", i32_ty());
    // Helium purge enabled for light element analysis
    ctx.push_obligation(ProofObligation::assume("hp", "he_purge == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "lem_def",
        "light_element_mode == if he_purge == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "enabled",
        "light_element_mode == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "XRF: helium purge on → light element mode enabled");
}
