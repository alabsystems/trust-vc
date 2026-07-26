// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_velocity() {
    let mut ctx = VerificationContext::new();
    for v in &["velocity_cm_s", "max_velocity_cm_s"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vel_ok", i32_ty());
    // Flow velocity in cm/s (Faraday's law: V = B×D×v)
    ctx.push_obligation(ProofObligation::assume("vc", "velocity_cm_s == 300")); // 3 m/s
    ctx.push_obligation(ProofObligation::assume("mv", "max_velocity_cm_s == 1500")); // 15 m/s
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vel_ok == if velocity_cm_s <= max_velocity_cm_s { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: 3 m/s velocity ≤ 15 m/s max → OK");
}

#[test]
fn pipe_diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dn_mm", u32_ty());
    ctx.declare_var_typed("valid_dn", i32_ty());
    // Standard DN sizes in mm
    ctx.push_obligation(ProofObligation::assume("dm", "dn_mm == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dn == if dn_mm == 15 || dn_mm == 25 || dn_mm == 50 || dn_mm == 100 || dn_mm == 150 || dn_mm == 200 || dn_mm == 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: DN100 is valid pipe diameter");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy as % of reading (×100 for 0.01%)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x100 == 100")); // 1.00%
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: 0.50% accuracy ≤ 1.00% max → OK");
}

#[test]
fn excitation_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["excite_hz_x10", "min_excite_hz_x10", "max_excite_hz_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("exc_ok", i32_ty());
    // Coil excitation frequency in Hz (×10 for 0.1 Hz)
    ctx.push_obligation(ProofObligation::assume("ex", "excite_hz_x10 == 62")); // 6.2 Hz
    ctx.push_obligation(ProofObligation::assume("mn", "min_excite_hz_x10 == 30")); // 3.0 Hz
    ctx.push_obligation(ProofObligation::assume("mx", "max_excite_hz_x10 == 250")); // 25.0 Hz
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "exc_ok == if excite_hz_x10 >= min_excite_hz_x10 && excite_hz_x10 <= max_excite_hz_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "exc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: 6.2 Hz excitation in [3.0, 25.0] → OK");
}

#[test]
fn conductivity() {
    let mut ctx = VerificationContext::new();
    for v in &["cond_us_cm", "min_cond_us_cm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cond_ok", i32_ty());
    // Minimum fluid conductivity in μS/cm
    ctx.push_obligation(ProofObligation::assume("cc", "cond_us_cm == 50"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cond_us_cm == 5")); // typical min
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cond_ok == if cond_us_cm >= min_cond_us_cm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cond_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: 50 μS/cm conductivity ≥ 5 min → OK");
}

#[test]
fn liner_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liner", u32_ty());
    ctx.declare_var_typed("valid_liner", i32_ty());
    // Liner materials: 1=PTFE, 2=PFA, 3=rubber, 4=ceramic, 5=polyurethane
    ctx.push_obligation(ProofObligation::assume("l", "liner == 1")); // PTFE
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_liner == if liner == 1 || liner == 2 || liner == 3 || liner == 4 || liner == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_liner == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: PTFE is valid liner material");
}

#[test]
fn electrode_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("electrode", u32_ty());
    ctx.declare_var_typed("valid_elec", i32_ty());
    // Electrode materials: 1=316L SS, 2=Hastelloy C, 3=titanium, 4=tantalum, 5=platinum
    ctx.push_obligation(ProofObligation::assume("e", "electrode == 2")); // Hastelloy
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_elec == if electrode == 1 || electrode == 2 || electrode == 3 || electrode == 4 || electrode == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_elec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: Hastelloy C is valid electrode material");
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "max_pressure_bar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Process pressure rating in bar
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 16"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar <= max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: 16 bar ≤ 40 bar max → OK");
}

#[test]
fn empty_pipe_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["epd_threshold_pct", "min_epd_pct", "max_epd_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("epd_ok", i32_ty());
    // Empty pipe detection threshold as % of full pipe
    ctx.push_obligation(ProofObligation::assume("ep", "epd_threshold_pct == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_epd_pct == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_epd_pct == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "epd_ok == if epd_threshold_pct >= min_epd_pct && epd_threshold_pct <= max_epd_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "epd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: 10% EPD threshold in [1, 50] → OK");
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature (offset +500): -20°C to 180°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 580")); // 80°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 480")); // -20°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 680")); // 180°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MagFlow: 80°C in [-20, 180] → OK");
}
