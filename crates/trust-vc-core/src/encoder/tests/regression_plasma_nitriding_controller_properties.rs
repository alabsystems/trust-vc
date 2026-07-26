// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_c", u32_ty());
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Plasma nitriding process temperature bounded [350, 600] °C
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c == 480"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c >= 350 && temp_c <= 600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Plasma nitriding: 480°C in [350, 600] → OK");
}

#[test]
fn voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_v", u32_ty());
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Glow discharge voltage bounded [200, 1000] V
    ctx.push_obligation(ProofObligation::assume("vv", "voltage_v == 650"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_v >= 200 && voltage_v <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Plasma nitriding: 650V in [200, 1000] → OK");
}

#[test]
fn pulse_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_hz", u32_ty());
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Pulse frequency bounded [100, 100000] Hz
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= 100 && freq_hz <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Plasma nitriding: 5000Hz in [100, 100000] → OK");
}

#[test]
fn gas_ratio_n2() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n2_ratio_x10", u32_ty());
    ctx.declare_var_typed("ratio_ok", i32_ty());
    // Gas ratio N2 scaled ×10 percent: e.g., 25.0% → 250, bounded [0, 1000]
    ctx.push_obligation(ProofObligation::assume("nr", "n2_ratio_x10 == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ratio_ok == if n2_ratio_x10 >= 0 && n2_ratio_x10 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ratio_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Plasma nitriding: N2 ratio 25.0% (250 ×10) in [0, 1000] → OK",
    );
}

#[test]
fn chamber_pressure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_pa", u32_ty());
    ctx.declare_var_typed("pres_ok", i32_ty());
    // Chamber pressure bounded [50, 1000] Pa
    ctx.push_obligation(ProofObligation::assume("pp", "pressure_pa == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pres_ok == if pressure_pa >= 50 && pressure_pa <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pres_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Plasma nitriding: 300Pa in [50, 1000] → OK");
}

#[test]
fn process_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_min", u32_ty());
    ctx.declare_var_typed("time_ok", i32_ty());
    // Process time bounded [60, 4800] minutes (1–80 hours)
    ctx.push_obligation(ProofObligation::assume("tm", "time_min == 720"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "time_ok == if time_min >= 60 && time_min <= 4800 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "time_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Plasma nitriding: 720min in [60, 4800] → OK");
}

#[test]
fn gas_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", u32_ty());
    ctx.declare_var_typed("valid_gas", i32_ty());
    // Gas type: 1=N2+H2, 2=N2+NH3, 3=N2+CH4
    ctx.push_obligation(ProofObligation::assume("g", "gas == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vg_def",
        "valid_gas == if gas == 1 || gas == 2 || gas == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_gas == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Plasma nitriding: N2+H2 is valid gas mixture");
}

#[test]
fn case_depth() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x10mm", u32_ty());
    ctx.declare_var_typed("depth_ok", i32_ty());
    // Case depth scaled ×10 mm: e.g., 0.3 mm → 3, bounded [1, 50]
    ctx.push_obligation(ProofObligation::assume("dx", "depth_x10mm == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if depth_x10mm >= 1 && depth_x10mm <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Plasma nitriding: case depth 0.3mm (3 ×10) in [1, 50] → OK",
    );
}

#[test]
fn power_supply_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("supply", u32_ty());
    ctx.declare_var_typed("valid_supply", i32_ty());
    // Power supply: 1=DC, 2=pulsed DC, 3=AC
    ctx.push_obligation(ProofObligation::assume("s", "supply == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_supply == if supply == 1 || supply == 2 || supply == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_supply == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Plasma nitriding: pulsed DC is valid power supply");
}

#[test]
fn arc_suppression_boolean_flag() {
    // Boolean flag encoded as i32: 0=arc suppression off, 1=arc suppression on
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("arc_flag", i32_ty());
    ctx.declare_var_typed("protection_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "arc_flag == 0 || arc_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "prot_def",
        "protection_active == if arc_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "protection_matches_flag",
        "protection_active == arc_flag",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "arc suppression flag propagates to protection status correctly",
    );
}
