// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Spark ignition controller properties for industrial burner management systems.
// Models key parameters: ignition energy, spark rate, fuel type, flame detection,
// trial for ignition, safety shutoff, pilot type, supply voltage, operating temp, lockout alarm.

#[test]
fn ignition_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_mj", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "energy_mj >= 1 && energy_mj <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("energy_lower", "energy_mj >= 1"));
    ctx.push_obligation(ProofObligation::assert("energy_upper", "energy_mj <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ignition energy (mJ) bounded [1, 5000]");
}

#[test]
fn spark_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spark_rate_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "spark_rate_hz >= 1 && spark_rate_hz <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert("rate_lower", "spark_rate_hz >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_upper",
        "spark_rate_hz <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spark rate (Hz) bounded [1, 100]");
}

#[test]
fn fuel_type_four_way_disjunction() {
    // 1=natural gas, 2=propane, 3=fuel oil, 4=biogas
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fuel_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fuel_valid",
        "fuel_type == 1 || fuel_type == 2 || fuel_type == 3 || fuel_type == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fuel_in_range",
        "fuel_type >= 1 && fuel_type <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fuel type is one of {natural gas, propane, fuel oil, biogas}",
    );
}

#[test]
fn flame_detection_three_way_disjunction() {
    // 1=UV, 2=ionization, 3=infrared
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_in_range",
        "detector >= 1 && detector <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flame detection is one of {UV, ionization, infrared}",
    );
}

#[test]
fn trial_for_ignition_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trial_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trial_range",
        "trial_s >= 1 && trial_s <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert("trial_lower", "trial_s >= 1"));
    ctx.push_obligation(ProofObligation::assert("trial_upper", "trial_s <= 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trial for ignition (s) bounded [1, 30]");
}

#[test]
fn safety_shutoff_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shutoff_ms", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shutoff_range",
        "shutoff_ms >= 100 && shutoff_ms <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shutoff_lower",
        "shutoff_ms >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shutoff_upper",
        "shutoff_ms <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "safety shutoff time (ms) bounded [100, 5000]");
}

#[test]
fn pilot_type_three_way_disjunction() {
    // 1=standing, 2=intermittent, 3=direct spark
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pilot", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pilot_valid",
        "pilot == 1 || pilot == 2 || pilot == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pilot_in_range",
        "pilot >= 1 && pilot <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pilot type is one of {standing, intermittent, direct spark}",
    );
}

#[test]
fn supply_voltage_bounded() {
    // 20-30V represented in millivolts: [20000, 30000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_mv", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage_mv >= 20000 && voltage_mv <= 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_lower",
        "voltage_mv >= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_upper",
        "voltage_mv <= 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply voltage (mV) bounded [20000, 30000] (20-30V)",
    );
}

#[test]
fn operating_temp_offset_bounded() {
    // Temperature uses offset +500: 20C -> 520.
    // Operating range: -250C to 500C -> offset [250, 1000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_offset >= 250 && temp_offset <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("temp_lower", "temp_offset >= 250"));
    ctx.push_obligation(ProofObligation::assert("temp_upper", "temp_offset <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp (offset +500) bounded [250, 1000]");
}

#[test]
fn lockout_alarm_boolean_flag() {
    // Boolean flag encoded as i32: 0=no alarm, 1=alarm active
    let mut ctx = VerificationContext::new();
    for v in &["lockout", "action"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "lockout_is_flag",
        "lockout == 0 || lockout == 1",
    ));
    // If lockout active (1), action = shut down (1); otherwise action = run (0)
    ctx.push_obligation(ProofObligation::assume(
        "action_def",
        "action == if lockout == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "action_matches_lockout",
        "action == lockout",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lockout alarm boolean flag: action mirrors lockout state",
    );
}
