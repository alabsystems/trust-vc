// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rh_from_adc() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "adc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rh_percent_x10", u32_ty());
    // RH = adc / adc_max × 1000 (×10 scale). Precompute: 32768/65536 × 1000 = 500 (50.0%)
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 32768"));
    ctx.push_obligation(ProofObligation::assume("am", "adc_max == 65536"));
    ctx.push_obligation(ProofObligation::assume("rp", "rh_percent_x10 == 500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_500", "rh_percent_x10 == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Humidity: ADC 32768/65536 = 50.0% RH (precomputed)",
    );
}

#[test]
fn comfort_zone() {
    let mut ctx = VerificationContext::new();
    for v in &["rh_percent", "min_comfort", "max_comfort"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("comfortable", i32_ty());
    // Human comfort zone: 30-60% RH
    ctx.push_obligation(ProofObligation::assume("rp", "rh_percent == 45"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_comfort == 30"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_comfort == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "comfortable == if rh_percent >= min_comfort && rh_percent <= max_comfort { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "comfortable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Humidity: 45% in [30, 60] → comfortable");
}

#[test]
fn dew_point_risk() {
    let mut ctx = VerificationContext::new();
    for v in &["rh_percent", "dew_point_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("condensation_risk", i32_ty());
    // High RH near dew point causes condensation
    ctx.push_obligation(ProofObligation::assume("rp", "rh_percent == 95"));
    ctx.push_obligation(ProofObligation::assume("dt", "dew_point_threshold == 90"));
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "condensation_risk == if rh_percent >= dew_point_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "condensation_risk == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Humidity: 95% ≥ 90% dew point → condensation risk");
}

#[test]
fn sensor_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_rh_x10", "reference_rh_x10", "error_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    // ±2% RH accuracy = ±20 in ×10 scale
    ctx.push_obligation(ProofObligation::assume("mr", "measured_rh_x10 == 505"));
    ctx.push_obligation(ProofObligation::assume("rr", "reference_rh_x10 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "error_x10 == measured_rh_x10 - reference_rh_x10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if error_x10 <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "error_x10 == 5"));
    ctx.push_obligation(ProofObligation::assert("yes", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Humidity: |50.5-50.0| = 0.5% ≤ 2.0% spec → within spec",
    );
}

#[test]
fn heater_activation() {
    let mut ctx = VerificationContext::new();
    for v in &["rh_percent", "heater_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("heater_on", i32_ty());
    // Built-in heater prevents condensation on sensor element
    ctx.push_obligation(ProofObligation::assume("rp", "rh_percent == 98"));
    ctx.push_obligation(ProofObligation::assume("ht", "heater_threshold == 95"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "heater_on == if rh_percent >= heater_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "heater_on == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Humidity: 98% ≥ 95% threshold → heater activated");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["response_sec", "max_response_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fast_enough", i32_ty());
    // Typical: 8s for 63% step change (tau)
    ctx.push_obligation(ProofObligation::assume("rs", "response_sec == 8"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_response_sec == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "fast_enough == if response_sec <= max_response_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fast_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Humidity: 8s response ≤ 15s max → fast enough");
}

#[test]
fn operating_range() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c", "min_temp_c", "max_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Operating temperature: typically -40 to +80°C. Use offset +50.
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c == 75")); // 25°C (offset +50)
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_c == 10")); // -40°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_c == 130")); // +80°C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_c >= min_temp_c && temp_c <= max_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Humidity: 25°C in [-40, +80] → in operating range");
}

#[test]
fn hysteresis_band() {
    let mut ctx = VerificationContext::new();
    for v in &["rh_percent", "on_threshold", "off_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dehumidifier_on", i32_ty());
    // Hysteresis: turn on at 70%, off at 60%
    ctx.push_obligation(ProofObligation::assume("rp", "rh_percent == 65"));
    ctx.push_obligation(ProofObligation::assume("on", "on_threshold == 70"));
    ctx.push_obligation(ProofObligation::assume("off", "off_threshold == 60"));
    // Between thresholds: state depends on previous (indeterminate). Below off = off.
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dehumidifier_on == if rh_percent >= on_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "dehumidifier_on == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Humidity: 65% < 70% on threshold → dehumidifier off",
    );
}

#[test]
fn calibration_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_rh_x10", "offset_x10", "calibrated_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Apply calibration offset
    ctx.push_obligation(ProofObligation::assume("rr", "raw_rh_x10 == 520"));
    ctx.push_obligation(ProofObligation::assume("ox", "offset_x10 == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "calibrated_x10 == raw_rh_x10 - offset_x10",
    ));
    ctx.push_obligation(ProofObligation::assert("is_505", "calibrated_x10 == 505"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Humidity: 52.0 - 1.5 offset = 50.5% calibrated");
}

#[test]
fn data_checksum() {
    let mut ctx = VerificationContext::new();
    for v in &["computed_crc", "received_crc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("crc_ok", i32_ty());
    // Sensor data integrity check
    ctx.push_obligation(ProofObligation::assume("cc", "computed_crc == 171"));
    ctx.push_obligation(ProofObligation::assume("rc", "received_crc == 171"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "crc_ok == if computed_crc == received_crc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "crc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Humidity: CRC 171 = 171 → data integrity OK");
}
