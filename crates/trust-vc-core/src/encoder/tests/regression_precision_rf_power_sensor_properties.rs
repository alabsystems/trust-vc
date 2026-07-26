// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_rf_power_sensor_frequency_range_bounded() {
    // Frequency in MHz: valid range 1–110000, assume 50000 MHz
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("freq", "freq_mhz == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if freq_mhz >= 1 && freq_mhz <= 110000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rf power sensor: 50000 MHz in [1, 110000]");
}

#[test]
fn test_rf_power_sensor_power_range_offset_bounded() {
    // Power with +200 dBm offset: -30 dBm=170, +20 dBm=220; valid range 100–300, assume 220
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_offset", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr", "power_offset == 220"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if power_offset >= 100 && power_offset <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rf power sensor: power offset 220 (+20 dBm) in [100, 300]",
    );
}

#[test]
fn test_rf_power_sensor_accuracy_scaled_thousandths() {
    // Accuracy as % x1000: 50 = 0.050%; valid range 1–1000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc", "accuracy_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if accuracy_x1000 >= 1 && accuracy_x1000 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rf power sensor: accuracy 0.050% (50) in [1, 1000]",
    );
}

#[test]
fn test_rf_power_sensor_dynamic_range_bounded() {
    // Dynamic range in dB: valid range 10–100, assume 80 dB
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range_db", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dr", "dynamic_range_db == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if dynamic_range_db >= 10 && dynamic_range_db <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rf power sensor: dynamic range 80 dB in [10, 100]");
}

#[test]
fn test_rf_power_sensor_rise_time_scaled_hundredths() {
    // Rise time in ns x100: 50 = 0.50 ns; valid range 1–10000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rise_time_x100", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt", "rise_time_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if rise_time_x100 >= 1 && rise_time_x100 <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rf power sensor: rise time 0.50 ns (50) in [1, 10000]",
    );
}

#[test]
fn test_rf_power_sensor_path_count_bounded() {
    // Number of measurement paths: valid range 1–4, assume 2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("paths", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "paths == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if paths >= 1 && paths <= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rf power sensor: 2 paths in [1, 4]");
}

#[test]
fn test_rf_power_sensor_sensor_type_selection() {
    // 1=thermocouple, 2=diode, 3=thermistor; assume diode
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rf power sensor: sensor type diode (2) valid");
}

#[test]
fn test_rf_power_sensor_measurement_mode_selection() {
    // 1=average, 2=peak, 3=time-gated; assume average
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mm", "meas_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if meas_mode == 1 || meas_mode == 2 || meas_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rf power sensor: measurement mode average (1) valid",
    );
}

#[test]
fn test_rf_power_sensor_connector_type_selection() {
    // 1=N-type, 2=SMA, 3=waveguide; assume SMA
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("connector_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "connector_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if connector_type == 1 || connector_type == 2 || connector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rf power sensor: connector SMA (2) valid");
}

#[test]
fn test_rf_power_sensor_internal_zero_calibration_flag() {
    // Boolean flag: 1=internal zero calibration enabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zero_cal", i32_ty());
    ctx.declare_var_typed("cal_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("zc", "zero_cal == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "cal_active == if zero_cal == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "cal_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rf power sensor: internal zero calibration enabled",
    );
}
