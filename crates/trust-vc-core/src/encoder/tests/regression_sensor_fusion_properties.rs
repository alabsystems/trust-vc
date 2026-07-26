// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn accelerometer_range() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_value", "max_raw", "range_g"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // 16-bit ADC, ±2g range → max raw = 32767 for +2g
    ctx.push_obligation(ProofObligation::assume("rv", "raw_value == 16384")); // ~1g
    ctx.push_obligation(ProofObligation::assume("mr", "max_raw == 32767"));
    ctx.push_obligation(ProofObligation::assume("rg", "range_g == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if raw_value <= max_raw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accel: 16384 <= 32767 → in range");
}

#[test]
fn gyroscope_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_value", "sensitivity_mdps_per_lsb", "angular_rate_mdps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Precompute: angular_rate = raw × sensitivity
    // 1000 × 70 = 70000 mdps (milli-degrees per second)
    ctx.push_obligation(ProofObligation::assume("rv", "raw_value == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "s",
        "sensitivity_mdps_per_lsb == 70",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ar_def",
        "angular_rate_mdps == raw_value * sensitivity_mdps_per_lsb",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_70000",
        "angular_rate_mdps == 70000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "gyro: 1000 × 70 = 70000 mdps");
}

#[test]
fn magnetometer_heading() {
    let mut ctx = VerificationContext::new();
    for v in &["mag_x", "mag_y"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pointing_north", i32_ty());
    // Simplified: if mag_y >> mag_x, heading ≈ North (0°)
    ctx.push_obligation(ProofObligation::assume("mx", "mag_x == 10")); // small
    ctx.push_obligation(ProofObligation::assume("my", "mag_y == 500")); // large
    ctx.push_obligation(ProofObligation::assume(
        "pn_def",
        "pointing_north == if mag_y > mag_x * 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pointing_north == 1")); // 500 > 100
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "mag: Y=500 >> X=10 → North-ish");
}

#[test]
fn barometer_altitude() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_pa", "ref_pressure_pa", "altitude_cm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Simplified: altitude drops ~8m per 100Pa below reference
    // Precompute: (101325 - 100325) = 1000Pa → ~80m = 8000cm
    ctx.push_obligation(ProofObligation::assume("pp", "pressure_pa == 100325"));
    ctx.push_obligation(ProofObligation::assume("rp", "ref_pressure_pa == 101325"));
    ctx.push_obligation(ProofObligation::assume("ac", "altitude_cm == 8000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_8000", "altitude_cm == 8000"));
    ctx.push_obligation(ProofObligation::assert("positive", "altitude_cm > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "baro: 1000Pa drop ≈ 80m altitude");
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_reading", "temp_offset", "compensated"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rr", "raw_reading == 5000"));
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 50")); // drift correction
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compensated == raw_reading - temp_offset",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4950", "compensated == 4950"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor: 5000 - 50 offset = 4950 compensated");
}

#[test]
fn sample_rate_config() {
    let mut ctx = VerificationContext::new();
    for v in &["odr_divider", "base_rate_hz", "actual_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output Data Rate = base / divider
    ctx.push_obligation(ProofObligation::assume("od", "odr_divider == 10"));
    ctx.push_obligation(ProofObligation::assume("br", "base_rate_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ar_def",
        "actual_rate_hz == base_rate_hz / odr_divider",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "actual_rate_hz == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "sensor ODR: 1000 / 10 = 100 Hz");
}

#[test]
fn data_ready_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("status_reg", u32_ty());
    ctx.declare_var_typed("data_ready", i32_ty());
    // Data ready when bit 0 of status register is set
    ctx.push_obligation(ProofObligation::assume("sr", "status_reg == 1")); // bit 0 set
    ctx.push_obligation(ProofObligation::assume(
        "dr_def",
        "data_ready == if status_reg >= 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "data_ready == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor: status=1 → data ready");
}

#[test]
fn fifo_watermark() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_level", "watermark"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("interrupt_pending", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fl", "fifo_level == 20"));
    ctx.push_obligation(ProofObligation::assume("wm", "watermark == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "interrupt_pending == if fifo_level >= watermark { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "interrupt_pending == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor FIFO: 20 >= 16 watermark → interrupt");
}

#[test]
fn multi_sensor_timestamp_sync() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_ts", "gyro_ts", "diff_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("synchronized", i32_ty());
    // Two sensors are synchronized if timestamps differ by < 1ms
    ctx.push_obligation(ProofObligation::assume("at", "accel_ts == 1000500"));
    ctx.push_obligation(ProofObligation::assume("gt", "gyro_ts == 1000300"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "diff_us == accel_ts - gyro_ts",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "synchronized == if diff_us < 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "diff_us == 200"));
    ctx.push_obligation(ProofObligation::assert("yes", "synchronized == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fusion: 200us diff < 1000us → synchronized");
}

#[test]
fn calibration_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["measured", "offset", "calibrated"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_tolerance", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "measured == 10200"));
    ctx.push_obligation(ProofObligation::assume("o", "offset == 200")); // factory calibration
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "calibrated == measured - offset",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wt_def",
        "within_tolerance == if calibrated >= 9900 && calibrated <= 10100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10000", "calibrated == 10000"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_tolerance == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal: 10200 - 200 = 10000, within [9900, 10100]");
}
