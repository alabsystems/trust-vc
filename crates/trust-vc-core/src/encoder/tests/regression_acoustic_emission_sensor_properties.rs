// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frequency_range_low() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_low_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_low_ok", i32_ty());
    // Lower frequency bound of AE sensor in kHz
    ctx.push_obligation(ProofObligation::assume("fl", "freq_low_khz == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "flo_def",
        "freq_low_ok == if freq_low_khz >= min_freq_khz && freq_low_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_low_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: 20 kHz lower freq in [1, 500] -> OK");
}

#[test]
fn frequency_range_high() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_high_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_high_ok", i32_ty());
    // Upper frequency bound of AE sensor in kHz
    ctx.push_obligation(ProofObligation::assume("fh", "freq_high_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "fho_def",
        "freq_high_ok == if freq_high_khz >= min_freq_khz && freq_high_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_high_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: 1000 kHz upper freq in [100, 2000] -> OK");
}

#[test]
fn sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["sens_offset", "min_sens_offset", "max_sens_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sens_ok", i32_ty());
    // Sensitivity in dB (ref: 1V/ubar), negative values use offset +100
    // Actual -65 dB -> offset 35, range -80 dB (20) to -40 dB (60)
    ctx.push_obligation(ProofObligation::assume("so", "sens_offset == 35")); // -65 dB
    ctx.push_obligation(ProofObligation::assume("mn", "min_sens_offset == 20")); // -80 dB
    ctx.push_obligation(ProofObligation::assume("mx", "max_sens_offset == 60")); // -40 dB
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sens_ok == if sens_offset >= min_sens_offset && sens_offset <= max_sens_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sens_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "AE: -65 dB sensitivity in [-80, -40] (offset +100) -> OK",
    );
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Sensor types: 1=resonant, 2=broadband, 3=differential, 4=integral preamp
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 || sensor_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: resonant (1) is valid sensor type");
}

#[test]
fn threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["threshold_db", "min_threshold_db", "max_threshold_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("thresh_ok", i32_ty());
    // Detection threshold in dB above noise floor
    ctx.push_obligation(ProofObligation::assume("td", "threshold_db == 40"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_threshold_db == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_threshold_db == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "thresh_ok == if threshold_db >= min_threshold_db && threshold_db <= max_threshold_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thresh_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: 40 dB threshold in [20, 80] -> OK");
}

#[test]
fn sample_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_rate_mhz", "min_rate_mhz", "max_rate_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // ADC sample rate in MHz
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_mhz == 5"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate_mhz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate_mhz == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if sample_rate_mhz >= min_rate_mhz && sample_rate_mhz <= max_rate_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: 5 MHz sample rate in [1, 40] -> OK");
}

#[test]
fn dynamic_range() {
    let mut ctx = VerificationContext::new();
    for v in &["dyn_range_db", "min_dyn_db", "max_dyn_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dyn_ok", i32_ty());
    // Dynamic range in dB
    ctx.push_obligation(ProofObligation::assume("dr", "dyn_range_db == 90"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_dyn_db == 60"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_dyn_db == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dyn_ok == if dyn_range_db >= min_dyn_db && dyn_range_db <= max_dyn_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dyn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: 90 dB dynamic range in [60, 120] -> OK");
}

#[test]
fn preamplifier_gain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain_db", u32_ty());
    ctx.declare_var_typed("gain_ok", i32_ty());
    // Preamplifier gain: valid settings are 20, 40, or 60 dB
    ctx.push_obligation(ProofObligation::assume("gd", "gain_db == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gain_ok == if gain_db == 20 || gain_db == 40 || gain_db == 60 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gain_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: 40 dB preamp gain is valid (20/40/60)");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature: offset +500, actual 20 C -> 520, range -40 C (460) to 180 C (680)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20 C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460")); // -40 C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 680")); // 180 C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "AE: 20 C operating temp in [-40, 180] (offset +500) -> OK",
    );
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_ok", i32_ty());
    // AE acquisition channel count
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 16"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_channels == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_channels == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ch_ok == if channels >= min_channels && channels <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE: 16 channels in [1, 128] -> OK");
}
