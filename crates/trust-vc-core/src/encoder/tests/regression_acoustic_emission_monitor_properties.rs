// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_frequency_range() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "freq_min", "freq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AE sensor bandwidth in kHz: value 300, valid range 20 to 1000
    ctx.push_obligation(ProofObligation::assume("fr_val", "freq_khz == 300"));
    ctx.push_obligation(ProofObligation::assume("fr_min", "freq_min == 20"));
    ctx.push_obligation(ProofObligation::assume("fr_max", "freq_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "fr_in_range",
        "freq_khz >= freq_min && freq_khz <= freq_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "AE frequency 300 kHz in sensor bandwidth [20,1000]",
    );
}

#[test]
fn test_channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "ch_min", "ch_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AE sensor input channels: value 16, valid range 1 to 128
    ctx.push_obligation(ProofObligation::assume("cc_val", "channels == 16"));
    ctx.push_obligation(ProofObligation::assume("cc_min", "ch_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cc_max", "ch_max == 128"));
    ctx.push_obligation(ProofObligation::assert(
        "cc_in_range",
        "channels >= ch_min && channels <= ch_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE channel count 16 in range [1,128]");
}

#[test]
fn test_threshold_db() {
    let mut ctx = VerificationContext::new();
    for v in &["thresh_db", "thresh_min", "thresh_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AE detection threshold in dB: value 40, valid range 20 to 80
    ctx.push_obligation(ProofObligation::assume("th_val", "thresh_db == 40"));
    ctx.push_obligation(ProofObligation::assume("th_min", "thresh_min == 20"));
    ctx.push_obligation(ProofObligation::assume("th_max", "thresh_max == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "th_in_range",
        "thresh_db >= thresh_min && thresh_db <= thresh_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE threshold 40 dB in detection range [20,80]");
}

#[test]
fn test_sample_rate_mhz() {
    let mut ctx = VerificationContext::new();
    for v in &["sr_mhz", "sr_min", "sr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AE ADC sample rate in MHz: value 10, valid range 1 to 40
    ctx.push_obligation(ProofObligation::assume("sr_val", "sr_mhz == 10"));
    ctx.push_obligation(ProofObligation::assume("sr_min", "sr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sr_max", "sr_max == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "sr_in_range",
        "sr_mhz >= sr_min && sr_mhz <= sr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE sample rate 10 MHz in ADC range [1,40]");
}

#[test]
fn test_sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor", u32_ty());
    ctx.declare_var_typed("valid_sensor", i32_ty());
    // AE sensor types: 1=resonant, 2=broadband, 3=waveguide
    ctx.push_obligation(ProofObligation::assume("st_val", "sensor == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "valid_sensor == if sensor == 1 || sensor == 2 || sensor == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_chk", "valid_sensor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE sensor type 1 (resonant) is valid");
}

#[test]
fn test_waveform_storage() {
    let mut ctx = VerificationContext::new();
    for v in &["records", "rec_min", "rec_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AE waveform storage capacity in records: value 50000, valid range 1000 to 1000000
    ctx.push_obligation(ProofObligation::assume("ws_val", "records == 50000"));
    ctx.push_obligation(ProofObligation::assume("ws_min", "rec_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("ws_max", "rec_max == 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "ws_in_range",
        "records >= rec_min && records <= rec_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "AE waveform storage 50000 records in range [1000,1000000]",
    );
}

#[test]
fn test_location_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("loc_method", u32_ty());
    ctx.declare_var_typed("valid_loc", i32_ty());
    // AE source location methods: 1=zone, 2=linear, 3=planar
    ctx.push_obligation(ProofObligation::assume("lm_val", "loc_method == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "lm_def",
        "valid_loc == if loc_method == 1 || loc_method == 2 || loc_method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("lm_chk", "valid_loc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE location method 2 (linear) is valid");
}

#[test]
fn test_dynamic_range_db() {
    let mut ctx = VerificationContext::new();
    for v in &["dyn_db", "dyn_min", "dyn_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AE measurement dynamic range in dB: value 90, valid range 60 to 120
    ctx.push_obligation(ProofObligation::assume("dr_val", "dyn_db == 90"));
    ctx.push_obligation(ProofObligation::assume("dr_min", "dyn_min == 60"));
    ctx.push_obligation(ProofObligation::assume("dr_max", "dyn_max == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "dr_in_range",
        "dyn_db >= dyn_min && dyn_db <= dyn_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "AE dynamic range 90 dB in measurement range [60,120]",
    );
}

#[test]
fn test_preamplifier_gain_db() {
    let mut ctx = VerificationContext::new();
    for v in &["gain_db", "gain_min", "gain_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AE preamplifier gain in dB: value 40, valid range 20 to 60
    ctx.push_obligation(ProofObligation::assume("pg_val", "gain_db == 40"));
    ctx.push_obligation(ProofObligation::assume("pg_min", "gain_min == 20"));
    ctx.push_obligation(ProofObligation::assume("pg_max", "gain_max == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "pg_in_range",
        "gain_db >= gain_min && gain_db <= gain_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE preamplifier gain 40 dB in range [20,60]");
}

#[test]
fn test_continuous_monitoring() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("continuous", i32_ty());
    ctx.declare_var_typed("monitoring_active", i32_ty());
    // AE continuous monitoring boolean flag: 1=enabled, 0=disabled
    ctx.push_obligation(ProofObligation::assume("cm_val", "continuous == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "monitoring_active == if continuous == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "monitoring_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AE continuous monitoring enabled (flag=1)");
}
