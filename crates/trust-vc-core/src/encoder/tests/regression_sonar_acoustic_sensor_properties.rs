// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn operating_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Sonar operating frequency (kHz)
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 200kHz in [20, 1000] → freq OK");
}

#[test]
fn beam_width() {
    let mut ctx = VerificationContext::new();
    for v in &["beam_x10", "min_beam_x10", "max_beam_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("beam_ok", i32_ty());
    // Beam width in degrees (×10 for 0.1° resolution)
    ctx.push_obligation(ProofObligation::assume("bx", "beam_x10 == 120")); // 12.0°
    ctx.push_obligation(ProofObligation::assume("mn", "min_beam_x10 == 10")); // 1.0°
    ctx.push_obligation(ProofObligation::assume("mx", "max_beam_x10 == 600")); // 60.0°
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "beam_ok == if beam_x10 >= min_beam_x10 && beam_x10 <= max_beam_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "beam_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 12.0° beam width in [1.0, 60.0] → OK");
}

#[test]
fn detection_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_m", "max_range_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Maximum detection range (meters)
    ctx.push_obligation(ProofObligation::assume("rm", "range_m == 500"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_range_m == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_m <= max_range_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 500m range ≤ 2000m max → OK");
}

#[test]
fn pulse_length() {
    let mut ctx = VerificationContext::new();
    for v in &["pulse_us", "min_pulse_us", "max_pulse_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pulse_ok", i32_ty());
    // Transmit pulse length (μs)
    ctx.push_obligation(ProofObligation::assume("pu", "pulse_us == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pulse_us == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pulse_us == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pulse_ok == if pulse_us >= min_pulse_us && pulse_us <= max_pulse_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pulse_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 500μs pulse in [10, 5000] → OK");
}

#[test]
fn tvg_gain() {
    let mut ctx = VerificationContext::new();
    for v in &["tvg_db", "max_tvg_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tvg_ok", i32_ty());
    // Time-Varied Gain: compensates for spreading/absorption losses
    ctx.push_obligation(ProofObligation::assume("td", "tvg_db == 40"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tvg_db == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tvg_ok == if tvg_db <= max_tvg_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tvg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 40dB TVG ≤ 80dB max → OK");
}

#[test]
fn noise_floor() {
    let mut ctx = VerificationContext::new();
    for v in &["noise_db", "max_noise_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("noise_ok", i32_ty());
    // Ambient noise floor (lower is better)
    ctx.push_obligation(ProofObligation::assume("nd", "noise_db == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_noise_db == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "noise_ok == if noise_db <= max_noise_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "noise_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 50dB noise ≤ 80dB max → OK");
}

#[test]
fn target_strength() {
    let mut ctx = VerificationContext::new();
    for v in &["ts_db", "min_ts_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ts_ok", i32_ty());
    // Target strength: echo return level (higher = easier detection)
    ctx.push_obligation(ProofObligation::assume("td", "ts_db == 30"));
    ctx.push_obligation(ProofObligation::assume("mt", "min_ts_db == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "ts_ok == if ts_db >= min_ts_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ts_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 30dB target strength ≥ 10dB min → OK");
}

#[test]
fn ping_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["pings_per_sec", "max_pps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ping_ok", i32_ty());
    // Ping repetition rate (limited by round-trip time)
    ctx.push_obligation(ProofObligation::assume("ps", "pings_per_sec == 10"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pps == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "ping_ok == if pings_per_sec <= max_pps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ping_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 10 pings/s ≤ 50 max → OK");
}

#[test]
fn blanking_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["blank_mm", "max_blank_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("blank_ok", i32_ty());
    // Near-field blanking: minimum detectable distance
    ctx.push_obligation(ProofObligation::assume("bm", "blank_mm == 300"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_blank_mm == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "blank_ok == if blank_mm <= max_blank_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blank_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Sonar: 300mm blanking ≤ 1000mm max → OK");
}

#[test]
fn speed_of_sound() {
    let mut ctx = VerificationContext::new();
    for v in &["sos_mps", "min_sos_mps", "max_sos_mps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sos_ok", i32_ty());
    // Speed of sound in water: ~1450-1550 m/s (temperature dependent)
    ctx.push_obligation(ProofObligation::assume("sm", "sos_mps == 1500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_sos_mps == 1450"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_sos_mps == 1550"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sos_ok == if sos_mps >= min_sos_mps && sos_mps <= max_sos_mps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sos_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Sonar: 1500 m/s in [1450, 1550] → speed of sound OK",
    );
}
