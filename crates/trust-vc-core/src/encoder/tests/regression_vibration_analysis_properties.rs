// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rms_velocity() {
    let mut ctx = VerificationContext::new();
    for v in &["velocity_x100", "max_velocity_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vel_ok", i32_ty());
    // RMS velocity in mm/s (×100 for 0.01 mm/s)
    ctx.push_obligation(ProofObligation::assume("vx", "velocity_x100 == 450")); // 4.50 mm/s
    ctx.push_obligation(ProofObligation::assume("mv", "max_velocity_x100 == 1120")); // 11.20 mm/s (ISO 10816 Zone B)
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vel_ok == if velocity_x100 <= max_velocity_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: 4.50 mm/s RMS ≤ 11.20 max → OK");
}

#[test]
fn peak_acceleration() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_mg", "max_accel_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Peak acceleration in milli-g
    ctx.push_obligation(ProofObligation::assume("am", "accel_mg == 500"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_accel_mg == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accel_mg <= max_accel_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: 500 mg peak ≤ 2000 max → OK");
}

#[test]
fn frequency_range() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Analysis frequency band
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz && freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: 1kHz in [10, 10000] Hz → OK");
}

#[test]
fn iso_severity_zone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zone", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    // ISO 10816 severity zones: 1=A(good), 2=B(acceptable), 3=C(alarm), 4=D(danger)
    ctx.push_obligation(ProofObligation::assume("z", "zone == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "az_def",
        "acceptable == if zone == 1 || zone == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: zone B is acceptable (ISO 10816)");
}

#[test]
fn crest_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["crest_x10", "max_crest_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("crest_ok", i32_ty());
    // Crest factor = peak/RMS (×10, normal ≈ 3.0-4.0)
    ctx.push_obligation(ProofObligation::assume("cx", "crest_x10 == 35")); // 3.5
    ctx.push_obligation(ProofObligation::assume("mc", "max_crest_x10 == 60")); // 6.0 (bearing fault threshold)
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "crest_ok == if crest_x10 <= max_crest_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "crest_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: crest factor 3.5 ≤ 6.0 max → OK");
}

#[test]
fn displacement_peak() {
    let mut ctx = VerificationContext::new();
    for v in &["disp_um", "max_disp_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("disp_ok", i32_ty());
    // Peak-to-peak displacement in micrometers
    ctx.push_obligation(ProofObligation::assume("du", "disp_um == 25"));
    ctx.push_obligation(ProofObligation::assume("md", "max_disp_um == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "disp_ok == if disp_um <= max_disp_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "disp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: 25μm displacement ≤ 100μm max → OK");
}

#[test]
fn fft_lines() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lines", u32_ty());
    ctx.declare_var_typed("valid_lines", i32_ty());
    // FFT resolution: standard line counts
    ctx.push_obligation(ProofObligation::assume("l", "lines == 1600"));
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_lines == if lines == 400 || lines == 800 || lines == 1600 || lines == 3200 || lines == 6400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_lines == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: 1600 FFT lines is valid setting");
}

#[test]
fn window_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("window", u32_ty());
    ctx.declare_var_typed("valid_window", i32_ty());
    // FFT window functions: 1=Hanning, 2=Hamming, 3=Flat-top, 4=Rectangular, 5=Kaiser
    ctx.push_obligation(ProofObligation::assume("w", "window == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vw_def",
        "valid_window == if window == 1 || window == 2 || window == 3 || window == 4 || window == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_window == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: Hanning is valid window function");
}

#[test]
fn averaging_count() {
    let mut ctx = VerificationContext::new();
    for v in &["averages", "min_averages", "max_averages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("avg_ok", i32_ty());
    // Spectral averaging for noise reduction
    ctx.push_obligation(ProofObligation::assume("a", "averages == 8"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_averages == 4"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_averages == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "avg_ok == if averages >= min_averages && averages <= max_averages { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "avg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: 8 averages in [4, 128] → OK");
}

#[test]
fn kurtosis() {
    let mut ctx = VerificationContext::new();
    for v in &["kurt_x10", "max_kurt_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("kurt_ok", i32_ty());
    // Kurtosis (×10, normal distribution ≈ 3.0)
    ctx.push_obligation(ProofObligation::assume("kx", "kurt_x10 == 32")); // 3.2
    ctx.push_obligation(ProofObligation::assume("mk", "max_kurt_x10 == 50")); // 5.0 (fault threshold)
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "kurt_ok == if kurt_x10 <= max_kurt_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "kurt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Vibration: kurtosis 3.2 ≤ 5.0 max → OK");
}
