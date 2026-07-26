// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn transducer_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_mhz_x10", "min_freq_x10", "max_freq_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Ultrasound transducer frequency range (×10 for 0.1MHz resolution)
    ctx.push_obligation(ProofObligation::assume("fm", "freq_mhz_x10 == 50")); // 5.0MHz
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_x10 == 10")); // 1.0MHz
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_x10 == 150")); // 15.0MHz
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_mhz_x10 >= min_freq_x10 && freq_mhz_x10 <= max_freq_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 5.0MHz in [1.0, 15.0] → freq OK");
}

#[test]
fn depth_penetration() {
    let mut ctx = VerificationContext::new();
    for v in &["depth_mm", "max_depth_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth_ok", i32_ty());
    // Imaging depth: higher freq → less penetration
    ctx.push_obligation(ProofObligation::assume("dm", "depth_mm == 150"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth_mm == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if depth_mm <= max_depth_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 150mm depth ≤ 300mm max → OK");
}

#[test]
fn frame_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["fps", "min_fps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Real-time imaging: typically 15-60 fps
    ctx.push_obligation(ProofObligation::assume("f", "fps == 30"));
    ctx.push_obligation(ProofObligation::assume("mf", "min_fps == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if fps >= min_fps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 30fps ≥ 15fps min → rate OK");
}

#[test]
fn beam_focus_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["focus_mm", "min_focus_mm", "max_focus_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("focus_ok", i32_ty());
    // Beam focus depth must be within transducer range
    ctx.push_obligation(ProofObligation::assume("fm", "focus_mm == 80"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_focus_mm == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_focus_mm == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "focus_ok == if focus_mm >= min_focus_mm && focus_mm <= max_focus_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "focus_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: focus 80mm in [10, 200] → OK");
}

#[test]
fn dynamic_range() {
    let mut ctx = VerificationContext::new();
    for v in &["dr_db", "min_dr_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dr_ok", i32_ty());
    // Dynamic range: 50-100dB typical
    ctx.push_obligation(ProofObligation::assume("dd", "dr_db == 80"));
    ctx.push_obligation(ProofObligation::assume("md", "min_dr_db == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dr_ok == if dr_db >= min_dr_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 80dB dynamic range ≥ 50dB min → OK");
}

#[test]
fn tgc_gain() {
    let mut ctx = VerificationContext::new();
    for v in &["gain_db", "max_gain_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("gain_ok", i32_ty());
    // Time-Gain Compensation: compensates for depth attenuation
    ctx.push_obligation(ProofObligation::assume("gd", "gain_db == 40"));
    ctx.push_obligation(ProofObligation::assume("mg", "max_gain_db == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gain_ok == if gain_db <= max_gain_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gain_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 40dB TGC ≤ 60dB max → OK");
}

#[test]
fn doppler_shift() {
    let mut ctx = VerificationContext::new();
    for v in &["shift_hz", "max_shift_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shift_ok", i32_ty());
    // Doppler frequency shift for blood flow measurement
    ctx.push_obligation(ProofObligation::assume("sh", "shift_hz == 5000"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_shift_hz == 20000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "shift_ok == if shift_hz <= max_shift_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 5kHz Doppler shift ≤ 20kHz max → OK");
}

#[test]
fn axial_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_um", "max_resolution_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Axial resolution (lower = better): wavelength/2
    ctx.push_obligation(ProofObligation::assume("ru", "resolution_um == 300"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resolution_um == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_um <= max_resolution_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasound: 300μm axial resolution ≤ 500μm max → OK",
    );
}

#[test]
fn transmit_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "max_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Acoustic output power (safety limits per FDA)
    ctx.push_obligation(ProofObligation::assume("pm", "power_mw == 200"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_mw == 720"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_mw <= max_power_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 200mW transmit ≤ 720mW FDA limit → OK");
}

#[test]
fn scan_lines() {
    let mut ctx = VerificationContext::new();
    for v in &["lines", "min_lines"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lines_ok", i32_ty());
    // Number of scan lines per frame (image quality)
    ctx.push_obligation(ProofObligation::assume("l", "lines == 128"));
    ctx.push_obligation(ProofObligation::assume("ml", "min_lines == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lines_ok == if lines >= min_lines { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lines_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasound: 128 scan lines ≥ 64 min → OK");
}
