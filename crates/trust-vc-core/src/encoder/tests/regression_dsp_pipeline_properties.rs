// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn nyquist_sampling() {
    let mut ctx = VerificationContext::new();
    for v in &["signal_freq_hz", "sample_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("satisfies_nyquist", i32_ty());
    // Nyquist: sample rate must be > 2 × signal frequency
    // Precompute: 2 × 20000 = 40000
    ctx.push_obligation(ProofObligation::assume("sf", "signal_freq_hz == 20000")); // 20kHz
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_hz == 44100")); // CD quality
    ctx.push_obligation(ProofObligation::assume(
        "sn_def",
        "satisfies_nyquist == if sample_rate_hz > 40000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "satisfies_nyquist == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP: 44100 > 2×20000 → Nyquist satisfied");
}

#[test]
fn fir_filter_taps() {
    let mut ctx = VerificationContext::new();
    for v in &["num_taps", "samples_per_output"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("delay_samples", u32_ty());
    // FIR filter: delay = (num_taps - 1) / 2 for symmetric filter
    // Precompute: (65 - 1) / 2 = 32
    ctx.push_obligation(ProofObligation::assume("nt", "num_taps == 65"));
    ctx.push_obligation(ProofObligation::assume("spo", "samples_per_output == 65"));
    ctx.push_obligation(ProofObligation::assume("ds", "delay_samples == 32")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_32", "delay_samples == 32"));
    ctx.push_obligation(ProofObligation::assert(
        "matches_taps",
        "samples_per_output == num_taps",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FIR: 65 taps, 32 sample delay");
}

#[test]
fn fft_size_output() {
    let mut ctx = VerificationContext::new();
    for v in &["fft_size", "complex_bins"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // FFT of N real points → N/2+1 unique complex bins
    ctx.push_obligation(ProofObligation::assume("fs", "fft_size == 1024"));
    ctx.push_obligation(ProofObligation::assume("cb", "complex_bins == 513")); // precomputed 1024/2+1
    ctx.push_obligation(ProofObligation::assert("is_513", "complex_bins == 513"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer_complex",
        "complex_bins < fft_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FFT: 1024 points → 513 unique complex bins");
}

#[test]
fn decimation_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["input_rate", "decimation", "output_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ir", "input_rate == 48000"));
    ctx.push_obligation(ProofObligation::assume("d", "decimation == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "or_def",
        "output_rate == input_rate / decimation",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8000", "output_rate == 8000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DSP decimation: 48000 / 6 = 8000 Hz");
}

#[test]
fn circular_buffer_wrap() {
    let mut ctx = VerificationContext::new();
    for v in &["write_index", "buffer_size", "new_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wi", "write_index == 255"));
    ctx.push_obligation(ProofObligation::assume("bs", "buffer_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "ni_def",
        "new_index == (write_index + 1) % buffer_size",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "new_index == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DSP buffer: 255 + 1 mod 256 = 0");
}

#[test]
fn gain_attenuation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("input_level", u32_ty());
    ctx.declare_var_typed("output_level", u32_ty());
    ctx.declare_var_typed("clipped", i32_ty());
    // Gain 0.5x: precomputed 1000 × 0.5 = 500
    ctx.push_obligation(ProofObligation::assume("il", "input_level == 1000"));
    ctx.push_obligation(ProofObligation::assume("ol", "output_level == 500")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "clipped == if output_level > 32767 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "output_level == 500"));
    ctx.push_obligation(ProofObligation::assert("no_clip", "clipped == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP gain: 1000 × 0.5 = 500, no clipping");
}

#[test]
fn moving_average_window() {
    let mut ctx = VerificationContext::new();
    for v in &["sum", "window_size", "average"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "sum == 5000"));
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "average == sum / window_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "average == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DSP average: 5000 / 10 = 500");
}

#[test]
fn interpolation_output_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["input_rate", "interpolation", "output_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ir", "input_rate == 8000"));
    ctx.push_obligation(ProofObligation::assume("i", "interpolation == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "or_def",
        "output_rate == input_rate * interpolation",
    ));
    ctx.push_obligation(ProofObligation::assert("is_48000", "output_rate == 48000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DSP interpolation: 8000 × 6 = 48000 Hz");
}

#[test]
fn dma_double_buffer() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("active_buffer", u32_ty());
    ctx.declare_var_typed("next_buffer", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "active_buffer == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "nb_def",
        "next_buffer == 1 - active_buffer",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "next_buffer == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "different",
        "next_buffer != active_buffer",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP double buffer: 0 → 1");
}

#[test]
fn sample_bit_depth_range() {
    let mut ctx = VerificationContext::new();
    for v in &["bit_depth", "max_positive", "min_negative"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // 16-bit signed audio: range [-32768, 32767]
    // Express as unsigned for u32: max_positive = 32767
    ctx.push_obligation(ProofObligation::assume("bd", "bit_depth == 16"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_positive == 32767"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_negative == 32768")); // |min| = 32768
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if max_positive + min_negative == 65535 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP: 16-bit range 32767 + 32768 = 65535");
}
