// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sample_clamp_positive() {
    // Clamp sample to [-32768, 32767] (i16 range)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("raw", i32_ty());
    ctx.declare_var_typed("clamped", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "raw == 40000"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "clamped == if raw > 32767 { 32767 } else { if raw < 0 - 32768 { 0 - 32768 } else { raw } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_max", "clamped == 32767"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(40000) = 32767");
}

#[test]
fn sample_clamp_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("raw", i32_ty());
    ctx.declare_var_typed("clamped", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "raw == 0 - 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "clamped == if raw > 32767 { 32767 } else { if raw < 0 - 32768 { 0 - 32768 } else { raw } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_min", "clamped == 0 - 32768"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(-50000) = -32768");
}

#[test]
fn mix_two_samples() {
    // Simple mix: (a + b) / 2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("mixed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1000"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3000"));
    ctx.push_obligation(ProofObligation::assume("m_def", "mixed == (a + b) / 2"));
    ctx.push_obligation(ProofObligation::assert("is_2000", "mixed == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "mix(1000, 3000) = 2000");
}

#[test]
fn stereo_interleave_left_index() {
    // Stereo interleave: left[i] at position 2*i
    let mut ctx = VerificationContext::new();
    for v in &["i", "output_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 3"));
    ctx.push_obligation(ProofObligation::assume("oi_def", "output_idx == i * 2"));
    ctx.push_obligation(ProofObligation::assert("is_6", "output_idx == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "stereo left[3] at index 6");
}

#[test]
fn stereo_interleave_right_index() {
    // Right channel: right[i] at position 2*i + 1
    let mut ctx = VerificationContext::new();
    for v in &["i", "output_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 3"));
    ctx.push_obligation(ProofObligation::assume("oi_def", "output_idx == i * 2 + 1"));
    ctx.push_obligation(ProofObligation::assert("is_7", "output_idx == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "stereo right[3] at index 7");
}

#[test]
fn silence_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample", i32_ty());
    ctx.declare_var_typed("is_silent", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "sample == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_silent == if sample == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("silent", "is_silent == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample 0 is silence");
}

#[test]
fn sample_rate_nyquist() {
    // Nyquist: sample_rate >= 2 * max_frequency
    let mut ctx = VerificationContext::new();
    for v in &["sample_rate", "max_freq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("nyquist_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate == 44100"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq == 20000"));
    ctx.push_obligation(ProofObligation::assume(
        "nq_def",
        "nyquist_ok == if sample_rate >= max_freq * 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "nyquist_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "44100 >= 2*20000 → Nyquist satisfied");
}

#[test]
fn frame_size_stereo_16bit() {
    // Frame = channels * bytes_per_sample: stereo 16-bit = 2*2 = 4 bytes
    let mut ctx = VerificationContext::new();
    for v in &["channels", "bytes_per_sample", "frame_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 2"));
    ctx.push_obligation(ProofObligation::assume("bps", "bytes_per_sample == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "fs_def",
        "frame_size == channels * bytes_per_sample",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "frame_size == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "stereo 16-bit: 4 bytes/frame");
}

#[test]
fn buffer_duration_samples() {
    // Duration in samples = sample_rate * seconds
    let mut ctx = VerificationContext::new();
    for v in &["sample_rate", "seconds", "buffer_samples"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate == 48000"));
    ctx.push_obligation(ProofObligation::assume("s", "seconds == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "bs_def",
        "buffer_samples == sample_rate * seconds",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_48000",
        "buffer_samples == 48000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "48000 Hz * 1s = 48000 samples");
}

#[test]
fn volume_scale_half() {
    // Volume at 50%: sample * 128 / 256
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample", i32_ty());
    ctx.declare_var_typed("scaled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "sample == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "sc_def",
        "scaled == sample * 128 / 256",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "scaled == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "volume 50%: 1000 → 500");
}
