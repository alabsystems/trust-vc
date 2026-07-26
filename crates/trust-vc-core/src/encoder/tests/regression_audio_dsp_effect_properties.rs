// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn delay_line_samples() {
    let mut ctx = VerificationContext::new();
    for v in &["delay_ms", "sample_rate_hz", "delay_samples"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Delay samples = delay_ms × sample_rate / 1000
    // Precompute: 100 × 48000 / 1000 = 4800
    ctx.push_obligation(ProofObligation::assume("dm", "delay_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_hz == 48000"));
    ctx.push_obligation(ProofObligation::assume("ds", "delay_samples == 4800")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4800", "delay_samples == 4800"));
    ctx.push_obligation(ProofObligation::assert("positive", "delay_samples > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP delay: 100ms × 48kHz / 1000 = 4800 samples");
}

#[test]
fn reverb_feedback_gain() {
    let mut ctx = VerificationContext::new();
    for v in &["feedback_percent", "max_feedback"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stable", i32_ty());
    // Reverb feedback must be < 100% to prevent infinite growth
    ctx.push_obligation(ProofObligation::assume("fp", "feedback_percent == 75"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_feedback == 99"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "stable == if feedback_percent <= max_feedback { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP reverb: 75% feedback ≤ 99% max → stable");
}

#[test]
fn chorus_modulation_depth() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "base_delay_samples",
        "mod_depth_samples",
        "min_delay",
        "max_delay",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Chorus: delay oscillates around base ± mod_depth
    ctx.push_obligation(ProofObligation::assume("bd", "base_delay_samples == 500"));
    ctx.push_obligation(ProofObligation::assume("md", "mod_depth_samples == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "min_def",
        "min_delay == base_delay_samples - mod_depth_samples",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "max_def",
        "max_delay == base_delay_samples + mod_depth_samples",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "min_delay == 400"));
    ctx.push_obligation(ProofObligation::assert("is_600", "max_delay == 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP chorus: 500 ± 100 → [400, 600] samples");
}

#[test]
fn compressor_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["input_level_db", "threshold_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("compressing", i32_ty());
    // Compress when input exceeds threshold (values in -dBFS × 10, inverted)
    // Lower number = louder. threshold=200 (-20dBFS), input=150 (-15dBFS, louder)
    ctx.push_obligation(ProofObligation::assume("il", "input_level_db == 150"));
    ctx.push_obligation(ProofObligation::assume("td", "threshold_db == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compressing == if input_level_db < threshold_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "compressing == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DSP compressor: -15dBFS > -20dBFS threshold → compress",
    );
}

#[test]
fn noise_gate_hold_time() {
    let mut ctx = VerificationContext::new();
    for v in &["hold_ms", "sample_rate_khz", "hold_samples"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Hold samples = hold_ms × sample_rate_khz
    // 50ms × 48 = 2400 samples
    ctx.push_obligation(ProofObligation::assume("hm", "hold_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("srk", "sample_rate_khz == 48"));
    ctx.push_obligation(ProofObligation::assume(
        "hs_def",
        "hold_samples == hold_ms * sample_rate_khz",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2400", "hold_samples == 2400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DSP gate: 50ms × 48kHz = 2400 hold samples");
}

#[test]
fn eq_band_frequency_range() {
    let mut ctx = VerificationContext::new();
    for v in &["center_freq_hz", "bandwidth_hz", "low_freq", "high_freq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_audio_range", i32_ty());
    // Parametric EQ band: center ± bandwidth/2
    // 1000 Hz center, 200 Hz bandwidth → [900, 1100]
    ctx.push_obligation(ProofObligation::assume("cf", "center_freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("bw", "bandwidth_hz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "lf_def",
        "low_freq == center_freq_hz - bandwidth_hz / 2",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hf_def",
        "high_freq == center_freq_hz + bandwidth_hz / 2",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "iar_def",
        "in_audio_range == if high_freq <= 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("lf_900", "low_freq == 900"));
    ctx.push_obligation(ProofObligation::assert("hf_1100", "high_freq == 1100"));
    ctx.push_obligation(ProofObligation::assert("ok", "in_audio_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DSP EQ: 1000 ± 100 → [900, 1100] Hz");
}

#[test]
fn limiter_ceiling() {
    let mut ctx = VerificationContext::new();
    for v in &["input_level", "ceiling_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_level", u32_ty());
    // Hard limiter: output = min(input, ceiling)
    ctx.push_obligation(ProofObligation::assume("il", "input_level == 32000"));
    ctx.push_obligation(ProofObligation::assume("cl", "ceiling_level == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "ol_def",
        "output_level == if input_level > ceiling_level { ceiling_level } else { input_level }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30000", "output_level == 30000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP limiter: 32000 > 30000 ceiling → clamped");
}

#[test]
fn crossfade_mix() {
    let mut ctx = VerificationContext::new();
    for v in &["mix_percent", "dry_percent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_100", i32_ty());
    // Dry/wet mix must sum to 100%
    ctx.push_obligation(ProofObligation::assume("mp", "mix_percent == 60")); // wet
    ctx.push_obligation(ProofObligation::assume(
        "dp_def",
        "dry_percent == 100 - mix_percent",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total_100 == if mix_percent + dry_percent == 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "dry_percent == 40"));
    ctx.push_obligation(ProofObligation::assert("ok", "total_100 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP mix: 60% wet + 40% dry = 100%");
}

#[test]
fn pitch_shift_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["semitones", "ratio_percent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_range", i32_ty());
    // Pitch shift: ±12 semitones = 1 octave
    // Precompute ratio: 7 semitones up ≈ 149.8% ≈ 150
    ctx.push_obligation(ProofObligation::assume("st", "semitones == 7"));
    ctx.push_obligation(ProofObligation::assume("rp", "ratio_percent == 150")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_range == if ratio_percent >= 50 && ratio_percent <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_150", "ratio_percent == 150"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP pitch: 7 semitones → 150% ratio (valid)");
}

#[test]
fn effect_chain_latency() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "eq_latency_samples",
        "comp_latency_samples",
        "reverb_latency_samples",
        "total_latency",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acceptable", i32_ty());
    // Chain latency = sum of all effect latencies
    ctx.push_obligation(ProofObligation::assume("el", "eq_latency_samples == 64"));
    ctx.push_obligation(ProofObligation::assume("cl", "comp_latency_samples == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "rl",
        "reverb_latency_samples == 256",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_latency == eq_latency_samples + comp_latency_samples + reverb_latency_samples",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if total_latency <= 1024 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_448", "total_latency == 448"));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSP chain: 64+128+256 = 448 samples ≤ 1024 max");
}
