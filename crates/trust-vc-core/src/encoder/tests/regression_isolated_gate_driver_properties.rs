// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn propagation_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["delay_ns", "max_delay_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("delay_ok", i32_ty());
    // Turn-on propagation delay
    ctx.push_obligation(ProofObligation::assume("dn", "delay_ns == 50"));
    ctx.push_obligation(ProofObligation::assume("md", "max_delay_ns == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "delay_ok == if delay_ns <= max_delay_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "delay_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 50ns propagation ≤ 200ns max → OK");
}

#[test]
fn delay_matching() {
    let mut ctx = VerificationContext::new();
    for v in &["skew_ns", "max_skew_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("skew_ok", i32_ty());
    // Turn-on to turn-off delay matching (skew)
    ctx.push_obligation(ProofObligation::assume("sn", "skew_ns == 10"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_skew_ns == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "skew_ok == if skew_ns <= max_skew_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "skew_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 10ns skew ≤ 50ns max → OK");
}

#[test]
fn peak_source_current() {
    let mut ctx = VerificationContext::new();
    for v in &["source_ma", "min_source_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("src_ok", i32_ty());
    // Peak gate drive source current
    ctx.push_obligation(ProofObligation::assume("sm", "source_ma == 4000")); // 4A
    ctx.push_obligation(ProofObligation::assume("ms", "min_source_ma == 2000")); // 2A
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "src_ok == if source_ma >= min_source_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "src_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 4A peak source ≥ 2A min → OK");
}

#[test]
fn peak_sink_current() {
    let mut ctx = VerificationContext::new();
    for v in &["sink_ma", "min_sink_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("snk_ok", i32_ty());
    // Peak gate drive sink current
    ctx.push_obligation(ProofObligation::assume("sm", "sink_ma == 6000")); // 6A
    ctx.push_obligation(ProofObligation::assume("ms", "min_sink_ma == 3000")); // 3A
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "snk_ok == if sink_ma >= min_sink_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "snk_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 6A peak sink ≥ 3A min → OK");
}

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["iso_vrms", "min_iso_vrms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("iso_ok", i32_ty());
    // Reinforced isolation rating
    ctx.push_obligation(ProofObligation::assume("iv", "iso_vrms == 5700"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_iso_vrms == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "iso_ok == if iso_vrms >= min_iso_vrms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "iso_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 5700Vrms isolation ≥ 3000 min → OK");
}

#[test]
fn cmti_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["cmti_kvps", "min_cmti_kvps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cmti_ok", i32_ty());
    // Common-mode transient immunity in kV/μs
    ctx.push_obligation(ProofObligation::assume("ck", "cmti_kvps == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cmti_kvps == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cmti_ok == if cmti_kvps >= min_cmti_kvps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cmti_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 100 kV/μs CMTI ≥ 50 min → OK");
}

#[test]
fn output_voltage_high() {
    let mut ctx = VerificationContext::new();
    for v in &["voh_mv", "min_voh_mv", "max_voh_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voh_ok", i32_ty());
    // Gate drive high-side output voltage
    ctx.push_obligation(ProofObligation::assume("vm", "voh_mv == 15000")); // 15V
    ctx.push_obligation(ProofObligation::assume("mn", "min_voh_mv == 12000")); // 12V
    ctx.push_obligation(ProofObligation::assume("mx", "max_voh_mv == 20000")); // 20V
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voh_ok == if voh_mv >= min_voh_mv && voh_mv <= max_voh_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voh_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 15V output in [12, 20] → OK");
}

#[test]
fn dead_time() {
    let mut ctx = VerificationContext::new();
    for v in &["dead_ns", "min_dead_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dead_ok", i32_ty());
    // Dead time for half-bridge (shoot-through protection)
    ctx.push_obligation(ProofObligation::assume("dn", "dead_ns == 500"));
    ctx.push_obligation(ProofObligation::assume("md", "min_dead_ns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dead_ok == if dead_ns >= min_dead_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dead_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 500ns dead time ≥ 100ns min → OK");
}

#[test]
fn under_voltage_lockout() {
    let mut ctx = VerificationContext::new();
    for v in &["uvlo_mv", "min_uvlo_mv", "max_uvlo_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("uvlo_ok", i32_ty());
    // UVLO threshold in millivolts
    ctx.push_obligation(ProofObligation::assume("um", "uvlo_mv == 11500")); // 11.5V
    ctx.push_obligation(ProofObligation::assume("mn", "min_uvlo_mv == 9000")); // 9.0V
    ctx.push_obligation(ProofObligation::assume("mx", "max_uvlo_mv == 13000")); // 13.0V
    ctx.push_obligation(ProofObligation::assume(
        "uo_def",
        "uvlo_ok == if uvlo_mv >= min_uvlo_mv && uvlo_mv <= max_uvlo_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "uvlo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 11.5V UVLO in [9, 13] → OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Maximum supported switching frequency
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 200"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_khz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gate driver: 200kHz switching ≤ 500kHz max → OK");
}
