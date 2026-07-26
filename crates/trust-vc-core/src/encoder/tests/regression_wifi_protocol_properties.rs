// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn channel_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channel_num", u32_ty());
    ctx.declare_var_typed("freq_mhz", u32_ty());
    // 2.4GHz: freq = 2407 + channel × 5. Precompute: ch6 = 2407 + 30 = 2437
    ctx.push_obligation(ProofObligation::assume("cn", "channel_num == 6"));
    ctx.push_obligation(ProofObligation::assume("fm", "freq_mhz == 2437")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2437", "freq_mhz == 2437"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WiFi: channel 6 → 2437 MHz (precomputed)");
}

#[test]
fn rssi_signal_quality() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rssi_offset", u32_ty());
    ctx.declare_var_typed("good_threshold_offset", u32_ty());
    ctx.declare_var_typed("signal_good", i32_ty());
    // RSSI as offset from -127: 57=-70dBm. Good threshold: 77=-50dBm
    ctx.push_obligation(ProofObligation::assume("ro", "rssi_offset == 87")); // -40 dBm (strong)
    ctx.push_obligation(ProofObligation::assume("gt", "good_threshold_offset == 57")); // -70 dBm
    ctx.push_obligation(ProofObligation::assume(
        "sg_def",
        "signal_good == if rssi_offset >= good_threshold_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "signal_good == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WiFi: RSSI -40dBm ≥ -70dBm threshold → good signal",
    );
}

#[test]
fn beacon_interval() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interval_tu", u32_ty());
    ctx.declare_var_typed("is_default", i32_ty());
    // Beacon interval in Time Units (1 TU = 1024μs). Default = 100 TU ≈ 102.4ms
    ctx.push_obligation(ProofObligation::assume("it", "interval_tu == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_default == if interval_tu == 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_default == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WiFi: beacon interval 100 TU → default");
}

#[test]
fn max_aggregation_size() {
    let mut ctx = VerificationContext::new();
    for v in &["amsdu_bytes", "max_amsdu"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // A-MSDU max: 3839 or 7935 bytes
    ctx.push_obligation(ProofObligation::assume("ab", "amsdu_bytes == 3500"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_amsdu == 3839"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if amsdu_bytes <= max_amsdu { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WiFi: A-MSDU 3500 ≤ 3839 max → size OK");
}

#[test]
fn retry_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["retry_count", "max_retries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_drop", i32_ty());
    // Short retry limit: typically 7
    ctx.push_obligation(ProofObligation::assume("rc", "retry_count == 7"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retries == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "should_drop == if retry_count >= max_retries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "should_drop == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WiFi: 7 retries = 7 max → should drop frame");
}

#[test]
fn rts_cts_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_bytes", "rts_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("use_rts", i32_ty());
    // RTS/CTS for frames exceeding threshold
    ctx.push_obligation(ProofObligation::assume("fb", "frame_bytes == 3000"));
    ctx.push_obligation(ProofObligation::assume("rt", "rts_threshold == 2347"));
    ctx.push_obligation(ProofObligation::assume(
        "ur_def",
        "use_rts == if frame_bytes >= rts_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "use_rts == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WiFi: 3000 bytes ≥ 2347 RTS threshold → use RTS/CTS",
    );
}

#[test]
fn power_save_dtim() {
    let mut ctx = VerificationContext::new();
    for v in &["dtim_count", "dtim_period"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_dtim_beacon", i32_ty());
    // DTIM: every Nth beacon indicates buffered multicast
    ctx.push_obligation(ProofObligation::assume("dc", "dtim_count == 0")); // DTIM at count 0
    ctx.push_obligation(ProofObligation::assume("dp", "dtim_period == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_dtim_beacon == if dtim_count == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_dtim_beacon == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WiFi: DTIM count 0 → DTIM beacon (wake for multicast)",
    );
}

#[test]
fn channel_bandwidth() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_mhz", u32_ty());
    ctx.declare_var_typed("is_wide", i32_ty());
    // 802.11n+: 20, 40, 80, 160 MHz. Wide = 80+
    ctx.push_obligation(ProofObligation::assume("bm", "bandwidth_mhz == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "iw_def",
        "is_wide == if bandwidth_mhz >= 80 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_wide == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WiFi: 80 MHz ≥ 80 → wide channel");
}

#[test]
fn association_id() {
    let mut ctx = VerificationContext::new();
    for v in &["aid", "max_aid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aid_valid", i32_ty());
    // Association ID: 1-2007
    ctx.push_obligation(ProofObligation::assume("a", "aid == 1"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_aid == 2007"));
    ctx.push_obligation(ProofObligation::assume(
        "av_def",
        "aid_valid == if aid >= 1 && aid <= max_aid { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "aid_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WiFi: AID 1 in [1, 2007] → valid association ID");
}

#[test]
fn fragmentation_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_bytes", "frag_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_frag", i32_ty());
    // Fragment frames exceeding threshold (256-2346 bytes)
    ctx.push_obligation(ProofObligation::assume("fb", "frame_bytes == 2000"));
    ctx.push_obligation(ProofObligation::assume("ft", "frag_threshold == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "nf_def",
        "needs_frag == if frame_bytes > frag_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_frag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WiFi: 2000 bytes > 1500 frag threshold → needs fragmentation",
    );
}
