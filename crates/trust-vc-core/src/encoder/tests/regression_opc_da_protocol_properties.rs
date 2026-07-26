// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn update_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_ms", "min_rate_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Requested update rate in milliseconds
    ctx.push_obligation(ProofObligation::assume("rm", "rate_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_ms >= min_rate_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 100ms update rate ≥ 10ms min → OK");
}

#[test]
fn item_count() {
    let mut ctx = VerificationContext::new();
    for v in &["items", "max_items"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("item_ok", i32_ty());
    // Items per group
    ctx.push_obligation(ProofObligation::assume("i", "items == 500"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_items == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "item_ok == if items >= 1 && items <= max_items { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "item_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 500 items in [1, 10000] → OK");
}

#[test]
fn quality_status() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("quality", u32_ty());
    ctx.declare_var_typed("valid_quality", i32_ty());
    // OPC quality codes: 0=Bad, 64=Uncertain, 192=Good, 216=GoodLocalOverride
    ctx.push_obligation(ProofObligation::assume("q", "quality == 192"));
    ctx.push_obligation(ProofObligation::assume(
        "vq_def",
        "valid_quality == if quality == 0 || quality == 64 || quality == 192 || quality == 216 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_quality == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: Good (192) is valid quality code");
}

#[test]
fn group_count() {
    let mut ctx = VerificationContext::new();
    for v in &["groups", "max_groups"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("grp_ok", i32_ty());
    // Number of OPC groups per connection
    ctx.push_obligation(ProofObligation::assume("g", "groups == 10"));
    ctx.push_obligation(ProofObligation::assume("mg", "max_groups == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "grp_ok == if groups >= 1 && groups <= max_groups { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "grp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 10 groups in [1, 256] → OK");
}

#[test]
fn deadband() {
    let mut ctx = VerificationContext::new();
    for v in &["deadband_x10", "max_deadband_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("db_ok", i32_ty());
    // Percent deadband (×10 for 0.1% precision, max 100.0% = 1000)
    ctx.push_obligation(ProofObligation::assume("dx", "deadband_x10 == 50")); // 5.0%
    ctx.push_obligation(ProofObligation::assume("md", "max_deadband_x10 == 1000")); // 100.0%
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "db_ok == if deadband_x10 <= max_deadband_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "db_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 5.0% deadband ≤ 100.0% max → OK");
}

#[test]
fn data_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vt_type", u32_ty());
    ctx.declare_var_typed("valid_vt", i32_ty());
    // VARIANT data types: 2=VT_I2, 3=VT_I4, 4=VT_R4, 5=VT_R8, 8=VT_BSTR, 11=VT_BOOL
    ctx.push_obligation(ProofObligation::assume("vt", "vt_type == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vv_def",
        "valid_vt == if vt_type == 2 || vt_type == 3 || vt_type == 4 || vt_type == 5 || vt_type == 8 || vt_type == 11 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_vt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: VT_R4 is valid VARIANT type");
}

#[test]
fn access_rights() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("access", u32_ty());
    ctx.declare_var_typed("valid_access", i32_ty());
    // Access rights: 1=readable, 2=writable, 3=readWritable
    ctx.push_obligation(ProofObligation::assume("a", "access == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_access == if access == 1 || access == 2 || access == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_access == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: readWritable is valid access right");
}

#[test]
fn scan_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["scan_ms", "max_scan_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("scan_ok", i32_ty());
    // Server scan rate in milliseconds
    ctx.push_obligation(ProofObligation::assume("sm", "scan_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_scan_ms == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "scan_ok == if scan_ms >= 1 && scan_ms <= max_scan_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "scan_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 50ms scan rate in [1, 10000] → OK");
}

#[test]
fn bandwidth_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["callbacks_sec", "max_callbacks_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Maximum callbacks per second
    ctx.push_obligation(ProofObligation::assume("cs", "callbacks_sec == 1000"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_callbacks_sec == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if callbacks_sec <= max_callbacks_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 1000 callbacks/s ≤ 50000 max → OK");
}

#[test]
fn timestamp_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["ts_us", "max_ts_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ts_ok", i32_ty());
    // Timestamp resolution in microseconds (FILETIME based)
    ctx.push_obligation(ProofObligation::assume("tu", "ts_us == 100")); // 100μs
    ctx.push_obligation(ProofObligation::assume("mt", "max_ts_us == 10000")); // 10ms
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "ts_ok == if ts_us <= max_ts_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ts_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 100μs timestamp ≤ 10ms max → OK");
}
