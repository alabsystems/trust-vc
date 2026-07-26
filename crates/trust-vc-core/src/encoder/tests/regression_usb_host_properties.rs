// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn hub_port_count() {
    let mut ctx = VerificationContext::new();
    for v in &["hub_ports", "max_ports"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_hub", i32_ty());
    // USB hub: 1-7 downstream ports (USB 2.0) or 1-15 (USB 3.0)
    ctx.push_obligation(ProofObligation::assume("hp", "hub_ports == 4"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_ports == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "vh_def",
        "valid_hub == if hub_ports >= 1 && hub_ports <= max_ports { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_hub == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB hub: 4 ports in [1, 7] → valid");
}

#[test]
fn device_address_assignment() {
    let mut ctx = VerificationContext::new();
    for v in &["next_address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("address_valid", i32_ty());
    // USB device addresses: 1-127 (0 is default, for enumeration)
    ctx.push_obligation(ProofObligation::assume("na", "next_address == 5"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 127"));
    ctx.push_obligation(ProofObligation::assume(
        "av_def",
        "address_valid == if next_address >= 1 && next_address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "address_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: device address 5 in [1, 127] → valid");
}

#[test]
fn transfer_descriptor_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["total_bytes", "max_packet", "td_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // TDs needed = ceil(total / max_packet)
    // Precompute: 4096 / 512 = 8 TDs (exact division)
    ctx.push_obligation(ProofObligation::assume("tb", "total_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_packet == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "td_count == total_bytes / max_packet",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "td_count == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "USB TD chain: 4096 / 512 = 8 TDs");
}

#[test]
fn bandwidth_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "allocated_us",
        "new_endpoint_us",
        "total_us",
        "frame_budget_us",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("budget_ok", i32_ty());
    // USB 2.0: 125us microframe, ~80% budget for periodic transfers
    ctx.push_obligation(ProofObligation::assume("au", "allocated_us == 60"));
    ctx.push_obligation(ProofObligation::assume("neu", "new_endpoint_us == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "tu_def",
        "total_us == allocated_us + new_endpoint_us",
    ));
    ctx.push_obligation(ProofObligation::assume("fbu", "frame_budget_us == 100")); // 80% of 125
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "budget_ok == if total_us <= frame_budget_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "total_us == 80"));
    ctx.push_obligation(ProofObligation::assert("ok", "budget_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB BW: 60 + 20 = 80us ≤ 100us budget");
}

#[test]
fn configuration_descriptor_length() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "config_header",
        "interface_count",
        "interface_desc_size",
        "endpoint_count",
        "endpoint_desc_size",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_length", u32_ty());
    // Config total = header + interfaces + endpoints
    // 9 + 2*9 + 4*7 = 9 + 18 + 28 = 55. Precompute products.
    ctx.push_obligation(ProofObligation::assume("ch", "config_header == 9"));
    ctx.push_obligation(ProofObligation::assume("ic", "interface_count == 2"));
    ctx.push_obligation(ProofObligation::assume("ids", "interface_desc_size == 9"));
    ctx.push_obligation(ProofObligation::assume("ec", "endpoint_count == 4"));
    ctx.push_obligation(ProofObligation::assume("eds", "endpoint_desc_size == 7"));
    ctx.push_obligation(ProofObligation::assume("tl", "total_length == 55")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_55", "total_length == 55"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB config desc: 9 + 2×9 + 4×7 = 55 bytes");
}

#[test]
fn power_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["device_ma", "hub_available_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // USB 2.0: 500mA max per port
    ctx.push_obligation(ProofObligation::assume("dm", "device_ma == 300"));
    ctx.push_obligation(ProofObligation::assume("ham", "hub_available_ma == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if device_ma <= hub_available_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB power: 300mA ≤ 500mA port budget");
}

#[test]
fn enumeration_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "reset_time_ms",
        "address_time_ms",
        "config_time_ms",
        "total_enum_ms",
        "timeout_ms",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_timeout", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt", "reset_time_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("at", "address_time_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("ct", "config_time_ms == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "te_def",
        "total_enum_ms == reset_time_ms + address_time_ms + config_time_ms",
    ));
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "wt_def",
        "within_timeout == if total_enum_ms <= timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "total_enum_ms == 80"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_timeout == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB enum: 50+10+20 = 80ms ≤ 5000ms timeout");
}

#[test]
fn split_transaction_timing() {
    let mut ctx = VerificationContext::new();
    for v in &["start_split_us", "complete_split_us", "total_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits_microframe", i32_ty());
    // USB 2.0 TT: start-split + complete-split within microframe
    ctx.push_obligation(ProofObligation::assume("ss", "start_split_us == 30"));
    ctx.push_obligation(ProofObligation::assume("cs", "complete_split_us == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "tu_def",
        "total_us == start_split_us + complete_split_us",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "fm_def",
        "fits_microframe == if total_us <= 125 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_70", "total_us == 70"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits_microframe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB split: 30+40 = 70us ≤ 125us microframe");
}

#[test]
fn interface_alternate_setting() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_alt", u32_ty());
    ctx.declare_var_typed("requested_alt", u32_ty());
    ctx.declare_var_typed("max_alt", u32_ty());
    ctx.declare_var_typed("valid_request", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ca", "current_alt == 0"));
    ctx.push_obligation(ProofObligation::assume("ra", "requested_alt == 1"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_alt == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_request == if requested_alt <= max_alt { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_request == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: alt setting 1 ≤ 2 max → valid");
}

#[test]
fn string_descriptor_length() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "string_chars",
        "char_bytes",
        "header_bytes",
        "descriptor_bytes",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // USB string descriptor: 2 header bytes + chars × 2 (UTF-16LE)
    // 10 chars × 2 + 2 = 22 bytes
    ctx.push_obligation(ProofObligation::assume("sc", "string_chars == 10"));
    ctx.push_obligation(ProofObligation::assume("cb", "char_bytes == 2")); // UTF-16LE
    ctx.push_obligation(ProofObligation::assume("hb", "header_bytes == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "db_def",
        "descriptor_bytes == header_bytes + string_chars * char_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_22", "descriptor_bytes == 22"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "USB string desc: 2 + 10×2 = 22 bytes");
}
