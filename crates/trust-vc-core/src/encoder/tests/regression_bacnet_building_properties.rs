// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn object_instance() {
    let mut ctx = VerificationContext::new();
    for v in &["instance", "max_instance"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("inst_ok", i32_ty());
    // BACnet object instance: 22-bit (0-4194303)
    ctx.push_obligation(ProofObligation::assume("i", "instance == 1000"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_instance == 4194303"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "inst_ok == if instance <= max_instance { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "inst_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: instance 1000 ≤ 4194303 → valid 22-bit");
}

#[test]
fn property_id() {
    let mut ctx = VerificationContext::new();
    for v in &["prop_id", "max_prop_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("prop_ok", i32_ty());
    // Standard property identifiers
    ctx.push_obligation(ProofObligation::assume("pi", "prop_id == 85")); // present-value
    ctx.push_obligation(ProofObligation::assume("mp", "max_prop_id == 4194303"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "prop_ok == if prop_id <= max_prop_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "prop_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: property 85 (present-value) → valid");
}

#[test]
fn device_id() {
    let mut ctx = VerificationContext::new();
    for v in &["device_id", "max_device_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dev_ok", i32_ty());
    // BACnet device instance: unique per network (22-bit)
    ctx.push_obligation(ProofObligation::assume("di", "device_id == 50001"));
    ctx.push_obligation(ProofObligation::assume("md", "max_device_id == 4194302")); // 4194303 reserved
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dev_ok == if device_id <= max_device_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dev_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: device 50001 ≤ 4194302 → valid");
}

#[test]
fn apdu_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("apdu_bytes", u32_ty());
    ctx.declare_var_typed("valid_apdu", i32_ty());
    // Standard max APDU sizes: 50, 128, 206, 480, 1024, 1476
    ctx.push_obligation(ProofObligation::assume("ab", "apdu_bytes == 480"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_apdu == if apdu_bytes == 50 || apdu_bytes == 128 || apdu_bytes == 206 || apdu_bytes == 480 || apdu_bytes == 1024 || apdu_bytes == 1476 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_apdu == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: 480-byte APDU is a valid max size");
}

#[test]
fn priority_array() {
    let mut ctx = VerificationContext::new();
    for v in &["priority", "max_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pri_ok", i32_ty());
    // BACnet command priority: 1-16 (1=highest, manual life safety)
    ctx.push_obligation(ProofObligation::assume("p", "priority == 8"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_priority == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pri_ok == if priority >= 1 && priority <= max_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pri_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: priority 8 in [1, 16] → valid");
}

#[test]
fn cov_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["increment_x100", "min_inc_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cov_ok", i32_ty());
    // Change of Value increment (×100 for 0.01 resolution)
    ctx.push_obligation(ProofObligation::assume("ix", "increment_x100 == 50")); // 0.50
    ctx.push_obligation(ProofObligation::assume("mi", "min_inc_x100 == 1")); // 0.01
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cov_ok == if increment_x100 >= min_inc_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cov_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: COV increment 0.50 ≥ 0.01 min → OK");
}

#[test]
fn network_number() {
    let mut ctx = VerificationContext::new();
    for v in &["network", "max_network"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("net_ok", i32_ty());
    // BACnet network number: 1-65534 (0=local, 65535=broadcast)
    ctx.push_obligation(ProofObligation::assume("n", "network == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_network == 65534"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "net_ok == if network >= 1 && network <= max_network { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "net_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: network 100 in [1, 65534] → valid");
}

#[test]
fn mstp_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_master"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // MS/TP master address: 0-127
    ctx.push_obligation(ProofObligation::assume("a", "address == 10"));
    ctx.push_obligation(ProofObligation::assume("mm", "max_master == 127"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address <= max_master { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: MS/TP address 10 ≤ 127 → valid");
}

#[test]
fn segmentation_support() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seg_type", u32_ty());
    ctx.declare_var_typed("valid_seg", i32_ty());
    // Segmentation: 0=both, 1=transmit, 2=receive, 3=none
    ctx.push_obligation(ProofObligation::assume("st", "seg_type == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_seg == if seg_type == 0 || seg_type == 1 || seg_type == 2 || seg_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_seg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: seg_type=0 (both) → valid segmentation");
}

#[test]
fn vendor_id() {
    let mut ctx = VerificationContext::new();
    for v in &["vendor", "max_vendor"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vendor_ok", i32_ty());
    // ASHRAE-assigned vendor ID: 16-bit
    ctx.push_obligation(ProofObligation::assume("v", "vendor == 123"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_vendor == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vendor_ok == if vendor <= max_vendor { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vendor_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: vendor 123 ≤ 65535 → valid 16-bit");
}
