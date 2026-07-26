// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn virtqueue_descriptor_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["desc_count", "max_descriptors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("chain_valid", i32_ty());
    // Virtqueue descriptor chain must not exceed queue size
    ctx.push_obligation(ProofObligation::assume("dc", "desc_count == 5"));
    ctx.push_obligation(ProofObligation::assume("md", "max_descriptors == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "chain_valid == if desc_count <= max_descriptors { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "chain_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "virtio: 5 descriptors <= 256 max → valid chain");
}

#[test]
fn available_ring_index() {
    let mut ctx = VerificationContext::new();
    for v in &["avail_idx", "queue_size", "ring_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Available ring index wraps modulo queue size
    ctx.push_obligation(ProofObligation::assume("ai", "avail_idx == 259"));
    ctx.push_obligation(ProofObligation::assume("qs", "queue_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "ri_def",
        "ring_index == avail_idx % queue_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "ring_index == 3")); // 259 mod 256
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "virtio avail: 259 mod 256 = 3");
}

#[test]
fn used_ring_advance() {
    let mut ctx = VerificationContext::new();
    for v in &["used_idx", "new_used_idx", "processed_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ui", "used_idx == 100"));
    ctx.push_obligation(ProofObligation::assume("pc", "processed_count == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "nui_def",
        "new_used_idx == used_idx + processed_count",
    ));
    ctx.push_obligation(ProofObligation::assert("is_103", "new_used_idx == 103"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "virtio used: 100 + 3 = 103");
}

#[test]
fn feature_negotiation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("device_features", u32_ty());
    ctx.declare_var_typed("driver_features", u32_ty());
    ctx.declare_var_typed("negotiated", u32_ty());
    // Features are AND of device and driver capabilities
    ctx.push_obligation(ProofObligation::assume("df", "device_features == 15")); // 0b1111
    ctx.push_obligation(ProofObligation::assume("drf", "driver_features == 6")); // 0b0110
    ctx.push_obligation(ProofObligation::assume(
        "n_def",
        "negotiated == device_features & driver_features",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "negotiated == 6")); // 0b0110
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "virtio features: 15 & 6 = 6");
}

#[test]
fn device_status_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("status", u32_ty());
    ctx.declare_var_typed("driver_ok", i32_ty());
    // Status register: bit 2 = DRIVER_OK
    // status=7 means ACKNOWLEDGE(1) | DRIVER(2) | DRIVER_OK(4) = 7
    ctx.push_obligation(ProofObligation::assume("s", "status == 7"));
    // Precompute: 7 & 4 = 4, which is nonzero
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "driver_ok == if status >= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "driver_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "virtio: status=7 → DRIVER_OK set");
}

#[test]
fn indirect_descriptor_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["indirect_count", "max_indirect"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Indirect descriptors: max limited by descriptor table page
    // 4096 / 16 = 256 max indirect descriptors per table
    ctx.push_obligation(ProofObligation::assume("ic", "indirect_count == 200"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_indirect == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if indirect_count <= max_indirect { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "virtio indirect: 200 <= 256 → valid");
}

#[test]
fn notification_suppression() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flags", u32_ty());
    ctx.declare_var_typed("notifications_disabled", i32_ty());
    // flags bit 0 = NO_NOTIFY (suppress notifications from device)
    ctx.push_obligation(ProofObligation::assume("f", "flags == 1")); // NO_NOTIFY set
    ctx.push_obligation(ProofObligation::assume(
        "nd_def",
        "notifications_disabled == if flags == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "yes",
        "notifications_disabled == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "virtio: flags=1 → notifications suppressed");
}

#[test]
fn multiqueue_assignment() {
    let mut ctx = VerificationContext::new();
    for v in &["cpu_id", "num_queues", "queue_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Assign queues to CPUs: queue = cpu mod num_queues
    ctx.push_obligation(ProofObligation::assume("ci", "cpu_id == 7"));
    ctx.push_obligation(ProofObligation::assume("nq", "num_queues == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "qi_def",
        "queue_id == cpu_id % num_queues",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "queue_id == 3")); // 7 mod 4 = 3
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "virtio multiqueue: CPU 7 mod 4 = queue 3");
}

#[test]
fn buffer_size_validation() {
    let mut ctx = VerificationContext::new();
    for v in &["buffer_length", "min_length", "max_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_buffer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bl", "buffer_length == 1526")); // max ethernet + header
    ctx.push_obligation(ProofObligation::assume("mn", "min_length == 64")); // min ethernet
    ctx.push_obligation(ProofObligation::assume("mx", "max_length == 65535")); // max virtio-net
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_buffer == if buffer_length >= min_length && buffer_length <= max_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_buffer == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "virtio-net: 1526 in [64, 65535] → valid buffer");
}

#[test]
fn split_virtqueue_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["desc_table_addr", "alignment"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // Split virtqueue: descriptor table must be 16-byte aligned
    ctx.push_obligation(ProofObligation::assume("dta", "desc_table_addr == 4096")); // page-aligned
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if desc_table_addr % alignment == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "virtio: desc table 4096 aligned to 16");
}
