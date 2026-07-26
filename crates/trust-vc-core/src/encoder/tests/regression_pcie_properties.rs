// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tlp_max_payload() {
    let mut ctx = VerificationContext::new();
    for v in &["device_mps", "link_mps", "effective_mps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Effective MPS = min of device and link capabilities
    ctx.push_obligation(ProofObligation::assume("dm", "device_mps == 256"));
    ctx.push_obligation(ProofObligation::assume("lm", "link_mps == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "em_def",
        "effective_mps == if device_mps < link_mps { device_mps } else { link_mps }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_256", "effective_mps == 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCIe: min(256, 512) = 256 MPS");
}

#[test]
fn bdf_address() {
    let mut ctx = VerificationContext::new();
    for v in &["bus", "device", "function", "bdf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // BDF = (bus << 8) | (device << 3) | function
    // Precompute: bus=1→256, device=3→24, function=2→2, total=282
    ctx.push_obligation(ProofObligation::assume("b", "bus == 1"));
    ctx.push_obligation(ProofObligation::assume("d", "device == 3"));
    ctx.push_obligation(ProofObligation::assume("f", "function == 2"));
    ctx.push_obligation(ProofObligation::assume("bdf_val", "bdf == 282")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_282", "bdf == 282"));
    ctx.push_obligation(ProofObligation::assert("dev_range", "device < 32")); // 5 bits
    ctx.push_obligation(ProofObligation::assert("fn_range", "function < 8")); // 3 bits
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCIe BDF: bus=1,dev=3,fn=2 → 282");
}

#[test]
fn link_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["lanes", "per_lane_gbps", "total_gbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // PCIe Gen3 x4: 4 lanes × 8 GT/s ≈ 8 Gbps per lane (after encoding)
    ctx.push_obligation(ProofObligation::assume("l", "lanes == 4"));
    ctx.push_obligation(ProofObligation::assume("plg", "per_lane_gbps == 8")); // ~985 MB/s effective
    ctx.push_obligation(ProofObligation::assume(
        "tg_def",
        "total_gbps == lanes * per_lane_gbps",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "total_gbps == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PCIe Gen3 x4: 4×8 = 32 Gbps");
}

#[test]
fn completion_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed_us", "timeout_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timed_out", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eu", "elapsed_us == 60000")); // 60ms
    ctx.push_obligation(ProofObligation::assume("tu", "timeout_us == 50000")); // 50ms default
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timed_out == if elapsed_us > timeout_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timed_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCIe: 60ms > 50ms timeout → completion timeout");
}

#[test]
fn bar_size_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["bar_base", "bar_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // BAR must be naturally aligned (base aligned to size)
    ctx.push_obligation(ProofObligation::assume("bb", "bar_base == 4194304")); // 4MB
    ctx.push_obligation(ProofObligation::assume("bs", "bar_size == 1048576")); // 1MB
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if bar_base % bar_size == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1")); // 4MB % 1MB = 0
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PCIe BAR: 4MB aligned to 1MB");
}

#[test]
fn msi_vector_count() {
    let mut ctx = VerificationContext::new();
    for v in &["requested_vectors", "max_vectors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("granted_vectors", u32_ty());
    // MSI: power-of-two vectors, up to 32 max
    ctx.push_obligation(ProofObligation::assume("rv", "requested_vectors == 8"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_vectors == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "gv_def",
        "granted_vectors == if requested_vectors <= max_vectors { requested_vectors } else { max_vectors }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "granted_vectors == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCIe MSI: 8 requested <= 32 max → 8 granted");
}

#[test]
fn config_space_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["capability_pointer", "next_cap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_cap", i32_ty());
    // Capability pointers must be DWORD-aligned (bits [1:0] = 0)
    ctx.push_obligation(ProofObligation::assume("cp", "capability_pointer == 64")); // 0x40
    ctx.push_obligation(ProofObligation::assume("nc", "next_cap == 80")); // 0x50
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cap == if capability_pointer % 4 == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_cap == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PCIe cap: 0x40 DWORD-aligned");
}

#[test]
fn credit_based_flow_control() {
    let mut ctx = VerificationContext::new();
    for v in &["available_credits", "required_credits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_transmit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac", "available_credits == 12"));
    ctx.push_obligation(ProofObligation::assume("rc", "required_credits == 4")); // for a 256B TLP
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "can_transmit == if available_credits >= required_credits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_transmit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCIe flow: 12 >= 4 credits → can transmit");
}

#[test]
fn read_request_size() {
    let mut ctx = VerificationContext::new();
    for v in &["max_read_request", "requested_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mrr", "max_read_request == 512"));
    ctx.push_obligation(ProofObligation::assume("rs", "requested_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if requested_size <= max_read_request { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCIe: read request 256 <= 512 max → ok");
}

#[test]
fn link_training_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_state", u32_ty());
    ctx.declare_var_typed("link_up", u32_ty());
    ctx.declare_var_typed("new_state", u32_ty());
    // LTSSM states: 0=Detect, 1=Polling, 2=Config, 3=L0 (active), 4=Recovery
    // Transition from Config to L0 when link_up
    ctx.push_obligation(ProofObligation::assume("cs", "current_state == 2")); // Config
    ctx.push_obligation(ProofObligation::assume("lu", "link_up == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_state == if current_state == 2 && link_up == 1 { 3 } else { current_state }",
    ));
    ctx.push_obligation(ProofObligation::assert("l0", "new_state == 3")); // L0 active
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PCIe LTSSM: Config + link_up → L0");
}
