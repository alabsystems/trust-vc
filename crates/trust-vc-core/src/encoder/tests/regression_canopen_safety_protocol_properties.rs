// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// CANopen Safety protocol (EN 50325-5) properties:
// SRD (Safety-Related Data) and SRDO (Safety-Related Data Object) verification.

#[test]
fn test_srdo_count() {
    let mut ctx = VerificationContext::new();
    for v in &["srdo_count", "srdo_min", "srdo_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of safety-relevant data objects on a CANopen Safety node
    ctx.push_obligation(ProofObligation::assume("sc_val", "srdo_count == 8"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "srdo_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "srdo_max == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_in_range",
        "srdo_count >= srdo_min && srdo_count <= srdo_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: SRDO count 8 in range [1,64]");
}

#[test]
fn test_safety_cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["sct_ms", "sct_min", "sct_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // SCT (Safety Cycle Time) in milliseconds per EN 50325-5
    ctx.push_obligation(ProofObligation::assume("sct_val", "sct_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("sct_lo", "sct_min == 10"));
    ctx.push_obligation(ProofObligation::assume("sct_hi", "sct_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "sct_in_range",
        "sct_ms >= sct_min && sct_ms <= sct_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: SCT 100 ms in range [10,5000]");
}

#[test]
fn test_safety_relevant_validation_time() {
    let mut ctx = VerificationContext::new();
    for v in &["srvt_ms", "srvt_min", "srvt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // SRVT (Safety-Relevant Validation Time) in milliseconds
    ctx.push_obligation(ProofObligation::assume("srvt_val", "srvt_ms == 20"));
    ctx.push_obligation(ProofObligation::assume("srvt_lo", "srvt_min == 5"));
    ctx.push_obligation(ProofObligation::assume("srvt_hi", "srvt_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "srvt_in_range",
        "srvt_ms >= srvt_min && srvt_ms <= srvt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: SRVT 20 ms in range [5,200]");
}

#[test]
fn test_sil_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sil", u32_ty());
    ctx.declare_var_typed("valid_sil", i32_ty());
    // SIL level for CANopen Safety: 1=SIL1, 2=SIL2, 3=SIL3
    ctx.push_obligation(ProofObligation::assume("sil_val", "sil == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_sil == if sil == 1 || sil == 2 || sil == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sil_check", "valid_sil == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: SIL 3 is valid (1, 2, or 3)");
}

#[test]
fn test_data_direction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("direction", u32_ty());
    ctx.declare_var_typed("valid_dir", i32_ty());
    // SRDO data direction: 1=transmit, 2=receive, 3=bidirectional
    ctx.push_obligation(ProofObligation::assume("dir_val", "direction == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dir == if direction == 1 || direction == 2 || direction == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dir_check", "valid_dir == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: direction 2 (receive) is valid");
}

#[test]
fn test_crc_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crc_type", u32_ty());
    ctx.declare_var_typed("valid_crc", i32_ty());
    // CRC type for SRDO integrity: 1=CRC-8, 2=CRC-16, 3=CRC-32
    ctx.push_obligation(ProofObligation::assume("ct_val", "crc_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_crc == if crc_type == 1 || crc_type == 2 || crc_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("crc_check", "valid_crc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: CRC type 2 (CRC-16) is valid");
}

#[test]
fn test_node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["nodes", "nodes_min", "nodes_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Safe nodes on a CANopen Safety network segment: bounded 1-127
    ctx.push_obligation(ProofObligation::assume("nc_val", "nodes == 16"));
    ctx.push_obligation(ProofObligation::assume("nc_min", "nodes_min == 1"));
    ctx.push_obligation(ProofObligation::assume("nc_max", "nodes_max == 127"));
    ctx.push_obligation(ProofObligation::assert(
        "nc_in_range",
        "nodes >= nodes_min && nodes <= nodes_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: node count 16 in range [1,127]");
}

#[test]
fn test_baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud_kbps", u32_ty());
    ctx.declare_var_typed("valid_baud", i32_ty());
    // CANopen baud rates (kbps): 125, 250, 500
    ctx.push_obligation(ProofObligation::assume("br_val", "baud_kbps == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_baud == if baud_kbps == 125 || baud_kbps == 250 || baud_kbps == 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("baud_check", "valid_baud == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: 250 kbps is valid baud rate");
}

#[test]
fn test_heartbeat_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["hb_ms", "hb_min", "hb_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Heartbeat/guarding interval in milliseconds
    ctx.push_obligation(ProofObligation::assume("hb_val", "hb_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("hb_lo", "hb_min == 50"));
    ctx.push_obligation(ProofObligation::assume("hb_hi", "hb_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "hb_in_range",
        "hb_ms >= hb_min && hb_ms <= hb_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "CANopen Safety: heartbeat 500 ms in range [50,10000]",
    );
}

#[test]
fn test_safety_configuration_lock() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config_locked", i32_ty());
    ctx.declare_var_typed("write_allowed", i32_ty());
    // Safety configuration lock flag: 1=locked (no writes), 0=unlocked (writes permitted)
    ctx.push_obligation(ProofObligation::assume("cl_val", "config_locked == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "wa_def",
        "write_allowed == if config_locked == 1 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "locked_no_write",
        "write_allowed == 0",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_bool",
        "config_locked == 0 || config_locked == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen Safety: config locked blocks writes");
}
