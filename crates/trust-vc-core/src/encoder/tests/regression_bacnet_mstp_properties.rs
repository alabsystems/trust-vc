// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn station_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // MS/TP station address (0-127 for master, 128-254 for slave, 255=broadcast)
    ctx.push_obligation(ProofObligation::assume("a", "address == 10"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 127")); // master range
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet MS/TP: address 10 ≤ 127 master max → OK");
}

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.declare_var_typed("valid_baud", i32_ty());
    // Standard baud rates
    ctx.push_obligation(ProofObligation::assume("b", "baud == 76800"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_baud == if baud == 9600 || baud == 19200 || baud == 38400 || baud == 76800 || baud == 115200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_baud == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet MS/TP: 76800 is valid baud rate");
}

#[test]
fn max_master() {
    let mut ctx = VerificationContext::new();
    for v in &["max_master", "min_max_master", "abs_max_master"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mm_ok", i32_ty());
    // Max_Master parameter (last master station to poll)
    ctx.push_obligation(ProofObligation::assume("mm", "max_master == 64"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_max_master == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "abs_max_master == 127"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mm_ok == if max_master >= min_max_master && max_master <= abs_max_master { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mm_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet MS/TP: Max_Master 64 in [0, 127] → OK");
}

#[test]
fn frame_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ftype", u32_ty());
    ctx.declare_var_typed("valid_ftype", i32_ty());
    // Frame types: 0=Token, 1=PollForMaster, 2=ReplyToPollForMaster,
    // 3=TestRequest, 4=TestResponse, 5=BACnetDataExpectingReply, 6=BACnetDataNotExpectingReply
    ctx.push_obligation(ProofObligation::assume("ft", "ftype == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_ftype == if ftype == 0 || ftype == 1 || ftype == 2 || ftype == 3 || ftype == 4 || ftype == 5 || ftype == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ftype == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BACnet MS/TP: BACnetDataExpectingReply is valid frame type",
    );
}

#[test]
fn max_info_frames() {
    let mut ctx = VerificationContext::new();
    for v in &["info_frames", "max_info_frames"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("if_ok", i32_ty());
    // Max_Info_Frames parameter (messages per token pass)
    ctx.push_obligation(ProofObligation::assume("if_val", "info_frames == 5"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_info_frames == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "if_ok == if info_frames >= 1 && info_frames <= max_info_frames { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "if_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet MS/TP: 5 info frames in [1, 100] → OK");
}

#[test]
fn token_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "max_timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("to_ok", i32_ty());
    // Tusage_timeout in ms (token holding time)
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "to_ok == if timeout_ms <= max_timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "to_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet MS/TP: 500ms token timeout ≤ 1000 max → OK");
}

#[test]
fn data_length() {
    let mut ctx = VerificationContext::new();
    for v in &["data_len", "max_data_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // NPDU data length in bytes
    ctx.push_obligation(ProofObligation::assume("dl", "data_len == 480"));
    ctx.push_obligation(ProofObligation::assume("md", "max_data_len == 1497"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if data_len <= max_data_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet MS/TP: 480-byte NPDU ≤ 1497 max → OK");
}

#[test]
fn object_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("obj_type", u32_ty());
    ctx.declare_var_typed("valid_obj", i32_ty());
    // Common BACnet object types: 0=AI, 1=AO, 2=AV, 3=BI, 4=BO, 5=BV, 8=Device
    ctx.push_obligation(ProofObligation::assume("ot", "obj_type == 0")); // Analog Input
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_obj == if obj_type == 0 || obj_type == 1 || obj_type == 2 || obj_type == 3 || obj_type == 4 || obj_type == 5 || obj_type == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_obj == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: Analog Input is valid object type");
}

#[test]
fn device_instance() {
    let mut ctx = VerificationContext::new();
    for v in &["instance", "max_instance"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("inst_ok", i32_ty());
    // BACnet device instance (22-bit, 0 to 4194302; 4194303 = wildcard)
    ctx.push_obligation(ProofObligation::assume("i", "instance == 100"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_instance == 4194302"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "inst_ok == if instance <= max_instance { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "inst_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: instance 100 ≤ 4194302 max → OK");
}

#[test]
fn network_number() {
    let mut ctx = VerificationContext::new();
    for v in &["network", "max_network"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("net_ok", i32_ty());
    // BACnet network number (16-bit, 1-65534; 0=local, 65535=broadcast)
    ctx.push_obligation(ProofObligation::assume("n", "network == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_network == 65534"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "net_ok == if network >= 1 && network <= max_network { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "net_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BACnet: network 1 in [1, 65534] → OK");
}
