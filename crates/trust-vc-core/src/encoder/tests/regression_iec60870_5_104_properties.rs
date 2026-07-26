// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn asdu_address() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("asdu_addr", u32_ty());
    ctx.declare_var_typed("addr_ok", i32_ty());
    // Common address of ASDU: 1-65534 (0 and 65535 reserved)
    ctx.push_obligation(ProofObligation::assume("aa", "asdu_addr == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if asdu_addr >= 1 && asdu_addr <= 65534 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: ASDU address 1 in [1, 65534]");
}

#[test]
fn ioa_address() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ioa", u32_ty());
    ctx.declare_var_typed("ioa_ok", i32_ty());
    // Information object address: 24-bit field, valid range 1-16777215
    ctx.push_obligation(ProofObligation::assume("io", "ioa == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "ioa_ok == if ioa >= 1 && ioa <= 16777215 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ioa_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: IOA 100 in [1, 16777215] (24-bit)");
}

#[test]
fn type_id() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tid", u32_ty());
    ctx.declare_var_typed("valid_tid", i32_ty());
    // Common type identifiers: 1=M_SP_NA (single-point), 3=M_DP_NA (double-point),
    // 13=M_ME_NC (float measured), 30=M_SP_TB (single with timestamp),
    // 45=C_SC_NA (single command), 50=C_SE_NC (set-point)
    ctx.push_obligation(ProofObligation::assume("t", "tid == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_tid == if tid == 1 || tid == 3 || tid == 13 || tid == 30 || tid == 45 || tid == 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_tid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: type ID 13 (M_ME_NC) is valid");
}

#[test]
fn cause_of_transmission() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cot", u32_ty());
    ctx.declare_var_typed("valid_cot", i32_ty());
    // Cause of transmission: 3=spontaneous, 5=requested, 6=activation,
    // 7=activation confirm, 10=return of remote
    ctx.push_obligation(ProofObligation::assume("c", "cot == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cot == if cot == 3 || cot == 5 || cot == 6 || cot == 7 || cot == 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cot == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: COT 3 (spontaneous) is valid");
}

#[test]
fn k_parameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("k", u32_ty());
    ctx.declare_var_typed("k_ok", i32_ty());
    // k = max number of outstanding I-format APDUs (1-32767)
    ctx.push_obligation(ProofObligation::assume("kv", "k == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "k_ok == if k >= 1 && k <= 32767 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "k_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: k=12 outstanding I-frames in [1, 32767]");
}

#[test]
fn w_parameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("w", u32_ty());
    ctx.declare_var_typed("w_ok", i32_ty());
    // w = latest acknowledgement after receiving w I-format APDUs (1-32767)
    ctx.push_obligation(ProofObligation::assume("wv", "w == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "w_ok == if w >= 1 && w <= 32767 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "w_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: w=8 ack threshold in [1, 32767]");
}

#[test]
fn t1_timeout() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t1", u32_ty());
    ctx.declare_var_typed("t1_ok", i32_ty());
    // t1 = timeout of connection establishment (seconds, 1-255)
    ctx.push_obligation(ProofObligation::assume("t1v", "t1 == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "t1o_def",
        "t1_ok == if t1 >= 1 && t1 <= 255 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "t1_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: t1=15s connection timeout in [1, 255]");
}

#[test]
fn t2_timeout() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t2", u32_ty());
    ctx.declare_var_typed("t2_ok", i32_ty());
    // t2 = timeout for acknowledging received APDUs (seconds, 1-255)
    ctx.push_obligation(ProofObligation::assume("t2v", "t2 == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "t2o_def",
        "t2_ok == if t2 >= 1 && t2 <= 255 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "t2_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: t2=10s ack timeout in [1, 255]");
}

#[test]
fn t3_timeout() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t3", u32_ty());
    ctx.declare_var_typed("t3_ok", i32_ty());
    // t3 = timeout for sending test frames (seconds, 1-255)
    ctx.push_obligation(ProofObligation::assume("t3v", "t3 == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "t3o_def",
        "t3_ok == if t3 >= 1 && t3 <= 255 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "t3_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: t3=20s test frame timeout in [1, 255]");
}

#[test]
fn apdu_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("apdu_len", u32_ty());
    ctx.declare_var_typed("len_ok", i32_ty());
    // Max APDU length: 253 bytes (255 minus 2-byte start/length fields)
    ctx.push_obligation(ProofObligation::assume("al", "apdu_len == 253"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if apdu_len >= 1 && apdu_len <= 253 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 104: APDU length 253 in [1, 253] bytes");
}
