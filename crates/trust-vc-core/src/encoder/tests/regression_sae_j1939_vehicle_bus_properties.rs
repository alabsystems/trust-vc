// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_kbps", u32_ty());
    // SAE J1939 mandates a fixed 250 kbps CAN bus data rate
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate_kbps == 250"));
    ctx.push_obligation(ProofObligation::assert("fixed_rate", "rate_kbps == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: fixed CAN bus rate is 250 kbps");
}

#[test]
fn source_address() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sa", u32_ty());
    ctx.declare_var_typed("sa_ok", i32_ty());
    // J1939 source address: 8-bit field, 0-253 valid (254-255 reserved)
    ctx.push_obligation(ProofObligation::assume("sa_val", "sa == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "sa_ok == if sa >= 0 && sa <= 253 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "sa_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: source address 128 in valid range 0-253");
}

#[test]
fn pgn_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pgn", u32_ty());
    ctx.declare_var_typed("pgn_ok", i32_ty());
    // Parameter Group Number: 18-bit field, max 262143
    ctx.push_obligation(ProofObligation::assume("pgn_val", "pgn == 65280"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "pgn_ok == if pgn >= 0 && pgn <= 262143 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "pgn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: PGN 65280 in valid 18-bit range 0-262143");
}

#[test]
fn priority() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prio", u32_ty());
    ctx.declare_var_typed("prio_ok", i32_ty());
    // J1939 priority: 3-bit field, values 0-7
    ctx.push_obligation(ProofObligation::assume("prio_val", "prio == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "prio_ok == if prio >= 0 && prio <= 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "prio_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: priority 3 in valid 3-bit range 0-7");
}

#[test]
fn data_page() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dp", u32_ty());
    ctx.declare_var_typed("dp_ok", i32_ty());
    // Data page bit: must be exactly 0 or 1
    ctx.push_obligation(ProofObligation::assume("dp_val", "dp == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "dp_ok == if dp == 0 || dp == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "dp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: data page bit 0 is valid (0 or 1)");
}

#[test]
fn transport_protocol() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tp", u32_ty());
    ctx.declare_var_typed("tp_ok", i32_ty());
    // Transport protocol modes: 1=single frame, 2=BAM (broadcast), 3=CMDT (connection)
    ctx.push_obligation(ProofObligation::assume("tp_val", "tp == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "tp_ok == if tp == 1 || tp == 2 || tp == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "tp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: transport protocol 2 (BAM) is valid mode");
}

#[test]
fn ecu_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ecus", u32_ty());
    ctx.declare_var_typed("ecus_ok", i32_ty());
    // Max ECUs on a J1939 bus segment: 1-253 (addresses 0-253 available)
    ctx.push_obligation(ProofObligation::assume("ecus_val", "ecus == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "ecus_ok == if ecus >= 1 && ecus <= 253 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "ecus_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: 30 ECUs in valid range 1-253");
}

#[test]
fn message_cycle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_ms", u32_ty());
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // Periodic message cycle time: 10-10000 ms typical range
    ctx.push_obligation(ProofObligation::assume("cycle_val", "cycle_ms == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "cycle_ok == if cycle_ms >= 10 && cycle_ms <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: cycle time 100 ms in valid range 10-10000");
}

#[test]
fn spn_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spn_bits", u32_ty());
    ctx.declare_var_typed("spn_ok", i32_ty());
    // Suspect Parameter Number length: 1-64 bits per signal
    ctx.push_obligation(ProofObligation::assume("spn_val", "spn_bits == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "spn_ok == if spn_bits >= 1 && spn_bits <= 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "spn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: SPN length 16 bits in valid range 1-64");
}

#[test]
fn address_claim_name() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("name_field", u32_ty());
    ctx.declare_var_typed("name_ok", i32_ty());
    // NAME field: 64-bit identity but validated as bounded (min 1, nonzero required)
    ctx.push_obligation(ProofObligation::assume("name_val", "name_field == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "name_ok == if name_field >= 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "name_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "J1939: NAME field 1000000 >= 1 (nonzero identity)");
}
