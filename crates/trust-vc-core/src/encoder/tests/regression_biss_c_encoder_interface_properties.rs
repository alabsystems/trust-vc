// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn clock_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["mhz", "mhz_min", "mhz_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // BiSS-C clock frequency in MHz: value 5, valid range 1 to 10
    ctx.push_obligation(ProofObligation::assume("cf_val", "mhz == 5"));
    ctx.push_obligation(ProofObligation::assume("cf_min", "mhz_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cf_max", "mhz_max == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "cf_in_range",
        "mhz >= mhz_min && mhz <= mhz_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BiSS-C clock frequency 5 MHz in range [1,10]");
}

#[test]
fn single_turn_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["st_bits", "st_min", "st_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Single-turn position resolution in bits: value 18, valid range 1 to 32
    ctx.push_obligation(ProofObligation::assume("sb_val", "st_bits == 18"));
    ctx.push_obligation(ProofObligation::assume("sb_min", "st_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sb_max", "st_max == 32"));
    ctx.push_obligation(ProofObligation::assert(
        "sb_in_range",
        "st_bits >= st_min && st_bits <= st_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "single-turn resolution 18 bits in range [1,32]");
}

#[test]
fn multi_turn_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["mt_bits", "mt_min", "mt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Multi-turn revolution counting in bits: value 12, valid range 0 to 16
    ctx.push_obligation(ProofObligation::assume("mb_val", "mt_bits == 12"));
    ctx.push_obligation(ProofObligation::assume("mb_min", "mt_min == 0"));
    ctx.push_obligation(ProofObligation::assume("mb_max", "mt_max == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "mb_in_range",
        "mt_bits >= mt_min && mt_bits <= mt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multi-turn counting 12 bits in range [0,16]");
}

#[test]
fn crc_polynomial() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crc_poly", u32_ty());
    ctx.declare_var_typed("valid_poly", i32_ty());
    // CRC polynomial types: 1=CRC-6, 2=CRC-8, 3=CRC-16
    ctx.push_obligation(ProofObligation::assume("cp_val", "crc_poly == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "valid_poly == if crc_poly == 1 || crc_poly == 2 || crc_poly == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cp_chk", "valid_poly == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CRC polynomial 1 (CRC-6) is valid BiSS-C type");
}

#[test]
fn data_length() {
    let mut ctx = VerificationContext::new();
    for v in &["d_bits", "d_min", "d_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Total data length in bits per frame: value 32, valid range 1 to 64
    ctx.push_obligation(ProofObligation::assume("dl_val", "d_bits == 32"));
    ctx.push_obligation(ProofObligation::assume("dl_min", "d_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dl_max", "d_max == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "dl_in_range",
        "d_bits >= d_min && d_bits <= d_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BiSS-C data length 32 bits in range [1,64]");
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_type", u32_ty());
    ctx.declare_var_typed("valid_sens", i32_ty());
    // Sensor types: 1=optical, 2=magnetic, 3=capacitive, 4=inductive
    ctx.push_obligation(ProofObligation::assume("st_val", "sens_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "valid_sens == if sens_type == 1 || sens_type == 2 || sens_type == 3 || sens_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_chk", "valid_sens == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensor type 2 (magnetic) is valid BiSS-C sensor");
}

#[test]
fn protocol_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("proto_mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Protocol modes: 1=BiSS-C sensor, 2=BiSS-C actuator, 3=BiSS-Safety
    ctx.push_obligation(ProofObligation::assume("pm_val", "proto_mode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pm_def",
        "valid_mode == if proto_mode == 1 || proto_mode == 2 || proto_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pm_chk", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "protocol mode 3 (BiSS-Safety) is valid mode");
}

#[test]
fn register_access() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reg_access", i32_ty());
    ctx.declare_var_typed("access_ok", i32_ty());
    // Register access support: 1=supported, 0=not supported
    ctx.push_obligation(ProofObligation::assume("ra_val", "reg_access == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "access_ok == if reg_access == 0 || reg_access == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ra_chk", "access_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "register access 1 (supported) is valid flag");
}

#[test]
fn daisy_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["devices", "dc_min", "dc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Daisy chain: devices on single BiSS-C bus, value 4, valid range 1 to 8
    ctx.push_obligation(ProofObligation::assume("dc_val", "devices == 4"));
    ctx.push_obligation(ProofObligation::assume("dc_min", "dc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dc_max", "dc_max == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "dc_in_range",
        "devices >= dc_min && devices <= dc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "daisy chain 4 devices in range [1,8]");
}

#[test]
fn error_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("err_bit", i32_ty());
    ctx.declare_var_typed("err_ok", i32_ty());
    // Error bit: 1=error active, 0=no error
    ctx.push_obligation(ProofObligation::assume("eb_val", "err_bit == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "eb_def",
        "err_ok == if err_bit == 0 || err_bit == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("eb_chk", "err_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "error bit 0 (no error) is valid BiSS-C status");
}
