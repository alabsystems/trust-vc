// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn seven_bit_address_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("address", u32_ty());
    ctx.declare_var_typed("max_7bit", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "address == 104")); // 0x68 (MPU-6050)
    ctx.push_obligation(ProofObligation::assume("m", "max_7bit == 127")); // 2^7 - 1
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if address <= max_7bit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C: addr 104 <= 127 (7-bit)");
}

#[test]
fn ten_bit_address_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("address", u32_ty());
    ctx.declare_var_typed("max_10bit", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "address == 500"));
    ctx.push_obligation(ProofObligation::assume("m", "max_10bit == 1023")); // 2^10 - 1
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if address <= max_10bit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C: addr 500 <= 1023 (10-bit)");
}

#[test]
fn clock_stretching_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["base_period_ns", "stretch_ns", "actual_period_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bp", "base_period_ns == 2500")); // 400kHz
    ctx.push_obligation(ProofObligation::assume("sn", "stretch_ns == 500")); // slave stretches
    ctx.push_obligation(ProofObligation::assume(
        "ap_def",
        "actual_period_ns == base_period_ns + stretch_ns",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_3000",
        "actual_period_ns == 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "slower",
        "actual_period_ns > base_period_ns",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C stretch: 2500+500=3000ns");
}

#[test]
fn address_byte_rw_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["slave_addr", "rw_bit", "address_byte"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Address byte = (slave_addr << 1) | rw_bit
    ctx.push_obligation(ProofObligation::assume("sa", "slave_addr == 104")); // 0x68
    ctx.push_obligation(ProofObligation::assume("rw", "rw_bit == 1")); // read
    ctx.push_obligation(ProofObligation::assume(
        "ab_def",
        "address_byte == (slave_addr << 1) | rw_bit",
    ));
    ctx.push_obligation(ProofObligation::assert("is_209", "address_byte == 209")); // 0x68<<1|1 = 0xD1 = 209
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "I2C addr byte: (0x68<<1)|1 = 0xD1 = 209");
}

#[test]
fn ack_nack_response() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ack_bit", u32_ty()); // 0=ACK, 1=NACK
    ctx.declare_var_typed("acknowledged", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "ack_bit == 0")); // ACK
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acknowledged == if ack_bit == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acknowledged == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C: ack_bit=0 → acknowledged");
}

#[test]
fn bus_speed_modes() {
    // Standard=100kHz, Fast=400kHz, Fast+=1MHz, High=3.4MHz
    let mut ctx = VerificationContext::new();
    for v in &["mode", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_fast", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1")); // 0=std, 1=fast, 2=fast+, 3=high
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_khz == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "if_def",
        "is_fast == if mode == 1 && max_freq_khz == 400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_fast == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C: mode 1 → Fast (400kHz)");
}

#[test]
fn multi_master_arbitration() {
    let mut ctx = VerificationContext::new();
    for v in &["master_a_bit", "master_b_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_loses", i32_ty());
    // I2C: master sending 1 while bus reads 0 loses arbitration
    ctx.push_obligation(ProofObligation::assume("ma", "master_a_bit == 1")); // sends 1
    ctx.push_obligation(ProofObligation::assume("mb", "master_b_bit == 0")); // sends 0, wins (wired-AND)
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "a_loses == if master_a_bit > master_b_bit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_loses == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C arb: A(1) > B(0) → A loses");
}

#[test]
fn byte_transfer_with_ack() {
    // 9 clock cycles per byte: 8 data + 1 ACK
    let mut ctx = VerificationContext::new();
    for v in &["num_bytes", "clocks_per_byte", "total_clocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nb", "num_bytes == 16"));
    ctx.push_obligation(ProofObligation::assume("cpb", "clocks_per_byte == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_clocks == num_bytes * clocks_per_byte",
    ));
    ctx.push_obligation(ProofObligation::assert("is_144", "total_clocks == 144"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "I2C: 16×9=144 clocks");
}

#[test]
fn reserved_addresses() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("address", u32_ty());
    ctx.declare_var_typed("is_general_call", i32_ty());
    // General call address is 0x00
    ctx.push_obligation(ProofObligation::assume("a", "address == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "gc_def",
        "is_general_call == if address == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_general_call == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C: addr 0 → general call");
}

#[test]
fn bus_capacitance_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["bus_capacitance_pf", "max_capacitance_pf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    // Standard mode: max 400pF bus capacitance
    ctx.push_obligation(ProofObligation::assume("bc", "bus_capacitance_pf == 300"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_capacitance_pf == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if bus_capacitance_pf <= max_capacitance_pf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2C: 300pF <= 400pF max");
}
