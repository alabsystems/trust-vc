// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "min_cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // SERCOS III communication cycle time in microseconds
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycle_us == 31"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycle_us == 65000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_us >= min_cycle_us && cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: 250us cycle in [31, 65000] range");
}

#[test]
fn slave_count() {
    let mut ctx = VerificationContext::new();
    for v in &["slaves", "min_slaves", "max_slaves"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slaves_ok", i32_ty());
    // Maximum slaves on SERCOS III ring
    ctx.push_obligation(ProofObligation::assume("sc", "slaves == 40"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_slaves == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_slaves == 511"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "slaves_ok == if slaves >= min_slaves && slaves <= max_slaves { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slaves_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: 40 slaves in [1, 511] range");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_mbps", u32_ty());
    // SERCOS III operates at fixed 100 Mbps Ethernet
    ctx.push_obligation(ProofObligation::assume("rm", "rate_mbps == 100"));
    ctx.push_obligation(ProofObligation::assert("fixed_rate", "rate_mbps == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: fixed 100 Mbps Ethernet data rate");
}

#[test]
fn topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // Topology modes: 1=line, 2=ring, 3=star
    ctx.push_obligation(ProofObligation::assume("tp", "topo == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: topology 2 (ring) is valid");
}

#[test]
fn phase() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cp", u32_ty());
    ctx.declare_var_typed("valid_cp", i32_ty());
    // Communication phases: 0=CP0 (init), 1=CP1 (parameterization),
    // 2=CP2 (IDN config), 3=CP3 (cyclic operation), 4=CP4 (cyclic + real-time)
    ctx.push_obligation(ProofObligation::assume("ph", "cp == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cp == if cp == 0 || cp == 1 || cp == 2 || cp == 3 || cp == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: phase CP3 (cyclic operation) is valid");
}

#[test]
fn idn_count() {
    let mut ctx = VerificationContext::new();
    for v in &["idns", "min_idns", "max_idns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("idns_ok", i32_ty());
    // Identification number (IDN) parameters per slave
    ctx.push_obligation(ProofObligation::assume("ic", "idns == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_idns == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_idns == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "idns_ok == if idns >= min_idns && idns <= max_idns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "idns_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SERCOS III: 200 IDN parameters in [1, 65535] range",
    );
}

#[test]
fn at_mdt_length() {
    let mut ctx = VerificationContext::new();
    for v in &["tlen_bytes", "min_tlen", "max_tlen"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tlen_ok", i32_ty());
    // AT/MDT telegram length in bytes
    ctx.push_obligation(ProofObligation::assume("tl", "tlen_bytes == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_tlen == 4"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_tlen == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tlen_ok == if tlen_bytes >= min_tlen && tlen_bytes <= max_tlen { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tlen_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SERCOS III: 100-byte AT/MDT telegram in [4, 1024] range",
    );
}

#[test]
fn jitter() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ns", "max_jitter_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("jitter_ok", i32_ty());
    // Cycle jitter in nanoseconds, max 1000ns
    ctx.push_obligation(ProofObligation::assume("jn", "jitter_ns == 50"));
    ctx.push_obligation(ProofObligation::assume("mj", "max_jitter_ns == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "jo_def",
        "jitter_ok == if jitter_ns <= max_jitter_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "jitter_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: 50ns jitter within 1000ns max");
}

#[test]
fn hot_plug() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hp", u32_ty());
    ctx.declare_var_typed("hp_ok", i32_ty());
    // Hot-plug support: 0=no, 1=yes
    ctx.push_obligation(ProofObligation::assume("hv", "hp == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hp_ok == if hp == 0 || hp == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: hot-plug value 1 (yes) is valid");
}

#[test]
fn safety_profile() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("safety", u32_ty());
    ctx.declare_var_typed("valid_safety", i32_ty());
    // Safety profiles: 1=none, 2=CIP Safety, 3=FSoE (Fail-Safe over EtherCAT compatible)
    ctx.push_obligation(ProofObligation::assume("sf", "safety == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_safety == if safety == 1 || safety == 2 || safety == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_safety == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SERCOS III: safety profile 3 (FSoE) is valid");
}
