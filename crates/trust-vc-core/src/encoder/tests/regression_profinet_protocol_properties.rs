// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cycle_time_class() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_ms", "max_cycle_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("class_ok", i32_ty());
    // PROFINET RT: 1-10ms cycle, IRT: <1ms
    ctx.push_obligation(ProofObligation::assume("cm", "cycle_ms == 4"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycle_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "class_ok == if cycle_ms <= max_cycle_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "class_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: 4ms cycle ≤ 10ms max → RT class OK");
}

#[test]
fn device_name_length() {
    let mut ctx = VerificationContext::new();
    for v in &["name_length", "max_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // Device name: 1-240 characters (DNS compatible)
    ctx.push_obligation(ProofObligation::assume("nl", "name_length == 30"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_length == 240"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if name_length >= 1 && name_length <= max_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: name 30 chars in [1, 240] → length OK");
}

#[test]
fn io_data_size() {
    let mut ctx = VerificationContext::new();
    for v in &["io_bytes", "max_io_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // I/O data per subslot: up to 1440 bytes
    ctx.push_obligation(ProofObligation::assume("ib", "io_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_io_bytes == 1440"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if io_bytes <= max_io_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: 256 bytes I/O ≤ 1440 max → size OK");
}

#[test]
fn alarm_priority() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm_type", u32_ty());
    ctx.declare_var_typed("is_high_priority", i32_ty());
    // Alarm types: 0=diagnostic, 1=process, 2=pull, 3=plug, 4=status, 5=update
    // High priority: diagnostic (0) and process (1)
    ctx.push_obligation(ProofObligation::assume("at", "alarm_type == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_high_priority == if alarm_type == 0 || alarm_type == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_high_priority == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PROFINET: alarm_type=0 (diagnostic) → high priority",
    );
}

#[test]
fn ar_count() {
    let mut ctx = VerificationContext::new();
    for v in &["active_ars", "max_ars"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ar_ok", i32_ty());
    // Application Relations: controller-device connections
    ctx.push_obligation(ProofObligation::assume("aa", "active_ars == 2"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_ars == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "ar_ok == if active_ars <= max_ars { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ar_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: 2 ARs ≤ 8 max → AR count OK");
}

#[test]
fn frame_id_range() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_id", "min_rt_id", "max_rt_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_rt_frame", i32_ty());
    // PROFINET RT frame IDs: 0x8000-0xBFFF
    ctx.push_obligation(ProofObligation::assume("fi", "frame_id == 33000")); // ~0x80E8
    ctx.push_obligation(ProofObligation::assume("mn", "min_rt_id == 32768")); // 0x8000
    ctx.push_obligation(ProofObligation::assume("mx", "max_rt_id == 49151")); // 0xBFFF
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_rt_frame == if frame_id >= min_rt_id && frame_id <= max_rt_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_rt_frame == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PROFINET: frame 0x80E8 in [0x8000, 0xBFFF] → RT frame",
    );
}

#[test]
fn watchdog_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["watchdog_ms", "min_watchdog_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timeout_ok", i32_ty());
    // Watchdog factor × reduction ratio determines timeout
    ctx.push_obligation(ProofObligation::assume("wm", "watchdog_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mw", "min_watchdog_ms == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timeout_ok == if watchdog_ms >= min_watchdog_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timeout_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: 100ms watchdog ≥ 20ms min → timeout OK");
}

#[test]
fn slot_subslot() {
    let mut ctx = VerificationContext::new();
    for v in &["slot", "max_slots"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slot_valid", i32_ty());
    // Module slots: 0 = DAP, 1+ = I/O modules
    ctx.push_obligation(ProofObligation::assume("s", "slot == 5"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_slots == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "slot_valid == if slot < max_slots { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slot_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: slot 5 < 64 max → slot valid");
}

#[test]
fn conformance_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cc_level", u32_ty());
    ctx.declare_var_typed("supports_irt", i32_ty());
    // Conformance Class: A=basic RT, B=diagnostics, C=IRT
    // 0=CC-A, 1=CC-B, 2=CC-C
    ctx.push_obligation(ProofObligation::assume("cl", "cc_level == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "si_def",
        "supports_irt == if cc_level >= 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "supports_irt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: CC-C → supports IRT");
}

#[test]
fn gsd_version() {
    let mut ctx = VerificationContext::new();
    for v in &["gsd_version", "min_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("version_ok", i32_ty());
    // GSDML version for device description
    ctx.push_obligation(ProofObligation::assume("gv", "gsd_version == 25")); // v2.5
    ctx.push_obligation(ProofObligation::assume("mv", "min_version == 23")); // v2.3
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "version_ok == if gsd_version >= min_version { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "version_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFINET: GSDML v2.5 ≥ v2.3 min → version OK");
}
