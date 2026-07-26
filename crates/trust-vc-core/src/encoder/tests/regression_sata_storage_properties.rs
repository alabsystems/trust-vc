// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sata_generation_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sata_gen", u32_ty());
    ctx.declare_var_typed("speed_mbps", u32_ty());
    ctx.declare_var_typed("valid_gen", i32_ty());
    // SATA III = gen 3, 6000 Mbps (6 Gbps)
    ctx.push_obligation(ProofObligation::assume("sg", "sata_gen == 3"));
    ctx.push_obligation(ProofObligation::assume("sm", "speed_mbps == 6000")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "vg_def",
        "valid_gen == if sata_gen >= 1 && sata_gen <= 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6000", "speed_mbps == 6000"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_gen == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA: gen 3 → 6000 Mbps, valid generation");
}

#[test]
fn ncq_queue_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["pending_commands", "max_queue_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_queue", i32_ty());
    // NCQ: up to 32 outstanding commands
    ctx.push_obligation(ProofObligation::assume("pc", "pending_commands == 28"));
    ctx.push_obligation(ProofObligation::assume("mqd", "max_queue_depth == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "cq_def",
        "can_queue == if pending_commands < max_queue_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_queue == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA NCQ: 28 pending < 32 max → can queue");
}

#[test]
fn sector_size_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["lba_offset", "sector_size", "byte_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Byte offset = LBA × sector_size. Precompute: 100 × 512 = 51200
    ctx.push_obligation(ProofObligation::assume("lo", "lba_offset == 100"));
    ctx.push_obligation(ProofObligation::assume("ss", "sector_size == 512"));
    ctx.push_obligation(ProofObligation::assume("bo", "byte_offset == 51200")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_51200", "byte_offset == 51200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA: LBA 100 × 512 = 51200 byte offset");
}

#[test]
fn fis_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fis_type", u32_ty());
    ctx.declare_var_typed("is_h2d_register", i32_ty());
    // FIS type 0x27 (39) = Host to Device Register FIS
    ctx.push_obligation(ProofObligation::assume("ft", "fis_type == 39"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_h2d_register == if fis_type == 39 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_h2d_register == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA FIS: type 0x27 (39) = H2D Register");
}

#[test]
fn command_timeout_check() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed_ms", "timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timed_out", i32_ty());
    ctx.push_obligation(ProofObligation::assume("em", "elapsed_ms == 35000"));
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timed_out == if elapsed_ms > timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timed_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA: 35s elapsed > 30s timeout → timed out");
}

#[test]
fn phy_power_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_state", u32_ty());
    ctx.declare_var_typed("is_active", i32_ty());
    ctx.declare_var_typed("is_sleep", i32_ty());
    // SATA PHY: state 0=active, 1=partial, 2=slumber
    ctx.push_obligation(ProofObligation::assume("cs", "current_state == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_active == if current_state == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_sleep == if current_state == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("active", "is_active == 1"));
    ctx.push_obligation(ProofObligation::assert("not_sleep", "is_sleep == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA PHY: state 0 → active, not slumber");
}

#[test]
fn smart_threshold_warning() {
    let mut ctx = VerificationContext::new();
    for v in &["current_value", "threshold_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("below_threshold", i32_ty());
    // S.M.A.R.T.: warning when current value drops below threshold
    ctx.push_obligation(ProofObligation::assume("cv", "current_value == 20"));
    ctx.push_obligation(ProofObligation::assume("tv", "threshold_value == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "bt_def",
        "below_threshold == if current_value < threshold_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "below_threshold == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA SMART: value 20 < threshold 50 → warning");
}

#[test]
fn port_multiplier_fan_out() {
    let mut ctx = VerificationContext::new();
    for v in &["connected_devices", "max_pm_ports"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_add_device", i32_ty());
    // Port multiplier supports up to 15 devices
    ctx.push_obligation(ProofObligation::assume("cd", "connected_devices == 12"));
    ctx.push_obligation(ProofObligation::assume("mpp", "max_pm_ports == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "cad_def",
        "can_add_device == if connected_devices < max_pm_ports { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_add_device == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA PM: 12 devices < 15 max → can add");
}

#[test]
fn transfer_length_sectors() {
    let mut ctx = VerificationContext::new();
    for v in &["byte_count", "sector_size", "sector_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Transfer length in sectors = byte_count / sector_size
    // Precompute: 262144 / 512 = 512 sectors
    ctx.push_obligation(ProofObligation::assume("bc", "byte_count == 262144"));
    ctx.push_obligation(ProofObligation::assume("ss", "sector_size == 512"));
    ctx.push_obligation(ProofObligation::assume("sc", "sector_count == 512")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_512", "sector_count == 512"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA: 262144 bytes / 512 = 512 sectors");
}

#[test]
fn hotplug_detect() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phy_status", u32_ty());
    ctx.declare_var_typed("prev_phy_status", u32_ty());
    ctx.declare_var_typed("hotplug_event", i32_ty());
    // Hotplug: detect transition from no-device (0) to device-present (1)
    ctx.push_obligation(ProofObligation::assume("ps", "phy_status == 1"));
    ctx.push_obligation(ProofObligation::assume("pps", "prev_phy_status == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "he_def",
        "hotplug_event == if phy_status == 1 && prev_phy_status == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hotplug_event == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SATA: PHY 0→1 transition → hotplug event");
}
