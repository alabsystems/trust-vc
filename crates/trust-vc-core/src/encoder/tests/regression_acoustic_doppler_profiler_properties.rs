// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frequency_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // ADCP operating frequency: 75-3000 kHz (e.g., 300 kHz broadband)
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 75"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: 300kHz in [75, 3000] → frequency OK");
}

#[test]
fn range_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["range_m", "min_range_m", "max_range_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // ADCP profiling range: 1-1000 meters
    ctx.push_obligation(ProofObligation::assume("rm", "range_m == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_range_m == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_range_m == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_m >= min_range_m && range_m <= max_range_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: 200m range in [1, 1000] → range OK");
}

#[test]
fn beam_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["beams", "min_beams", "max_beams"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("beams_ok", i32_ty());
    // ADCP beam count: 2-9 (typically 4 for Janus configuration)
    ctx.push_obligation(ProofObligation::assume("b", "beams == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_beams == 2"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_beams == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "beams_ok == if beams >= min_beams && beams <= max_beams { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "beams_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: 4 beams in [2, 9] → beam count OK");
}

#[test]
fn cell_size_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["cell_x10", "min_cell_x10", "max_cell_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cell_ok", i32_ty());
    // ADCP depth cell size (×10 meters): 0.5m → 5, range [1, 500] (0.1m to 50.0m)
    ctx.push_obligation(ProofObligation::assume("cx", "cell_x10 == 5")); // 0.5m
    ctx.push_obligation(ProofObligation::assume("mn", "min_cell_x10 == 1")); // 0.1m
    ctx.push_obligation(ProofObligation::assume("mx", "max_cell_x10 == 500")); // 50.0m
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cell_ok == if cell_x10 >= min_cell_x10 && cell_x10 <= max_cell_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cell_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: 0.5m cell size in [0.1, 50.0] → cell OK");
}

#[test]
fn mounting_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mounting", u32_ty());
    ctx.declare_var_typed("valid_mount", i32_ty());
    // Mounting type: 1=bottom-mounted, 2=vessel-mounted, 3=buoy-mounted
    ctx.push_obligation(ProofObligation::assume("m", "mounting == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mount == if mounting == 1 || mounting == 2 || mounting == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mount == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: mounting=2 (vessel-mounted) → valid");
}

#[test]
fn velocity_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x100", "min_acc_x100", "max_acc_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Velocity accuracy (×100 m/s): 0.01 m/s → 1, range [1, 100] (0.01 to 1.00 m/s)
    ctx.push_obligation(ProofObligation::assume("ax", "acc_x100 == 5")); // 0.05 m/s
    ctx.push_obligation(ProofObligation::assume("mn", "min_acc_x100 == 1")); // 0.01 m/s
    ctx.push_obligation(ProofObligation::assume("mx", "max_acc_x100 == 100")); // 1.00 m/s
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if acc_x100 >= min_acc_x100 && acc_x100 <= max_acc_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: 0.05 m/s accuracy in [0.01, 1.00] → OK");
}

#[test]
fn ping_rate_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["ping_hz", "min_ping_hz", "max_ping_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ping_ok", i32_ty());
    // ADCP ping rate: 1-100 Hz
    ctx.push_obligation(ProofObligation::assume("ph", "ping_hz == 8"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ping_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ping_hz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "ping_ok == if ping_hz >= min_ping_hz && ping_hz <= max_ping_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ping_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: 8Hz ping rate in [1, 100] → ping OK");
}

#[test]
fn communication_interface_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // Communication interface: 1=RS-232, 2=RS-485, 3=Ethernet
    ctx.push_obligation(ProofObligation::assume("c", "comm == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_comm == if comm == 1 || comm == 2 || comm == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: comm=3 (Ethernet) → valid interface");
}

#[test]
fn operating_depth_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["depth_m", "min_depth_m", "max_depth_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth_ok", i32_ty());
    // ADCP operating depth: 1-6000 meters
    ctx.push_obligation(ProofObligation::assume("dm", "depth_m == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_depth_m == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_depth_m == 6000"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if depth_m >= min_depth_m && depth_m <= max_depth_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: 500m depth in [1, 6000] → depth OK");
}

#[test]
fn bottom_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bt_enabled", i32_ty());
    ctx.declare_var_typed("bt_valid", i32_ty());
    // Bottom tracking: boolean flag (0=disabled, 1=enabled)
    ctx.push_obligation(ProofObligation::assume("bt", "bt_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "bv_def",
        "bt_valid == if bt_enabled == 0 || bt_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bt_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADCP: bt_enabled=1 → valid boolean flag");
}
