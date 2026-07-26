// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn autoneg_speed_select() {
    let mut ctx = VerificationContext::new();
    for v in &["local_max_mbps", "remote_max_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("negotiated_mbps", u32_ty());
    // Auto-negotiation selects highest common speed
    ctx.push_obligation(ProofObligation::assume("lm", "local_max_mbps == 1000"));
    ctx.push_obligation(ProofObligation::assume("rm", "remote_max_mbps == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "n_def",
        "negotiated_mbps == if local_max_mbps < remote_max_mbps { local_max_mbps } else { remote_max_mbps }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "negotiated_mbps == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PHY autoneg: min(1000, 100) = 100 Mbps");
}

#[test]
fn link_status_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("link_status_reg", u32_ty());
    ctx.declare_var_typed("link_up", i32_ty());
    // MII register bit 2 (value 4) indicates link status
    ctx.push_obligation(ProofObligation::assume("lsr", "link_status_reg == 5")); // bits 0+2 set
    ctx.push_obligation(ProofObligation::assume("link_val", "link_up == 1")); // precomputed: 5 & 4 != 0
    ctx.push_obligation(ProofObligation::assert("yes", "link_up == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PHY: register 5 has bit 2 set → link up (precomputed)",
    );
}

#[test]
fn mdio_register_address() {
    let mut ctx = VerificationContext::new();
    for v in &["phy_addr", "reg_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_phy", i32_ty());
    ctx.declare_var_typed("valid_reg", i32_ty());
    // MDIO: 5-bit PHY address (0-31), 5-bit register address (0-31)
    ctx.push_obligation(ProofObligation::assume("pa", "phy_addr == 1"));
    ctx.push_obligation(ProofObligation::assume("ra", "reg_addr == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_phy == if phy_addr <= 31 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_reg == if reg_addr <= 31 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("phy_ok", "valid_phy == 1"));
    ctx.push_obligation(ProofObligation::assert("reg_ok", "valid_reg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PHY MDIO: addr 1 ≤ 31, reg 0 ≤ 31 → both valid");
}

#[test]
fn cable_length_estimate() {
    let mut ctx = VerificationContext::new();
    for v in &["signal_delay_ns", "propagation_speed_m_per_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cable_length_m", u32_ty());
    // Cable length ≈ delay × speed / 2 (round trip). Precompute.
    // 500ns delay, 200 m/μs → 500 × 200 / 2000 = 50m
    ctx.push_obligation(ProofObligation::assume("sd", "signal_delay_ns == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ps",
        "propagation_speed_m_per_us == 200",
    ));
    ctx.push_obligation(ProofObligation::assume("cl", "cable_length_m == 50")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_50", "cable_length_m == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PHY TDR: 500ns × 200m/μs / 2 = 50m cable (precomputed)",
    );
}

#[test]
fn energy_efficient_ethernet() {
    let mut ctx = VerificationContext::new();
    for v in &["idle_time_us", "eee_threshold_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("enter_lpi", i32_ty());
    // EEE: enter Low Power Idle when idle exceeds threshold
    ctx.push_obligation(ProofObligation::assume("it", "idle_time_us == 50"));
    ctx.push_obligation(ProofObligation::assume("et", "eee_threshold_us == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "el_def",
        "enter_lpi == if idle_time_us >= eee_threshold_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "enter_lpi == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PHY EEE: 50us idle ≥ 30us threshold → enter LPI");
}

#[test]
fn rx_error_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rx_errors", "rx_total", "error_threshold_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("error_rate_ppm", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    // Error rate in PPM. Precompute: 5 / 1000000 × 1000000 = 5 PPM
    ctx.push_obligation(ProofObligation::assume("re", "rx_errors == 5"));
    ctx.push_obligation(ProofObligation::assume("rt", "rx_total == 1000000"));
    ctx.push_obligation(ProofObligation::assume("er", "error_rate_ppm == 5")); // precomputed
    ctx.push_obligation(ProofObligation::assume("eth", "error_threshold_ppm == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if error_rate_ppm <= error_threshold_ppm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "error_rate_ppm == 5"));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PHY: 5 PPM error rate ≤ 10 PPM threshold → acceptable",
    );
}

#[test]
fn duplex_mismatch_detect() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("local_duplex", u32_ty());
    ctx.declare_var_typed("remote_duplex", u32_ty());
    ctx.declare_var_typed("mismatch", i32_ty());
    // 0 = half duplex, 1 = full duplex
    ctx.push_obligation(ProofObligation::assume("ld", "local_duplex == 1"));
    ctx.push_obligation(ProofObligation::assume("rd", "remote_duplex == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "mismatch == if local_duplex != remote_duplex { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mismatch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PHY: full ≠ half duplex → mismatch detected");
}

#[test]
fn mdi_crossover() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("local_mdi", u32_ty());
    ctx.declare_var_typed("remote_mdi", u32_ty());
    ctx.declare_var_typed("needs_crossover", i32_ty());
    // MDI-X: same mode needs crossover cable (or auto-MDIX)
    // 0 = MDI, 1 = MDI-X
    ctx.push_obligation(ProofObligation::assume("lm", "local_mdi == 0"));
    ctx.push_obligation(ProofObligation::assume("rm", "remote_mdi == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "needs_crossover == if local_mdi == remote_mdi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_crossover == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PHY: both MDI → needs crossover (or auto-MDIX)");
}

#[test]
fn loopback_test() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_pattern", "rx_pattern"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("loopback_ok", i32_ty());
    // PHY loopback: TX pattern should match RX pattern
    ctx.push_obligation(ProofObligation::assume("tp", "tx_pattern == 43690")); // 0xAAAA
    ctx.push_obligation(ProofObligation::assume("rp", "rx_pattern == 43690"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "loopback_ok == if tx_pattern == rx_pattern { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "loopback_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PHY loopback: TX 0xAAAA == RX 0xAAAA → pass");
}

#[test]
fn wake_on_lan_magic_packet() {
    let mut ctx = VerificationContext::new();
    for v in &["sync_bytes", "mac_repeats"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_bytes", u32_ty());
    ctx.declare_var_typed("valid_wol", i32_ty());
    // WOL magic packet: 6 sync bytes (0xFF) + 16 × 6-byte MAC = 102 bytes
    ctx.push_obligation(ProofObligation::assume("sb", "sync_bytes == 6"));
    ctx.push_obligation(ProofObligation::assume("mr", "mac_repeats == 96")); // 16×6 precomputed
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == sync_bytes + mac_repeats",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vw_def",
        "valid_wol == if total_bytes == 102 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_102", "total_bytes == 102"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_wol == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PHY WOL: 6 sync + 96 MAC = 102 byte magic packet");
}
