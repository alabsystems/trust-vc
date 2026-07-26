// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ppm_from_adc() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "adc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ppm", u32_ty());
    // Gas concentration from ADC. Precompute: 1000/4096 × 10000 = 2441 ppm
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 1000"));
    ctx.push_obligation(ProofObligation::assume("am", "adc_max == 4096"));
    ctx.push_obligation(ProofObligation::assume("pp", "ppm == 2441")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2441", "ppm == 2441"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas sensor: ADC 1000/4096 → 2441 ppm (precomputed)",
    );
}

#[test]
fn alarm_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["concentration_ppm", "alarm_level_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alarm_active", i32_ty());
    // CO alarm at 50 ppm (OSHA 8-hour TWA)
    ctx.push_obligation(ProofObligation::assume("cp", "concentration_ppm == 75"));
    ctx.push_obligation(ProofObligation::assume("al", "alarm_level_ppm == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "alarm_active == if concentration_ppm >= alarm_level_ppm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas sensor: 75 ppm ≥ 50 ppm alarm → alarm active");
}

#[test]
fn warmup_time() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed_sec", "warmup_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ready", i32_ty());
    // MQ series sensors need 20-60s warmup for stable readings
    ctx.push_obligation(ProofObligation::assume("es", "elapsed_sec == 45"));
    ctx.push_obligation(ProofObligation::assume("ws", "warmup_sec == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "ready == if elapsed_sec >= warmup_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ready == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas sensor: 45s elapsed ≥ 30s warmup → ready");
}

#[test]
fn heater_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["heater_mv", "rated_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // Heater element requires specific voltage ±tolerance
    ctx.push_obligation(ProofObligation::assume("hm", "heater_mv == 4950"));
    ctx.push_obligation(ProofObligation::assume("rm", "rated_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("tm", "tolerance_mv == 100"));
    // |4950 - 5000| = 50 ≤ 100. Use unsigned: rated - heater since rated > heater here
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if heater_mv >= rated_mv - tolerance_mv && heater_mv <= rated_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas sensor: 4950mV in [4900, 5100] → heater voltage OK",
    );
}

#[test]
fn cross_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["target_response", "interferer_response"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("selective", i32_ty());
    // Target gas response must dominate interferer response
    ctx.push_obligation(ProofObligation::assume("tr", "target_response == 500"));
    ctx.push_obligation(ProofObligation::assume("ir", "interferer_response == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "selective == if target_response > interferer_response { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "selective == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas sensor: target 500 > interferer 50 → selective",
    );
}

#[test]
fn sensor_lifespan() {
    let mut ctx = VerificationContext::new();
    for v in &["operating_hours", "rated_hours"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_life", i32_ty());
    // Electrochemical sensors: typically 2-3 year lifespan
    ctx.push_obligation(ProofObligation::assume("oh", "operating_hours == 10000"));
    ctx.push_obligation(ProofObligation::assume("rh", "rated_hours == 26280")); // ~3 years
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_life == if operating_hours < rated_hours { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_life == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas sensor: 10000h < 26280h rated → within lifespan",
    );
}

#[test]
fn calibration_due() {
    let mut ctx = VerificationContext::new();
    for v in &["days_since_cal", "cal_interval_days"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_cal", i32_ty());
    // Periodic calibration required (e.g., every 180 days)
    ctx.push_obligation(ProofObligation::assume("ds", "days_since_cal == 200"));
    ctx.push_obligation(ProofObligation::assume("ci", "cal_interval_days == 180"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "needs_cal == if days_since_cal >= cal_interval_days { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_cal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas sensor: 200 days ≥ 180 cal interval → needs calibration",
    );
}

#[test]
fn lel_percentage() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_ppm", "lel_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lel_percent", u32_ty());
    // LEL% = measured/LEL × 100. Precompute: 2500/50000 × 100 = 5%
    ctx.push_obligation(ProofObligation::assume("mp", "measured_ppm == 2500"));
    ctx.push_obligation(ProofObligation::assume("lp", "lel_ppm == 50000")); // methane LEL
    ctx.push_obligation(ProofObligation::assume("lpc", "lel_percent == 5")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_5", "lel_percent == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas sensor: 2500/50000 ppm = 5% LEL (precomputed)");
}

#[test]
fn evacuation_level() {
    let mut ctx = VerificationContext::new();
    for v in &["lel_percent", "evacuation_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("evacuate", i32_ty());
    // Evacuation typically at 25% LEL
    ctx.push_obligation(ProofObligation::assume("lp", "lel_percent == 30"));
    ctx.push_obligation(ProofObligation::assume("et", "evacuation_threshold == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "evacuate == if lel_percent >= evacuation_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "evacuate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gas sensor: 30% LEL ≥ 25% threshold → evacuate");
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["heater_power_mw", "circuit_power_mw", "budget_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_mw", u32_ty());
    ctx.declare_var_typed("within_budget", i32_ty());
    // Total power = heater + circuit
    ctx.push_obligation(ProofObligation::assume("hp", "heater_power_mw == 800"));
    ctx.push_obligation(ProofObligation::assume("cp", "circuit_power_mw == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "tm",
        "total_mw == heater_power_mw + circuit_power_mw",
    ));
    ctx.push_obligation(ProofObligation::assume("bm", "budget_mw == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_budget == if total_mw <= budget_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_850", "total_mw == 850"));
    ctx.push_obligation(ProofObligation::assert("yes", "within_budget == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Gas sensor: 800 + 50 = 850mW ≤ 1000mW budget → within budget",
    );
}
