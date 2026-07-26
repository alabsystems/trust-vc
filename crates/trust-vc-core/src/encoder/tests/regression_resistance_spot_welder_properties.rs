// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_weld_current_amps() {
    let mut ctx = VerificationContext::new();
    for v in &["current_a", "min_current", "max_current"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // Weld current in amperes
    ctx.push_obligation(ProofObligation::assume("ca", "current_a == 12000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_current == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_current == 200000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_a >= min_current && current_a <= max_current { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RSW: 12000A weld current in [1000, 200000] -> OK");
}

#[test]
fn test_electrode_force_newtons() {
    let mut ctx = VerificationContext::new();
    for v in &["force_n", "min_force", "max_force"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("force_ok", i32_ty());
    // Electrode force in newtons
    ctx.push_obligation(ProofObligation::assume("fn_", "force_n == 3500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_force == 500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_force == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "force_ok == if force_n >= min_force && force_n <= max_force { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "force_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RSW: 3500N electrode force in [500, 50000] -> OK");
}

#[test]
fn test_weld_time_ms() {
    let mut ctx = VerificationContext::new();
    for v in &["weld_ms", "min_weld", "max_weld"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("time_ok", i32_ty());
    // Weld time in milliseconds
    ctx.push_obligation(ProofObligation::assume("wm", "weld_ms == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_weld == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_weld == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "time_ok == if weld_ms >= min_weld && weld_ms <= max_weld { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "time_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RSW: 200ms weld time in [10, 2000] -> OK");
}

#[test]
fn test_controller_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_type", u32_ty());
    ctx.declare_var_typed("valid_ctrl", i32_ty());
    // Controller types: 1=constant current, 2=constant voltage, 3=adaptive
    ctx.push_obligation(ProofObligation::assume("ct", "ctrl_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_ctrl == if ctrl_type == 1 || ctrl_type == 2 || ctrl_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ctrl == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RSW: adaptive is valid controller type (3-way)");
}

#[test]
fn test_power_supply_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("psu_type", u32_ty());
    ctx.declare_var_typed("valid_psu", i32_ty());
    // Power supply types: 1=AC, 2=MFDC (mid-frequency DC), 3=capacitor discharge
    ctx.push_obligation(ProofObligation::assume("pt", "psu_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_psu == if psu_type == 1 || psu_type == 2 || psu_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_psu == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RSW: MFDC is valid power supply type (3-way)");
}

#[test]
fn test_electrode_tip_diameter_x10mm() {
    let mut ctx = VerificationContext::new();
    for v in &["tip_dia_x10", "min_dia", "max_dia"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dia_ok", i32_ty());
    // Electrode tip diameter scaled by 10 (6.0mm -> 60)
    ctx.push_obligation(ProofObligation::assume("td", "tip_dia_x10 == 60"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_dia == 30"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_dia == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dia_ok == if tip_dia_x10 >= min_dia && tip_dia_x10 <= max_dia { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dia_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RSW: 6.0mm tip diameter (x10=60) in [30, 200] -> OK",
    );
}

#[test]
fn test_sheet_thickness_max_x100mm() {
    let mut ctx = VerificationContext::new();
    for v in &["thick_x100", "min_thick", "max_thick"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("thick_ok", i32_ty());
    // Sheet thickness max scaled by 100 (3.00mm -> 300)
    ctx.push_obligation(ProofObligation::assume("tx", "thick_x100 == 300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_thick == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_thick == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "thick_ok == if thick_x100 >= min_thick && thick_x100 <= max_thick { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thick_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RSW: 3.00mm sheet thickness (x100=300) in [10, 600] -> OK",
    );
}

#[test]
fn test_squeeze_time_ms() {
    let mut ctx = VerificationContext::new();
    for v in &["squeeze_ms", "min_squeeze", "max_squeeze"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("squeeze_ok", i32_ty());
    // Squeeze time in milliseconds
    ctx.push_obligation(ProofObligation::assume("sm", "squeeze_ms == 150"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_squeeze == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_squeeze == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "squeeze_ok == if squeeze_ms >= min_squeeze && squeeze_ms <= max_squeeze { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "squeeze_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RSW: 150ms squeeze time in [10, 1000] -> OK");
}

#[test]
fn test_cooling_water_flow_lpm() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_lpm", "min_flow", "max_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Cooling water flow rate in liters per minute
    ctx.push_obligation(ProofObligation::assume("fl", "flow_lpm == 8"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_lpm >= min_flow && flow_lpm <= max_flow { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RSW: 8 L/min cooling water flow in [1, 50] -> OK");
}

#[test]
fn test_nugget_monitoring_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nugget_mon", i32_ty());
    ctx.declare_var_typed("mon_active", i32_ty());
    // Nugget monitoring system as boolean flag (i32: 1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("nm", "nugget_mon == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ma_def",
        "mon_active == if nugget_mon == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mon_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RSW: nugget monitoring enabled -> active (boolean flag)",
    );
}
