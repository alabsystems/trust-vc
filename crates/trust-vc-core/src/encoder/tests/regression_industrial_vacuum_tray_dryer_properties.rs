// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Industrial vacuum tray dryer property verification tests.
// All physical quantities use integer scaling to avoid floating-point.

use super::*;

/// Test 1: Operating pressure (scaled ×10, units: mbar).
/// Vacuum tray dryers operate between 0.01 mbar and 10,000 mbar.
/// press_x10 encodes pressure × 10, so valid range is (0, 100000).
#[test]
fn test_vacuum_tray_dryer_operating_pressure_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_bounds",
        "press_x10 > 0 && press_x10 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_positive",
        "press_x10 >= 1 && press_x10 <= 99999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating pressure within valid scaled range");
}

/// Test 2: Shelf temperature (offset +100, units: °C).
/// Actual temperature = temp_off - 100, covering -99 °C to +399 °C.
/// temp_off in (100, 500) keeps the offset positive.
#[test]
fn test_vacuum_tray_dryer_shelf_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_bounds",
        "temp_off > 100 && temp_off < 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_positive_offset",
        "temp_off >= 101 && temp_off <= 499",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf temperature offset within valid range");
}

/// Test 3: Shelf area (scaled ×10, units: m²).
/// Typical range 0.1 m² to 499.9 m², encoded as area_x10 in (0, 5000).
#[test]
fn test_vacuum_tray_dryer_shelf_area_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_bounds",
        "area_x10 > 0 && area_x10 < 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_positive",
        "area_x10 >= 1 && area_x10 <= 4999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf area within valid scaled range");
}

/// Test 4: Condenser capacity (scaled ×10, units: kg/h).
/// Range 0.1 kg/h to 4999.9 kg/h, encoded as cap_x10 in (0, 50000).
#[test]
fn test_vacuum_tray_dryer_condenser_capacity_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capacity_bounds",
        "cap_x10 > 0 && cap_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_positive",
        "cap_x10 >= 1 && cap_x10 <= 49999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "condenser capacity within valid scaled range");
}

/// Test 5: Drying time (scaled ×100, units: hours).
/// Range 0.01 h to 499.99 h, encoded as time_x100 in (0, 50000).
#[test]
fn test_vacuum_tray_dryer_drying_time_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_bounds",
        "time_x100 > 0 && time_x100 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_positive",
        "time_x100 >= 1 && time_x100 <= 49999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying time within valid scaled range");
}

/// Test 6: Number of shelves bounded between 1 and 30 inclusive.
#[test]
fn test_vacuum_tray_dryer_shelf_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelves", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shelf_bounds",
        "shelves >= 1 && shelves <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shelf_valid",
        "shelves > 0 && shelves < 31",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf count within 1-30 range");
}

/// Test 7: Heating method disjunction.
/// 1 = hot-water, 2 = steam, 3 = electric.
#[test]
fn test_vacuum_tray_dryer_heating_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_valid",
        "heat == 1 || heat == 2 || heat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heat_in_range",
        "heat >= 1 && heat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method is one of hot-water, steam, or electric",
    );
}

/// Test 8: Vacuum pump type disjunction.
/// 1 = rotary-vane, 2 = liquid-ring, 3 = dry-scroll.
#[test]
fn test_vacuum_tray_dryer_vacuum_pump_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pump_valid",
        "pump == 1 || pump == 2 || pump == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pump_in_range",
        "pump >= 1 && pump <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vacuum pump type is one of rotary-vane, liquid-ring, or dry-scroll",
    );
}

/// Test 9: Condenser type disjunction.
/// 1 = shell-tube, 2 = plate, 3 = coil.
#[test]
fn test_vacuum_tray_dryer_condenser_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cond_valid",
        "cond == 1 || cond == 2 || cond == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cond_in_range",
        "cond >= 1 && cond <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condenser type is one of shell-tube, plate, or coil",
    );
}

/// Test 10: Automatic leak detection flag.
/// Boolean encoded as i32: 0 = disabled, 1 = enabled.
#[test]
fn test_vacuum_tray_dryer_leak_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_detect", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "leak_detect == 0 || leak_detect == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "leak_detect >= 0 && leak_detect <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leak detection flag is a valid boolean encoding");
}
