// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Industrial heat pump dryer property verification tests
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_heat_pump_dryer_cop_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cop_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cop_range",
        "cop_x100 > 0 && cop_x100 < 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cop_positive_bounded",
        "cop_x100 >= 1 && cop_x100 <= 999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "COP scaled x100 must be positive and bounded within valid range",
    );
}

#[test]
fn test_heat_pump_dryer_drying_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off > 100 && temp_off < 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_above_baseline",
        "temp_off >= 101 && temp_off <= 399",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Drying temperature offset +100 must stay within safe operating range",
    );
}

#[test]
fn test_heat_pump_dryer_airflow_rate_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 > 0 && flow_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_positive_bounded",
        "flow_x10 >= 1 && flow_x10 <= 9999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Airflow rate scaled x10 m3/min must be positive and bounded",
    );
}

#[test]
fn test_heat_pump_dryer_moisture_extraction_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moist_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "moist_range",
        "moist_x100 > 0 && moist_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "moist_positive_bounded",
        "moist_x100 >= 1 && moist_x100 <= 99999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Moisture extraction scaled x100 kg/h must be positive and bounded",
    );
}

#[test]
fn test_heat_pump_dryer_compressor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power_kw >= 1 && power_kw <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_within_bounds",
        "power_kw > 0 && power_kw < 501",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Compressor power must be bounded between 1 and 500 kW",
    );
}

#[test]
fn test_heat_pump_dryer_evaporator_coil_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coils", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "coil_range",
        "coils >= 1 && coils <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "coil_positive_bounded",
        "coils > 0 && coils < 13",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Number of evaporator coils must be between 1 and 12",
    );
}

#[test]
fn test_heat_pump_dryer_refrigerant_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ref_valid",
        "ref_type == 1 || ref_type == 2 || ref_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ref_in_known_set",
        "ref_type >= 1 && ref_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Refrigerant type must be one of R134a(1), R410A(2), or CO2(3)",
    );
}

#[test]
fn test_heat_pump_dryer_expansion_device_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dev", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dev_valid",
        "dev == 1 || dev == 2 || dev == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dev_in_known_set",
        "dev >= 1 && dev <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Expansion device must be one of TXV(1), EEV(2), or capillary(3)",
    );
}

#[test]
fn test_heat_pump_dryer_defrost_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("defrost", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "defrost_valid",
        "defrost == 1 || defrost == 2 || defrost == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "defrost_in_known_set",
        "defrost >= 1 && defrost <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Defrost method must be one of hot-gas(1), reverse-cycle(2), or electric(3)",
    );
}

#[test]
fn test_heat_pump_dryer_automatic_humidity_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_humid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "auto_humid == 0 || auto_humid == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "auto_humid >= 0 && auto_humid <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Automatic humidity control flag must be boolean (0 or 1)",
    );
}
