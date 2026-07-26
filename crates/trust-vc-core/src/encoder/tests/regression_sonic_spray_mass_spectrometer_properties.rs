// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Nebulizer gas pressure (x10 psi) — bounded [10, 1000].
/// 10 represents 1.0 psi, 1000 represents 100.0 psi.
#[test]
fn test_sonic_spray_gas_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gp_a",
        "gas_x10 >= 10 && gas_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gp_c",
        "gas_x10 >= 10 && gas_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nebulizer gas pressure x10 in [10, 1000] representing 1.0-100.0 psi",
    );
}

/// Test 2: Liquid flow rate (x100 uL/min) — bounded [1, 100000].
/// 1 represents 0.01 uL/min, 100000 represents 1000.00 uL/min.
#[test]
fn test_sonic_spray_flow_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "flow_x100 >= 1 && flow_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "flow_x100 >= 1 && flow_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x100 in [1, 100000] representing 0.01-1000.00 uL/min",
    );
}

/// Test 3: Capillary inner diameter (x10 um) — bounded [10, 5000].
/// 10 represents 1.0 um, 5000 represents 500.0 um.
#[test]
fn test_sonic_spray_capillary_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cd_a",
        "cap_x10 >= 10 && cap_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cd_c",
        "cap_x10 >= 10 && cap_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capillary diameter x10 in [10, 5000] representing 1.0-500.0 um",
    );
}

/// Test 4: Mass range (m/z) — bounded [10, 4000].
#[test]
fn test_sonic_spray_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mz_a", "mz >= 10 && mz <= 4000"));
    ctx.push_obligation(ProofObligation::assert("mz_c", "mz >= 10 && mz <= 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range in [10, 4000] m/z");
}

/// Test 5: Orifice-to-capillary distance (x100 mm) — bounded [1, 500].
/// 1 represents 0.01 mm, 500 represents 5.00 mm.
#[test]
fn test_sonic_spray_orifice_distance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dist_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dist_a",
        "dist_x100 >= 1 && dist_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dist_c",
        "dist_x100 >= 1 && dist_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "orifice distance x100 in [1, 500] representing 0.01-5.00 mm",
    );
}

/// Test 6: Desolvation temperature offset +100 (deg C) — bounded [100, 600].
/// 100 represents 0 C, 600 represents 500 C.
#[test]
fn test_sonic_spray_desolvation_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("desolv_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "desolv_temp >= 100 && desolv_temp <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "desolv_temp >= 100 && desolv_temp <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "desolvation temp offset+100 in [100, 600] representing 0-500 C",
    );
}

/// Test 7: Nebulizer gas — 3-way disjunction.
/// 1=nitrogen, 2=helium, 3=compressed-air.
#[test]
fn test_sonic_spray_nebulizer_gas_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("neb_gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ng_a",
        "neb_gas == 1 || neb_gas == 2 || neb_gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ng_c",
        "neb_gas >= 1 && neb_gas <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nebulizer gas 3-way (nitrogen/helium/compressed-air)",
    );
}

/// Test 8: Spray geometry — 3-way disjunction.
/// 1=coaxial, 2=cross-flow, 3=orthogonal.
#[test]
fn test_sonic_spray_geometry_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geom", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "geom_a",
        "geom == 1 || geom == 2 || geom == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("geom_c", "geom >= 1 && geom <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray geometry 3-way (coaxial/cross-flow/orthogonal)",
    );
}

/// Test 9: Detection mode — 3-way disjunction.
/// 1=full-scan, 2=SIM, 3=MRM.
#[test]
fn test_sonic_spray_detection_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dm_a",
        "det_mode == 1 || det_mode == 2 || det_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dm_c",
        "det_mode >= 1 && det_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection mode 3-way (full-scan/SIM/MRM)");
}

/// Test 10: Voltage-free ionization flag — boolean.
/// 0=with-voltage, 1=voltage-free.
#[test]
fn test_sonic_spray_voltage_free_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage-free ionization flag is boolean (0 or 1)");
}
