// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Nuclear/ionizing radiation detector properties for process and safety applications.
// Detector type codes: 1=Geiger-Muller, 2=scintillation, 3=semiconductor,
//                      4=ionization chamber, 5=proportional counter
// Radiation type codes: 1=alpha, 2=beta, 3=gamma, 4=neutron

#[test]
fn detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("det_type_val", "det_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_detector_type",
        "det_type == 1 || det_type == 2 || det_type == 3 || det_type == 4 || det_type == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scintillation detector (type 2) is valid 5-way detector type",
    );
}

#[test]
fn energy_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_energy_kev", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "max_energy_val",
        "max_energy_kev == 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_in_range",
        "max_energy_kev >= 10 && max_energy_kev <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max energy 3000 keV within valid range 10-10000 keV",
    );
}

#[test]
fn count_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_count_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "count_rate_val",
        "max_count_rate == 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "count_rate_bounded",
        "max_count_rate <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max count rate 100000 cps within 1000000 cps limit",
    );
}

#[test]
fn dead_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dead_time_us", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dead_time_val",
        "dead_time_us == 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dead_time_bounded",
        "dead_time_us <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dead time 100 us within 1000 us maximum");
}

#[test]
fn radiation_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rad_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rad_type_val", "rad_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_radiation_type",
        "rad_type == 1 || rad_type == 2 || rad_type == 3 || rad_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gamma radiation (type 3) is valid 4-way radiation type",
    );
}

#[test]
fn sensitivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensitivity_cps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sensitivity_val",
        "sensitivity_cps == 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sensitivity_in_range",
        "sensitivity_cps >= 1 && sensitivity_cps <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity 100 counts per uSv/h within range 1-10000",
    );
}

#[test]
fn dose_rate_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_dose_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "max_dose_rate_val",
        "max_dose_rate == 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dose_rate_in_range",
        "max_dose_rate >= 1 && max_dose_rate <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max dose rate 100000 uSv/h (100 mSv/h) within range 1-10000000",
    );
}

#[test]
fn high_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bias_voltage", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bias_voltage_val",
        "bias_voltage == 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_in_range",
        "bias_voltage >= 100 && bias_voltage <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector bias voltage 900 V within range 100-2000 V",
    );
}

#[test]
fn alarm_threshold() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm_setpoint", u32_ty());
    ctx.push_obligation(ProofObligation::assume("alarm_val", "alarm_setpoint == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "alarm_in_range",
        "alarm_setpoint >= 1 && alarm_setpoint <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "alarm setpoint 25 uSv/h within range 1-10000 uSv/h",
    );
}

#[test]
fn measurement_interval() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("integration_time", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "interval_val",
        "integration_time == 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "interval_in_range",
        "integration_time >= 1 && integration_time <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "integration time 10 s within range 1-3600 s");
}
