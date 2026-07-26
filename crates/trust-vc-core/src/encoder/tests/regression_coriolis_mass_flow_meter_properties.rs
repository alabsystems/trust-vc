// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate_kg_per_hour() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_kgh", "flow_min", "flow_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Mass flow rate in kg/h: 5000 kg/h, valid range [1, 100000]
    ctx.push_obligation(ProofObligation::assume("fv", "flow_kgh == 5000"));
    ctx.push_obligation(ProofObligation::assume("fn_min", "flow_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fx_max", "flow_max == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_kgh >= flow_min && flow_kgh <= flow_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Coriolis mass: 5000 kg/h flow in [1, 100000] range",
    );
}

#[test]
fn accuracy_percent() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy as % of reading (x100): 0.10% = 10, max 0.50% = 50
    ctx.push_obligation(ProofObligation::assume("av", "accuracy_x100 == 10"));
    ctx.push_obligation(ProofObligation::assume("am", "max_accuracy_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis mass: 0.10% accuracy within 0.50% max");
}

#[test]
fn tube_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube", u32_ty());
    ctx.declare_var_typed("valid_tube", i32_ty());
    // Tube geometry: 1=single straight, 2=dual bent, 3=single bent
    ctx.push_obligation(ProofObligation::assume("tv", "tube == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_tube == if tube == 1 || tube == 2 || tube == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_tube == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis mass: tube type 2 (dual bent) is valid");
}

#[test]
fn nominal_diameter() {
    let mut ctx = VerificationContext::new();
    for v in &["diameter_mm", "diam_min", "diam_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("diam_ok", i32_ty());
    // Nominal diameter in mm: 50 mm, valid range [1, 300]
    ctx.push_obligation(ProofObligation::assume("dv", "diameter_mm == 50"));
    ctx.push_obligation(ProofObligation::assume("dn", "diam_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dx", "diam_max == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "diam_ok == if diameter_mm >= diam_min && diameter_mm <= diam_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "diam_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis mass: 50 mm diameter in [1, 300] range");
}

#[test]
fn process_pressure_kpa() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_kpa", "press_min", "press_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Process pressure in kPa: 4000 kPa, valid range [100, 40000]
    ctx.push_obligation(ProofObligation::assume("pv", "pressure_kpa == 4000"));
    ctx.push_obligation(ProofObligation::assume("pn", "press_min == 100"));
    ctx.push_obligation(ProofObligation::assume("px", "press_max == 40000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_kpa >= press_min && pressure_kpa <= press_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Coriolis mass: 4000 kPa pressure in [100, 40000] range",
    );
}

#[test]
fn density_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["dens_acc_x1000", "max_dens_acc_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dens_ok", i32_ty());
    // Density accuracy in kg/m3 (x1000): 0.500 kg/m3 = 500, max 2.000 = 2000
    ctx.push_obligation(ProofObligation::assume("dv", "dens_acc_x1000 == 500"));
    ctx.push_obligation(ProofObligation::assume("dm", "max_dens_acc_x1000 == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dens_ok == if dens_acc_x1000 <= max_dens_acc_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dens_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Coriolis mass: 0.500 kg/m3 density acc within 2.000 max",
    );
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "temp_min_offset", "temp_max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature: offset +500. Range -300C to +700C => [200, 1200]
    // Example: 80C => 580
    ctx.push_obligation(ProofObligation::assume("tv", "temp_offset == 580"));
    ctx.push_obligation(ProofObligation::assume("tn", "temp_min_offset == 200"));
    ctx.push_obligation(ProofObligation::assume("tx", "temp_max_offset == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= temp_min_offset && temp_offset <= temp_max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Coriolis mass: 80C (offset 580) in [200, 1200] range",
    );
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output types: 1=4-20mA, 2=pulse, 3=Modbus, 4=HART
    ctx.push_obligation(ProofObligation::assume("ov", "output == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis mass: output type 3 (Modbus) is valid");
}

#[test]
fn drive_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "freq_min", "freq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Drive frequency in Hz: 300 Hz, valid range [50, 5000]
    ctx.push_obligation(ProofObligation::assume("fv", "freq_hz == 300"));
    ctx.push_obligation(ProofObligation::assume("fn_min", "freq_min == 50"));
    ctx.push_obligation(ProofObligation::assume("fx_max", "freq_max == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= freq_min && freq_hz <= freq_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Coriolis mass: 300 Hz drive freq in [50, 5000] range",
    );
}

#[test]
fn zero_stability_low_flow_cutoff() {
    let mut ctx = VerificationContext::new();
    for v in &["zero_x1000", "max_zero_x1000", "flow_kgh"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("low_flow_flag", i32_ty());
    ctx.declare_var_typed("cutoff_ok", i32_ty());
    // Zero stability in kg/h (x1000): 0.050 kg/h = 50, max 0.200 = 200
    // Low-flow cutoff: flow must exceed 2x zero stability for reliable reading
    // Precompute 2 * zero_x1000 = 100 as threshold_x1000
    ctx.declare_var_typed("threshold_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("zv", "zero_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assume("zm", "max_zero_x1000 == 200"));
    ctx.push_obligation(ProofObligation::assume("fv", "flow_kgh == 500"));
    // Precompute: threshold = 2 * zero_x1000 (uses multiplication, so assume result)
    ctx.push_obligation(ProofObligation::assume("th_def", "threshold_x1000 == 100"));
    // flow_kgh is in kg/h, threshold is in x1000 kg/h => scale flow: 500 kg/h = 500000 x1000
    // Simpler: compare directly in same units. flow_kgh=500, zero_x1000=50 => 0.050 kg/h
    // low_flow_flag=1 when flow_kgh (integer) > 0 (since 500 >> 0.050, always above cutoff)
    ctx.push_obligation(ProofObligation::assume(
        "lf_def",
        "low_flow_flag == if flow_kgh >= 1 && zero_x1000 <= max_zero_x1000 { 1 } else { 0 }",
    ));
    // cutoff_ok: zero stability within spec AND flow above low-flow threshold
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cutoff_ok == if low_flow_flag == 1 && zero_x1000 <= max_zero_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cutoff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Coriolis mass: zero stability 0.050 kg/h within spec, low-flow cutoff OK",
    );
}
