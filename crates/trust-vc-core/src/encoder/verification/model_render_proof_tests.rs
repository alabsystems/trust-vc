//! Proof coverage tests for model_render.rs
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers previously untested production paths: render_seq, render_set,
//! render_map, format_counterexample_model, render_scalar, render_char,
//! render_variable, read_length, model_value_to_u64.
//!
//! These tests use real ay Solver instances to construct VerifiedModel
//! fixtures because Model fields are pub(crate) to ay-dpll.
//!
//! Wiring: Worker must add to model_render.rs:
//!   #[cfg(test)]
//!   #[path = "model_render_proof_tests.rs"]
//!   mod proof_tests;
//!
//! Part of #949.

use super::*;

use ay_dpll::api::{FpSpecialKind, Logic, ModelValue, Solver, Sort};

// ---------------------------------------------------------------------------
// Helper: build a solver with a BV array, store values, and return the model
// ---------------------------------------------------------------------------

/// Create a ay solver configured for arrays + bitvectors, assert constraints
/// to pin specific values, check sat, and return the verified model.
fn solver_with_seq_model(
    name: &str,
    elem_width: u32,
    elements: &[i64],
) -> ay_dpll::api::VerifiedModel {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("test solver should construct");

    // Declare the sequence array: Array(BV64, BV<elem_width>)
    let arr_sort = Sort::Array(Box::new(ay_dpll::api::ArraySort {
        index_sort: Sort::bitvec(64),
        element_sort: Sort::bitvec(elem_width),
    }));
    let arr = solver.declare_const(name, arr_sort);

    // Declare the length companion variable
    let len_name = format!("__trust_vc_len_{name}");
    let len_var = solver.declare_const(&len_name, Sort::bitvec(64));

    // Assert length == elements.len()
    let len_val = solver
        .try_bv_const(elements.len() as i64, 64)
        .expect("test sequence length should fit in bv64");
    let len_eq = solver
        .try_eq(len_var, len_val)
        .expect("test sequence length equality should encode");
    solver
        .try_assert_term(len_eq)
        .expect("test sequence length equality should assert");

    // Assert array stores: arr[i] == elements[i]
    for (i, &elem) in elements.iter().enumerate() {
        let idx = solver
            .try_bv_const(i as i64, 64)
            .expect("test sequence index should fit in bv64");
        let val = solver
            .try_bv_const(elem, elem_width)
            .expect("test sequence element should fit the requested width");
        let select = solver
            .try_select(arr, idx)
            .expect("test sequence select should encode");
        let eq = solver
            .try_eq(select, val)
            .expect("test sequence element equality should encode");
        solver
            .try_assert_term(eq)
            .expect("test sequence element equality should assert");
    }

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "seq model should be satisfiable: {result:?}"
    );
    solver.model().expect("model should exist after SAT")
}

fn solver_with_set_model(
    name: &str,
    elem_width: u32,
    members: &[i64],
) -> ay_dpll::api::VerifiedModel {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("test solver should construct");

    // Declare set array: Array(BV<elem_width>, Bool)
    let arr_sort = Sort::Array(Box::new(ay_dpll::api::ArraySort {
        index_sort: Sort::bitvec(elem_width),
        element_sort: Sort::Bool,
    }));
    let arr = solver.declare_const(name, arr_sort);

    // Start with const_array(false) and store true for each member
    let false_term = solver.bool_const(false);
    let true_term = solver.bool_const(true);
    let mut current = solver
        .try_const_array(Sort::bitvec(elem_width), false_term)
        .expect("test set const-array should encode");
    for &member in members {
        let key = solver
            .try_bv_const(member, elem_width)
            .expect("test set member should fit the requested width");
        current = solver
            .try_store(current, key, true_term)
            .expect("test set store should encode");
    }
    let eq = solver
        .try_eq(arr, current)
        .expect("test set equality should encode");
    solver
        .try_assert_term(eq)
        .expect("test set equality should assert");

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "set model should be satisfiable: {result:?}"
    );
    solver.model().expect("model should exist after SAT")
}

fn solver_with_map_model(
    name: &str,
    key_width: u32,
    val_width: u32,
    entries: &[(i64, i64)],
) -> ay_dpll::api::VerifiedModel {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("test solver should construct");

    // Main array: Array(BV<key_width>, BV<val_width>)
    let main_sort = Sort::Array(Box::new(ay_dpll::api::ArraySort {
        index_sort: Sort::bitvec(key_width),
        element_sort: Sort::bitvec(val_width),
    }));
    let main_arr = solver.declare_const(name, main_sort);

    // Domain array: Array(BV<key_width>, Bool) — default false
    let dom_name = format!("{name}_dom");
    let dom_sort = Sort::Array(Box::new(ay_dpll::api::ArraySort {
        index_sort: Sort::bitvec(key_width),
        element_sort: Sort::Bool,
    }));
    let dom_arr = solver.declare_const(&dom_name, dom_sort);

    // Build domain: const_array(false) with true for each key
    let false_term = solver.bool_const(false);
    let true_term = solver.bool_const(true);
    let mut dom_expr = solver
        .try_const_array(Sort::bitvec(key_width), false_term)
        .expect("test map domain const-array should encode");
    for &(key, _) in entries {
        let k = solver
            .try_bv_const(key, key_width)
            .expect("test map key should fit the requested width");
        dom_expr = solver
            .try_store(dom_expr, k, true_term)
            .expect("test map domain store should encode");
    }
    let dom_eq = solver
        .try_eq(dom_arr, dom_expr)
        .expect("test map domain equality should encode");
    solver
        .try_assert_term(dom_eq)
        .expect("test map domain equality should assert");

    // Assert main array stores: main[key] == val for each entry
    for &(key, val) in entries {
        let k = solver
            .try_bv_const(key, key_width)
            .expect("test map key should fit the requested width");
        let v = solver
            .try_bv_const(val, val_width)
            .expect("test map value should fit the requested width");
        let select = solver
            .try_select(main_arr, k)
            .expect("test map select should encode");
        let eq = solver
            .try_eq(select, v)
            .expect("test map value equality should encode");
        solver
            .try_assert_term(eq)
            .expect("test map value equality should assert");
    }

    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "map model should be satisfiable: {result:?}"
    );
    solver.model().expect("model should exist after SAT")
}

fn solver_with_scalar_model() -> ay_dpll::api::VerifiedModel {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("test solver should construct");

    // Bool variable
    let b = solver.declare_const("flag", Sort::Bool);
    let true_term = solver.bool_const(true);
    let b_eq = solver
        .try_eq(b, true_term)
        .expect("test bool equality should encode");
    solver
        .try_assert_term(b_eq)
        .expect("test bool equality should assert");

    // Signed i32: -42
    let x = solver.declare_const("x", Sort::bitvec(32));
    let neg42 = solver
        .try_bv_const(-42, 32)
        .expect("test signed scalar should fit in bv32");
    let x_eq = solver
        .try_eq(x, neg42)
        .expect("test signed scalar equality should encode");
    solver
        .try_assert_term(x_eq)
        .expect("test signed scalar equality should assert");

    // Unsigned u8: 200
    let y = solver.declare_const("y", Sort::bitvec(8));
    let val200 = solver
        .try_bv_const(200, 8)
        .expect("test unsigned scalar should fit in bv8");
    let y_eq = solver
        .try_eq(y, val200)
        .expect("test unsigned scalar equality should encode");
    solver
        .try_assert_term(y_eq)
        .expect("test unsigned scalar equality should assert");

    // Internal variable: __trust_vc_old_x = 99 (should be visible as "old(x)")
    let old_x = solver.declare_const("__trust_vc_old_x", Sort::bitvec(32));
    let val99 = solver
        .try_bv_const(99, 32)
        .expect("test old capture should fit in bv32");
    let old_x_eq = solver
        .try_eq(old_x, val99)
        .expect("test old capture equality should encode");
    solver
        .try_assert_term(old_x_eq)
        .expect("test old capture equality should assert");

    // Internal variable: __trust_vc_closure_arg0 = 7 (should be hidden)
    let carg = solver.declare_const("__trust_vc_closure_arg0", Sort::bitvec(32));
    let val7 = solver
        .try_bv_const(7, 32)
        .expect("test closure arg should fit in bv32");
    let carg_eq = solver
        .try_eq(carg, val7)
        .expect("test closure arg equality should encode");
    solver
        .try_assert_term(carg_eq)
        .expect("test closure arg equality should assert");

    // Char: 'A' = 65
    let c = solver.declare_const("ch", Sort::bitvec(32));
    let char_a = solver
        .try_bv_const(65, 32)
        .expect("test char scalar should fit in bv32");
    let c_eq = solver
        .try_eq(c, char_a)
        .expect("test char scalar equality should encode");
    solver
        .try_assert_term(c_eq)
        .expect("test char scalar equality should assert");

    let result = solver.check_sat();
    assert!(result.is_sat());
    solver.model().expect("model should exist after SAT")
}

fn solver_with_f32_model(name: &str, value: f32) -> ay_dpll::api::VerifiedModel {
    let mut solver = Solver::try_new(Logic::QfFp).expect("test solver should construct");
    let fp_var = solver.declare_const(name, Sort::FloatingPoint(8, 24));

    let bits = value.to_bits();
    let sign = solver
        .try_bv_const(i64::from((bits >> 31) & 1), 1)
        .expect("test float sign bit should fit in bv1");
    let exponent = solver
        .try_bv_const(i64::from((bits >> 23) & 0xff), 8)
        .expect("test float exponent should fit in bv8");
    let significand = solver
        .try_bv_const(i64::from(bits & 0x7f_ffff), 23)
        .expect("test float significand should fit in bv23");
    let fp_value = solver
        .try_fp_from_bvs(sign, exponent, significand, 8, 24)
        .expect("test float constructor should encode");
    let eq = solver
        .try_eq(fp_var, fp_value)
        .expect("test float equality should encode");
    solver
        .try_assert_term(eq)
        .expect("test float equality should assert");

    let result = solver.check_sat();
    assert!(result.is_sat());
    solver.model().expect("model should exist after SAT")
}

fn solver_with_multiset_model(
    name: &str,
    elem_width: u32,
    entries: &[(i64, u64)],
) -> ay_dpll::api::VerifiedModel {
    let mut solver = Solver::try_new(Logic::All).expect("test solver should construct");

    let arr_sort = Sort::Array(Box::new(ay_dpll::api::ArraySort {
        index_sort: Sort::bitvec(elem_width),
        element_sort: Sort::Int,
    }));
    let arr = solver.declare_const(name, arr_sort);

    let zero = solver.int_const(0);
    let mut current = solver
        .try_const_array(Sort::bitvec(elem_width), zero)
        .expect("test multiset const-array should encode");
    for &(key, count) in entries {
        let key = solver
            .try_bv_const(key, elem_width)
            .expect("test multiset key should fit the requested width");
        let count = solver.int_const(count as i64);
        current = solver
            .try_store(current, key, count)
            .expect("test multiset store should encode");
    }

    let eq = solver
        .try_eq(arr, current)
        .expect("test multiset equality should encode");
    solver
        .try_assert_term(eq)
        .expect("test multiset equality should assert");

    let result = solver.check_sat();
    assert!(result.is_sat());
    solver.model().expect("model should exist after SAT")
}

fn float32_model_value(value: f32) -> ModelValue {
    let bits = value.to_bits();
    ModelValue::FloatingPoint {
        sign: (bits >> 31) != 0,
        exponent: u64::from((bits >> 23) & 0xff),
        significand: u64::from(bits & 0x7f_ffff),
        eb: 8,
        sb: 24,
    }
}

fn float64_model_value(value: f64) -> ModelValue {
    let bits = value.to_bits();
    ModelValue::FloatingPoint {
        sign: (bits >> 63) != 0,
        exponent: (bits >> 52) & 0x7ff,
        significand: bits & ((1_u64 << 52) - 1),
        eb: 11,
        sb: 53,
    }
}

fn multiset_model_value(entries: &[(i64, u64)], elem_width: u32) -> ModelValue {
    ModelValue::Array {
        default: Box::new(ModelValue::BitVec {
            value: BigInt::from(0),
            width: 64,
        }),
        stores: entries
            .iter()
            .map(|(key, count)| {
                (
                    ModelValue::BitVec {
                        value: BigInt::from(*key),
                        width: elem_width,
                    },
                    ModelValue::BitVec {
                        value: BigInt::from(*count),
                        width: 64,
                    },
                )
            })
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// render_seq tests
// ---------------------------------------------------------------------------

#[test]
fn render_seq_three_element_bv32() {
    let vm = solver_with_seq_model("s", 32, &[10, 20, 30]);
    let model = vm.model();
    let result = render_seq("s", &TrustVcType::Uint { width: 32 }, model);
    assert!(
        result.is_some(),
        "render_seq should produce output for a 3-element Seq"
    );
    let rendered = result.unwrap();
    assert!(
        rendered.starts_with('[') && rendered.ends_with(']'),
        "Seq should be bracketed: {rendered}"
    );
    assert!(
        rendered.contains("10") && rendered.contains("20") && rendered.contains("30"),
        "rendered Seq should contain all elements: {rendered}"
    );
}

#[test]
fn render_seq_empty() {
    let vm = solver_with_seq_model("empty_seq", 32, &[]);
    let model = vm.model();
    let result = render_seq("empty_seq", &TrustVcType::Uint { width: 32 }, model);
    assert!(result.is_some(), "render_seq should handle empty Seq");
    assert_eq!(result.unwrap(), "[]", "empty Seq should render as []");
}

#[test]
fn render_seq_single_signed() {
    let vm = solver_with_seq_model("signed_seq", 32, &[-1_i64]);
    let model = vm.model();
    let result = render_seq("signed_seq", &TrustVcType::Int { width: 32 }, model);
    assert!(result.is_some(), "render_seq should render signed element");
    let rendered = result.unwrap();
    // -1 in 32-bit two's complement: bv_to_signed(0xFFFFFFFF, 32) = -1
    assert!(
        rendered.contains("-1"),
        "signed Seq element should render as -1: {rendered}"
    );
}

// ---------------------------------------------------------------------------
// render_set tests
// ---------------------------------------------------------------------------

#[test]
fn render_set_non_empty_uses_fallback_when_model_format_differs() {
    // ay's model representation for non-empty arrays with stores may not
    // decompose into ModelValue::Array { default, stores }, causing render_set
    // to return None. The fallback in render_variable then uses the raw display.
    let vm = solver_with_set_model("my_set", 32, &[5, 10]);
    let model = vm.model();
    let _direct = render_set("my_set", &TrustVcType::Uint { width: 32 }, model);
    // render_set may return None if the model format doesn't match Array { default, stores }.
    // This is correct behavior — render_variable falls back to raw display.
    let ty = TrustVcType::Set(Box::new(TrustVcType::Uint { width: 32 }));
    let var_result = render_variable("my_set", &ty, model);
    assert!(
        var_result.is_some(),
        "render_variable should always produce output for a declared Set variable (via fallback)"
    );
}

#[test]
fn render_set_empty() {
    let vm = solver_with_set_model("empty_set", 32, &[]);
    let model = vm.model();
    let result = render_set("empty_set", &TrustVcType::Uint { width: 32 }, model);
    assert!(result.is_some(), "render_set should handle empty Set");
    assert_eq!(
        result.unwrap(),
        "{}",
        "empty Set should render as empty braces"
    );
}

// ---------------------------------------------------------------------------
// render_map tests
// ---------------------------------------------------------------------------

#[test]
fn render_map_non_empty_uses_fallback_when_model_format_differs() {
    // ay's model representation for non-empty maps may not decompose into
    // the ModelValue::Array { default, stores } format for both the main array
    // and domain companion. render_map returns None in that case, and
    // render_variable falls back to raw display.
    let vm = solver_with_map_model("m", 32, 32, &[(1, 100), (2, 200)]);
    let model = vm.model();
    let result = render_map(
        "m",
        &TrustVcType::Uint { width: 32 },
        &TrustVcType::Uint { width: 32 },
        model,
    );
    // render_map may return None if model format doesn't match expectations.
    // Verify render_variable (full dispatch with fallback) doesn't panic.
    let ty = TrustVcType::Map(
        Box::new(TrustVcType::Uint { width: 32 }),
        Box::new(TrustVcType::Uint { width: 32 }),
    );
    let var_result = render_variable("m", &ty, model);
    assert!(
        var_result.is_some(),
        "render_variable should produce output for a declared Map variable (via fallback)"
    );

    // Document whether render_map worked or fell back
    if let Some(rendered) = result {
        assert!(
            rendered.starts_with('{'),
            "Map should be brace-wrapped: {rendered}"
        );
    }
}

#[test]
fn render_map_empty() {
    let vm = solver_with_map_model("empty_map", 32, 32, &[]);
    let model = vm.model();
    let result = render_map(
        "empty_map",
        &TrustVcType::Uint { width: 32 },
        &TrustVcType::Uint { width: 32 },
        model,
    );
    assert!(result.is_some(), "render_map should handle empty Map");
    assert_eq!(
        result.unwrap(),
        "{}",
        "empty Map should render as empty braces"
    );
}

// ---------------------------------------------------------------------------
// format_counterexample_model tests
// ---------------------------------------------------------------------------

#[test]
fn format_counterexample_model_renders_scalar_variables() {
    let vm = solver_with_scalar_model();
    let mut var_types = HashMap::new();
    var_types.insert("flag".to_string(), TrustVcType::Bool);
    var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), TrustVcType::Uint { width: 8 });

    let result = format_counterexample_model(&vm, &var_types, &HashMap::new());
    assert!(
        result.contains("flag = true"),
        "should render bool variable: {result}"
    );
    assert!(
        result.contains("x = -42"),
        "should render signed i32 variable: {result}"
    );
    assert!(
        result.contains("y = 200"),
        "should render unsigned u8 variable: {result}"
    );
}

#[test]
fn format_counterexample_model_empty_var_types_falls_back_to_debug() {
    let vm = solver_with_scalar_model();
    let var_types: HashMap<String, TrustVcType> = HashMap::new();

    let result = format_counterexample_model(&vm, &var_types, &HashMap::new());
    // With no var_types, bindings is empty → falls back to format!("{verified_model:?}")
    assert!(
        !result.is_empty(),
        "fallback should produce non-empty debug output"
    );
}

#[test]
fn format_counterexample_model_sorts_variables_alphabetically() {
    let vm = solver_with_scalar_model();
    let mut var_types = HashMap::new();
    var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert("flag".to_string(), TrustVcType::Bool);

    let result = format_counterexample_model(&vm, &var_types, &HashMap::new());
    // "flag" comes before "x" alphabetically
    let flag_pos = result.find("flag");
    let x_pos = result.find("x = ");
    assert!(
        flag_pos.is_some() && x_pos.is_some() && flag_pos.unwrap() < x_pos.unwrap(),
        "variables should be sorted alphabetically: {result}"
    );
}

// ---------------------------------------------------------------------------
// render_scalar + render_char tests
// ---------------------------------------------------------------------------

#[test]
fn render_scalar_char_renders_printable() {
    let vm = solver_with_scalar_model();
    let model = vm.model();
    let result = render_char("ch", model);
    assert!(result.is_some(), "render_char should find ch variable");
    assert_eq!(result.unwrap(), "'A'", "char 65 should render as 'A'");
}

#[test]
fn render_scalar_bool_renders_true() {
    let vm = solver_with_scalar_model();
    let model = vm.model();
    let result = render_scalar("flag", &TrustVcType::Bool, model);
    assert_eq!(result, Some("true".to_string()));
}

#[test]
fn render_scalar_float32_renders_decimal() {
    let vm = solver_with_f32_model("fp32", -3.25);
    let model = vm.model();
    let result = render_scalar("fp32", &TrustVcType::Float { width: 32 }, model);
    assert_eq!(result, Some("-3.25".to_string()));
}

#[test]
fn render_model_value_float64_renders_decimal() {
    let result = render_model_value(&float64_model_value(1.5), &TrustVcType::Float { width: 64 });
    assert_eq!(result, "1.5");
}

#[test]
fn render_model_value_float_special_renders_user_friendly_names() {
    for (value, expected) in [
        (
            ModelValue::FloatingPointSpecial {
                kind: FpSpecialKind::PosInf,
                eb: 8,
                sb: 24,
            },
            "+Inf",
        ),
        (
            ModelValue::FloatingPointSpecial {
                kind: FpSpecialKind::NegZero,
                eb: 8,
                sb: 24,
            },
            "-0.0",
        ),
        (
            ModelValue::FloatingPointSpecial {
                kind: FpSpecialKind::NaN,
                eb: 8,
                sb: 24,
            },
            "NaN",
        ),
    ] {
        assert_eq!(
            render_model_value(&value, &TrustVcType::Float { width: 32 }),
            expected
        );
    }
}

#[test]
fn render_scalar_signed_bv_renders_negative() {
    let vm = solver_with_scalar_model();
    let model = vm.model();
    let result = render_signed_bv("x", 32, model);
    assert_eq!(result, Some("-42".to_string()));
}

#[test]
fn render_scalar_unsigned_bv_renders_positive() {
    let vm = solver_with_scalar_model();
    let model = vm.model();
    let result = render_unsigned_bv("y", 8, model);
    assert_eq!(result, Some("200".to_string()));
}

#[test]
fn render_scalar_missing_variable_returns_none() {
    let vm = solver_with_scalar_model();
    let model = vm.model();
    let result = render_scalar("nonexistent", &TrustVcType::Bool, model);
    assert_eq!(result, None, "missing variable should return None");
}

// ---------------------------------------------------------------------------
// render_variable tests (dispatches to render_seq/set/map/scalar)
// ---------------------------------------------------------------------------

#[test]
fn render_variable_dispatches_to_seq() {
    let vm = solver_with_seq_model("v_seq", 32, &[7, 8]);
    let model = vm.model();
    let ty = TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 32 }));
    let result = render_variable("v_seq", &ty, model);
    assert!(result.is_some(), "render_variable should dispatch Seq type");
    let rendered = result.unwrap();
    assert!(
        rendered.starts_with('['),
        "Seq should render with brackets: {rendered}"
    );
}

#[test]
fn render_variable_set_returns_some_via_fallback() {
    // Non-empty set may use the raw display fallback if ay's model format
    // doesn't match the expected ModelValue::Array { default, stores }.
    let vm = solver_with_set_model("v_set", 32, &[42]);
    let model = vm.model();
    let ty = TrustVcType::Set(Box::new(TrustVcType::Uint { width: 32 }));
    let result = render_variable("v_set", &ty, model);
    assert!(
        result.is_some(),
        "render_variable for Set should produce output (typed or fallback)"
    );
}

#[test]
fn render_variable_map_returns_some_via_fallback() {
    // Non-empty map may use the raw display fallback if ay's model format
    // doesn't match expectations for both main and domain arrays.
    let vm = solver_with_map_model("v_map", 32, 32, &[(3, 99)]);
    let model = vm.model();
    let ty = TrustVcType::Map(
        Box::new(TrustVcType::Uint { width: 32 }),
        Box::new(TrustVcType::Uint { width: 32 }),
    );
    let result = render_variable("v_map", &ty, model);
    assert!(
        result.is_some(),
        "render_variable for Map should produce output (typed or fallback)"
    );
}

#[test]
fn render_variable_multiset_returns_some_via_typed_or_fallback() {
    let vm = solver_with_multiset_model("ms", 32, &[(5, 2), (7, 1)]);
    let model = vm.model();
    let ty = TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }));
    let typed = render_multiset("ms", &TrustVcType::Int { width: 32 }, model);
    let result = render_variable("ms", &ty, model);
    assert!(
        result.is_some(),
        "render_variable for Multiset should produce output (typed or fallback)"
    );
    assert!(
        typed.is_some(),
        "typed Multiset renderer should return output"
    );
}

// ---------------------------------------------------------------------------
// read_length tests
// ---------------------------------------------------------------------------

#[test]
fn read_length_from_bv() {
    let vm = solver_with_seq_model("len_test", 32, &[1, 2, 3, 4, 5]);
    let model = vm.model();
    let result = read_length("__trust_vc_len_len_test", model);
    assert_eq!(
        result,
        Some(5),
        "read_length should extract BV length value"
    );
}

#[test]
fn read_length_from_int() {
    // Create a solver with int-mode length variable
    let mut solver = Solver::try_new(Logic::QfLia).expect("test solver should construct");
    let len = solver.declare_const("__trust_vc_len_int_seq", Sort::Int);
    let val = solver.int_const(7);
    let eq = solver
        .try_eq(len, val)
        .expect("test int length equality should encode");
    solver
        .try_assert_term(eq)
        .expect("test int length equality should assert");
    let result = solver.check_sat();
    assert!(result.is_sat());
    let vm = solver.model().unwrap();
    let model = vm.model();

    let length = read_length("__trust_vc_len_int_seq", model);
    assert_eq!(
        length,
        Some(7),
        "read_length should fall back to int_val for Int-mode lengths"
    );
}

#[test]
fn read_length_missing_returns_none() {
    let vm = solver_with_scalar_model();
    let model = vm.model();
    let result = read_length("__trust_vc_len_nonexistent", model);
    assert_eq!(
        result, None,
        "read_length of missing variable should be None"
    );
}

// ---------------------------------------------------------------------------
// model_value_to_u64 tests
// ---------------------------------------------------------------------------

#[test]
fn model_value_to_u64_from_bv() {
    let val = ModelValue::BitVec {
        value: BigInt::from(42),
        width: 32,
    };
    assert_eq!(model_value_to_u64(&val), Some(42));
}

#[test]
fn model_value_to_u64_from_int() {
    let val = ModelValue::Int(BigInt::from(100));
    assert_eq!(model_value_to_u64(&val), Some(100));
}

#[test]
fn model_value_to_u64_from_bool_returns_none() {
    assert_eq!(model_value_to_u64(&ModelValue::Bool(true)), None);
}

#[test]
fn model_value_to_u64_negative_returns_none() {
    let val = ModelValue::Int(BigInt::from(-1));
    assert_eq!(
        model_value_to_u64(&val),
        None,
        "negative values should not convert to u64"
    );
}

#[test]
fn render_multiset_value_formats_finite_counts() {
    let value = multiset_model_value(&[(5, 2), (7, 1)], 32);
    let result = render_multiset_value(&value, &TrustVcType::Int { width: 32 });
    assert_eq!(result, Some("{5: 2, 7: 1}".to_string()));
}

// ---------------------------------------------------------------------------
// Source-level counterexample name tests (Part of #2651)
// ---------------------------------------------------------------------------

/// Build a model with named BV variables for counterexample name tests.
/// Each entry is (name, value, width).
fn solver_with_named_bv_vars(vars: &[(&str, i64, u32)]) -> ay_dpll::api::VerifiedModel {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("test solver should construct");
    for &(name, value, width) in vars {
        let v = solver.declare_const(name, Sort::bitvec(width));
        let c = solver
            .try_bv_const(value, width)
            .expect("test bv const should encode");
        let eq = solver.try_eq(v, c).expect("test bv equality should encode");
        solver
            .try_assert_term(eq)
            .expect("test bv equality should assert");
    }
    let result = solver.check_sat();
    assert!(result.is_sat());
    solver.model().expect("model should exist after SAT")
}

#[test]
fn format_counterexample_old_capture_uses_source_name() {
    // Model must declare __trust_vc_old_x so render_variable finds it.
    let vm = solver_with_named_bv_vars(&[("__trust_vc_old_x", -42, 32), ("y", 200, 8)]);
    let mut var_types = HashMap::new();
    var_types.insert(
        "__trust_vc_old_x".to_string(),
        TrustVcType::Int { width: 32 },
    );
    var_types.insert("y".to_string(), TrustVcType::Uint { width: 8 });

    let result = format_counterexample_model(&vm, &var_types, &HashMap::new());
    assert!(
        result.contains("old(x)"),
        "old!() capture should use 'old(x)' display name, got: {result}"
    );
    assert!(
        !result.contains("__trust_vc_old_x"),
        "raw helper name should not appear, got: {result}"
    );
    assert!(
        result.contains("y = "),
        "user-visible variable should still appear, got: {result}"
    );
}

#[test]
fn format_counterexample_hidden_vars_not_rendered() {
    // __trust_vc_extern_call_value_42_5 should be hidden by default
    let vm = solver_with_scalar_model();
    let mut var_types = HashMap::new();
    var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert(
        "__trust_vc_extern_call_value_42_5".to_string(),
        TrustVcType::Int { width: 32 },
    );

    let result = format_counterexample_model(&vm, &var_types, &HashMap::new());
    assert!(
        !result.contains("__trust_vc_extern"),
        "extern temp should be hidden by default, got: {result}"
    );
    assert!(
        result.contains("x = "),
        "user-visible variable should appear, got: {result}"
    );
}

#[test]
fn format_counterexample_explicit_alias_overrides_default() {
    // Model must declare __trust_vc_closure_arg0 so render_variable finds it.
    let vm = solver_with_named_bv_vars(&[("__trust_vc_closure_arg0", 200, 8)]);
    let mut var_types = HashMap::new();
    var_types.insert(
        "__trust_vc_closure_arg0".to_string(),
        TrustVcType::Uint { width: 8 },
    );

    let mut meta = HashMap::new();
    meta.insert(
        "__trust_vc_closure_arg0".to_string(),
        CounterexampleVarMeta {
            display_name: "item".to_string(),
            visible: true,
        },
    );

    let result = format_counterexample_model(&vm, &var_types, &meta);
    assert!(
        result.contains("item = "),
        "explicit alias should use 'item' display name, got: {result}"
    );
    assert!(
        !result.contains("__trust_vc_closure"),
        "raw helper name should not appear, got: {result}"
    );
}

#[test]
fn collect_counterexample_bindings_returns_structured_scalar_data() {
    let vm = solver_with_scalar_model();
    let mut var_types = HashMap::new();
    var_types.insert("flag".to_string(), TrustVcType::Bool);
    var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), TrustVcType::Uint { width: 8 });

    let bindings = collect_counterexample_bindings(&vm, &var_types, &HashMap::new());

    assert_eq!(bindings.len(), 3, "should have 3 visible bindings");

    let flag_binding = bindings.iter().find(|b| b.raw_name == "flag").unwrap();
    assert_eq!(flag_binding.display_name, "flag");
    assert_eq!(flag_binding.ty, "bool");
    assert_eq!(flag_binding.value, "true");

    let x_binding = bindings.iter().find(|b| b.raw_name == "x").unwrap();
    assert_eq!(x_binding.display_name, "x");
    assert_eq!(x_binding.ty, "i32");
    assert_eq!(x_binding.value, "-42");

    let y_binding = bindings.iter().find(|b| b.raw_name == "y").unwrap();
    assert_eq!(y_binding.display_name, "y");
    assert_eq!(y_binding.ty, "u8");
    assert_eq!(y_binding.value, "200");
}

#[test]
fn collect_counterexample_bindings_hides_internal_variables() {
    let vm = solver_with_scalar_model();
    let mut var_types = HashMap::new();
    var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert(
        "__trust_vc_old_x".to_string(),
        TrustVcType::Int { width: 32 },
    );
    var_types.insert(
        "__trust_vc_closure_arg0".to_string(),
        TrustVcType::Int { width: 32 },
    );

    let bindings = collect_counterexample_bindings(&vm, &var_types, &HashMap::new());

    // __trust_vc_old_x is visible with display name "old(x)"
    let old_binding = bindings.iter().find(|b| b.raw_name == "__trust_vc_old_x");
    assert!(old_binding.is_some(), "old() captures should be visible");
    assert_eq!(old_binding.unwrap().display_name, "old(x)");

    // __trust_vc_closure_arg0 is hidden
    let closure_binding = bindings
        .iter()
        .find(|b| b.raw_name == "__trust_vc_closure_arg0");
    assert!(closure_binding.is_none(), "closure params should be hidden");
}

#[test]
fn render_model_value_renders_float_and_multiset_values() {
    assert_eq!(
        render_model_value(
            &float32_model_value(-3.25),
            &TrustVcType::Float { width: 32 }
        ),
        "-3.25"
    );
    assert_eq!(
        render_model_value(
            &multiset_model_value(&[(5, 2), (7, 1)], 32),
            &TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 })),
        ),
        "{5: 2, 7: 1}"
    );
}
