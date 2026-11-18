//! Native legacy mode semantics, real primitive ownership and false twins.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

const OPTIONS: &[&str] = &["--no-external-by-default"];

fn no_credit(result: &common::Run) {
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|function| {
                function["verdict"] != "verified"
                    && function["sites_proved"].as_u64().unwrap_or(0) == 0
            }),
        "{result:?}"
    );
}

fn checked(name: &str, source: &str, function: &str, sites: u64) {
    let result = common::run(name, source, OPTIONS);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    let row = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["def_path"] == function)
        .unwrap();
    assert_eq!(row["verdict"], "verified", "{result:?}");
    assert_eq!(row["sites_proved"], sites, "{result:?}");
    assert_eq!(row["sites_failed"], 0, "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
}

fn false_assertion(name: &str, source: &str) {
    let result = common::run(name, source, OPTIONS);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 1, "{result:?}");
    assert_eq!(result.errors()[0].message, "assertion failed", "{result:?}");
    assert_eq!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["sites_failed"].as_u64().unwrap_or(0))
            .sum::<u64>(),
        1,
        "{result:?}"
    );
}

fn mode_error(name: &str, source: &str, message: &str) {
    let result = common::run(name, source, OPTIONS);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    assert!(
        result
            .errors()
            .iter()
            .any(|error| error.message.contains(message)),
        "{result:?}"
    );
    no_credit(&result);
}

fn missing_erasure(name: &str, source: &str) {
    let result = common::run(name, source, OPTIONS);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|row| row["tag"] == "legacy-erasure"),
        "{result:?}"
    );
    no_credit(&result);
}

#[test]
fn original_let_spec_pass_and_false_twin_reach_real_proof() {
    checked(
        "legacy-let-spec-pass",
        r#"
fn test1() {
    #[verifier::spec] let x: u64 = 2;
    verus_builtin::assert_(x == 2);
}
"#,
        "test1",
        1,
    );
    false_assertion(
        "legacy-let-spec-false",
        r#"
fn test1() {
    #[verifier::spec] let x: u64 = 2;
    verus_builtin::assert_(x == 3);
}
"#,
    );
}

#[test]
fn original_eq_mode_keeps_native_spec_parameter_and_binding() {
    checked(
        "legacy-eq-mode",
        r#"
fn eq_mode(#[verifier::spec] i: u128) {
    #[verifier::spec] let b: bool = i == 13;
}
"#,
        "eq_mode",
        0,
    );
}

#[test]
fn original_spec_conditions_do_not_authorize_exec_mutations() {
    mode_error(
        "legacy-if-spec-cond",
        r#"
fn if_spec_cond(#[verifier::spec] i: u128) -> u64 {
    let mut a: u64 = 2;
    if i == 3 { a = a + 1; }
    a
}
"#,
        "cannot assign to exec variable from proof mode",
    );
    mode_error(
        "legacy-assign-from-proof",
        r#"
fn myfun(#[verifier::spec] a: bool) -> bool {
    let mut b = false;
    if a { b = true; }
    b
}
"#,
        "cannot assign to exec variable from proof mode",
    );
}

#[test]
fn legacy_return_checks_outer_mode_instead_of_block_classification() {
    mode_error(
        "legacy-spec-branch-return",
        r#"
fn f(#[verifier::spec] b: bool) -> u64 {
    if b { return 0; }
    1
}
"#,
        "cannot return from non-exec code in exec function",
    );
}

#[test]
fn macro_functions_keep_ghost_block_mode_restrictions() {
    mode_error(
        "modern-spec-init-denied",
        r#"
verus! { fn f() { #[verus::internal(spec)] let x: u64 = 2; } }
"#,
        "exec code cannot initialize non-exec variables",
    );
    mode_error(
        "modern-direct-assert-denied",
        r#"
verus! { fn f() { verus_builtin::assert_(true); } }
"#,
        "assert",
    );
}

#[test]
fn exec_syntax_spec_initializer_keeps_exec_call_and_overflow_obligations() {
    checked(
        "legacy-exec-initializer",
        r#"
verus! {
    fn one() -> (r: u8) ensures r == 1 { 1 }
}
fn f() {
    #[verifier::spec] let x: u8 = one();
    verus_builtin::assert_(x == 1);
}
"#,
        "f",
        1,
    );
    let overflow = common::run(
        "legacy-spec-init-overflow",
        r#"
fn f(x: u8) {
    #[verifier::spec] let y: u8 = x + 1;
    verus_builtin::assert_(true);
}
"#,
        OPTIONS,
    );
    assert_eq!(overflow.exit, 1, "{overflow:?}");
    assert_eq!(overflow.outcome(), "verification-failed", "{overflow:?}");
    assert!(
        overflow
            .errors()
            .iter()
            .any(|error| error.message.contains("overflow")),
        "{overflow:?}"
    );
}

#[test]
fn logical_assert_operand_keeps_actual_legacy_syntax_for_autospec() {
    // The raw legacy Assert argument keeps in_ghost=false in A40. Its pure
    // mode therefore cannot quietly redirect this Exec call to `logical`.
    mode_error(
        "legacy-assert-autospec-stays-exec",
        r#"
verus! {
    #[verifier::when_used_as_spec(logical)]
    fn actual() -> bool { true }
    spec fn logical() -> bool { false }
}
fn f() { verus_builtin::assert_(actual()); }
"#,
        "cannot call function",
    );
}

#[test]
fn immutable_ghost_reassignment_is_an_explicit_unimplemented_erasure_boundary() {
    // Unchanged original decl_init_let_spec_fail expects an actual false
    // assertion. The first scalar lane must not mislabel this refusal parity.
    missing_erasure(
        "legacy-immutable-spec-storage",
        r#"
fn test1() {
    #[verifier::spec] let x: u64;
    x = 2;
    x = 3;
    verus_builtin::assert_(false);
}
"#,
    );
}

#[test]
fn references_and_affine_carriers_do_not_gain_ownership_from_modes() {
    missing_erasure(
        "legacy-shared-param",
        r#"
fn f(#[verifier::spec] input: &u8) {
    #[verifier::spec] let value: u8 = *input;
    verus_builtin::assert_(value == value);
}
"#,
    );
    missing_erasure(
        "legacy-opaque-value",
        r#"
fn f<T>(#[verifier::spec] input: T) {
    #[verifier::spec] let value = input;
}
"#,
    );
}

#[test]
fn legacy_classification_does_not_change_default_external_policy() {
    let result = common::run(
        "legacy-default-external",
        r#"
fn f() { #[verifier::spec] let value: u8 = 1; verus_builtin::assert_(false); }
"#,
        &[],
    );
    assert_eq!(result.exit, 0, "{result:?}");
    let row = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["def_path"] == "f")
        .unwrap();
    assert_eq!(row["verdict"], "external", "{result:?}");
    assert!(row["sites_proved"].is_null(), "{result:?}");
}

#[test]
fn primitive_legacy_bodies_cannot_skip_real_native_lifetime_checking() {
    let result = common::run(
        "legacy-no-lifetime",
        r#"
fn test1() {
    #[verifier::spec] let x: u64 = 2;
    verus_builtin::assert_(x == 2);
}
"#,
        &["--no-external-by-default", "--no-lifetime"],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    assert!(
        result
            .diags
            .iter()
            .any(|diagnostic| diagnostic.message.contains("native ownership checking")),
        "{result:?}"
    );
    let row = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["def_path"] == "test1")
        .unwrap();
    assert_eq!(row["verdict"], "skipped", "{result:?}");
    assert_eq!(row["tag"], "crate-refused", "{result:?}");
    assert!(
        row["sites_proved"].is_null() && row["sites_failed"].is_null(),
        "{result:?}"
    );
    no_credit(&result);
}

#[test]
fn shadowed_scalar_bindings_keep_distinct_native_occurrences_and_false_twin() {
    checked(
        "legacy-shadowed-bindings",
        r#"
fn test1() {
    #[verifier::spec] let x: u64 = 2;
    { #[verifier::spec] let x: u64 = 3; verus_builtin::assert_(x == 3); }
    verus_builtin::assert_(x == 2);
}
"#,
        "test1",
        2,
    );
    false_assertion(
        "legacy-shadowed-bindings-false",
        r#"
fn test1() {
    #[verifier::spec] let x: u64 = 2;
    { #[verifier::spec] let x: u64 = 3; verus_builtin::assert_(x == 2); }
    verus_builtin::assert_(x == 2);
}
"#,
    );
}

#[test]
fn repeated_scalar_calls_preserve_two_actual_occurrences_and_false_twin() {
    checked(
        "legacy-repeated-calls",
        r#"
verus! { fn one() -> (r: u8) ensures r == 1 { 1 } }
fn test1() {
    #[verifier::spec] let x: u8 = one();
    #[verifier::spec] let y: u8 = one();
    verus_builtin::assert_(x == 1);
    verus_builtin::assert_(y == 1);
}
"#,
        "test1",
        2,
    );
    false_assertion(
        "legacy-repeated-calls-false",
        r#"
verus! { fn one() -> (r: u8) ensures r == 1 { 1 } }
fn test1() {
    #[verifier::spec] let x: u8 = one();
    #[verifier::spec] let y: u8 = one();
    verus_builtin::assert_(x == 1);
    verus_builtin::assert_(y == 2);
}
"#,
    );
}

#[test]
fn injected_mir_affine_values_and_uninitialized_storage_do_not_gain_ownership() {
    let source = format!(
        "#![feature(custom_mir)]\n{}{}",
        common::PRELUDE,
        r#"
#[custom_mir(dialect = "runtime", phase = "optimized")]
fn test1() {
    #[verifier::spec] let x: u64 = 2;
    verus_builtin::assert_(false);
}
"#
    );
    let result = common::run_raw("legacy-custom-mir-denied", &source, OPTIONS);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    no_credit(&result);
    missing_erasure(
        "legacy-affine-duplicate-denied",
        r#"
fn test1<T>(input: T) {
    let first = input;
    let second = input;
    verus_builtin::assert_(false);
}
"#,
    );
    missing_erasure(
        "legacy-uninitialized-spec-storage",
        r#"
fn test1() {
    #[verifier::spec] let x: u8;
    x = 1;
    verus_builtin::assert_(x == 1);
}
"#,
    );
}

#[test]
fn exec_valued_legacy_initializer_keeps_its_false_assertion() {
    checked(
        "legacy-exec-initializer-arithmetic-true",
        r#"
fn f() {
    #[verifier::spec] let value: u8 = 1u8 + 1u8;
    verus_builtin::assert_(value == 2);
}
"#,
        "f",
        2,
    );
    false_assertion(
        "legacy-exec-initializer-arithmetic-false",
        r#"
fn f() {
    #[verifier::spec] let value: u8 = 1u8 + 1u8;
    verus_builtin::assert_(value == 3);
}
"#,
    );
}

#[test]
fn exec_valued_legacy_initializer_keeps_effect_order_and_shadowing() {
    checked(
        "legacy-exec-initializer-once",
        r#"
fn f() {
    let mut count: u64 = 0;
    #[verifier::spec] let value: u64 = { count = count + 1; count + 1 };
    verus_builtin::assert_(count == 1);
    verus_builtin::assert_(value == 2);
}
"#,
        "f",
        4,
    );
    checked(
        "legacy-exec-initializer-shadowing",
        r#"
fn f() {
    let value: u8 = 1;
    #[verifier::spec] let value: u8 = value + 1;
    verus_builtin::assert_(value == 2);
}
"#,
        "f",
        2,
    );
    false_assertion(
        "legacy-exec-initializer-once-false",
        r#"
fn f() {
    let mut count: u64 = 0;
    #[verifier::spec] let value: u64 = { count = count + 1; count + 1 };
    verus_builtin::assert_(count == 2);
}
"#,
    );
}

#[test]
fn spec_valued_legacy_initializer_does_not_gain_exec_permission() {
    checked(
        "legacy-spec-initializer-stays-spec",
        r#"
fn f(#[verifier::spec] value: u128) {
    #[verifier::spec] let same: bool = value == value;
    verus_builtin::assert_(same);
}
"#,
        "f",
        1,
    );
    false_assertion(
        "legacy-spec-initializer-stays-spec-false",
        r#"
fn f(#[verifier::spec] value: u128) {
    #[verifier::spec] let equal: bool = value == 13;
    verus_builtin::assert_(equal);
}
"#,
    );
    mode_error(
        "legacy-spec-initializer-cannot-control-exec-write",
        r#"
fn f(#[verifier::spec] value: u128) {
    #[verifier::spec] let equal: bool = value == 13;
    let mut state: u64 = 0;
    if equal { state = 1; }
}
"#,
        "cannot assign to exec variable from proof mode",
    );
}

#[test]
fn pure_conditional_legacy_initializers_keep_spec_and_unit_transport() {
    checked(
        "legacy-pure-conditional-value",
        r#"
fn f(#[verifier::spec] choose: bool) {
    #[verifier::spec] let value: u8 = if choose { 1 } else { 2 };
    verus_builtin::assert_(if choose { value == 1 } else { value == 2 });
}
"#,
        "f",
        1,
    );
    false_assertion(
        "legacy-pure-conditional-value-false",
        r#"
fn f(#[verifier::spec] choose: bool) {
    #[verifier::spec] let value: u8 = if choose { 1 } else { 2 };
    verus_builtin::assert_(value == 0);
}
"#,
    );
    checked(
        "legacy-pure-conditional-unit",
        r#"
fn f(#[verifier::spec] choose: bool) {
    #[verifier::spec] let value: () = if choose { () } else { () };
    verus_builtin::assert_(true);
}
"#,
        "f",
        1,
    );
    false_assertion(
        "legacy-pure-conditional-unit-false",
        r#"
fn f(#[verifier::spec] choose: bool) {
    #[verifier::spec] let value: () = if choose { () } else { () };
    verus_builtin::assert_(false);
}
"#,
    );
}

#[test]
fn spec_valued_checked_initializer_keeps_range_proof_and_false_twin() {
    checked(
        "legacy-spec-checked-range-true",
        r#"
fn f(#[verifier::spec] x: u8) {
    if x < 255 {
        #[verifier::spec] let y: u8 = x + 1;
        verus_builtin::assert_(y > x);
    }
}
"#,
        "f",
        2,
    );
    false_assertion(
        "legacy-spec-checked-range-false",
        r#"
fn f(#[verifier::spec] x: u8) {
    if x < 255 {
        #[verifier::spec] let y: u8 = x + 1;
        verus_builtin::assert_(y == x);
    }
}
"#,
    );
    let overflow = common::run(
        "legacy-spec-valued-checked-overflow",
        r#"
fn f(#[verifier::spec] x: u8) {
    #[verifier::spec] let y: u8 = x + 1;
    verus_builtin::assert_(true);
}
"#,
        OPTIONS,
    );
    assert_eq!(overflow.exit, 1, "{overflow:?}");
    assert_eq!(overflow.outcome(), "verification-failed", "{overflow:?}");
    assert!(
        overflow
            .errors()
            .iter()
            .any(|error| error.message.contains("overflow")),
        "{overflow:?}"
    );
}

#[test]
fn spec_valued_initializer_checks_only_the_selected_conditional_arm() {
    checked(
        "legacy-spec-checked-conditional-true",
        r#"
fn f(#[verifier::spec] x: u8) {
    #[verifier::spec] let y: u8 = if x < 255 { x + 1 } else { 0 };
    verus_builtin::assert_(if x < 255 { y > x } else { y == 0 });
}
"#,
        "f",
        2,
    );
    false_assertion(
        "legacy-spec-checked-conditional-false",
        r#"
fn f(#[verifier::spec] x: u8) {
    #[verifier::spec] let y: u8 = if x < 255 { x + 1 } else { 0 };
    verus_builtin::assert_(y == 1);
}
"#,
    );
}

#[test]
fn spec_valued_initializer_saves_left_value_before_later_effect() {
    checked(
        "legacy-spec-checked-operand-order-true",
        r#"
fn f(#[verifier::spec] x: u8) {
    let mut count: u8 = 0;
    #[verifier::spec] let y: u8 = x + { count = count + 1; 0 };
    verus_builtin::assert_(count == 1);
    verus_builtin::assert_(y == x);
}
"#,
        "f",
        4,
    );
    false_assertion(
        "legacy-spec-checked-operand-order-false",
        r#"
fn f(#[verifier::spec] x: u8) {
    let mut count: u8 = 0;
    #[verifier::spec] let y: u8 = x + { count = count + 1; 0 };
    verus_builtin::assert_(count == 2);
}
"#,
    );
}

#[test]
fn spec_valued_initializer_preserves_effectful_branch_values() {
    checked(
        "legacy-spec-checked-effectful-branch-true",
        r#"
fn f(choose: bool, #[verifier::spec] x: u8) {
    let mut count: u8 = 0;
    #[verifier::spec] let y: u8 = if choose {
        count = 1;
        x + 0
    } else {
        count = 2;
        x + 0
    };
    verus_builtin::assert_(if choose { count == 1 } else { count == 2 });
    verus_builtin::assert_(y == x);
}
"#,
        "f",
        4,
    );
    false_assertion(
        "legacy-spec-checked-effectful-branch-false",
        r#"
fn f(choose: bool, #[verifier::spec] x: u8) {
    let mut count: u8 = 0;
    #[verifier::spec] let y: u8 = if choose {
        count = 1;
        x + 0
    } else {
        count = 2;
        x + 0
    };
    verus_builtin::assert_(count == 3);
}
"#,
    );
}

#[test]
fn original_legacy_tuple1_and_spec_field_truth_reach_real_checks() {
    checked(
        "legacy-original-tuple1",
        r#"
fn test1(i: bool, j: bool) {
    let s = (i, j);
}
fn test3(i: bool, #[verifier::spec] j: bool) {
    #[verifier::spec] let s = (i, j);
    #[verifier::spec] let ii = s.0;
    #[verifier::spec] let jj = s.1;
}
"#,
        "test3",
        0,
    );
    checked(
        "legacy-tuple-field-truth",
        r#"
fn f(i: bool, #[verifier::spec] j: bool) {
    #[verifier::spec] let s = (i, j);
    #[verifier::spec] let ii = s.0;
    #[verifier::spec] let jj = s.1;
    verus_builtin::assert_(ii == i);
    verus_builtin::assert_(jj == j);
}
"#,
        "f",
        2,
    );
    false_assertion(
        "legacy-tuple-field-false",
        r#"
fn f(i: bool, #[verifier::spec] j: bool) {
    #[verifier::spec] let s = (i, j);
    #[verifier::spec] let ii = s.0;
    verus_builtin::assert_(ii != i);
}
"#,
    );
}

#[test]
fn nested_legacy_copy_products_keep_each_projection() {
    checked(
        "legacy-nested-tuple-true",
        r#"
fn f() {
    #[verifier::spec] let value = (1u8, (2u8, 3u8));
    #[verifier::spec] let same = value;
    verus_builtin::assert_(same.0 == 1 && same.1.0 == 2 && same.1.1 == 3);
}
"#,
        "f",
        1,
    );
    false_assertion(
        "legacy-nested-tuple-false",
        r#"
fn f() {
    #[verifier::spec] let value = (1u8, (2u8, 3u8));
    #[verifier::spec] let same = value;
    verus_builtin::assert_(same.1.0 == 3);
}
"#,
    );
}

#[test]
fn legacy_tuple_field_writes_keep_other_components_and_modes() {
    checked(
        "legacy-tuple-write-true",
        r#"
fn f() {
    let mut value = (1u8, 2u8);
    value.0 = 3;
    verus_builtin::assert_(value.0 == 3);
    verus_builtin::assert_(value.1 == 2);
    #[verifier::spec] let mut ghost = (4u8, 5u8);
    ghost.1 = 6;
    verus_builtin::assert_(ghost.0 == 4);
    verus_builtin::assert_(ghost.1 == 6);
}
"#,
        "f",
        4,
    );
    false_assertion(
        "legacy-tuple-write-false",
        r#"
fn f() {
    let mut value = (1u8, 2u8);
    value.0 = 3;
    verus_builtin::assert_(value.1 == 3);
}
"#,
    );
}

#[test]
fn legacy_tuple_return_calls_preserve_contracts_and_false_twin() {
    checked(
        "legacy-tuple-call-true",
        r#"
verus! {
    fn pair() -> (r: (u8, u8)) ensures r.0 == 1, r.1 == 2 { (1, 2) }
}
fn f() {
    #[verifier::spec] let value = pair();
    verus_builtin::assert_(value.0 == 1);
    verus_builtin::assert_(value.1 == 2);
}
"#,
        "f",
        2,
    );
    false_assertion(
        "legacy-tuple-call-false",
        r#"
verus! {
    fn pair() -> (r: (u8, u8)) ensures r.0 == 1, r.1 == 2 { (1, 2) }
}
fn f() {
    #[verifier::spec] let value = pair();
    verus_builtin::assert_(value.0 == 2);
}
"#,
    );
}

#[test]
fn legacy_copy_products_do_not_supply_missing_native_ownership() {
    missing_erasure(
        "legacy-tuple-reference-denied",
        r#"
fn f(input: &bool) {
    #[verifier::spec] let value = (input, true);
    verus_builtin::assert_(false);
}
"#,
    );
    missing_erasure(
        "legacy-tuple-generic-denied",
        r#"
fn f<T: Copy>(input: T) {
    #[verifier::spec] let value = (input, true);
    verus_builtin::assert_(false);
}
"#,
    );
    let result = common::run(
        "legacy-tuple-no-lifetime-denied",
        r#"
fn f() {
    #[verifier::spec] let value = (true, false);
    verus_builtin::assert_(value.0);
}
"#,
        &["--no-external-by-default", "--no-lifetime"],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "refused", "{result:?}");
    no_credit(&result);
}

#[test]
fn legacy_copy_product_depth_is_bounded_before_ownership_admission() {
    let mut value = "true".to_owned();
    for _ in 0..40 {
        value = format!("({value},)");
    }
    let source = format!("fn f() {{ let value = {value}; verus_builtin::assert_(true); }}");
    missing_erasure("legacy-tuple-depth-denied", &source);
}

#[test]
fn direct_place_inventory_does_not_reclassify_nonplace_ghost_initializers() {
    checked(
        "legacy-proof-nonplace-native-facts",
        r#"
#[verifier::proof]
fn f() {
    #[verifier::spec] let value: u8 = 1;
    verus_builtin::assert_(value == 1);
}
"#,
        "f",
        1,
    );
    checked(
        "modern-proof-nonplace-native-facts",
        r#"
verus! {
    proof fn f() {
        let value: u8 = 1;
        assert(value == 1);
    }
}
"#,
        "f",
        1,
    );
}

#[test]
fn legacy_spec_assignment_keeps_rhs_checks_and_false_assertions() {
    checked(
        "legacy-spec-assignment-rhs-true",
        r#"
fn f(#[verifier::spec] input: u8) {
    #[verifier::spec] let mut value: u8 = input;
    value = input + 0;
    verus_builtin::assert_(value == input);
}
"#,
        "f",
        2,
    );
    false_assertion(
        "legacy-spec-assignment-rhs-false",
        r#"
fn f(#[verifier::spec] input: u8) {
    #[verifier::spec] let mut value: u8 = input;
    value = input + 0;
    verus_builtin::assert_(value != input);
}
"#,
    );
    let overflow = common::run(
        "legacy-spec-assignment-overflow",
        r#"
fn f(#[verifier::spec] input: u8) {
    #[verifier::spec] let mut value: u8 = input;
    value = input + 1;
    verus_builtin::assert_(true);
}
"#,
        OPTIONS,
    );
    assert_eq!(overflow.exit, 1, "{overflow:?}");
    assert_eq!(overflow.outcome(), "verification-failed", "{overflow:?}");
    assert!(
        overflow
            .errors()
            .iter()
            .any(|error| error.message.contains("overflow")),
        "{overflow:?}"
    );
}
