//! Native constant paths, declaration modes and false assertion twins.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn pair(name: &str, source: &str, claim: &str, false_claim: &str, verified: usize) {
    assert_eq!(source.matches(claim).count(), 1);
    let twin = source.replace(claim, false_claim);
    for (suffix, source, expected) in [
        ("positive", source, "checked"),
        ("false", twin.as_str(), "verification-failed"),
    ] {
        let run = common::run(&format!("constant_{name}_{suffix}"), source, &[]);
        assert_eq!(run.outcome(), expected, "{run:?}");
        assert!(run.raw.is_empty(), "{run:?}");
        let functions = run.record["functions"]
            .as_array()
            .expect("function records");
        let verified_count = functions
            .iter()
            .filter(|function| function["verdict"] == "verified")
            .count();
        assert_eq!(
            verified_count,
            verified - usize::from(expected == "verification-failed"),
            "{run:?}"
        );
        assert!(
            functions.iter().any(|function| function["kind"] == "Const"),
            "{run:?}"
        );
        assert!(
            functions.iter().all(|function| !function["def_path"]
                .as_str()
                .unwrap()
                .contains("VERUS_UNERASED_PROXY__")),
            "{run:?}"
        );
        if expected == "verification-failed" {
            let errors = run.errors();
            assert_eq!(errors.len(), 1, "{run:?}");
            assert_eq!(errors[0].message, "assertion failed");
        }
    }
}

#[test]
fn spec_constant_uses_its_checked_value() {
    pair(
        "int",
        r#"verus! {
spec const VALUE: int = 7;
proof fn test() { assert(VALUE == 7); }
}"#,
        "VALUE == 7",
        "VALUE == 8",
        2,
    );
}

#[test]
fn constant_dependencies_use_native_definitions() {
    pair(
        "dependency",
        r#"verus! {
spec const FIRST: int = 7;
spec const SECOND: int = FIRST + 2;
proof fn test() { assert(SECOND == 9); }
}"#,
        "SECOND == 9",
        "SECOND == 10",
        3,
    );
}

#[test]
fn same_spelling_in_different_modules_keeps_distinct_values() {
    pair(
        "modules",
        r#"
mod a { use super::*; verus! { pub spec const VALUE: u64 = 3; } }
mod b { use super::*; verus! { pub spec const VALUE: u64 = 5; } }
verus! { proof fn test() { assert(a::VALUE + b::VALUE == 8); } }
"#,
        "a::VALUE + b::VALUE == 8",
        "a::VALUE + b::VALUE == 9",
        3,
    );
}

#[test]
fn spec_constant_is_not_an_exec_value() {
    let run = common::run(
        "constant_spec_in_exec",
        r#"verus! {
spec const VALUE: u64 = 3;
fn test() -> u64 { VALUE }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), 1, "{run:?}");
    assert_eq!(errors[0].message, "cannot read const with mode spec");
}

#[test]
fn trait_default_constant_requires_an_exec_initializer() {
    let source = "verus! {\nspec const Q: u8 = 3;\ntrait T {\n    const C: u8 = Q;\n}\n}";
    let rejected = common::run("constant_trait_spec_initializer", source, &[]);
    assert_eq!(rejected.outcome(), "verus-rejected", "{rejected:?}");
    let errors = rejected.errors();
    assert_eq!(errors.len(), 1, "{rejected:?}");
    assert_eq!(
        errors[0].message,
        "expression has mode spec, expected mode exec"
    );

    let accepted = common::run(
        "constant_trait_dual_initializer",
        &source.replace("spec const Q", "const Q"),
        &[],
    );
    assert_eq!(accepted.outcome(), "checked", "{accepted:?}");
    assert_eq!(accepted.exit, 0, "{accepted:?}");
    assert!(accepted.errors().is_empty(), "{accepted:?}");
}

#[test]
fn a_similarly_named_function_does_not_define_a_rust_constant() {
    let run = common::run(
        "constant_prefix",
        r#"
const VALUE: u64 = 5;
verus! {
spec fn VERUS_UNERASED_PROXY__VALUE() -> u64 { 3 }
proof fn test() { assert(VALUE == 3); }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "refused", "{run:?}");
}

#[test]
fn executable_constants_keep_their_exec_read_mode() {
    for (suffix, declaration) in [("exec", "exec const VALUE: u64 = 3;")] {
        let run = common::run(
            &format!("constant_unrepresented_{suffix}"),
            &format!("verus! {{ {declaration} proof fn test() {{ assert(VALUE == 3); }} }}"),
            &[],
        );
        assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
        assert!(
            run.errors()
                .iter()
                .any(|error| error.message == "cannot read const with mode exec"),
            "{run:?}"
        );
    }
}

#[test]
fn constant_mode_rejection_preserves_earlier_errors_and_other_refusals() {
    for (name, source, message) in [
        (
            "constant_mode_rust_to_vir_first",
            "verus! { exec const VALUE: u64 = 3; proof fn test() { assert(VALUE == 3); no_method_body() } }",
            "no statements are allowed before no_method_body()",
        ),
        (
            "constant_mode_well_formed_first",
            "verus! { exec const VALUE: u64 = 3; proof fn main() { assert(VALUE == 3); } }",
            "`main` function should be #[verifier::exec]",
        ),
    ] {
        let run = common::run(name, source, &[]);
        assert_eq!(run.exit, 1, "{run:?}");
        assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
        assert_eq!(run.errors().len(), 1, "{run:?}");
        assert_eq!(run.errors()[0].message, message, "{run:?}");
        assert!(
            run.record["functions"].as_array().unwrap().iter().all(|row| {
                row["verdict"] != "verified"
                    && row["sites_proved"].is_null()
                    && row["sites_failed"].is_null()
            }),
            "{run:?}"
        );
    }
    let run = common::run(
        "constant_mode_unknown_external_stays_refused",
        "verus! { exec const VALUE: u64 = 3; proof fn test() { let _ = core::mem::size_of::<u8>(); assert(VALUE == 3); } }",
        &[],
    );
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.outcome(), "refused", "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
    assert!(
        run.errors()[0]
            .message
            .starts_with("trust-vc refused: external-call: "),
        "{run:?}"
    );
    assert!(
        run.errors()[0]
            .message
            .ends_with(" is not a Verus function of this crate"),
        "{run:?}"
    );
    let functions = run.record["functions"].as_array().unwrap();
    let test: Vec<_> = functions
        .iter()
        .filter(|row| row["def_path"] == "test")
        .collect();
    assert_eq!(test.len(), 1, "{run:?}");
    assert_eq!(test[0]["verdict"], "refused", "{run:?}");
    assert_eq!(test[0]["tag"], "external-call", "{run:?}");
    assert!(
        functions.iter().all(|row| row["verdict"] != "verified"
            && row["sites_proved"].is_null()
            && row["sites_failed"].is_null()),
        "{run:?}"
    );
}

#[test]
fn constant_function_dependencies_preserve_cycle_checks() {
    let source = r#"verus! {
spec const VALUE: int = value();
spec fn value() -> int { 7 }
proof fn test() { assert(VALUE == 7); }
}"#;
    pair("function_dependency", source, "VALUE == 7", "VALUE == 8", 3);

    let cycle = source.replace("-> int { 7 }", "-> int { VALUE }");
    let run = common::run("constant_function_cycle", &cycle, &[]);
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    let errors = run.errors();
    assert!(!errors.is_empty(), "{run:?}");
    assert!(
        errors
            .iter()
            .all(|error| error.message == "recursive function must have a decreases clause"),
        "{run:?}"
    );
}

#[test]
fn unused_constants_require_a_complete_declaration() {
    for (suffix, declaration) in [(
        "unpaired",
        "#[verus::internal(encoded_const)] spec fn UNUSED() -> int { 3 }",
    )] {
        let source = format!("verus! {{ {declaration} proof fn test() {{ }} }}");
        let run = common::run(&format!("constant_unused_{suffix}"), &source, &[]);
        assert_eq!(run.outcome(), "refused", "{run:?}");
        assert!(run.raw.is_empty(), "{run:?}");
    }
}

#[test]
fn dual_constants_have_a_checked_initializer_and_one_mathematical_value() {
    pair("dual_value", "verus! { const VALUE: u64 = { let x = 3u64; x + 2 }; proof fn test() { assert(VALUE == 5); } }", "VALUE == 5", "VALUE == 6", 2);
    let run = common::run(
        "constant_dual_exec_read",
        "verus! { const VALUE: u64 = 3; fn test() -> (result: u64) ensures result == 3 { VALUE } }",
        &[],
    );
    assert_eq!(run.outcome(), "checked", "{run:?}");
    assert!(run.errors().is_empty(), "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
}

#[test]
fn unused_dual_initializers_are_checked() {
    let run = common::run(
        "constant_unused_dual",
        "verus! { const UNUSED: u64 = { let x = 3u64; x + 1 }; proof fn test() {} }",
        &[],
    );
    assert_eq!(run.outcome(), "checked", "{run:?}");
    let declaration = run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "UNUSED")
        .expect("actual constant declaration");
    assert_eq!(declaration["verdict"], "verified", "{run:?}");
    assert!(
        declaration["sites_proved"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "{run:?}"
    );
}

#[test]
fn a_partial_initializer_uses_its_actual_branch_guard() {
    pair("dual_guarded_division", "verus! { const VALUE: u64 = { let x = 0u64; if x == 0 { 7 } else { 1 / x } }; proof fn test() { assert(VALUE == 7); } }", "VALUE == 7", "VALUE == 8", 2);
}

#[test]
fn associated_constant_instances_preserve_native_generic_substitution() {
    let source = "verus! { struct Holder<A> { value: A } impl<A> Holder<A> { const VALUE: u64 = 7; } proof fn test() { assert(Holder::<u8>::VALUE + Holder::<u16>::VALUE == 14); } }";
    for (suffix, source, expected) in [
        ("positive", source.to_owned(), "checked"),
        (
            "false",
            source.replace("== 14", "== 15"),
            "verification-failed",
        ),
    ] {
        let run = common::run(&format!("constant_generic_owner_{suffix}"), &source, &[]);
        assert_eq!(run.outcome(), expected, "{run:?}");
        assert!(run.raw.is_empty(), "{run:?}");
        assert_eq!(run.record["erase_exit"], 0, "{run:?}");
    }
}

fn executable_value_pair(label: &str, source: &str, claim: &str, twin: &str) {
    assert_eq!(source.matches(claim).count(), 1);
    for (suffix, source, outcome) in [
        ("true", source.to_owned(), "checked"),
        ("false", source.replace(claim, twin), "verification-failed"),
    ] {
        let run = common::run(&format!("exec_value_{label}_{suffix}"), &source, &[]);
        assert_eq!(run.outcome(), outcome, "{run:?}");
        assert!(run.raw.is_empty(), "{run:?}");
        let functions = run.record["functions"]
            .as_array()
            .expect("actual function records");
        assert!(functions.len() >= 2, "{run:?}");
        if outcome == "checked" {
            assert!(
                functions
                    .iter()
                    .all(|function| function["verdict"] == "verified"),
                "{run:?}"
            );
        } else {
            assert_eq!(run.errors().len(), 1, "{run:?}");
            assert_eq!(run.errors()[0].message, "assertion failed");
        }
    }
}

// Only the two fixtures with a genuine const-fn pair use this expectation.
// Its erased native function is external; the verification proxy, initializer
// and consumer must each have the exact independently checked result below.
fn const_function_value_pair(
    label: &str,
    source: &str,
    claim: &str,
    twin: &str,
    function: &str,
    constant_kind: &str,
    constant_sites: u64,
) {
    assert_eq!(source.matches(claim).count(), 1);
    let line = |prefix: &str| {
        let lines: Vec<_> = source
            .lines()
            .enumerate()
            .filter(|(_, line)| line.starts_with(prefix))
            .map(|(index, _)| common::PRELUDE.lines().count() + index + 1)
            .collect();
        assert_eq!(lines.len(), 1);
        lines[0]
    };
    let function_line = line(&format!("const fn {function}"));
    let constant_line = line(if constant_kind == "Const" {
        "exec const VALUE:"
    } else {
        assert_eq!(
            constant_kind,
            "Static { safety: Safe, mutability: Not, nested: false }"
        );
        "exec static VALUE:"
    });
    let consumer_line = line("fn test()");
    for (suffix, source, outcome) in [
        ("true", source.to_owned(), "checked"),
        ("false", source.replace(claim, twin), "verification-failed"),
    ] {
        let run = common::run(&format!("exec_value_{label}_{suffix}"), &source, &[]);
        assert_eq!(run.outcome(), outcome, "{run:?}");
        assert_eq!(run.exit, if suffix == "true" { 0 } else { 1 }, "{run:?}");
        assert_eq!(run.record["erase_exit"], 0, "{run:?}");
        assert_eq!(run.record["refused"], false, "{run:?}");
        assert!(run.record["crate_refusals"].as_array().unwrap().is_empty());
        assert!(run.raw.is_empty(), "{run:?}");
        let functions = run.record["functions"].as_array().unwrap();
        assert_eq!(functions.len(), 4, "{run:?}");
        for (name, kind, line, verdict, proved, failed) in [
            (function, "Fn", function_line, "verified", 1, 0),
            (
                "VALUE",
                constant_kind,
                constant_line,
                "verified",
                constant_sites,
                0,
            ),
            (
                "test",
                "Fn",
                consumer_line,
                if suffix == "true" {
                    "verified"
                } else {
                    "failed"
                },
                if suffix == "true" { 1 } else { 0 },
                if suffix == "true" { 0 } else { 1 },
            ),
        ] {
            let rows: Vec<_> = functions
                .iter()
                .filter(|row| row["def_path"] == name && row["verdict"] == verdict)
                .collect();
            assert_eq!(rows.len(), 1, "{run:?}");
            let row = rows[0];
            assert_eq!(row["kind"], kind, "{run:?}");
            assert_eq!(row["file"], run.record["entry_file"], "{run:?}");
            assert_eq!(row["lines"], serde_json::json!([line, line]), "{run:?}");
            assert!(row["tag"].is_null(), "{run:?}");
            assert_eq!(row["sites_proved"], proved, "{run:?}");
            assert_eq!(row["sites_failed"], failed, "{run:?}");
        }
        let counterpart: Vec<_> = functions
            .iter()
            .filter(|row| row["def_path"] == function && row["verdict"] == "external")
            .collect();
        assert_eq!(counterpart.len(), 1, "{run:?}");
        let counterpart = counterpart[0];
        assert_eq!(counterpart["kind"], "Fn", "{run:?}");
        assert_eq!(counterpart["file"], run.record["entry_file"], "{run:?}");
        assert_eq!(
            counterpart["lines"],
            serde_json::json!([function_line, function_line]),
            "{run:?}"
        );
        for field in ["tag", "sites_proved", "sites_failed"] {
            assert!(counterpart[field].is_null(), "{run:?}");
        }
        if suffix == "true" {
            assert!(run.errors().is_empty(), "{run:?}");
        } else {
            assert_eq!(run.errors().len(), 1, "{run:?}");
            assert_eq!(run.errors()[0].message, "assertion failed");
        }
    }
}

#[test]
fn executable_constant_const_function_and_checked_self_postcondition_compose() {
    const_function_value_pair(
        "const_fn",
        r#"verus! {
const fn one() -> (ret: u64) ensures ret == 1 { 1 }
exec const VALUE: u64 ensures VALUE == 2 { 1 + one() }
fn test() { let value = VALUE; assert(value == 2); }
}"#,
        "value == 2",
        "value == 3",
        "one",
        "Const",
        2,
    );
}

#[test]
fn static_contract_type_facts_and_stable_shared_reads_compose() {
    executable_value_pair(
        "static",
        r#"verus! {
exec static VALUE: u64 ensures 2 <= VALUE && VALUE <= 4 { 3 }
fn test() {
    let first = &VALUE;
    let second = &VALUE;
    assert(first == second);
    let copy = VALUE;
    assert(copy <= 4);
}
}"#,
        "copy <= 4",
        "copy < 2",
    );
    executable_value_pair(
        "static_types",
        r#"verus! {
exec static VALUE: u8 = 3;
fn test() { let value = VALUE; assert(value <= 255); }
}"#,
        "value <= 255",
        "value > 255",
    );
}

#[test]
fn executable_reads_export_no_initializer_equation_or_cross_read_freshness() {
    for (label, declaration) in [
        ("exec_fresh", "exec const VALUE: u64 ensures true { 3 }"),
        (
            "static_opaque_value",
            "exec static VALUE: u64 ensures true { 3 }",
        ),
    ] {
        let source = format!(
            "verus! {{ {declaration} fn test() {{ let value = VALUE; assert(value == 3); }} }}"
        );
        let run = common::run(label, &source, &[]);
        assert_eq!(run.outcome(), "verification-failed", "{run:?}");
        assert_eq!(run.errors().len(), 1, "{run:?}");
    }
    let run = common::run(
        "exec_const_reads_are_fresh",
        r#"verus! {
exec const VALUE: u64 ensures true { 3 }
fn test() { let first = VALUE; let second = VALUE; assert(first == second); }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
}

#[test]
fn executable_initializers_verify_their_actual_return_and_proof_effects() {
    let run = common::run(
        "exec_const_wrong_return",
        r#"verus! {
exec const VALUE: u64 ensures VALUE == 2 { 3 }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
    for kind in ["const", "static"] {
        let source = format!(
            "verus! {{ exec {kind} VALUE: u64 ensures VALUE == 3 {{ assert(false); 3 }} }}"
        );
        let run = common::run(&format!("exec_{kind}_proof_effect"), &source, &[]);
        assert_eq!(run.outcome(), "verification-failed", "{run:?}");
        assert!(
            run.errors()
                .iter()
                .any(|error| error.message == "assertion failed"),
            "{run:?}"
        );
    }
}

#[test]
fn native_const_legality_and_ghost_read_legality_stay_hard() {
    let run = common::run(
        "const_fn_native_legality",
        "verus! { fn non_const() {} const fn invalid() { non_const() } }",
        &[],
    );
    assert_eq!(run.outcome(), "erase-rejected", "{run:?}");
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.record["erase_exit"], 1, "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
    assert_eq!(run.errors()[0].code.as_deref(), Some("E0015"), "{run:?}");
    assert_eq!(
        run.errors()[0].message,
        "cannot call non-const function `non_const` in constant functions",
        "{run:?}"
    );
    assert!(
        run.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| {
                row["verdict"] != "verified"
                    && row["sites_proved"].is_null()
                    && row["sites_failed"].is_null()
            }),
        "{run:?}"
    );
    let run = common::run(
        "dual_cannot_call_const_fn",
        "verus! { const fn one() -> u64 { 1 } const VALUE: u64 = one(); }",
        &[],
    );
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.message.contains("with mode exec")),
        "{run:?}"
    );
    for kind in ["const", "static"] {
        let source = format!(
            "verus! {{ exec {kind} VALUE: u64 = 3; proof fn test() {{ let value = VALUE; }} }}"
        );
        let run = common::run(&format!("exec_{kind}_ghost_read"), &source, &[]);
        assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
        assert!(
            run.errors()
                .iter()
                .any(|error| error.message == format!("cannot read {kind} with mode exec")),
            "{run:?}"
        );
    }
}

#[test]
fn an_unowned_native_const_function_does_not_license_a_dual_initializer() {
    let run = common::run(
        "dual_native_const_fn_is_not_an_owned_declaration",
        "const fn one() -> u64 { 1 } verus! { const VALUE: u64 = one(); }",
        &[],
    );
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.outcome(), "refused", "{run:?}");
    assert!(run.record["erase_exit"].is_null(), "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
    assert_eq!(
        run.errors()[0].message,
        "trust-vc refused: constant-initializer: a function call in a dual constant initializer",
        "{run:?}"
    );
    let functions = run.record["functions"].as_array().unwrap();
    assert_eq!(functions.len(), 2, "{run:?}");
    for (name, verdict, tag) in [
        ("one", "external", serde_json::Value::Null),
        (
            "VALUE",
            "refused",
            serde_json::json!("constant-initializer"),
        ),
    ] {
        let rows: Vec<_> = functions
            .iter()
            .filter(|row| row["def_path"] == name)
            .collect();
        assert_eq!(rows.len(), 1, "{run:?}");
        let row = rows[0];
        assert_eq!(row["verdict"], verdict, "{run:?}");
        assert_eq!(row["tag"], tag, "{run:?}");
        assert!(row["sites_proved"].is_null(), "{run:?}");
        assert!(row["sites_failed"].is_null(), "{run:?}");
    }
}

#[test]
fn native_generic_const_instance_keeps_static_contract_and_false_consumer() {
    const_function_value_pair(
        "generic_const_instance",
        r#"verus! {
const fn identity<T: Copy>(x: T) -> (ret: T) ensures ret == x { x }
exec static VALUE: u8 ensures VALUE == 3 { identity::<u8>(3) }
fn test() { let value = VALUE; assert(value == 3); }
}"#,
        "value == 3",
        "value == 4",
        "identity",
        "Static { safety: Safe, mutability: Not, nested: false }",
        1,
    );
    let run = common::run(
        "static_generic_const_bad_body",
        r#"verus! {
const fn identity<T: Copy>(x: T) -> (ret: T) ensures ret != x { x }
exec static VALUE: u8 ensures VALUE == 3 { identity::<u8>(3) }
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.message == "postcondition not satisfied"),
        "{run:?}"
    );
}

#[test]
fn static_initializer_does_not_invent_a_native_copy_bound() {
    let run = common::run(
        "static_generic_const_missing_copy",
        r#"verus! {
struct NotCopy { value: u8 }
const fn identity<T: Copy>(x: T) -> (ret: T) ensures ret == x { x }
exec static VALUE: u8 ensures VALUE == 3 {
    let value = identity::<NotCopy>(NotCopy { value: 3 }); value.value
}
}"#,
        &[],
    );
    assert_eq!(run.outcome(), "front-end-rejected", "{run:?}");
}
