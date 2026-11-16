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
fn executable_constants_require_initializer_and_read_semantics() {
    for (suffix, declaration) in [("exec", "exec const VALUE: u64 = 3;")] {
        let run = common::run(
            &format!("constant_unrepresented_{suffix}"),
            &format!("verus! {{ {declaration} proof fn test() {{ assert(VALUE == 3); }} }}"),
            &[],
        );
        assert_eq!(run.outcome(), "refused", "{run:?}");
    }
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
