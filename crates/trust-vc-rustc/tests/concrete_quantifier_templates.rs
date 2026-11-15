//! Exact upstream concrete-domain generic trigger regressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn run(name: &str, whole_source: &str, positive: bool) {
    // Retain the literal original program body; the ordinary native harness
    // supplies its checked-in prelude. The captured complete original file is
    // also retained byte-for-byte in the fixture, never a rewritten twin.
    let start = whole_source
        .find("::verus_builtin_macros::verus!")
        .expect("actual upstream macro body");
    let source = &whole_source[start..];
    let result = common::run(&format!("concrete_template_{name}"), source, &[]);
    assert!(result.raw.is_empty(), "{result:?}");
    let function = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test1")
        .expect("the actual original proof");
    if positive {
        assert_eq!(result.exit, 0, "{result:?}");
        assert_eq!(result.outcome(), "checked", "{result:?}");
        assert_eq!(function["verdict"], "verified");
        assert_eq!(function["sites_proved"], 2);
        assert_eq!(function["sites_failed"], 0);
        assert!(result.errors().is_empty());
    } else {
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verification-failed", "{result:?}");
        assert_eq!(function["verdict"], "failed");
        assert_eq!(function["sites_failed"], 1);
        let errors = result.errors();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].message, "assertion failed");
        assert_eq!(errors[0].primary_lines, vec![7], "{errors:?}");
    }
}

#[test]
fn material_nat_call_licenses_its_generic_existential_trigger() {
    run(
        "test1g",
        include_str!("concrete_quantifier_templates/test1g.rs"),
        true,
    );
}
#[test]
fn absent_material_call_does_not_invent_an_existential_witness() {
    run(
        "test1g_fails",
        include_str!("concrete_quantifier_templates/test1g_fails.rs"),
        false,
    );
}
#[test]
fn one_material_predicate_keeps_the_original_two_predicate_formula() {
    run(
        "test2g",
        include_str!("concrete_quantifier_templates/test2g.rs"),
        true,
    );
}
#[test]
fn reversing_the_material_seed_preserves_the_original_formula() {
    run(
        "test3g",
        include_str!("concrete_quantifier_templates/test3g.rs"),
        true,
    );
}
