//! Real native proof/diagnostic twins; all newly prepared controls are unrun.
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

fn function<'a>(run: &'a common::Run, name: &str) -> &'a serde_json::Value {
    run.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == name)
        .unwrap()
}

fn failed_once(run: &common::Run, name: &str) {
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert_eq!(function(run, name)["verdict"], "failed", "{run:?}");
    assert_eq!(function(run, name)["sites_failed"], 1, "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
    assert_eq!(run.errors()[0].message, "assertion failed", "{run:?}");
    complete_recommends(run);
}

fn complete_recommends(run: &common::Run) {
    assert!(
        !run.diags.iter().any(|diagnostic| diagnostic
            .message
            .starts_with("trust-vc could not complete recommends diagnostics:")),
        "the authored diagnostic control must complete even when no recommendation fails: {run:?}"
    );
}

fn choice_notes(run: &common::Run) -> Vec<&common::Diag> {
    run.diags
        .iter()
        .filter(|diagnostic| {
            diagnostic.level == "note"
                && diagnostic
                    .message
                    .starts_with("recommendation not met: cannot prove that there exists")
        })
        .collect()
}

fn recommendation_notes(run: &common::Run) -> Vec<&common::Diag> {
    run.diags
        .iter()
        .filter(|diagnostic| {
            diagnostic.level == "note" && diagnostic.message == "recommendation not met"
        })
        .collect()
}

#[test]
fn an_unrelated_recommends_clause_does_not_replace_a_real_failure() {
    let source = "verus! { spec fn unused(x: int) -> int recommends x > 0, { x } proof fn bad() { assert(false); } }";
    let run = common::run("recommends_unrelated_real_failure", source, &[]);
    failed_once(&run, "bad");
    assert!(recommendation_notes(&run).is_empty(), "{run:?}");
}

#[test]
fn valid_domain_true_and_false_twins_keep_the_original_proof_verdicts() {
    let positive = "verus! { spec fn s(x: int) -> int recommends x > 0, { x + 1 } proof fn good() { assert(s(1) == 2); } }";
    let negative = positive
        .replace("fn good()", "fn bad()")
        .replace("s(1) == 2", "s(1) == 3");
    let good = common::run("recommends_valid_domain_true", positive, &[]);
    assert_eq!(good.outcome(), "checked", "{good:?}");
    assert_eq!(function(&good, "good")["verdict"], "verified", "{good:?}");
    assert!(good.errors().is_empty(), "{good:?}");
    let bad = common::run("recommends_valid_domain_false", &negative, &[]);
    failed_once(&bad, "bad");
    assert!(recommendation_notes(&bad).is_empty(), "{bad:?}");
}

#[test]
fn an_unmet_recommendation_is_a_note_and_never_a_value_premise() {
    let source = "verus! { spec fn s(x: int) -> int recommends x > 0, { x } proof fn good() { assert(s(0) == 0); } proof fn bad() { assert(s(0) == 1); } }";
    let run = common::run("recommends_outside_domain_not_premise", source, &[]);
    failed_once(&run, "bad");
    assert_eq!(function(&run, "good")["verdict"], "verified", "{run:?}");
    let notes = recommendation_notes(&run);
    assert_eq!(notes.len(), 1, "{run:?}");
    assert!(!notes[0].primary_lines.is_empty(), "{run:?}");
    assert!(
        notes[0]
            .spans
            .iter()
            .any(|(_, label)| label.as_deref() == Some("failed recommendation")),
        "{run:?}"
    );
}

#[test]
fn actual_short_circuit_guards_control_the_optional_domain_goal() {
    let guarded = "verus! { spec fn s(x: int) -> int recommends x > 0, { x + 1 } proof fn bad(x: int) { assert(x > 0 ==> s(x) == x + 1); assert(false); } }";
    let unguarded = guarded.replace("x > 0 ==> s(x) == x + 1", "s(x) == x + 1");
    let guarded = common::run("recommends_guarded_call", guarded, &[]);
    failed_once(&guarded, "bad");
    assert!(recommendation_notes(&guarded).is_empty(), "{guarded:?}");
    let unguarded = common::run("recommends_unguarded_call", &unguarded, &[]);
    failed_once(&unguarded, "bad");
    assert_eq!(recommendation_notes(&unguarded).len(), 1, "{unguarded:?}");
}

#[test]
fn actual_generic_formals_preserve_values_and_domain_arguments() {
    let source = "verus! { spec fn s<A>(x: A, allowed: bool) -> A recommends allowed, { x } proof fn bad() { assert(s::<u8>(7u8, true) == 8u8); } }";
    let run = common::run("recommends_actual_generic_formals", source, &[]);
    failed_once(&run, "bad");
    assert!(recommendation_notes(&run).is_empty(), "{run:?}");
    // The same primary false assertion must survive a false domain too.
    let outside = source.replace("7u8, true", "7u8, false");
    let outside = common::run("recommends_actual_generic_false_domain", &outside, &[]);
    failed_once(&outside, "bad");
    assert_eq!(recommendation_notes(&outside).len(), 1, "{outside:?}");
}

#[test]
fn generic_uf_bool_and_integer_parameters_keep_native_diagnostic_sorts() {
    for (label, allowed, limit, expected) in [
        ("valid", "true", "1", 0),
        ("false_bool", "false", "1", 1),
        ("false_integer", "true", "0", 1),
    ] {
        let source = format!("verus! {{ spec fn s<A>(x: A, allowed: bool, limit: int) -> A recommends allowed && limit > 0, {{ x }} proof fn bad() {{ assert(s::<bool>(true, {allowed}, {limit}) == false); }} }}");
        let run = common::run(
            &format!("recommends_generic_native_sorts_{label}"),
            &source,
            &[],
        );
        failed_once(&run, "bad");
        assert_eq!(recommendation_notes(&run).len(), expected, "{run:?}");
    }
}

#[test]
fn quantified_domains_use_arbitrary_typed_binders_and_actual_guards() {
    let guarded = "verus! { spec fn s(x: int) -> int recommends x > 0, { x } proof fn bad() { assert(forall|x: int| #![trigger s(x)] x > 0 ==> s(x) == x); assert(false); } }";
    let unguarded = guarded.replace("x > 0 ==> s(x) == x", "s(x) == x");
    let good_domain = common::run("recommends_quantified_guarded", guarded, &[]);
    failed_once(&good_domain, "bad");
    assert!(
        recommendation_notes(&good_domain).is_empty(),
        "{good_domain:?}"
    );
    let bad_domain = common::run("recommends_quantified_unguarded", &unguarded, &[]);
    failed_once(&bad_domain, "bad");
    assert_eq!(recommendation_notes(&bad_domain).len(), 1, "{bad_domain:?}");
    assert!(
        !bad_domain
            .diags
            .iter()
            .any(|diagnostic| diagnostic.message.contains("could not complete recommends")),
        "{bad_domain:?}"
    );
    let nested = "verus! { spec fn s(x: int) -> int recommends x > 0, { x } proof fn bad() { assert(forall|outer: int| #![trigger s(outer)] outer > 0 ==> (forall|inner: int| #![trigger s(inner)] inner > 0 ==> s(inner) == inner)); assert(false); } }";
    let missing_inner_guard =
        nested.replace("inner > 0 ==> s(inner) == inner", "s(inner) == inner");
    for (label, program, expected) in [
        ("recommends_nested_quantified_guarded", nested, 0),
        (
            "recommends_nested_quantified_unguarded",
            missing_inner_guard.as_str(),
            1,
        ),
    ] {
        let run = common::run(label, program, &[]);
        failed_once(&run, "bad");
        assert_eq!(recommendation_notes(&run).len(), expected, "{run:?}");
    }
}

#[test]
fn choose_existence_is_a_note_without_assuming_the_chosen_predicate() {
    let unseeded = "verus! { spec fn identity(x: int) -> int { x } proof fn bad() { let chosen = choose|x: int| identity(x) == 3; assert(chosen == chosen); assert(false); } }";
    // Actual source assertion supplies a verified material application. The
    // exact unseeded first-red program remains a faithful incompleteness twin.
    let source = unseeded.replace("let chosen", "assert(identity(3) == 3); let chosen");
    let impossible = source.replace("identity(x) == 3", "identity(x) != identity(x)");
    for (label, program, expected) in [
        ("recommends_choose_witness", source.as_str(), 0),
        ("recommends_choose_unseeded_warning", unseeded, 1),
        ("recommends_choose_impossible", impossible.as_str(), 1),
    ] {
        let run = common::run(label, program, &[]);
        failed_once(&run, "bad");
        assert_eq!(choice_notes(&run).len(), expected, "{run:?}");
    }
    let guarded = "verus! { spec fn s(x: int) -> int recommends x > 0, { x } proof fn bad() { let chosen = choose|x: int| x > 0 && s(x) == x; assert(chosen == chosen); assert(false); } }";
    let arbitrary = guarded.replace("x > 0 && s(x) == x", "s(x) == 0");
    for (label, program, expected) in [
        ("recommends_choose_guarded_domain", guarded, 0),
        ("recommends_choose_arbitrary_domain", arbitrary.as_str(), 1),
    ] {
        let run = common::run(label, program, &[]);
        failed_once(&run, "bad");
        assert_eq!(recommendation_notes(&run).len(), expected, "{run:?}");
    }
}

#[test]
fn a_nested_declared_domain_is_a_predicate_not_recursive_contract_evaluation() {
    let source = "verus! { spec fn inner(x: int) -> int recommends x > 0, { x } spec fn outer(x: int) -> int recommends inner(x) > 0, { x } proof fn bad() { assert(outer(0) == 1); } }";
    let run = common::run("recommends_nested_declared_predicate", source, &[]);
    failed_once(&run, "bad");
    assert_eq!(recommendation_notes(&run).len(), 1, "{run:?}");
    assert!(
        !run.diags
            .iter()
            .any(|diagnostic| diagnostic.message.contains("could not complete recommends")),
        "{run:?}"
    );
}

#[test]
fn recursive_spec_followup_keeps_failed_termination_and_checks_its_own_domain() {
    let source = "verus! { spec fn allowed(x: int) -> bool recommends x > 0, { true } spec fn cycle(n: int) -> int recommends allowed(n), decreases n, { if n >= 0 { cycle(n) } else { 0 } } }";
    let run = common::run("recommends_recursive_spec_own_nested_domain", source, &[]);
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert_eq!(function(&run, "cycle")["verdict"], "failed", "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
    assert!(run.errors()[0].message.contains("termination"), "{run:?}");
    assert_eq!(recommendation_notes(&run).len(), 1, "{run:?}");
    complete_recommends(&run);
    assert!(
        !run.diags
            .iter()
            .any(|diagnostic| diagnostic.message.contains("could not complete recommends")),
        "{run:?}"
    );
}

#[test]
fn recursive_spec_proof_assumptions_affect_only_later_domain_events() {
    let after = "verus! { spec fn domain(n: int) -> bool recommends n > 0, { true } spec fn cycle(n: int) -> int recommends n >= 0, decreases n, { proof { assume(n > 0); } let allowed = domain(n); if allowed { cycle(n) } else { 0 } } }";
    let before = after.replace(
        "proof { assume(n > 0); } let allowed = domain(n);",
        "let allowed = domain(n); proof { assume(n > 0); }",
    );
    for (label, program, expected) in [
        ("recommends_recursive_proof_before_domain", after, 0),
        (
            "recommends_recursive_proof_after_domain",
            before.as_str(),
            1,
        ),
    ] {
        let run = common::run(label, program, &[]);
        assert_eq!(run.outcome(), "verification-failed", "{run:?}");
        assert_eq!(function(&run, "cycle")["verdict"], "failed", "{run:?}");
        assert_eq!(run.errors().len(), 1, "{run:?}");
        assert!(run.errors()[0].message.contains("termination"), "{run:?}");
        assert_eq!(recommendation_notes(&run).len(), expected, "{run:?}");
        complete_recommends(&run);
    }
}

#[test]
fn proof_bearing_choice_and_following_physical_block_keep_diagnostic_order() {
    let source = r#"verus! {
spec fn identity(x: int) -> int { x }
spec fn domain(n: int) -> bool recommends n > 0, { true }
spec fn stronger(n: int) -> bool recommends n > 1, { true }
spec fn cycle(n: int) -> int decreases n, {
    let recursive = if n >= 0 { cycle(n) } else { 0 };
    let chosen = choose|x: int| #![trigger identity(x)] {
        proof { assume(n > 0); assert(identity(n) == n); }
        let allowed = domain(n);
        identity(x) == n && allowed
    };
    proof { assume(n > 1); }
    let later = stronger(n);
    if later { recursive + chosen - chosen } else { recursive }
}
}"#;
    let before = source.replace(
        "proof { assume(n > 0); assert(identity(n) == n); }\n        let allowed = domain(n);",
        "let allowed = domain(n);\n        proof { assume(n > 0); assert(identity(n) == n); }",
    );
    assert_ne!(source, before);
    for (label, program, expected) in [
        ("recommends_choice_proof_before_domain", source, 0),
        ("recommends_choice_proof_after_domain", before.as_str(), 1),
    ] {
        let run = common::run(label, program, &[]);
        assert_eq!(run.outcome(), "verification-failed", "{run:?}");
        assert_eq!(function(&run, "cycle")["verdict"], "failed", "{run:?}");
        assert_eq!(run.errors().len(), 1, "{run:?}");
        assert!(run.errors()[0].message.contains("termination"), "{run:?}");
        assert_eq!(recommendation_notes(&run).len(), expected, "{run:?}");
        assert!(
            choice_notes(&run).is_empty(),
            "ordered real witness must decide existence: {run:?}"
        );
        complete_recommends(&run);
        assert!(
            !run.diags
                .iter()
                .any(|diagnostic| diagnostic.message.contains("could not complete recommends")),
            "{run:?}"
        );
    }
}

#[test]
fn arithmetic_only_choice_keeps_upstream_missing_trigger_rejection() {
    let source = "verus! { proof fn bad() { let chosen = choose|x: int| x == 3; assert(chosen == chosen); assert(false); } }";
    let run = common::run("recommends_arithmetic_choice_missing_trigger", source, &[]);
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.errors().len(), 1, "{run:?}");
    assert_eq!(
        run.errors()[0].message,
        trust_vc_vcir::triggers::MSG_NO_TRIGGERS,
        "{run:?}"
    );
    assert!(run.raw.is_empty(), "{run:?}");
    assert_eq!(function(&run, "bad")["verdict"], "rejected", "{run:?}");
    assert!(recommendation_notes(&run).is_empty(), "{run:?}");
}
