//! Actual compiler controls for scoped local broadcast proof contracts.
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
mod common;

const ORIGINAL: &str = r#"verus! {
        mod M {
            pub struct A {}
            impl A {
                pub uninterp spec fn f1(&self) -> bool;
                pub uninterp spec fn f2(&self) -> bool;
                pub uninterp spec fn f3(&self) -> bool;
            }

            #[verifier::external_body]
            pub broadcast proof fn ab(a: A)
                ensures #![trigger a.f1()] (a.f1() ==> a.f2()) && a.f3()
            {
            }
        }

        use M::*;
        proof fn p(a: A)
            requires a.f1(),
            ensures a.f2(),
        {
            broadcast use ab;
        }
}"#;

#[test]
fn original_upstream_inner_trigger_broadcast_and_false_conclusion() {
    let run = common::run("broadcast_original", ORIGINAL, &[]);
    assert_eq!(run.exit, 0, "{run:?}");
    assert_eq!(run.outcome(), "checked", "{run:?}");
    assert!(run.raw.is_empty() && run.errors().is_empty(), "{run:?}");
    let functions = run.record["functions"].as_array().unwrap();
    assert_eq!(
        functions.iter().find(|f| f["def_path"] == "M::ab").unwrap()["verdict"],
        "trusted"
    );
    let false_source = ORIGINAL.replace("ensures a.f2(),", "ensures !a.f2(),");
    let run = common::run("broadcast_false_conclusion", &false_source, &[]);
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert!(!run.errors().is_empty() && run.raw.is_empty(), "{run:?}");
    let run = common::run("broadcast_no_cheating", ORIGINAL, &["--no-cheating"]);
    assert_ne!(run.exit, 0, "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.message.contains("external_body/assume_specification")),
        "{run:?}"
    );
}

const RULE: &str = r#"
    uninterp spec fn p(x: int) -> bool;
    uninterp spec fn q(x: int) -> bool;
    #[verifier::external_body]
    broadcast proof fn rule(x: int) requires p(x), ensures #[trigger] q(x) { }
"#;

#[test]
fn preconditions_function_identity_and_branch_guards_remain_authoritative() {
    for (name, body, positive) in [
        ("positive", "broadcast use rule; assert(q(7));", true),
        ("missing_use", "assert(q(7));", false),
        (
            "different_value",
            "broadcast use rule; assert(q(8));",
            false,
        ),
        (
            "then_only",
            "if flag { broadcast use rule; assert(q(7)); } else { assert(q(7)); }",
            false,
        ),
        (
            "join",
            "if flag { broadcast use rule; } assert(q(7));",
            false,
        ),
        (
            "both",
            "if flag { broadcast use rule; } else { broadcast use rule; } assert(q(7));",
            true,
        ),
    ] {
        let source =
            format!("verus! {{ {RULE} proof fn test(flag: bool) requires p(7), {{ {body} }} }}");
        let run = common::run(&format!("broadcast_{name}"), &source, &[]);
        assert_eq!(run.exit, if positive { 0 } else { 1 }, "{name}: {run:?}");
        assert_eq!(
            run.outcome(),
            if positive {
                "checked"
            } else {
                "verification-failed"
            },
            "{name}: {run:?}"
        );
        assert!(run.raw.is_empty(), "{name}: {run:?}");
    }
    let source =
        format!("verus! {{ {RULE} proof fn test() {{ broadcast use rule; assert(q(7)); }} }}");
    let run = common::run("broadcast_missing_precondition", &source, &[]);
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    let source = format!(
        "verus! {{ {RULE}
        proof fn enabled() requires p(7), {{ broadcast use rule; assert(q(7)); }}
        proof fn disabled() requires p(7), {{ assert(q(7)); }}
    }}"
    );
    let run = common::run("broadcast_function_scope", &source, &[]);
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    let functions = run.record["functions"].as_array().unwrap();
    assert_eq!(
        functions
            .iter()
            .find(|f| f["def_path"] == "enabled")
            .unwrap()["verdict"],
        "verified"
    );
    assert_eq!(
        functions
            .iter()
            .find(|f| f["def_path"] == "disabled")
            .unwrap()["verdict"],
        "failed"
    );
    let other = r#"mod Other {
        use super::*;
        pub uninterp spec fn q(x: int) -> bool;
        #[verifier::external_body]
        pub broadcast proof fn rule(x: int) ensures #[trigger] q(x) { }
    }"#;
    for (name, claim, positive) in [
        ("original_identity", "Other::q(7)", true),
        ("same_spelling", "q(7)", false),
    ] {
        let source = format!("verus! {{ {RULE} {other} proof fn test() requires p(7), {{ broadcast use Other::rule; assert({claim}); }} }}");
        let run = common::run(&format!("broadcast_{name}"), &source, &[]);
        assert_eq!(
            run.outcome(),
            if positive {
                "checked"
            } else {
                "verification-failed"
            },
            "{run:?}"
        );
    }
    let source =
        "verus! { proof fn ordinary(x: int) {} proof fn test() { broadcast use ordinary; } }";
    let run = common::run("broadcast_unmarked_target", source, &[]);
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|error| error.message.contains("broadcast proof fn")),
        "{run:?}"
    );
}

#[test]
fn checked_proof_bodies_and_nested_binders_are_retained() {
    let source = r#"verus! {
        #[verifier::opaque] spec fn f(x: int) -> bool { true }
        broadcast proof fn rule(x: int) ensures #[trigger] f(x) { }
        proof fn test() { broadcast use rule; assert(f(7)); }
    }"#;
    let run = common::run("broadcast_false_body", source, &[]);
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    assert_eq!(
        run.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["def_path"] == "rule")
            .unwrap()["verdict"],
        "failed"
    );
    let source = r#"verus! {
        uninterp spec fn p(x: int) -> bool;
        uninterp spec fn q(x: int, y: int) -> bool;
        #[verifier::external_body]
        broadcast proof fn rule(x: int) requires p(x),
            ensures #![trigger p(x)] forall|y: int| #[trigger] q(x,y)
        { }
        proof fn test() requires p(7), { broadcast use rule; assert(q(7,8)); }
    }"#;
    let run = common::run("broadcast_nested_binders", source, &[]);
    assert_eq!(run.exit, 0, "{run:?}");
    assert_eq!(run.outcome(), "checked", "{run:?}");
    let false_source = source.replace("assert(q(7,8))", "assert(q(8,7))");
    let run = common::run("broadcast_nested_false_binding", &false_source, &[]);
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
}

#[test]
fn recursive_broadcasts_and_generic_or_effectful_contracts_stay_refused() {
    for (name, source) in [
        ("cycle", "verus! { #[verifier::opaque] spec fn p(i:int)->bool { true } broadcast proof fn rule(i:int) ensures #[trigger] p(i) decreases i { broadcast use rule; } }"),
        ("generic", "verus! { uninterp spec fn p<A>(x:A)->bool; #[verifier::external_body] broadcast proof fn rule<A>(x:A) ensures #[trigger] p(x) {} }"),
        ("effect", "verus! { uninterp spec fn p(x:int)->bool; fn effect()->bool { true } #[verifier::external_body] broadcast proof fn rule(x:int) ensures #![trigger p(x)] effect() {} }"),
    ] {
        let run = common::run(&format!("broadcast_refused_{name}"), source, &[]);
        assert_ne!(run.exit, 0, "{name}: {run:?}");
        assert_ne!(run.outcome(), "checked", "{name}: {run:?}");
    }
}

#[test]
fn source_nat_domain_is_not_the_erased_integer_parameter_sort() {
    for (value, positive) in [("7", true), ("-1", false)] {
        let source = format!(
            r#"verus! {{
            uninterp spec fn p(x: int) -> bool;
            uninterp spec fn q(x: int) -> bool;
            #[verifier::external_body]
            broadcast proof fn rule(x: nat) requires p(x as int),
                ensures #![trigger p(x as int)] q(x as int) {{ }}
            proof fn test() requires p({value}), {{ broadcast use rule; assert(q({value})); }}
        }}"#
        );
        let run = common::run(&format!("broadcast_nat_{positive}"), &source, &[]);
        assert_eq!(
            run.outcome(),
            if positive {
                "checked"
            } else {
                "verification-failed"
            },
            "{run:?}"
        );
        assert!(run.raw.is_empty(), "{run:?}");
    }
}

#[test]
fn zero_parameter_broadcast_uses_ground_contract_and_disallows_direct_call() {
    let prefix = r#"uninterp spec fn p(x: int) -> bool;
        #[verifier::external_body]
        broadcast proof fn rule() ensures p(7) { }
    "#;
    let source =
        format!("verus! {{ {prefix} proof fn test() {{ broadcast use rule; assert(p(7)); }} }}");
    let run = common::run("broadcast_zero", &source, &[]);
    assert_eq!(run.outcome(), "checked", "{run:?}");
    let false_source = source.replace("assert(p(7))", "assert(p(8))");
    let run = common::run("broadcast_zero_false", &false_source, &[]);
    assert_eq!(run.outcome(), "verification-failed", "{run:?}");
    let direct = source.replace("broadcast use rule;", "rule();");
    let run = common::run("broadcast_zero_direct", &direct, &[]);
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(
        run.errors()
            .iter()
            .any(|e| e.message
                == "cannot call a broadcast_forall function with 0 arguments directly"),
        "{run:?}"
    );
}

#[test]
fn mutable_proof_parameter_syntax_is_refused_only_for_broadcast_contracts() {
    let source = r#"verus! {
        uninterp spec fn p(x: int) -> bool;
        proof fn ordinary(mut x: int)
            ensures #![trigger p(x)] p(x) || !p(x)
        { x = 1; }
    }"#;
    let ordinary = common::run("broadcast_mutable_ordinary", source, &[]);
    assert_eq!(ordinary.outcome(), "checked", "{ordinary:?}");
    let marked = source.replace("proof fn ordinary", "broadcast proof fn ordinary");
    let broadcast = common::run("broadcast_mutable_binding", &marked, &[]);
    assert_eq!(broadcast.outcome(), "refused", "{broadcast:?}");
    assert!(
        broadcast.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|function| function["def_path"] == "ordinary"
                && function["tag"] == "broadcast-contract"),
        "{broadcast:?}"
    );
    assert!(
        broadcast
            .errors()
            .iter()
            .any(|error| error.message.contains("mutable by-value parameter binding")),
        "{broadcast:?}"
    );
}
