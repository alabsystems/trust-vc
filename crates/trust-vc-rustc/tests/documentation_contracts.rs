//! Documentation expansion must not silently drop verified const contracts.

mod common;

fn run(name: &str, source: &str, mode: Option<&str>, flags: &[&str]) -> common::Run {
    common::run_with_environment(name, source, flags, &[("VERUSDOC", mode)])
}

fn refused(run: &common::Run) {
    assert_eq!(run.exit, 1, "{run:?}");
    assert_eq!(run.outcome(), "refused", "{run:?}");
    assert!(
        run.record["crate_refusals"]
            .as_array()
            .unwrap()
            .iter()
            .any(|reason| { reason.as_str().unwrap().contains("documentation-const") }),
        "{run:?}"
    );
    assert!(
        run.record["functions"].as_array().unwrap().is_empty(),
        "{run:?}"
    );
    assert!(run.record["erase_exit"].is_null(), "{run:?}");
    assert!(run.vcir.is_none(), "{run:?}");
}

#[test]
fn const_contracts_refuse_before_reader_and_verification() {
    for (name, postcondition) in [("false", "false"), ("positive", "r == 0")] {
        refused(&run(
            &format!("doc_const_{name}"),
            &format!(
                "verus! {{ pub const fn subject() -> (r: u8) ensures {postcondition} {{ 0 }} }}"
            ),
            Some("1"),
            &[],
        ));
    }
}

#[test]
fn associated_const_function_contracts_are_also_refused() {
    refused(&run(
        "doc_const_method",
        "verus! { struct S {} impl S { pub const fn subject() -> (r: u8) ensures false { 0 } } }",
        Some("1"),
        &[],
    ));
}

#[test]
fn nonconst_documentation_proofs_keep_positive_and_false_outcomes() {
    for (name, postcondition, exit, verdict) in [
        ("positive", "r == 0", 0, "verified"),
        ("false", "false", 1, "failed"),
    ] {
        let result = run(
            &format!("doc_nonconst_{name}"),
            &format!("verus! {{ pub fn subject() -> (r: u8) ensures {postcondition} {{ 0 }} }}"),
            Some("1"),
            &[],
        );
        assert_eq!(result.exit, exit, "{result:?}");
        assert!(
            result.record["crate_refusals"]
                .as_array()
                .unwrap()
                .is_empty(),
            "{result:?}"
        );
        assert_eq!(
            result.record["functions"][0]["verdict"], verdict,
            "{result:?}"
        );
        assert!(
            result.vcir.as_deref().unwrap().contains("ensures"),
            "{result:?}"
        );
    }
}

#[test]
fn inactive_documentation_values_keep_existing_const_refusal() {
    for (name, value) in [("absent", None), ("empty", Some("")), ("other", Some("0"))] {
        let result = run(
            &format!("doc_const_inactive_{name}"),
            "verus! { pub const fn subject() -> (r: u8) ensures false { 0 } }",
            value,
            &[],
        );
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
        assert!(
            result.record["crate_refusals"]
                .as_array()
                .unwrap()
                .iter()
                .all(|reason| !reason.as_str().unwrap().contains("documentation-const")),
            "{result:?}"
        );
    }
}

#[test]
fn injected_documentation_mode_takes_precedence_over_process_value() {
    let source = "verus! { pub const fn subject() -> (r: u8) ensures false { 0 } }";
    refused(&run(
        "doc_const_injected_active",
        source,
        None,
        &["-Zunstable-options", "--env-set=VERUSDOC=1"],
    ));
    let inactive = run(
        "doc_const_injected_inactive",
        source,
        Some("1"),
        &["-Zunstable-options", "--env-set=VERUSDOC="],
    );
    assert_eq!(inactive.exit, 1, "{inactive:?}");
    assert!(
        inactive.record["crate_refusals"]
            .as_array()
            .unwrap()
            .iter()
            .all(|reason| !reason.as_str().unwrap().contains("documentation-const")),
        "{inactive:?}"
    );
    assert!(
        inactive.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|function| function["verdict"] != "verified"),
        "{inactive:?}"
    );
}

#[test]
fn ordinary_const_without_documentation_macro_expansion_remains_supported() {
    let result = run(
        "doc_const_no_macro",
        "pub const fn subject() -> u8 { 0 }",
        Some("1"),
        &[],
    );
    assert_eq!(result.exit, 0, "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
    assert_eq!(
        result.record["functions"][0]["verdict"], "external",
        "{result:?}"
    );
    assert!(
        result.record["functions"][0]["sites_proved"].is_null(),
        "{result:?}"
    );
    assert!(
        result.record["functions"][0]["sites_failed"].is_null(),
        "{result:?}"
    );
}
