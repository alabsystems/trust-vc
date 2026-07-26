// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use std::path::{Path, PathBuf};

const CARGO_RS_UPSTREAM_PATH: &str = "source/rust_verify_test/tests/cargo.rs";
const PINNED_VERUS_REF: &str = "a40d57c73650cd3648b09386bfdb96ab5c270626";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MappingStatus {
    ReplacementScout,
    UnsupportedStateMachineProducer,
    UnsupportedStateMachineConsumer,
}

#[derive(Clone, Copy, Debug)]
struct CargoExampleMapping {
    group: &'static str,
    fixture: &'static str,
    case_id: &'static str,
    local_fixtures: &'static [&'static str],
    status: MappingStatus,
}

const CARGO_NEW_CASES: &[&str] = &["cargo_new_builds", "cargo_new_verifies"];

// Inventory from cargo_examples!(true) and cargo_examples!(false) in the pinned
// cargo.rs harness. This is intentionally zero-obligation scout evidence: it
// proves we can name and map the harness cases before claiming replacement
// evidence for the verifier behavior of each fixture.
const CARGO_EXAMPLES: &[CargoExampleMapping] = &[
    CargoExampleMapping {
        group: "unverified",
        fixture: "consume_basic_verified_lib",
        case_id: "unverified_consume_basic_verified_lib",
        local_fixtures: &["cargo_unverified_consume_basic_verified_lib"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "unverified",
        fixture: "consume_machines",
        case_id: "unverified_consume_machines",
        local_fixtures: &["cargo_unverified_consume_machines"],
        status: MappingStatus::UnsupportedStateMachineConsumer,
    },
    CargoExampleMapping {
        group: "unverified",
        fixture: "consume_vstd",
        case_id: "unverified_consume_vstd",
        local_fixtures: &["cargo_unverified_consume_vstd"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "unverified",
        fixture: "spec_use",
        case_id: "unverified_spec_use",
        local_fixtures: &["cargo_unverified_spec_use"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "unverified",
        fixture: "structural",
        case_id: "unverified_structural",
        local_fixtures: &["structural_fixture"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "basic_verified_lib",
        case_id: "verified_basic_verified_lib",
        local_fixtures: &["cargo_basic_verified_lib"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "basic_verified_lib_consumer_verified",
        case_id: "verified_basic_verified_lib_consumer_verified",
        local_fixtures: &["cargo_basic_verified_lib_consumer_verified"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "big_rlimit",
        case_id: "verified_big_rlimit",
        local_fixtures: &["cargo_big_rlimit"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "lib_with_bin",
        case_id: "verified_lib_with_bin",
        local_fixtures: &["cargo_lib_with_bin_lib", "cargo_lib_with_bin_bin"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "spec_def",
        case_id: "verified_spec_def",
        local_fixtures: &["cargo_spec_def"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "spec_def2",
        case_id: "verified_spec_def2",
        local_fixtures: &["cargo_spec_def2"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "spec_use",
        case_id: "verified_spec_use",
        local_fixtures: &["cargo_spec_use"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "state_machine_macro_usage",
        case_id: "verified_state_machine_macro_usage",
        local_fixtures: &["cargo_state_machine_macro_usage"],
        status: MappingStatus::UnsupportedStateMachineProducer,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "transitive1",
        case_id: "verified_transitive1",
        local_fixtures: &["cargo_transitive1"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "transitive2",
        case_id: "verified_transitive2",
        local_fixtures: &["cargo_transitive2"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "transitive3",
        case_id: "verified_transitive3",
        local_fixtures: &["cargo_transitive3"],
        status: MappingStatus::ReplacementScout,
    },
    CargoExampleMapping {
        group: "verified",
        fixture: "vstd_macro_usage",
        case_id: "verified_vstd_macro_usage",
        local_fixtures: &["cargo_vstd_macro_usage"],
        status: MappingStatus::ReplacementScout,
    },
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root should canonicalize")
}

fn fixture_path(repo_root: &Path, fixture: &str) -> PathBuf {
    repo_root.join("evals/verus/ported").join(fixture)
}

fn cargo_examples_case_id(group: &str, fixture: &str) -> String {
    format!("{group}_{}", fixture.replace('-', "_"))
}

fn cargo_rs_manifest_entry(repo_root: &Path) -> Value {
    let manifest_path = repo_root.join("evals/verus/verus-tests.json");
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(&manifest_path).expect("Verus manifest should be readable"),
    )
    .expect("Verus manifest should be JSON");
    manifest["entries"]
        .as_array()
        .expect("manifest entries should be an array")
        .iter()
        .find(|entry| entry["upstream_path"] == CARGO_RS_UPSTREAM_PATH)
        .unwrap_or_else(|| {
            panic!("manifest should contain the cargo.rs row for pinned ref {PINNED_VERUS_REF}")
        })
        .clone()
}

#[test]
fn cargo_examples_fixture_inventory_maps_active_pinned_cases_to_local_trust_vc_fixtures() {
    let repo_root = repo_root();

    for explicit_case in CARGO_NEW_CASES {
        assert!(
            explicit_case.starts_with("cargo_new_"),
            "explicit cargo.rs case should be a cargo new wrapper case: {explicit_case}"
        );
    }

    let mut observed_case_ids = CARGO_NEW_CASES.to_vec();
    observed_case_ids.extend(CARGO_EXAMPLES.iter().map(|mapping| mapping.case_id));
    observed_case_ids.sort_unstable();

    assert_eq!(
        observed_case_ids,
        vec![
            "cargo_new_builds",
            "cargo_new_verifies",
            "unverified_consume_basic_verified_lib",
            "unverified_consume_machines",
            "unverified_consume_vstd",
            "unverified_spec_use",
            "unverified_structural",
            "verified_basic_verified_lib",
            "verified_basic_verified_lib_consumer_verified",
            "verified_big_rlimit",
            "verified_lib_with_bin",
            "verified_spec_def",
            "verified_spec_def2",
            "verified_spec_use",
            "verified_state_machine_macro_usage",
            "verified_transitive1",
            "verified_transitive2",
            "verified_transitive3",
            "verified_vstd_macro_usage",
        ],
        "cargo.rs integration evidence must keep the full pinned cargo_examples inventory visible",
    );

    for mapping in CARGO_EXAMPLES {
        assert_eq!(
            mapping.case_id,
            cargo_examples_case_id(mapping.group, mapping.fixture),
            "case id should match cargo_examples! expansion for {}/{}",
            mapping.group,
            mapping.fixture
        );
        assert!(
            !mapping.local_fixtures.is_empty(),
            "{} should have at least one TrustVc fixture mapping",
            mapping.case_id
        );
        for fixture in mapping.local_fixtures {
            let local_fixture = fixture_path(&repo_root, fixture);
            assert!(
                local_fixture.join("Cargo.toml").is_file(),
                "{} should map to a local cargo fixture with Cargo.toml at {}",
                mapping.case_id,
                local_fixture.display()
            );
        }
    }
}

#[test]
fn cargo_examples_state_machine_fixture_mappings_remain_unsupported_scouts() {
    let repo_root = repo_root();
    let unsupported_cases = CARGO_EXAMPLES
        .iter()
        .filter(|mapping| mapping.status != MappingStatus::ReplacementScout)
        .map(|mapping| (mapping.case_id, mapping.status))
        .collect::<Vec<_>>();
    assert_eq!(
        unsupported_cases,
        vec![
            (
                "unverified_consume_machines",
                MappingStatus::UnsupportedStateMachineConsumer
            ),
            (
                "verified_state_machine_macro_usage",
                MappingStatus::UnsupportedStateMachineProducer
            ),
        ],
        "only the state-machine producer and consumer should be pinned as unsupported cargo.rs fixture mappings"
    );

    let producer_macros = std::fs::read_to_string(
        fixture_path(&repo_root, "cargo_state_machine_macro_usage")
            .join("verus_state_machines_macros/src/lib.rs"),
    )
    .expect("state-machine macro support crate should be readable");
    assert!(
        producer_macros.contains("compile_error!")
            && producer_macros.contains("state_machine! expansion")
            && producer_macros.contains("tokenized_state_machine! expansion"),
        "state_machine_macro_usage support crate should fail closed for unsupported Verus macros"
    );

    let consumer_support = std::fs::read_to_string(
        fixture_path(&repo_root, "cargo_unverified_consume_machines")
            .join("state_machine_macro_usage_support/src/lib.rs"),
    )
    .expect("consume_machines support crate should be readable");
    assert!(
        consumer_support.contains("pub struct Global")
            && consumer_support.contains("pub atomic: AtomicCounter")
            && consumer_support.contains("pub instance: Tracked<X::Instance>"),
        "consume_machines should still be wired to the simplified Global support state"
    );
    assert!(
        !consumer_support.contains("state_machine!")
            && !consumer_support.contains("tokenized_state_machine!"),
        "consume_machines support should not pretend to implement upstream state-machine macros"
    );
}

#[test]
fn cargo_rs_manifest_row_remains_unsupported_until_state_machine_fixtures_are_faithful() {
    let repo_root = repo_root();
    let row = cargo_rs_manifest_entry(&repo_root);
    assert_eq!(row["classification"], "unsupported-gap");
    assert_eq!(row["evidence_kind"], "cargo_trust_vc_integration_test");

    let reason = row["reason"]
        .as_str()
        .expect("cargo.rs row reason should be a string");
    assert!(
        reason.contains("not promotion-ready") && reason.contains("cargo_examples fixture cases"),
        "cargo.rs row should keep the promotion blocker explicit: {reason}"
    );

    let known_gaps = row["known_gaps"]
        .as_array()
        .expect("cargo.rs row known_gaps should be an array")
        .iter()
        .map(|gap| gap.as_str().expect("known gap should be a string"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        known_gaps.contains("state_machine_macro_usage")
            && known_gaps.contains("unverified/consume_machines")
            && known_gaps.contains("unsupported"),
        "cargo.rs row should explicitly name the unsupported state-machine producer and consumer gaps: {known_gaps}"
    );
}
