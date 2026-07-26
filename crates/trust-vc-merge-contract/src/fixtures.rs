// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::{
    BroadcastLemmaMeta, DecreasesClause, FuelAxiomMeta, FuncDeclMeta, MergeBundle,
    MergeBundleError, SortMeta, TriggerGroup, TypedExpr, VarDecl,
};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use thiserror::Error;

pub const REPRESENTATIVE_FIXTURE_REL_PATH: &str =
    "fixtures/merge_bundle/representative_obligation_v3.json";
pub const REPRESENTATIVE_COUNTEREXAMPLE_FIXTURE_REL_PATH: &str =
    "fixtures/merge_bundle/representative_counterexample_v3.json";
pub const REPRESENTATIVE_V4_FIXTURE_REL_PATH: &str =
    "fixtures/merge_bundle/representative_obligation_v4.json";

fn standard_metadata() -> BTreeMap<String, String> {
    let mut metadata = BTreeMap::new();
    metadata.insert("capabilities".to_string(), "decreases,triggers".to_string());
    metadata.insert("source_backend".to_string(), "ay".to_string());
    metadata.insert("source_repo".to_string(), "trust_vc".to_string());
    metadata
}

fn fixture_path(rel_path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel_path)
}

fn write_fixture_json(path: impl AsRef<Path>, json: String) -> Result<(), FixtureError> {
    let path = path.as_ref();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|source| FixtureError::CreateDir {
            path: parent.to_path_buf(),
            source,
        })?;
    }

    fs::write(path, json).map_err(|source| FixtureError::WriteFile {
        path: path.to_path_buf(),
        source,
    })
}

/// Deterministic representative fixture for merge-boundary compatibility checks.
///
/// All `TypedExpr.expr` strings are canonical SMT-LIB2 term text, matching the
/// v3 wire format (`expression_format: smt_lib2_term_v1`).
#[must_use]
pub fn representative_bundle() -> MergeBundle {
    MergeBundle::new("trust_vc::examples::arith::lemma_sum_nonneg")
        .with_bundle_version(3)
        .with_variables(vec![
            VarDecl::new(
                "n",
                SortMeta::BitVector {
                    width: 32,
                    signed: false,
                },
            ),
            VarDecl::new(
                "sum_n",
                SortMeta::BitVector {
                    width: 64,
                    signed: false,
                },
            ),
        ])
        .with_assumptions(vec![TypedExpr::new(
            "(= sum_n ((_ zero_extend 32) n))",
            SortMeta::Bool,
        )])
        .with_assertions(vec![TypedExpr::new(
            "(bvuge sum_n ((_ zero_extend 32) n))",
            SortMeta::Bool,
        )])
        .with_decreases(vec![DecreasesClause::new(
            "lemma_sum_nonneg",
            vec![TypedExpr::new(
                "n",
                SortMeta::BitVector {
                    width: 32,
                    signed: false,
                },
            )],
        )])
        .with_triggers(vec![TriggerGroup::new(
            "lemma_sum_nonneg",
            vec![TypedExpr::new(
                "(sum n)",
                SortMeta::BitVector {
                    width: 64,
                    signed: false,
                },
            )],
        )])
        .with_metadata(standard_metadata())
}

/// Deterministic counterexample fixture for executable merge-boundary checks.
#[must_use]
pub fn representative_counterexample_bundle() -> MergeBundle {
    MergeBundle::new("trust_vc::examples::arith::lemma_sum_counterexample")
        .with_bundle_version(3)
        .with_variables(vec![VarDecl::new("x", SortMeta::MathInt)])
        .with_assumptions(vec![TypedExpr::new("(= x 7)", SortMeta::Bool)])
        .with_assertions(vec![TypedExpr::new("(> x 100)", SortMeta::Bool)])
        .with_decreases(vec![DecreasesClause::new(
            "lemma_sum_counterexample",
            vec![TypedExpr::new("x", SortMeta::MathInt)],
        )])
        .with_triggers(vec![TriggerGroup::new(
            "lemma_sum_counterexample",
            vec![TypedExpr::new("x", SortMeta::MathInt)],
        )])
        .with_metadata(standard_metadata())
}

/// Deterministic v4 representative fixture with function declarations,
/// fuel axioms, and broadcast lemmas.
#[must_use]
pub fn representative_v4_bundle() -> MergeBundle {
    let bv64 = SortMeta::BitVector {
        width: 64,
        signed: false,
    };
    let mut metadata = standard_metadata();
    metadata.insert(
        "capabilities".to_string(),
        "decreases,triggers,func_decls,fuel_axioms,broadcast_lemmas".to_string(),
    );

    MergeBundle::new("trust_vc::examples::arith::factorial_with_broadcast")
        .with_variables(vec![
            VarDecl::new("n", bv64.clone()),
            VarDecl::new(
                "weight",
                SortMeta::FloatingPoint {
                    exponent_bits: 8,
                    significand_bits: 24,
                },
            ),
            VarDecl::new(
                "items",
                SortMeta::Seq {
                    elem: Box::new(SortMeta::MathInt),
                },
            ),
            VarDecl::new(
                "buf",
                SortMeta::Array {
                    index: Box::new(bv64.clone()),
                    element: Box::new(SortMeta::BitVector {
                        width: 32,
                        signed: false,
                    }),
                },
            ),
        ])
        .with_assumptions(vec![TypedExpr::new(
            "(bvule n (_ bv20 64))",
            SortMeta::Bool,
        )])
        .with_assertions(vec![TypedExpr::new(
            "(bvugt (factorial n) (_ bv0 64))",
            SortMeta::Bool,
        )])
        .with_decreases(vec![DecreasesClause::new(
            "factorial",
            vec![TypedExpr::new("n", bv64.clone())],
        )])
        .with_metadata(metadata)
        .with_func_decls(vec![FuncDeclMeta::new(
            "factorial",
            vec!["n".to_string()],
            vec![bv64.clone()],
            bv64.clone(),
        )
        .with_recursive(true)])
        .with_fuel_axioms(vec![FuelAxiomMeta::new(
            "factorial",
            vec![VarDecl::new("n", bv64.clone())],
            TypedExpr::new(
                "(= (factorial n) (ite (= n (_ bv0 64)) (_ bv1 64) (bvmul n (factorial (bvsub n (_ bv1 64))))))",
                SortMeta::Bool,
            ),
            TypedExpr::new("(factorial n)", bv64.clone()),
        )])
        .with_broadcast_lemmas(vec![BroadcastLemmaMeta::new(
            "broadcast_factorial_positive",
            vec![VarDecl::new("n", bv64.clone())],
            TypedExpr::new("(bvugt (factorial n) (_ bv0 64))", SortMeta::Bool),
            vec![vec![TypedExpr::new("(factorial n)", bv64)]],
        )
        .with_guard_expr(TypedExpr::new(
            "(bvule n (_ bv20 64))",
            SortMeta::Bool,
        ))])
}

#[must_use]
pub fn representative_fixture_path() -> PathBuf {
    fixture_path(REPRESENTATIVE_FIXTURE_REL_PATH)
}

#[must_use]
pub fn representative_counterexample_fixture_path() -> PathBuf {
    fixture_path(REPRESENTATIVE_COUNTEREXAMPLE_FIXTURE_REL_PATH)
}

pub fn representative_fixture_json() -> Result<String, MergeBundleError> {
    let mut json = representative_bundle().to_pretty_json()?;
    json.push('\n');
    Ok(json)
}

pub fn representative_counterexample_fixture_json() -> Result<String, MergeBundleError> {
    let mut json = representative_counterexample_bundle().to_pretty_json()?;
    json.push('\n');
    Ok(json)
}

pub fn representative_v4_fixture_json() -> Result<String, MergeBundleError> {
    let mut json = representative_v4_bundle().to_pretty_json()?;
    json.push('\n');
    Ok(json)
}

#[must_use]
pub fn representative_v4_fixture_path() -> PathBuf {
    fixture_path(REPRESENTATIVE_V4_FIXTURE_REL_PATH)
}

pub fn read_checked_in_representative_fixture() -> Result<String, FixtureError> {
    let path = representative_fixture_path();
    fs::read_to_string(&path).map_err(|source| FixtureError::ReadFile { path, source })
}

pub fn read_checked_in_representative_counterexample_fixture() -> Result<String, FixtureError> {
    let path = representative_counterexample_fixture_path();
    fs::read_to_string(&path).map_err(|source| FixtureError::ReadFile { path, source })
}

pub fn read_checked_in_v4_fixture() -> Result<String, FixtureError> {
    let path = representative_v4_fixture_path();
    fs::read_to_string(&path).map_err(|source| FixtureError::ReadFile { path, source })
}

pub fn write_representative_fixture(path: impl AsRef<Path>) -> Result<(), FixtureError> {
    write_fixture_json(path, representative_fixture_json()?)
}

pub fn write_representative_counterexample_fixture(
    path: impl AsRef<Path>,
) -> Result<(), FixtureError> {
    write_fixture_json(path, representative_counterexample_fixture_json()?)
}

pub fn write_default_representative_fixture() -> Result<PathBuf, FixtureError> {
    let path = representative_fixture_path();
    write_representative_fixture(&path)?;
    Ok(path)
}

pub fn write_default_representative_counterexample_fixture() -> Result<PathBuf, FixtureError> {
    let path = representative_counterexample_fixture_path();
    write_representative_counterexample_fixture(&path)?;
    Ok(path)
}

pub fn write_default_v4_fixture() -> Result<PathBuf, FixtureError> {
    let path = representative_v4_fixture_path();
    write_fixture_json(&path, representative_v4_fixture_json()?)?;
    Ok(path)
}

#[derive(Debug, Error)]
pub enum FixtureError {
    #[error(transparent)]
    Bundle(#[from] MergeBundleError),
    #[error("failed to create fixture directory {path}: {source}")]
    CreateDir {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to read fixture file {path}: {source}")]
    ReadFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("failed to write fixture file {path}: {source}")]
    WriteFile {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
}

#[cfg(test)]
mod tests {
    use super::{
        read_checked_in_representative_counterexample_fixture,
        read_checked_in_representative_fixture, read_checked_in_v4_fixture,
        representative_counterexample_fixture_json, representative_fixture_json,
        representative_v4_fixture_json,
    };
    use crate::MergeBundle;

    #[test]
    fn representative_fixture_generation_is_deterministic() {
        let first = representative_fixture_json().expect("first fixture generation should succeed");
        let second =
            representative_fixture_json().expect("second fixture generation should succeed");
        assert_eq!(first, second, "fixture generation must be deterministic");
    }

    #[test]
    fn checked_in_fixture_matches_generator_output() {
        let generated = representative_fixture_json().expect("fixture generation should succeed");
        let checked_in = read_checked_in_representative_fixture()
            .expect("checked-in representative fixture should be readable");
        assert_eq!(
            generated, checked_in,
            "checked-in fixture drifted from deterministic generator output"
        );
    }

    #[test]
    fn representative_counterexample_fixture_generation_is_deterministic() {
        let first = representative_counterexample_fixture_json()
            .expect("first counterexample fixture generation should succeed");
        let second = representative_counterexample_fixture_json()
            .expect("second counterexample fixture generation should succeed");
        assert_eq!(
            first, second,
            "counterexample fixture generation must be deterministic"
        );
    }

    #[test]
    fn checked_in_counterexample_fixture_matches_generator_output() {
        let generated = representative_counterexample_fixture_json()
            .expect("counterexample fixture generation should succeed");
        let checked_in = read_checked_in_representative_counterexample_fixture()
            .expect("checked-in representative counterexample fixture should be readable");
        assert_eq!(
            generated, checked_in,
            "checked-in counterexample fixture drifted from deterministic generator output"
        );
    }

    #[test]
    fn v4_fixture_generation_is_deterministic() {
        let first =
            representative_v4_fixture_json().expect("first v4 fixture generation should succeed");
        let second =
            representative_v4_fixture_json().expect("second v4 fixture generation should succeed");
        assert_eq!(first, second, "v4 fixture generation must be deterministic");
    }

    #[test]
    fn checked_in_v4_fixture_matches_generator_output() {
        let generated =
            representative_v4_fixture_json().expect("v4 fixture generation should succeed");
        let checked_in =
            read_checked_in_v4_fixture().expect("checked-in v4 fixture should be readable");
        assert_eq!(
            generated, checked_in,
            "checked-in v4 fixture drifted from deterministic generator output"
        );
    }

    #[test]
    fn v3_fixture_parses_under_v4_code() {
        let v3_json = read_checked_in_representative_fixture()
            .expect("checked-in v3 fixture should be readable");
        let bundle =
            MergeBundle::from_json_str(&v3_json).expect("v3 fixture should parse under v4 code");
        assert_eq!(bundle.bundle_version(), 3);
        assert!(
            bundle.func_decls().is_empty(),
            "v3 bundle should have no func_decls"
        );
        assert!(
            bundle.fuel_axioms().is_empty(),
            "v3 bundle should have no fuel_axioms"
        );
        assert!(
            bundle.broadcast_lemmas().is_empty(),
            "v3 bundle should have no broadcast_lemmas"
        );
    }

    #[test]
    fn v4_fixture_round_trips() {
        let v4_json =
            representative_v4_fixture_json().expect("v4 fixture generation should succeed");
        let bundle = MergeBundle::from_json_str(&v4_json).expect("v4 fixture should parse");
        assert_eq!(bundle.bundle_version(), 4);
        assert_eq!(bundle.func_decls().len(), 1, "should have 1 func_decl");
        assert_eq!(bundle.fuel_axioms().len(), 1, "should have 1 fuel_axiom");
        assert_eq!(
            bundle.broadcast_lemmas().len(),
            1,
            "should have 1 broadcast_lemma"
        );
        assert_eq!(bundle.func_decls()[0].name(), "factorial");
        assert!(bundle.func_decls()[0].is_recursive());
        assert_eq!(bundle.fuel_axioms()[0].function_name(), "factorial");
        assert_eq!(
            bundle.broadcast_lemmas()[0].name(),
            "broadcast_factorial_positive"
        );
        assert!(bundle.broadcast_lemmas()[0].guard_expr().is_some());
        assert_eq!(bundle.broadcast_lemmas()[0].trigger_groups().len(), 1);
        // Round-trip: re-serialize and compare
        let reserialized = bundle.to_pretty_json().expect("should re-serialize");
        let mut reserialized_nl = reserialized;
        reserialized_nl.push('\n');
        assert_eq!(
            v4_json, reserialized_nl,
            "v4 fixture should round-trip identically"
        );
    }
}
