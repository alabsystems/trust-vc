// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable MergeBundle runner using the ay SMT solver.
//!
//! Loads a `MergeBundle` (v3+) file, renders its executable core (variables,
//! assumptions, assertions) into an SMT-LIB2 script, executes it through
//! ay-dpll's `Executor`, and returns a normalized verdict.
//!
//! The runner requires `bundle_version >= 3` (the executable contract floor)
//! and `expression_format == smt_lib2_term_v1`. v4 proof metadata fields
//! (`func_decls`, `fuel_axioms`, `broadcast_lemmas`) are rendered as
//! `declare-fun` and quantified assertions before the assumption/assertion
//! block.
//!
//! Part of #2453, #2580, #2596.

pub mod error;
mod model;
mod render;

use std::path::Path;

use serde::Serialize;
use trust_vc_merge_contract::{ExpressionFormat, MergeBundle};

use crate::error::RunnerError;
use crate::model::extract_model_fingerprint;
use crate::render::{render_bundle_to_smt, validate_bundle_sorts};

/// Normalized verdict matching the shape expected by `merge_parity_common`.
#[derive(Debug, Clone, Serialize)]
pub struct NormalizedVerdict {
    fixture_id: String,
    engine: String,
    status: String,
    obligation_id: String,
    obligation_name: String,
    model_fingerprint: Option<String>,
    reason_class: Option<String>,
    raw_reason: Option<String>,
}

impl NormalizedVerdict {
    #[must_use]
    pub fn new(
        fixture_id: impl Into<String>,
        engine: impl Into<String>,
        status: impl Into<String>,
        obligation_id: impl Into<String>,
        obligation_name: impl Into<String>,
    ) -> Self {
        Self {
            fixture_id: fixture_id.into(),
            engine: engine.into(),
            status: status.into(),
            obligation_id: obligation_id.into(),
            obligation_name: obligation_name.into(),
            model_fingerprint: None,
            reason_class: None,
            raw_reason: None,
        }
    }

    #[must_use]
    pub fn with_model_fingerprint(mut self, fp: Option<String>) -> Self {
        self.model_fingerprint = fp;
        self
    }

    #[must_use]
    pub fn with_reason(mut self, reason_class: Option<String>, raw_reason: Option<String>) -> Self {
        self.reason_class = reason_class;
        self.raw_reason = raw_reason;
        self
    }

    #[must_use]
    pub fn fixture_id(&self) -> &str {
        &self.fixture_id
    }

    #[must_use]
    pub fn engine(&self) -> &str {
        &self.engine
    }

    #[must_use]
    pub fn status(&self) -> &str {
        &self.status
    }

    #[must_use]
    pub fn obligation_id(&self) -> &str {
        &self.obligation_id
    }

    #[must_use]
    pub fn obligation_name(&self) -> &str {
        &self.obligation_name
    }

    #[must_use]
    pub fn model_fingerprint(&self) -> Option<&str> {
        self.model_fingerprint.as_deref()
    }

    #[must_use]
    pub fn reason_class(&self) -> Option<&str> {
        self.reason_class.as_deref()
    }

    #[must_use]
    pub fn raw_reason(&self) -> Option<&str> {
        self.raw_reason.as_deref()
    }
}

/// Runs a MergeBundle from a file path and returns a normalized verdict.
///
/// This is the primary entry point for both the CLI and tests.
pub fn run_bundle_path(
    bundle_path: impl AsRef<Path>,
    obligation_id: &str,
    engine: &str,
) -> Result<NormalizedVerdict, RunnerError> {
    let path = bundle_path.as_ref();
    let payload = std::fs::read_to_string(path)?;
    let bundle = MergeBundle::from_json_str(&payload)?;
    run_bundle(&bundle, obligation_id, engine)
}

/// Runs a MergeBundle directly and returns a normalized verdict.
pub fn run_bundle(
    bundle: &MergeBundle,
    obligation_id: &str,
    engine: &str,
) -> Result<NormalizedVerdict, RunnerError> {
    validate_executable_bundle(bundle)?;
    validate_bundle_sorts(bundle)?;

    let smt_script = render_bundle_to_smt(bundle)?;

    let (status, model_text) = execute_smt(&smt_script)?;

    let model_fingerprint = if status == "sat" {
        let fp = model_text
            .as_deref()
            .map(|text| extract_model_fingerprint(text, bundle.variables()))
            .unwrap_or_else(|| "?".to_string());
        Some(fp)
    } else {
        None
    };

    let normalized_status = match status.as_str() {
        "unsat" => "verified",
        "sat" => "counterexample",
        "unknown" => "unknown",
        _ => "error",
    };

    Ok(NormalizedVerdict::new(
        bundle.source_id(),
        engine,
        normalized_status,
        obligation_id,
        obligation_id,
    )
    .with_model_fingerprint(model_fingerprint)
    .with_reason(
        if normalized_status == "error" {
            Some("executor_error".to_string())
        } else {
            None
        },
        if normalized_status == "error" {
            Some(status)
        } else {
            None
        },
    ))
}

/// Minimum bundle version that contains the executable contract
/// (variables, assumptions, assertions with `expression_format == smt_lib2_term_v1`).
const MIN_EXECUTABLE_BUNDLE_VERSION: u32 = 3;

/// Validates that the bundle meets the executable contract requirements.
///
/// Rejects bundles below the executable floor (v3) and bundles above the
/// contract crate's max supported version. The upper bound is delegated to
/// [`MergeBundle::enforce_supported_version`] so it stays in one place.
fn validate_executable_bundle(bundle: &MergeBundle) -> Result<(), RunnerError> {
    bundle.enforce_supported_version()?;

    if bundle.bundle_version() < MIN_EXECUTABLE_BUNDLE_VERSION {
        return Err(RunnerError::UnsupportedVersion {
            found: bundle.bundle_version(),
            min_executable: MIN_EXECUTABLE_BUNDLE_VERSION,
        });
    }

    match bundle.expression_format() {
        Some(ExpressionFormat::SmtLib2TermV1) => Ok(()),
        Some(_) => Err(RunnerError::UnsupportedExpressionFormat),
        None => Err(RunnerError::MissingExpressionFormat),
    }
}

/// Executes an SMT-LIB2 script through ay-dpll and returns (status, model_text).
fn execute_smt(smt_script: &str) -> Result<(String, Option<String>), RunnerError> {
    let commands =
        ay_frontend::parse(smt_script).map_err(|e| RunnerError::SmtParse(format!("{e:?}")))?;

    let mut executor = ay_dpll::Executor::new();
    let mut status = String::new();
    let mut model_text: Option<String> = None;

    for cmd in &commands {
        match executor.execute(cmd) {
            Ok(Some(output)) => {
                let trimmed = output.trim();
                if trimmed == "sat" || trimmed == "unsat" || trimmed == "unknown" {
                    status = trimmed.to_string();
                } else if trimmed.starts_with('(') {
                    // Model output or other S-expression
                    model_text = Some(trimmed.to_string());
                }
            }
            Ok(None) => {}
            Err(e) => {
                return Err(RunnerError::Executor(format!("{e:?}")));
            }
        }
    }

    if status.is_empty() {
        return Err(RunnerError::Executor(
            "no check-sat result received".to_string(),
        ));
    }

    Ok((status, model_text))
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_merge_contract::{
        BroadcastLemmaMeta, FuelAxiomMeta, FuncDeclMeta, SortMeta, TypedExpr, VarDecl,
    };

    fn verified_bundle() -> MergeBundle {
        MergeBundle::new("test_verified")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new("x", SortMeta::MathInt)])
            .with_assumptions(vec![TypedExpr::new("(> x 0)", SortMeta::Bool)])
            .with_assertions(vec![TypedExpr::new("(>= x 1)", SortMeta::Bool)])
    }

    fn counterexample_bundle() -> MergeBundle {
        MergeBundle::new("test_cex")
            .with_bundle_version(3)
            .with_variables(vec![VarDecl::new("x", SortMeta::MathInt)])
            .with_assertions(vec![TypedExpr::new("(> x 100)", SortMeta::Bool)])
    }

    #[test]
    fn test_run_verified_bundle() {
        let verdict = run_bundle(&verified_bundle(), "test_ob", "trust_vc_native").unwrap();
        assert_eq!(verdict.status(), "verified", "x > 0 implies x >= 1");
        assert!(verdict.model_fingerprint().is_none());
        assert_eq!(verdict.engine(), "trust_vc_native");
        assert_eq!(verdict.obligation_id(), "test_ob");
    }

    #[test]
    fn test_run_counterexample_bundle() {
        let verdict = run_bundle(&counterexample_bundle(), "test_ob", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "counterexample",
            "unconstrained x may be <= 100"
        );
        assert!(
            verdict.model_fingerprint().is_some(),
            "SAT should produce a model fingerprint"
        );
        let fp = verdict
            .model_fingerprint()
            .expect("SAT should produce a model fingerprint");
        assert!(
            fp.starts_with("x="),
            "fingerprint should contain x=...: {fp}"
        );
    }

    #[test]
    fn test_rejects_pre_v3_bundles() {
        for v in [1, 2] {
            let bundle = verified_bundle().with_bundle_version(v);
            let err = run_bundle(&bundle, "ob", "eng").unwrap_err();
            assert!(
                err.to_string().contains("version"),
                "should reject v{v} below executable floor: {err}"
            );
        }
    }

    #[test]
    fn test_rejects_unsupported_future_version() {
        let bundle = verified_bundle()
            .with_bundle_version(trust_vc_merge_contract::MERGE_BUNDLE_VERSION + 1);
        let err = run_bundle(&bundle, "ob", "eng").unwrap_err();
        assert!(
            err.to_string().contains("version"),
            "should reject version above contract max: {err}"
        );
    }

    #[test]
    fn test_rejects_missing_expression_format() {
        let bundle = verified_bundle().with_expression_format(None);
        let err = run_bundle(&bundle, "ob", "eng").unwrap_err();
        assert!(
            err.to_string().contains("expression_format"),
            "should reject missing format: {err}"
        );
    }

    #[test]
    fn test_v3_backward_compat_verified() {
        let verdict = run_bundle(&verified_bundle(), "v3_compat", "trust_vc_native").unwrap();
        assert_eq!(verdict.status(), "verified", "v3 bundles still verify");
    }

    #[test]
    fn test_v4_bundle_with_empty_proof_fields_verified() {
        let bundle = verified_bundle().with_bundle_version(4);
        let verdict = run_bundle(&bundle, "v4_empty", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "verified",
            "v4 bundle with empty proof fields should verify identically to v3"
        );
    }

    #[test]
    fn test_v4_bundle_with_nonempty_proof_fields_verified() {
        let bundle = verified_bundle()
            .with_bundle_version(4)
            .with_func_decls(vec![FuncDeclMeta::new(
                "factorial",
                vec!["n".to_string()],
                vec![SortMeta::MathInt],
                SortMeta::MathInt,
            )
            .with_recursive(true)])
            .with_fuel_axioms(vec![FuelAxiomMeta::new(
                "factorial",
                vec![VarDecl::new("n", SortMeta::MathInt)],
                TypedExpr::new(
                    "(= (factorial n) (ite (= n 0) 1 (* n (factorial (- n 1)))))",
                    SortMeta::Bool,
                ),
                TypedExpr::new("(factorial n)", SortMeta::MathInt),
            )])
            .with_broadcast_lemmas(vec![BroadcastLemmaMeta::new(
                "broadcast_factorial_nonneg",
                vec![VarDecl::new("n", SortMeta::MathInt)],
                TypedExpr::new("(>= (factorial n) 0)", SortMeta::Bool),
                vec![vec![TypedExpr::new("(factorial n)", SortMeta::MathInt)]],
            )
            .with_guard_expr(TypedExpr::new("(>= n 0)", SortMeta::Bool))]);

        let verdict = run_bundle(&bundle, "v4_proof", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "verified",
            "v4 bundle with proof fields renders and verifies correctly"
        );
    }

    #[test]
    fn test_v4_counterexample_with_unrelated_func_decl() {
        let bundle = counterexample_bundle()
            .with_bundle_version(4)
            .with_func_decls(vec![FuncDeclMeta::new(
                "f",
                vec!["a".to_string()],
                vec![SortMeta::MathInt],
                SortMeta::MathInt,
            )]);

        let verdict = run_bundle(&bundle, "v4_cex", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "counterexample",
            "unrelated func_decl does not affect counterexample verdict"
        );
    }

    #[test]
    fn test_v4_factorial_with_axiom_verifies() {
        let bundle = MergeBundle::new("factorial_axiom_test")
            .with_func_decls(vec![FuncDeclMeta::new(
                "factorial",
                vec!["n".to_string()],
                vec![SortMeta::MathInt],
                SortMeta::MathInt,
            )
            .with_recursive(true)])
            .with_fuel_axioms(vec![FuelAxiomMeta::new(
                "factorial",
                vec![VarDecl::new("n", SortMeta::MathInt)],
                TypedExpr::new(
                    "(= (factorial n) (ite (= n 0) 1 (* n (factorial (- n 1)))))",
                    SortMeta::Bool,
                ),
                TypedExpr::new("(factorial n)", SortMeta::MathInt),
            )])
            .with_assertions(vec![TypedExpr::new("(= (factorial 3) 6)", SortMeta::Bool)]);

        let verdict = run_bundle(&bundle, "factorial_axiom", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "verified",
            "factorial(3) == 6 should verify with defining axiom"
        );
    }

    #[test]
    fn test_v4_without_axiom_is_counterexample() {
        let bundle = MergeBundle::new("factorial_no_axiom_test")
            .with_func_decls(vec![FuncDeclMeta::new(
                "factorial",
                vec!["n".to_string()],
                vec![SortMeta::MathInt],
                SortMeta::MathInt,
            )
            .with_recursive(true)])
            // NO fuel_axioms — factorial is unconstrained
            .with_assertions(vec![TypedExpr::new("(= (factorial 3) 6)", SortMeta::Bool)]);

        let verdict = run_bundle(&bundle, "factorial_no_axiom", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "counterexample",
            "without axiom, factorial is unconstrained — solver picks factorial(3) != 6"
        );
    }

    #[test]
    fn test_run_checked_in_fixture() {
        let fixture_json =
            trust_vc_merge_contract::fixtures::read_checked_in_representative_fixture()
                .expect("checked-in fixture should be readable");
        let bundle = MergeBundle::from_json_str(&fixture_json).expect("fixture should parse");
        let verdict = run_bundle(&bundle, "lemma_sum_nonneg", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "verified",
            "representative fixture should verify: {verdict:?}"
        );
    }

    #[test]
    fn test_run_checked_in_counterexample_fixture() {
        let fixture_json =
            trust_vc_merge_contract::fixtures::read_checked_in_representative_counterexample_fixture(
            )
            .expect("checked-in counterexample fixture should be readable");
        let bundle = MergeBundle::from_json_str(&fixture_json).expect("fixture should parse");
        let verdict = run_bundle(&bundle, "lemma_sum_counterexample", "trust_vc_native").unwrap();
        assert_eq!(
            verdict.status(),
            "counterexample",
            "counterexample fixture should remain satisfiable: {verdict:?}"
        );
        assert_eq!(
            verdict.model_fingerprint(),
            Some("x=7"),
            "counterexample fixture should keep a deterministic fingerprint"
        );
    }
}
