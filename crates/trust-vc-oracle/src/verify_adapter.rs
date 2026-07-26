// trust-vc-oracle — Real verification adapter (trust-vc-core bridge)
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Connects the oracle/adaptive system to the actual trust_vc verification
// engine. Translates `FunctionSignature` + `ProposedAnnotations` into
// `Proof` obligations, invokes ay via `Verifier`, and returns structured
// `ProofFeedback`.

use std::time::Instant;

use trust_vc_core::verification_report::VerificationReportOptions;
use trust_vc_core::verify::{Proof, Verifier};

use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;
use crate::verify::report_to_feedback;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Solver mode selection for verification.
///
/// Maps to trust-vc-core solver modes: default (EUF + LRA), non-linear
/// integer arithmetic (NIA), or bit-vector precise reasoning.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolverMode {
    /// EUF + LRA theories — fastest, suitable for most linear specs.
    Default,
    /// Non-linear integer arithmetic (NIA) — required for multiplication.
    NonlinearArith,
    /// Bit-vector precise — exact hardware semantics for overflow/shift.
    BitVector,
}

impl SolverMode {
    fn as_str(&self) -> &'static str {
        match self {
            SolverMode::Default => "default",
            SolverMode::NonlinearArith => "nonlinear_arith",
            SolverMode::BitVector => "bit_vector",
        }
    }
}

/// Configuration for the verification adapter.
#[derive(Debug, Clone)]
pub struct VerifyConfig {
    /// Timeout in milliseconds for a single verification query.
    pub timeout_ms: u64,
    /// Which solver theory to use.
    pub solver_mode: SolverMode,
    /// Whether to enable per-assertion SMT pruning.
    pub enable_pruning: bool,
    /// Whether to emit verbose diagnostics to stderr.
    pub verbose: bool,
}

impl Default for VerifyConfig {
    fn default() -> Self {
        Self {
            timeout_ms: 30_000,
            solver_mode: SolverMode::Default,
            enable_pruning: true,
            verbose: false,
        }
    }
}

impl VerifyConfig {
    /// Creates a new config with defaults.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the timeout in milliseconds.
    #[must_use]
    pub fn with_timeout_ms(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Sets the solver mode.
    #[must_use]
    pub fn with_solver_mode(mut self, mode: SolverMode) -> Self {
        self.solver_mode = mode;
        self
    }

    /// Enables or disables per-assertion pruning.
    #[must_use]
    pub fn with_pruning(mut self, enable: bool) -> Self {
        self.enable_pruning = enable;
        self
    }

    /// Enables or disables verbose diagnostics.
    #[must_use]
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

// ---------------------------------------------------------------------------
// TrustVcVerifyAdapter
// ---------------------------------------------------------------------------

/// Low-level adapter that connects directly to the trust_vc verification engine.
///
/// Takes raw function metadata (name, variables, requires/ensures clauses),
/// constructs a `Proof` via the trust-vc-core builder API, runs ay, and
/// converts the `VerificationReport` into `ProofFeedback`.
pub struct TrustVcVerifyAdapter {
    config: VerifyConfig,
}

impl TrustVcVerifyAdapter {
    /// Creates a new adapter with the given configuration.
    pub fn new(config: VerifyConfig) -> Self {
        Self { config }
    }

    /// Verifies a single function given its raw parts.
    ///
    /// `function_name`: identifier for error messages.
    /// `variables`: (name, type) pairs for SMT variable declarations.
    /// `requires`: precondition strings (assumed true).
    /// `ensures`: postcondition strings (asserted).
    pub fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback {
        if self.config.verbose {
            eprintln!(
                "[verify_adapter] verifying '{}' mode={} vars={} req={} ens={}",
                function_name,
                self.config.solver_mode.as_str(),
                variables.len(),
                requires.len(),
                ensures.len(),
            );
        }

        let mut proof = Proof::new(function_name);

        for (name, ty) in variables {
            proof = proof.with_variable(name, ty);
        }

        for (idx, req) in requires.iter().enumerate() {
            let label = format!("requires_{}", idx);
            proof = proof.with_assumption(&label, req);
        }

        for ens in ensures {
            proof = proof.with_assertion(ens);
        }

        let options = VerificationReportOptions::new().with_verbose(self.config.verbose);
        let report = Verifier::verify_with_report(&proof, options);

        report_to_feedback(&report)
    }
}

// ---------------------------------------------------------------------------
// AnnotationVerifier
// ---------------------------------------------------------------------------

/// Higher-level verifier that works with `FunctionSignature` and
/// `ProposedAnnotations` directly.
///
/// Converts the oracle's domain types into verification obligations,
/// invokes the adapter, and returns `ProofFeedback` with counterexample
/// bindings when available.
pub struct AnnotationVerifier {
    adapter: TrustVcVerifyAdapter,
}

impl AnnotationVerifier {
    /// Creates a new annotation verifier with the given configuration.
    pub fn new(config: VerifyConfig) -> Self {
        Self {
            adapter: TrustVcVerifyAdapter::new(config),
        }
    }

    /// Returns a reference to the underlying configuration.
    #[must_use]
    pub fn config(&self) -> &VerifyConfig {
        &self.adapter.config
    }

    /// Verifies a set of proposed annotations against a function signature.
    ///
    /// The function's parameters become SMT variables. If the function has
    /// a return type, a `result` variable is added. The annotations'
    /// `requires` become assumptions and `ensures` become assertions.
    pub fn verify_annotations(
        &self,
        func: &FunctionSignature,
        annotations: &ProposedAnnotations,
    ) -> ProofFeedback {
        // No ensures means nothing to assert — trivially verified.
        if annotations.ensures.is_empty() {
            return ProofFeedback::Verified {
                steps: vec![],
                elapsed: std::time::Duration::ZERO,
                certificate_info: None,
            };
        }

        let mut variables: Vec<(String, String)> = func.params.clone();

        // Add a `result` variable if the function has a return type.
        if let Some(ref ret_ty) = func.return_type {
            variables.push(("result".to_string(), ret_ty.clone()));
        }

        self.adapter.verify(
            &func.name,
            &variables,
            &annotations.requires,
            &annotations.ensures,
        )
    }
}

// ---------------------------------------------------------------------------
// BatchVerifier
// ---------------------------------------------------------------------------

/// Verifies multiple (function, annotations) pairs sequentially.
///
/// Returns a vector of (function_name, feedback) pairs. Verification is
/// serialized because the trust-vc-core test-gate mutex serializes ay
/// calls within a single process.
pub struct BatchVerifier {
    verifier: AnnotationVerifier,
}

impl BatchVerifier {
    /// Creates a new batch verifier with the given configuration.
    pub fn new(config: VerifyConfig) -> Self {
        Self {
            verifier: AnnotationVerifier::new(config),
        }
    }

    /// Verifies a batch of (function, annotations) pairs.
    ///
    /// Returns a `Vec<(function_name, ProofFeedback)>` in the same order
    /// as the input. Each function is verified independently.
    pub fn verify_batch(
        &self,
        functions: &[(FunctionSignature, ProposedAnnotations)],
    ) -> Vec<(String, ProofFeedback)> {
        let verbose = self.verifier.config().verbose;

        if verbose {
            eprintln!("[batch_verifier] verifying {} functions", functions.len());
        }

        let start = Instant::now();

        let results: Vec<(String, ProofFeedback)> = functions
            .iter()
            .map(|(func, annotations)| {
                let feedback = self.verifier.verify_annotations(func, annotations);
                (func.name.clone(), feedback)
            })
            .collect();

        if verbose {
            let elapsed = start.elapsed();
            let verified_count = results.iter().filter(|(_, fb)| fb.is_verified()).count();
            eprintln!(
                "[batch_verifier] done: {}/{} verified in {:.1}ms",
                verified_count,
                results.len(),
                elapsed.as_secs_f64() * 1000.0,
            );
        }

        results
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::ProposedAnnotations;
    use crate::engine::FunctionSignature;

    fn empty_annotations() -> ProposedAnnotations {
        ProposedAnnotations {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            decreases: vec![],
            raw_response: String::new(),
        }
    }

    fn trivial_func(name: &str, param_ty: &str) -> FunctionSignature {
        FunctionSignature {
            name: name.to_string(),
            params: vec![("x".to_string(), param_ty.to_string())],
            return_type: Some(param_ty.to_string()),
            source: format!("fn {}(x: {}) -> {} {{ x }}", name, param_ty, param_ty),
            ..Default::default()
        }
    }

    // -----------------------------------------------------------------------
    // VerifyConfig tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_config_default() {
        let cfg = VerifyConfig::default();
        assert_eq!(cfg.timeout_ms, 30_000);
        assert_eq!(cfg.solver_mode, SolverMode::Default);
        assert!(cfg.enable_pruning);
        assert!(!cfg.verbose);
    }

    #[test]
    fn test_solver_mode_variants() {
        assert_eq!(SolverMode::Default.as_str(), "default");
        assert_eq!(SolverMode::NonlinearArith.as_str(), "nonlinear_arith");
        assert_eq!(SolverMode::BitVector.as_str(), "bit_vector");
        // Verify enum equality
        assert_ne!(SolverMode::Default, SolverMode::BitVector);
        assert_ne!(SolverMode::NonlinearArith, SolverMode::BitVector);
    }

    #[test]
    fn test_config_builder_pattern() {
        let cfg = VerifyConfig::new()
            .with_timeout_ms(5_000)
            .with_solver_mode(SolverMode::BitVector)
            .with_pruning(false)
            .with_verbose(true);

        assert_eq!(cfg.timeout_ms, 5_000);
        assert_eq!(cfg.solver_mode, SolverMode::BitVector);
        assert!(!cfg.enable_pruning);
        assert!(cfg.verbose);
    }

    #[test]
    fn test_config_timeout_propagation() {
        let cfg = VerifyConfig::new().with_timeout_ms(100);
        let verifier = AnnotationVerifier::new(cfg);
        assert_eq!(verifier.config().timeout_ms, 100);
    }

    #[test]
    fn test_config_verbose_mode_propagation() {
        let cfg = VerifyConfig::new().with_verbose(true);
        let verifier = AnnotationVerifier::new(cfg);
        assert!(verifier.config().verbose);
    }

    // -----------------------------------------------------------------------
    // AnnotationVerifier tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_annotation_verifier_empty_annotations() {
        let verifier = AnnotationVerifier::new(VerifyConfig::default());
        let func = trivial_func("empty_test", "u32");
        let annotations = empty_annotations();

        // No assertions means nothing to disprove — should verify.
        let feedback = verifier.verify_annotations(&func, &annotations);
        assert!(
            feedback.is_verified(),
            "empty annotations should verify trivially: {:?}",
            feedback
        );
    }

    #[test]
    fn test_annotation_verifier_trivially_true_requires() {
        let verifier = AnnotationVerifier::new(VerifyConfig::default());
        let func = trivial_func("trivial_req", "u32");

        // u32 >= 0 is always true; add it as both requires and ensures.
        let annotations = ProposedAnnotations {
            requires: vec!["x >= 0".to_string()],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "requires!(x >= 0) ensures!(x >= 0)".to_string(),
        };

        let feedback = verifier.verify_annotations(&func, &annotations);
        assert!(
            feedback.is_verified(),
            "u32 x >= 0 with requires x >= 0 should verify: {:?}",
            feedback
        );
    }

    #[test]
    fn test_annotation_verifier_contradictory_requires_ensures() {
        let verifier = AnnotationVerifier::new(VerifyConfig::default());
        let func = trivial_func("contradict", "i32");

        // Requires x > 0 but ensures x < 0 — contradictory, should fail.
        let annotations = ProposedAnnotations {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["x < 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "requires!(x > 0) ensures!(x < 0)".to_string(),
        };

        let feedback = verifier.verify_annotations(&func, &annotations);
        assert!(
            feedback.is_failed() || feedback.is_unknown(),
            "x > 0 contradicts x < 0: {:?}",
            feedback
        );
    }

    #[test]
    fn test_annotation_verifier_requires_only() {
        let verifier = AnnotationVerifier::new(VerifyConfig::default());
        let func = trivial_func("req_only", "i32");

        // Only requires, no ensures — nothing to assert, should verify.
        let annotations = ProposedAnnotations {
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            invariants: vec![],
            decreases: vec![],
            raw_response: "requires!(x > 0)".to_string(),
        };

        let feedback = verifier.verify_annotations(&func, &annotations);
        assert!(
            feedback.is_verified(),
            "requires-only with no ensures should verify: {:?}",
            feedback
        );
    }

    #[test]
    fn test_annotation_verifier_ensures_only() {
        let verifier = AnnotationVerifier::new(VerifyConfig::default());
        let func = trivial_func("ens_only", "u32");

        // u32 is always >= 0, no requires needed.
        let annotations = ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x >= 0)".to_string(),
        };

        let feedback = verifier.verify_annotations(&func, &annotations);
        assert!(
            feedback.is_verified(),
            "u32 x >= 0 without requires should verify: {:?}",
            feedback
        );
    }

    #[test]
    fn test_annotation_verifier_return_type_adds_result_var() {
        let verifier = AnnotationVerifier::new(VerifyConfig::default());

        // Function with return type — should get a `result` variable.
        let func = FunctionSignature {
            name: "with_ret".to_string(),
            params: vec![("x".to_string(), "u32".to_string())],
            return_type: Some("u32".to_string()),
            source: "fn with_ret(x: u32) -> u32 { x }".to_string(),
            ..Default::default()
        };

        // Assert on the `result` variable.
        let annotations = ProposedAnnotations {
            requires: vec![],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(result >= 0)".to_string(),
        };

        let feedback = verifier.verify_annotations(&func, &annotations);
        assert!(
            feedback.is_verified(),
            "u32 result >= 0 should verify: {:?}",
            feedback
        );
    }

    #[test]
    fn test_annotation_verifier_no_return_type() {
        let verifier = AnnotationVerifier::new(VerifyConfig::default());

        // Function without return type — no `result` variable.
        let func = FunctionSignature {
            name: "no_ret".to_string(),
            params: vec![("x".to_string(), "u32".to_string())],
            return_type: None,
            source: "fn no_ret(x: u32) { }".to_string(),
            ..Default::default()
        };

        let annotations = ProposedAnnotations {
            requires: vec!["x >= 0".to_string()],
            ensures: vec![],
            invariants: vec![],
            decreases: vec![],
            raw_response: "requires!(x >= 0)".to_string(),
        };

        let feedback = verifier.verify_annotations(&func, &annotations);
        assert!(
            feedback.is_verified(),
            "no-return-type function with trivial requires should verify: {:?}",
            feedback
        );
    }

    // -----------------------------------------------------------------------
    // TrustVcVerifyAdapter tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_adapter_direct_verify_passing() {
        let adapter = TrustVcVerifyAdapter::new(VerifyConfig::default());
        let feedback = adapter.verify(
            "direct_pass",
            &[("x".to_string(), "u32".to_string())],
            &[],
            &["x >= 0".to_string()],
        );
        assert!(
            feedback.is_verified(),
            "u32 x >= 0 should verify via adapter: {:?}",
            feedback
        );
    }

    #[test]
    fn test_adapter_direct_verify_failing() {
        let adapter = TrustVcVerifyAdapter::new(VerifyConfig::default());
        let feedback = adapter.verify(
            "direct_fail",
            &[("x".to_string(), "i32".to_string())],
            &[],
            &["x > 0".to_string()],
        );
        assert!(
            feedback.is_failed() || feedback.is_unknown(),
            "i32 x > 0 without requires should fail: {:?}",
            feedback
        );
    }

    // -----------------------------------------------------------------------
    // BatchVerifier tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_batch_verifier_empty_batch() {
        let batch = BatchVerifier::new(VerifyConfig::default());
        let results = batch.verify_batch(&[]);
        assert!(results.is_empty(), "empty batch produces empty results");
    }

    #[test]
    fn test_batch_verifier_single_function() {
        let batch = BatchVerifier::new(VerifyConfig::default());
        let func = trivial_func("single", "u32");
        let annotations = ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x >= 0)".to_string(),
        };

        let results = batch.verify_batch(&[(func, annotations)]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, "single");
        assert!(
            results[0].1.is_verified(),
            "single u32 batch should verify: {:?}",
            results[0].1
        );
    }

    #[test]
    fn test_batch_verifier_multiple_functions() {
        let batch = BatchVerifier::new(VerifyConfig::default());

        let pass_func = trivial_func("batch_pass", "u32");
        let pass_ann = ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x >= 0)".to_string(),
        };

        let fail_func = trivial_func("batch_fail", "i32");
        let fail_ann = ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x > 0)".to_string(),
        };

        let results = batch.verify_batch(&[(pass_func, pass_ann), (fail_func, fail_ann)]);

        assert_eq!(results.len(), 2);
        assert_eq!(results[0].0, "batch_pass");
        assert!(
            results[0].1.is_verified(),
            "u32 x >= 0 should verify: {:?}",
            results[0].1
        );
        assert_eq!(results[1].0, "batch_fail");
        assert!(
            results[1].1.is_failed() || results[1].1.is_unknown(),
            "i32 x > 0 without requires should fail: {:?}",
            results[1].1
        );
    }

    // -----------------------------------------------------------------------
    // ProofFeedback conversion correctness
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_feedback_conversion_verified() {
        let adapter = TrustVcVerifyAdapter::new(VerifyConfig::default());

        // Tautology: x > 0 implies x >= 0
        let feedback = adapter.verify(
            "conversion_test",
            &[("x".to_string(), "i32".to_string())],
            &["x > 0".to_string()],
            &["x >= 0".to_string()],
        );

        assert!(
            feedback.is_verified(),
            "tautology should verify: {:?}",
            feedback
        );
        if let ProofFeedback::Verified { elapsed, .. } = &feedback {
            assert!(elapsed.as_nanos() > 0, "elapsed time should be positive");
        }
    }

    #[test]
    fn test_proof_feedback_conversion_failed_has_info() {
        let adapter = TrustVcVerifyAdapter::new(VerifyConfig::default());

        // i32 can be negative, so x > 0 without requires should fail.
        let feedback = adapter.verify(
            "fail_info_test",
            &[("x".to_string(), "i32".to_string())],
            &[],
            &["x > 0".to_string()],
        );

        // Should be Failed (with counterexample) or Unknown.
        assert!(
            feedback.is_failed() || feedback.is_unknown(),
            "i32 x > 0 should fail: {:?}",
            feedback
        );

        if let ProofFeedback::Failed {
            counterexamples,
            elapsed,
            ..
        } = &feedback
        {
            assert!(elapsed.as_nanos() > 0, "elapsed time should be positive");
            // Counterexamples may or may not be populated depending on solver.
            let _ = counterexamples;
        }
    }

    // -----------------------------------------------------------------------
    // Error handling
    // -----------------------------------------------------------------------

    #[test]
    fn test_error_handling_malformed_source() {
        let adapter = TrustVcVerifyAdapter::new(VerifyConfig::default());

        // Malformed expression — the encoder may return Error feedback.
        let feedback = adapter.verify(
            "malformed",
            &[("x".to_string(), "i32".to_string())],
            &[],
            &["!!!INVALID!!!".to_string()],
        );

        // Accept Error or Unknown — both are valid for malformed input.
        // The important thing is that it does not panic.
        assert!(
            feedback.is_error() || feedback.is_unknown() || feedback.is_failed(),
            "malformed source should produce error/unknown/failed, not verified: {:?}",
            feedback
        );
    }
}
