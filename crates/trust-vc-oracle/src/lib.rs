// trust-vc-oracle — LLM Proof Oracle with Semantic Feedback
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Provides a programmatic API for LLM-guided proof synthesis.
// The oracle proposes annotations, verifies them via trust_vc, and returns
// structured semantic feedback (typed counterexamples, failure localization,
// proof certificates) that enables LLMs to refine their proposals.

pub mod adaptive;
pub mod backend;
pub mod cgsr;
pub mod cgsr_engine;
pub mod cgsr_metrics;
pub mod codex_backend;
pub mod convergence;
pub mod engine;
pub mod error;
pub mod feedback;
pub mod mining;
pub mod orchestrator;
pub mod planner;
pub mod prompt;
pub mod prompt_templates;
pub mod quality;
pub mod refinement_loop;
pub mod session;
pub mod source_parser;
pub mod spec_diff;
pub mod spec_language;
pub mod spec_ranking;
pub mod spec_store;
pub mod templates;
mod verify;
pub mod verify_adapter;

pub use backend::{LlmBackend, LlmConfig, MockBackend, ProposedAnnotations};
pub use codex_backend::{ClaudeBackend, CodexBackend};
pub use engine::{run_oracle, FunctionSignature, OracleConfig, OracleResult};
pub use error::OracleError;
pub use feedback::{
    CertificateInfo, CounterexampleField, FailureLocalization, ProofFeedback, StepSummary,
    SubAssertionResult, SubAssertionStatus,
};
pub use mining::{mine_specs, MinedSpec, MiningConfig};
pub use source_parser::{parse_function_by_name, parse_functions, try_parse_functions};
pub use spec_ranking::{rank_specs, RankedSpec, SpecScore};
pub use spec_store::{SpecStore, StoredSpec};
pub use templates::{all_templates, applicable_templates, SpecTemplate};
