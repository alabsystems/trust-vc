//! TrustVc core - Verification condition generation
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This crate is the verification engine of trust-vc, the proof backend of
//! Trust (the rustc fork), driving the pure-Rust `ay` solver. Drop-in
//! Verus parity is the benchmark/gate, not the end goal; the destination is
//! Trust's proof calculus + SMT backend. See `design-trust-proof-backend.md`.
//!
//! Generates ay verification conditions for Verus-style proof features:
//! - Proof functions and recursive proof blocks
//! - Termination proofs via well-founded orderings
//! - Broadcast lemmas with triggers and selective import groups
//! - Spec-only ghost functions
//!
//! # Verification pipeline
//!
//! TrustVc verifies concrete contexts via `VerificationContext::verify()`:
//! - `#[proof]` functions are marked with internal attributes
//! - Proof obligations become verification conditions
//! - `VerificationContext::verify()` routes into the encoder and ay
//! - proc-macro collection flows through `VerificationPipeline::verify()`
//!
//! # Public API
//!
//! Merge-facing consumers should import from the crate root plus these modules:
//! - `VerifyResult` and `UnknownCategory` for verification outcomes
//! - `vc` for `VerificationContext`, obligations, and typed variable setup
//! - `ir` for `TrustVcType` and `TrustVcExpr`
//! - `verify` for the lightweight `Proof`/`Verifier` builder API
//! - `verification_bridge` for proc-macro driven collection in tests
//!
//! # Quick Start
//!
//! ```no_run
//! use trust_vc_core::ir::TrustVcType;
//! use trust_vc_core::vc::{ProofObligation, VerificationContext};
//! use trust_vc_core::VerifyResult;
//!
//! let mut ctx = VerificationContext::new();
//! ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
//! ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));
//!
//! let result = ctx.verify();
//! assert!(matches!(
//!     result,
//!     VerifyResult::Verified
//!         | VerifyResult::Counterexample { .. }
//!         | VerifyResult::Unknown { .. }
//!         | VerifyResult::Error { .. }
//! ));
//! ```
//!
//! # Verification Entry Points
//!
//! TrustVc exposes three intended verification layers:
//! - `VerificationPipeline::verify()` for proc-macro driven tests that collect
//!   proof state from thread-local registration.
//! - `verify::Proof` plus `Verifier::verify()` for programmatic proof/test APIs.
//! - `VerificationContext::verify()` for direct context construction and
//!   integration code that already owns the lowered verification state.

// Trust bootstrap applies rustc-internal warning policy to this proof-backend
// verifier crate; trust_vc keeps public APIs for downstream verifier consumers and
// intentionally uses std hashes/non-query iteration outside rustc query providers.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unreachable_pub
)]

use trust_vc_merge_contract as _;

/// Bare no-op marker shims (`requires`/`ensures`/`forall`/`exists`) the trust_vc
/// macros emit under `--cfg trust_vc_driver` for the rustc-driver front end.
#[doc(hidden)]
pub mod __driver_markers;
pub(crate) mod assert_by_parser;
pub(crate) mod assert_forall_binder_inference;
pub(crate) mod assert_forall_by_parser;
pub(crate) mod assert_seqs_equal_parser;
pub(crate) mod attr_doc_metadata;
pub(crate) mod attributes;
pub(crate) mod ay_contracts;
pub(crate) mod broadcast;
pub(crate) mod broadcast_state;
pub(crate) mod calc_parser;
pub(crate) mod chained_comparisons;
pub mod compilation_proven_facts;
pub(crate) mod context_management;
pub(crate) mod contract_monitor;
pub(crate) mod contract_registry;
pub(crate) mod counterexample_names;
pub(crate) mod decreases;
pub(crate) mod decreases_lex;
pub(crate) mod decreases_runtime;
#[doc(hidden)]
pub mod decreases_to_runtime;
pub(crate) mod diverging_if_desugar;
pub(crate) mod encoder;
pub(crate) mod encoder_instrumentation;
pub(crate) mod enum_int_cast_desugar;
/// Serialized process-environment mutation — the workspace's blessed choke
/// point for `std::env::set_var` / `remove_var` (see the module docs).
pub mod env;
pub(crate) mod error;
#[allow(dead_code)]
pub(crate) mod error_catalog;
pub(crate) mod expr_codegen;
pub(crate) mod expr_depth;
pub(crate) mod extensional_eq;
pub(crate) mod extern_spec;
pub(crate) mod extern_spec_call_bindings;
pub(crate) mod extern_spec_catalog;
pub(crate) mod extern_spec_helpers;
pub(crate) mod extern_spec_registry;
pub(crate) mod extern_spec_verify;
pub(crate) mod for_range_desugar;
pub mod full_verification;
pub mod harness;
pub(crate) mod impl_trait_desugar;
pub mod ir;
#[doc(hidden)]
pub mod ir_builder;
mod ir_error;
pub(crate) mod ir_expr;
mod ir_expr_methods;
pub(crate) mod ir_expr_traversal;
pub(crate) mod ir_lowering;
pub(crate) mod ir_place;
mod local_vars;
mod local_vars_helpers;
pub mod loop_metadata;
pub(crate) mod marker_extraction;
pub(crate) mod match_pattern_scope;
pub(crate) mod matches_macro_desugar;
pub mod mode;
pub(crate) mod mode_attrs;
pub(crate) mod mode_body;
pub(crate) mod mode_index;
pub(crate) mod mode_paths;
pub(crate) mod mode_scan;
pub(crate) mod monitor_hooks;
mod mut_ref_proof;
pub(crate) mod named_groups;
pub(crate) mod obligation_collection;
#[cfg(test)]
mod obligation_collection_origin_tests;
pub(crate) mod prepared_context;
pub(crate) mod proof_doc_metadata;
pub(crate) mod proof_expand;
pub mod proof_note;
pub(crate) mod proof_session;
pub(crate) mod proof_stmt_bridge;
pub(crate) mod proof_var_mode;
#[cfg(feature = "ty")]
pub mod protocol;
pub(crate) mod protocol_expand;
pub mod proven_facts;
pub(crate) mod recursion_graph;
#[cfg(test)]
pub(crate) mod smtlib2_emit;
mod solver_mode_assert_parser;
pub(crate) mod source_tree;
pub(crate) mod spec_expand;
pub(crate) mod spec_function_catalog;
#[cfg(test)]
pub(crate) mod static_extraction;
pub(crate) mod struct_rest_pattern_desugar;
pub(crate) mod support_root;
pub(crate) mod theory_contracts;
pub(crate) mod tracked_syntax;
pub(crate) mod trait_catalog;
pub(crate) mod trait_expand;
pub(crate) mod trait_instantiation;
pub(crate) mod trait_registry;
pub(crate) mod translator;
pub(crate) mod trigger_inference;
pub(crate) mod try_desugar;
pub(crate) mod type_syntax;
pub mod vc;
pub(crate) mod vc_extraction;
pub mod verification_bridge;
pub mod verification_report;
pub mod verify;
#[doc(hidden)]
pub mod verify_macro;
mod verify_result;
// Scaffolding modules for v2/v3 features — not yet wired into the
// verification pipeline.  Suppress dead-code warnings at the module level
// so the scaffolding is preserved without noise.
#[allow(dead_code)]
pub(crate) mod assumption_tracker;
#[allow(dead_code)]
pub(crate) mod invariant_inference;
#[cfg(test)]
mod monitoring_e2e_tests;
#[allow(dead_code)]
pub(crate) mod proof_automation;
#[allow(dead_code)]
pub(crate) mod proof_cache;
#[allow(dead_code)]
pub(crate) mod quantifier_heuristics;
#[allow(dead_code)]
pub(crate) mod solver_strategy;
#[allow(dead_code)]
pub(crate) mod theory_lemma_gen;
#[allow(dead_code)]
pub(crate) mod vc_analyzer;

pub use encoder::BatchVerifyResult;
pub use encoder::UnknownCategory;
pub use harness::{HarnessAssertion, HarnessOutcome};
#[cfg(feature = "proof-certificates")]
pub use verification_report::ProofCertificate;
pub use verification_report::{
    DemandInlineRecovery, PipelineSummary, SolverStatValue, SolverStats, StepDiagnostic,
    StepResultKind, UnknownDiagnostic, VerificationPhase, VerificationReport,
    VerificationReportOptions,
};
pub use verify_result::{CounterexampleBinding, VerifyResult};

#[doc(hidden)]
pub use error::{TrustVcError, TrustVcResult};
#[doc(hidden)]
pub use ir_lowering::LoweringError;
#[doc(hidden)]
pub use solver_mode_assert_parser::{parse_solver_mode_assert, SolverModeAssertInput};

#[doc(hidden)]
pub use attributes::{
    __assume, expand_ext_eq, expand_ext_ne, expand_external_body, expand_memoize,
    expand_opens_invariants, expand_returns, expand_strict_eq,
};
#[doc(hidden)]
pub use broadcast::{
    expand_all_triggers, expand_auto_trigger, expand_broadcast, expand_broadcast_with_group,
    expand_trigger_with_group,
};
#[doc(hidden)]
pub use broadcast_state::{
    register_broadcast_lemma_with_group, register_broadcast_use, set_trigger_inference_mode,
};
#[doc(hidden)]
pub use decreases::{expand_decreases, expand_decreases_with_clauses, expand_via_fn};
#[doc(hidden)]
pub use extern_spec::{expand_extern_spec, ExternSpecInput};
#[doc(hidden)]
pub use extern_spec_verify::{
    clear_extern_contracts, register_extern_spec_from_call_site,
    register_extern_spec_from_manifest_scope, register_extern_spec_from_manifest_scope_for_call,
    register_extern_spec_from_source,
};
#[doc(hidden)]
pub use spec_expand::expand_spec;
#[doc(hidden)]
pub use support_root::macro_support_root;
#[doc(hidden)]
pub use tracked_syntax::{
    parse_file_allow_tracked, parse_item_fn_allow_tracked, parse_item_fn_with_tracked_info,
    TrackedParseResult,
};
#[doc(hidden)]
pub use trait_expand::{expand_trait_impl, expand_trait_spec};
#[doc(hidden)]
pub use trait_registry::{register_traits_from_manifest_scope, register_traits_from_source};
#[doc(hidden)]
pub use translator::RustToSmtTranslator;
#[doc(hidden)]
pub use trigger_inference::TriggerInferenceMode;
#[doc(hidden)]
pub use vc_extraction::{
    extract_verification_conditions, extract_verification_conditions_with_file_context,
    verify_function_from_file,
};

/// Trait-impl conformance as first-class, addressable cases.
///
/// A conformance failure is an obligation of the IMPL, not of whatever function
/// happened to be verified in the same file. `verify_function_from_file` reports
/// a function's own obligations; these two entry points report the file's impls.
/// Both are needed to certify a file — `cargo trust-vc check` enumerates
/// conformance obligations as their own check targets, so a non-conforming impl
/// is reported even when nothing in the file calls it.
pub use vc_extraction::{list_trait_conformance_obligations, verify_trait_conformance_obligation};

// Cross-crate entrypoints for the trust_vc proc-macro crate.
// These allow the support modules above to be pub(crate) while the
// proc-macro crate accesses only crate-root hidden re-exports.
#[doc(hidden)]
pub use assert_by_parser::{parse_assert_by, AssertByParsed};
#[doc(hidden)]
pub use assert_forall_by_parser::{
    parse_assert_forall_by, AssertForallByBoundVar, AssertForallByParsed,
};
#[doc(hidden)]
pub use assert_seqs_equal_parser::{parse_assert_seqs_equal, AssertSeqsEqualInput};
#[doc(hidden)]
pub use calc_parser::{parse_calc, transitive_op, CalcBlock, CalcOp};
#[doc(hidden)]
pub use chained_comparisons::{parse_expr_str_with_chains, parse_expr_tokens_with_chains};
#[doc(hidden)]
pub use context_management::enter_invariant_mask_scope;
#[doc(hidden)]
pub use expr_codegen::{closure_to_quantifier_tokens, expr_to_try_builder_tokens};
#[doc(hidden)]
pub use inventory;
#[doc(hidden)]
pub use named_groups::{
    push_reveal_or_group, register_broadcast_use_or_group, BroadcastFnGroupDef, NamedRevealGroupDef,
};
#[doc(hidden)]
pub use obligation_collection::collect_let_binding_runtime_value_from_ref;
#[doc(hidden)]
pub use obligation_collection::collect_variable_runtime;
#[doc(hidden)]
pub use obligation_collection::{
    collect_symbolic_assume_expr, collect_symbolic_let_binding_expr,
    register_counterexample_display, register_prophecy_local,
};
#[doc(hidden)]
pub use protocol_expand::{expand_action, expand_liveness, expand_protocol, expand_safety};
#[doc(hidden)]
pub use verify_macro::push_hide;

// Quantifier-bound variable type registration for proc macro codegen.
// Re-exported here to avoid modifying verify_macro.rs (cross-worker ownership).
#[doc(hidden)]
pub use obligation_collection::{
    register_quantifier_bound_var, unregister_quantifier_bound_var, QuantifierBoundVarGuard,
};

use proc_macro2::TokenStream;
#[doc(hidden)]
pub use proof_expand::register_invariant_predicate_helper;
#[doc(hidden)]
pub use proof_expand::{expand_proof, expand_proof_with_tracked, expand_spec_mode};
use syn::visit::Visit;

/// Escape a string for safe inclusion in JSON output.
///
/// Handles `"`, `\`, control characters (`\n`, `\r`, `\t`), and any other
/// control character via `\uXXXX` notation.
pub fn json_escape(text: &str) -> String {
    use std::fmt::Write;
    let mut escaped = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            c if c.is_control() => {
                let _ = write!(escaped, "\\u{:04x}", c as u32);
            }
            c => escaped.push(c),
        }
    }
    escaped
}

/// Abort an intentional TrustVc runtime boundary.
///
/// Macro-expanded proof, extern-spec, and ghost projection helpers cannot
/// change the caller's return type to `Result` without changing the public API.
/// Those paths build a concrete diagnostic and route failures through this
/// single boundary.
#[doc(hidden)]
pub fn __trust_vc_runtime_boundary(message: impl Into<String>) -> ! {
    std::panic::panic_any(message.into())
}

#[doc(hidden)]
pub fn __trust_vc_result_ok_0<T, E>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(_) => __trust_vc_runtime_boundary("TrustVc Result Ok_0 projection evaluated on Err"),
    }
}

#[doc(hidden)]
pub fn __trust_vc_result_err_0<T, E>(result: Result<T, E>) -> E {
    match result {
        Ok(_) => __trust_vc_runtime_boundary("TrustVc Result Err_0 projection evaluated on Ok"),
        Err(error) => error,
    }
}

/// Returns `true` if `block` contains a direct call to `fn_name`.
/// Used by spec expansion to detect self-recursive spec functions (#2220).
pub(crate) fn block_contains_self_call(fn_name: &str, block: &syn::Block) -> bool {
    let mut collector = mode_paths::PathCallCollector::default();
    collector.visit_block(block);
    collector.calls.iter().any(|c| c.fn_name() == fn_name)
}

pub(crate) fn validate_function_calls_for_mode(
    caller_mode: mode::FunctionMode,
    block: &syn::Block,
    scan: Option<&mode_scan::ModeScan>,
    crate_index: Option<&mode_index::CrateModeIndex>,
    caller_module: &[String],
) -> Vec<TokenStream> {
    let mut collector = mode_paths::PathCallCollector::default();
    collector.visit_block(block);

    collector
        .calls
        .into_iter()
        .filter_map(|call| {
            // Skip paths with leading `::` — these are absolute/external paths
            // (e.g., ::trust_vc_core::verify_macro::*). (#2081 category 2)
            if call.leading_colon {
                return None;
            }

            // Skip known-safe stdlib variant constructors.
            // (#2081 category 1)
            const SAFE_CONSTRUCTORS: &[&str] = &["Some", "Ok", "Err"];
            if call.is_simple() && SAFE_CONSTRUCTORS.contains(&call.fn_name()) {
                return None;
            }

            // Resolution priority:
            // 1. Crate index (handles qualified paths: self::, super::, crate::, multi-segment)
            // 2. Same-module scan (unqualified single-segment)
            // 3. Compile-time registry
            // 4. Unknown → skip (compatible per #2081: trait-bound methods,
            //    stdlib constructors, and injected infrastructure aren't in
            //    any mode registry)
            let callee_mode = if let Some(index) = crate_index {
                mode_paths::resolve_callee_mode(&call, caller_module, index)
            } else {
                None
            }
            .or_else(|| {
                if call.is_simple() {
                    scan.and_then(|s| s.sibling_modes.get(call.fn_name()).copied())
                } else {
                    None
                }
            })
            .or_else(|| mode::lookup_compile_time_function_mode(call.fn_name()));

            let callee_mode = match callee_mode {
                Some(m) => m,
                None => return None,
            };

            if caller_mode.can_call(callee_mode) {
                None
            } else {
                Some(
                    syn::Error::new(
                        call.span,
                        format!(
                            "{} function cannot call {} function `{}`",
                            caller_mode,
                            callee_mode,
                            call.fn_name()
                        ),
                    )
                    .to_compile_error(),
                )
            }
        })
        .collect()
}

#[cfg(test)]
#[path = "lib_tests/mod.rs"]
mod tests;
