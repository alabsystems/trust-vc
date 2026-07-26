//! AY encoder - converts verification conditions to SMT queries.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module bridges trust_vc's abstract verification conditions with ay's
//! SMT solver, enabling actual verification of proof obligations.
//!
//! # Architecture
//!
//! ```text
//! VerificationContext (obligations, variables)
//!           |
//!           v
//!     AYEncoder::verify()
//!           |
//!           v
//!     ay_dpll::api::Solver
//!           |
//!           v
//!     VerifyResult (Verified/Counterexample/Unknown/Error)
//! ```
//!
//! # Usage
//!
//! Normal callers that already have a `VerificationContext` should use
//! `VerificationContext::verify()`. Production code that collects proof state
//! from proc macros should use `VerificationPipeline::verify()`. Direct
//! `AYEncoder::verify()` calls are the low-level encoder boundary underneath
//! those APIs and remain useful for encoder-focused tests.
//!
//! See `crates/trust_vc/tests/` for end-to-end usage patterns. The primary
//! verification path uses typed `TrustVcExpr` IR; the string API
//! (`declare_var`/`add_assert`) remains available for backward compatibility.

#[macro_use]
mod flag_macro;
pub(crate) use flag_macro::with_flag_unwind_safe;

mod arith_semantics;
mod array_axioms;
mod binding_scope;
mod collection_axioms;
mod collection_map;
mod collection_seq;
#[cfg(feature = "native-seq")]
mod collection_seq_native;
mod collection_set;
mod collection_set_higher;
mod collection_shared;
mod collection_state;
pub(crate) mod datatype;
pub(crate) mod diagnostics;
mod encoder_state;
pub(crate) mod eval;
pub(crate) mod fuel;
pub(crate) mod ground_pool;
mod ir_encoder; // Re-enabled: #1865 Phase 4 — all 26 CollectionOp variants now encoded.
mod operators;
mod parser_state;
pub(crate) mod polymorphism;
mod quantifier_scope;
mod quantifiers;
pub(crate) mod trait_encoding;
pub(crate) mod types;
mod unicode;
pub(crate) mod unit;
mod verification;
mod width_coercion;

pub(crate) use ir_encoder::normalize::normalize_int_expr;
#[cfg(feature = "native-seq")]
use parser_state::native_seq_shadow_var_name;
pub(crate) use parser_state::AstExpressionParser;
pub use types::VerifyResult;
pub(crate) use verification::outcome::AssertionOutcome;
pub use verification::unknown_category::UnknownCategory;

pub use encoder_state::BatchVerifyResult;
use encoder_state::FeatureRegistries;
pub(crate) use encoder_state::{EncoderFunctionContext, VerificationState, BROADCAST_INSTANCE_CAP};

use crate::counterexample_names::CounterexampleVarMeta;
use crate::encoder::types::sort_for_type;
use crate::error::{TrustVcError, TrustVcResult};
use crate::prepared_context::{prepare_context, PreparedVerificationContext};
use crate::vc::{VariableDecl, VerificationContext};
use ay_dpll::api::{ArraySort, Logic, Solver, Sort, Term};
// FuncDecl re-imported for test modules that rely on `use super::*`.
#[cfg(test)]
use ay_dpll::api::FuncDecl;

const VERIFY_STACK_RED_ZONE: usize = 8 * 1024 * 1024;
const VERIFY_STACK_SIZE: usize = 128 * 1024 * 1024;
use ay_dpll::CounterexampleStyle;

/// Encodes verification conditions to ay SMT queries.
#[must_use = "encoder builders should be configured and then used for verification"]
pub struct AYEncoder {
    /// The ay solver instance.
    solver: Solver,
    /// Mapping from variable names to ay terms.
    variables: std::collections::HashMap<String, Term>,
    /// Mapping from variable names to their types for selecting correct operations.
    var_types: std::collections::HashMap<String, crate::ir::TrustVcType>,
    /// Mapping from collection variable names to their length/cardinality terms.
    /// For Seq/Set/Map types, we track length separately from the array content.
    collection_lengths: std::collections::HashMap<String, Term>,
    /// Function declarations and type metadata. Part of #2447 Slice 1.
    pub(crate) fn_ctx: EncoderFunctionContext,
    /// Mutable verification state and caches. Part of #2447 Slice 3.
    pub(crate) state: VerificationState,
    /// Feature-specific encoding registries. Part of #2447 Slice 2.
    registries: FeatureRegistries,
    /// Counterexample display metadata keyed by raw solver variable name.
    /// Used by model_render to show user-facing names. Part of #2651.
    pub(in crate::encoder) counterexample_var_meta:
        std::collections::HashMap<String, CounterexampleVarMeta>,
}

/// Process-wide Seq::flat_map quantifier mode.
///
/// Environment configuration is snapshotted once so cache fingerprinting and
/// the subsequent solve cannot observe different modes.
pub(in crate::encoder) fn seq_flat_map_quantifiers_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TRUST_VC_SEQ_FLAT_MAP_QUANTIFIERS").is_some())
}

/// Process-wide optional per-encoder term-memory limit in MiB.
///
/// Invalid values retain the established no-limit behavior. As with the
/// flat_map switch, snapshotting keeps the cache key and solver configuration
/// on one immutable ambient profile.
pub(in crate::encoder) fn configured_term_memory_mb() -> Option<usize> {
    static TERM_MEMORY_MB: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    *TERM_MEMORY_MB.get_or_init(|| {
        std::env::var("TRUST_VC_TERM_MEMORY_MB")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
    })
}

impl AYEncoder {
    /// Returns the solver's interrupt handle for cross-thread cancellation.
    ///
    /// The caller stores `true` into the returned `Arc<AtomicBool>` to signal
    /// the solver to stop. On the next `check_sat()`, ay-dpll reads the flag
    /// and returns `Unknown(Interrupted)`. Phase 4 of #2242; mitigates #1703.
    pub(crate) fn interrupt_handle(&self) -> std::sync::Arc<std::sync::atomic::AtomicBool> {
        self.solver.interrupt_handle()
    }

    /// Does the solver's CURRENT assertion set contain a quantified formula?
    ///
    /// Mirrors the scan ay itself performs at check-sat entry to decide whether
    /// the solve enters the quantified pipeline (whose termination is governed
    /// by deterministic instantiation budgets with a far-out wall-clock
    /// backstop, ay 62695cfe04). Used by the assertion watchdog to pick the
    /// matching far-out hang-protection budget instead of the tight ground-BV
    /// cap — see `verification::timeout::far_out_watchdog_timeout`.
    ///
    /// Memoized DAG walk over the public introspection API: each distinct term
    /// node is visited at most once, so the cost is linear in the assertion
    /// DAG size (the same order as ay's own per-check-sat scan). Quantifiers
    /// asserted only AFTER this is called (e.g. axioms lazily emitted while
    /// encoding the goal inside the watchdog closure) are covered separately
    /// by the goal-expression checks at the call site.
    pub(in crate::encoder) fn has_quantified_assertions(&self) -> bool {
        use ay_dpll::api::TermKind;
        let mut visited: std::collections::HashSet<Term> = std::collections::HashSet::new();
        let mut stack: Vec<Term> = self.solver.assertions();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            if matches!(
                self.solver.term_kind(term),
                TermKind::Forall | TermKind::Exists
            ) {
                return true;
            }
            stack.extend(self.solver.term_children(term));
        }
        false
    }

    /// Creates a new encoder with auto-detected logic.
    ///
    /// Uses `Logic::All` so ay auto-detects the actual theories needed
    /// (BV, arrays, UF, etc.) from the formula at check-sat time.
    pub fn new() -> Self {
        Self::with_logic(Logic::All)
    }

    /// Creates a new encoder with a specific SMT logic.
    pub fn with_logic(logic: Logic) -> Self {
        // Constructor is infallible for supported ay logics; making this fallible needs an API migration.
        let mut solver =
            Solver::try_new(logic).expect("invariant: supported logic should construct a solver"); // quality-audit: allow-expect
        solver.set_counterexample_style(CounterexampleStyle::Readable);
        #[cfg(feature = "proof-certificates")]
        solver.set_produce_proofs(true);
        // TrustVc gives proof assumptions internal names even without
        // user-facing core reporting; current ay requires core mode for that path
        // to avoid false UNSAT in array-heavy assumption frames.
        solver.set_produce_unsat_cores(true);
        Self {
            solver,
            variables: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            fn_ctx: EncoderFunctionContext::new(),
            state: VerificationState::new(),
            registries: FeatureRegistries::new(),
            counterexample_var_meta: std::collections::HashMap::new(),
        }
    }

    /// Sets the E-matching round limit for adaptive escalation (#2720).
    ///
    /// Overrides the ay-dpll default of 8 rounds. Lower values speed up
    /// easy proofs; higher values allow deeper quantifier instantiation
    /// chains. Clamped to [1, 64] by ay-dpll.
    pub fn set_ematching_round_limit(&mut self, n: usize) {
        self.solver.set_ematching_round_limit(n);
    }

    pub fn with_limits(mut self, timeout_ms: u64, memory_mb: usize) -> Self {
        self.solver
            .set_timeout(Some(std::time::Duration::from_millis(timeout_ms)));
        self.solver
            .set_memory_limit(process_memory_limit_bytes(memory_mb));
        // Per-instance term_memory_limit is opt-in via TRUST_VC_TERM_MEMORY_MB
        // env var to avoid false solver interrupts on NIA-heavy queries.
        if let Some(term_mb) = configured_term_memory_mb() {
            self.solver
                .set_term_memory_limit(Some(term_mb * 1024 * 1024));
        }
        self
    }

    /// Verifies all obligations in a verification context.
    ///
    /// Prefer `VerificationContext::verify()` for normal callers that already
    /// have a context. This method is the lower-level encoder entry point used
    /// by that canonical boundary and by encoder-focused tests.
    ///
    /// The verification pipeline is:
    /// 1. `prepare_context` parses + lowers every obligation condition to typed IR
    ///    (`TrustVcExpr`) with fail-closed errors.
    /// 2. `verify_prepared` runs verification using those prepared expressions.
    ///
    /// Under `#[cfg(test)]`, acquires the test verification gate to serialize
    /// solver-backed unit tests, preventing ay-dpll non-determinism (#2273).
    pub fn verify(ctx: &VerificationContext) -> VerifyResult {
        // Prepare context outside the gate (pure lowering, no solver). Part of #2646.
        let prepared = match prepare_context(ctx) {
            Ok(prepared) => prepared,
            Err(err) => return VerifyResult::from(err),
        };
        // Cache lookup before acquiring the solver gate. Part of #2646.
        if let Some(cached) = verification::cache::lookup_cache(&prepared) {
            return cached;
        }
        verification::cache::bump_cache_miss_count();
        let result = verification::test_gate::with_verify_test_gate(|| {
            Self::verify_prepared_inner(&prepared)
        });
        verification::cache::store_cache(&prepared, &result);
        result
    }

    /// Verifies a context that has already been prepared into typed conditions.
    ///
    /// Routes through the typed verification path which operates directly on
    /// `PreparedVerificationContext`. Obligations carry their `TrustVcExpr`
    /// directly — no thread-local lookup or legacy round-trip needed.
    /// Part of #2219.
    ///
    /// Under `#[cfg(test)]`, acquires the test verification gate (#2273).
    #[cfg(test)]
    pub(crate) fn verify_prepared(ctx: &PreparedVerificationContext) -> VerifyResult {
        // Cache lookup before acquiring the solver gate. Part of #2646.
        if let Some(cached) = verification::cache::lookup_cache(ctx) {
            return cached;
        }
        verification::cache::bump_cache_miss_count();
        let result =
            verification::test_gate::with_verify_test_gate(|| Self::verify_prepared_inner(ctx));
        verification::cache::store_cache(ctx, &result);
        result
    }

    /// Inner verification path, called from within the test gate.
    /// Avoids nested gate acquisition when `verify()` delegates to `verify_prepared()`.
    ///
    /// `pub(crate)` visibility enables `verify_batch_parallel` to call this
    /// from spawned threads without going through the test gate. Part of #2647.
    pub(crate) fn verify_prepared_inner(ctx: &PreparedVerificationContext) -> VerifyResult {
        stacker::maybe_grow(VERIFY_STACK_RED_ZONE, VERIFY_STACK_SIZE, || {
            Self::verify_prepared_inner_on_grown_stack(ctx)
        })
    }

    /// A function's verdict is its OWN obligations — trait-impl conformance is
    /// NOT folded in.
    ///
    /// Conformance is an obligation of the IMPL, not of whatever function
    /// happened to be verified in the same file (ATTRIBUTION, not scoping — see
    /// the internal conformance-attribution design note). Every impl is
    /// still checked, always: each conformance obligation is a first-class,
    /// addressable case
    /// ([`crate::list_trait_conformance_obligations`] /
    /// [`crate::verify_trait_conformance_obligation`]), enumerated as its own
    /// check target by `cargo trust-vc check`. So a non-conforming impl is still
    /// reported even when nothing in the file calls it — only the BLAME moved.
    ///
    /// Folding it here made upstream trait files structurally unportable: Verus
    /// compiles each `test_verify_one_file!` case as its own file, so one
    /// deliberately-violating impl could never touch a sibling. Upstream
    /// `returns_postcondition.rs::trait_returns_on_trait_method_decl` pins
    /// exactly this — the GENERIC caller `test_call<T: Tr>` VERIFIES while impls
    /// Y/Z/W of that same trait FAIL (`assert_fails(err, 5)`).
    fn verify_prepared_inner_on_grown_stack(ctx: &PreparedVerificationContext) -> VerifyResult {
        Self::verify_typed(ctx)
    }

    /// Every trait-impl conformance obligation in the prepared context, named
    /// exactly as the verification path names them.
    pub(crate) fn list_conformance_obligations(
        ctx: &PreparedVerificationContext,
    ) -> TrustVcResult<Vec<String>> {
        verification::trait_conformance::list_trait_conformance_obligations(ctx)
    }

    /// Verifies exactly one conformance obligation, addressed by name. An
    /// unknown name fails closed (`Error`), never `Verified`.
    ///
    /// Acquires the test verification gate (#2273) exactly as [`Self::verify`]
    /// does: this is a top-level entry point, never reached from inside an
    /// already-gated verification.
    pub(crate) fn verify_conformance_obligation(
        ctx: &PreparedVerificationContext,
        obligation_name: &str,
    ) -> VerifyResult {
        verification::test_gate::with_verify_test_gate(|| {
            verification::trait_conformance::verify_trait_conformance_obligation(
                ctx,
                obligation_name,
            )
        })
    }

    /// Verifies multiple prepared contexts in parallel using one thread per context.
    ///
    /// Each context gets an independent solver on a separate thread. Results are
    /// returned in the same order as the input contexts. Panicking threads produce
    /// `VerifyResult::Error`.
    ///
    /// For batches of 1 or fewer, falls back to sequential execution to avoid
    /// thread-spawn overhead.
    ///
    /// The test gate is intentionally **not** acquired: each `PreparedVerificationContext`
    /// is self-contained (no thread-local reads during `verify_prepared_inner`), so
    /// parallel execution is safe even in test builds. Part of #2647.
    pub fn verify_batch_parallel(
        contexts: Vec<PreparedVerificationContext>,
    ) -> Vec<BatchVerifyResult> {
        use std::thread;
        use std::time::Instant;

        /// Verify a single prepared context with cache support. Does NOT
        /// acquire the test gate — callers in the parallel batch path must
        /// not reintroduce serialization. Part of #2646.
        fn verify_cached(ctx: &PreparedVerificationContext) -> VerifyResult {
            if let Some(cached) = verification::cache::lookup_cache(ctx) {
                return cached;
            }
            verification::cache::bump_cache_miss_count();
            let result = AYEncoder::verify_prepared_inner(ctx);
            verification::cache::store_cache(ctx, &result);
            result
        }

        if contexts.len() <= 1 {
            return contexts
                .into_iter()
                .enumerate()
                .map(|(index, ctx)| {
                    let start = Instant::now();
                    let result = verify_cached(&ctx);
                    BatchVerifyResult::new(index, result, start.elapsed())
                })
                .collect();
        }

        let max_threads = verification::timeout::max_solver_threads();

        let total = contexts.len();
        let mut results = Vec::with_capacity(total);
        let mut remaining: Vec<_> = contexts.into_iter().enumerate().collect();
        while !remaining.is_empty() {
            let chunk_size = remaining.len().min(max_threads);
            let chunk: Vec<_> = remaining.drain(..chunk_size).collect();
            let chunk_indices: Vec<usize> = chunk.iter().map(|(index, _)| *index).collect();
            let handles: Vec<_> = chunk
                .into_iter()
                .map(|(index, ctx)| {
                    thread::spawn(move || {
                        let start = Instant::now();
                        let result = verify_cached(&ctx);
                        BatchVerifyResult::new(index, result, start.elapsed())
                    })
                })
                .collect();
            for (handle, expected_index) in handles.into_iter().zip(chunk_indices) {
                results.push(handle.join().unwrap_or_else(|_| {
                    BatchVerifyResult::new(
                        expected_index,
                        VerifyResult::Error {
                            message: "Verification thread panicked".to_string(),
                        },
                        std::time::Duration::ZERO,
                    )
                }));
            }
        }
        results
    }

    /// Declares a variable in the solver.
    /// Returns error if variable name is already declared (fixes #58).
    /// For collection-bearing types (Seq, Set, Map, String, str), also creates
    /// a length term with length >= 0 constraint.
    /// Part of #1690: returns `TrustVcResult` instead of `Result<(), String>`.
    fn declare_variable(&mut self, var: &VariableDecl) -> TrustVcResult<()> {
        if self.variables.contains_key(&var.name) {
            return Err(TrustVcError::Encoding {
                context: "declare variable",
                detail: format!("Variable '{}' already declared", var.name),
            });
        }
        // Reject variables with opaque types (defense-in-depth for #1926).
        // The typed.rs guard catches these before setup_from_prepared calls
        // declare_variable, but this prevents unsound Sort::Int encoding if
        // any code path bypasses the guard.
        if var.ty.contains_opaque() {
            return Err(TrustVcError::Encoding {
                context: "declare variable",
                detail: format!(
                    "Variable '{}' has unrecognized type '{}' that cannot be soundly encoded",
                    var.name,
                    var.ty.to_type_string()
                ),
            });
        }
        let sort = sort_for_type(&var.ty);
        let term = self.solver.declare_const(&var.name, sort);
        self.variables.insert(var.name.clone(), term);
        self.var_types.insert(var.name.clone(), var.ty.clone());
        self.state
            .lowering_env
            .insert(var.name.clone(), var.ty.clone());
        self.state.cached_int_width.set(None); // Invalidate — new type entry. #1786.

        if matches!(var.ty, crate::ir::TrustVcType::Char) {
            self.assert_valid_char_term(term)?;
        }

        if matches!(var.ty, crate::ir::TrustVcType::Unit) {
            unit::assert_unit_term(&mut self.solver, term, "declare variable", &var.name)?;
        }

        // For Nat-typed variables, assert non-negativity: x >= 0.
        // Nat maps to Sort::Int (same as MathInt) but with the invariant
        // that the value is non-negative. Part of #2418.
        if matches!(var.ty, crate::ir::TrustVcType::Nat) {
            let zero = self.solver.int_const(0);
            let nonneg = self
                .solver
                .try_ge(term, zero)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!(
                        "Failed to create nat non-negativity guard for '{}': {}",
                        var.name, e
                    ),
                })?;
            self.solver
                .try_assert_term(nonneg)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!(
                        "Failed to assert nat non-negativity for '{}': {}",
                        var.name, e
                    ),
                })?;
        }

        if let crate::ir::TrustVcType::Multiset(ref elem_ty) = var.ty {
            self.assert_multiset_counts_nonnegative(&var.name, term, elem_ty)?;
        }

        // For collection types, create an associated length term with unsigned semantics.
        // Uses pointer_width() to match Seq index sort and Rust's usize. Fixes #1745.
        //
        // Under native-seq (#2680 Slice 2), Seq variables use Int-sorted
        // seq.len(s) instead of a BV __len companion. This avoids bv2int/int2bv
        // cross-theory terms that ay-dpll's model validator cannot evaluate.
        // Under native-seq, both Seq and String/StrSlice use seq.len aliases
        // instead of BV __len companions (#2680 Slice 2 + Slice 3).
        #[cfg(all(feature = "native-seq", feature = "native-strings"))]
        let needs_bv_len = var.ty.has_collection_length()
            && !matches!(
                var.ty,
                crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _)
            )
            && !var.ty.is_string_like();
        #[cfg(all(feature = "native-seq", not(feature = "native-strings")))]
        let needs_bv_len = var.ty.has_collection_length()
            && !matches!(
                var.ty,
                crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _)
            )
            && !var.ty.is_string_like();
        #[cfg(all(not(feature = "native-seq"), feature = "native-strings"))]
        let needs_bv_len = var.ty.has_collection_length() && !var.ty.is_string_like();
        #[cfg(all(not(feature = "native-seq"), not(feature = "native-strings")))]
        let needs_bv_len = var.ty.has_collection_length();

        if needs_bv_len {
            // Route A (#2779 length layer): model spec-collection LENGTH as an
            // unbounded non-negative Int instead of a fixed-width BitVec. This
            // removes the spurious "concat/push length no overflow" obligations
            // (Int addition is monotone and cannot wrap), so symbolic
            // length/concat properties verify instead of returning Unknown,
            // while near-MAX wrap goals stay correctly fail-closed (MAX+1 != 0
            // over the integers — there is no representable MAX to contradict).
            // Mirrors the native-strings (mod.rs:504+) and native-seq (mod.rs:567+)
            // Int-length patterns; `register_collection_meta`
            // (collection_state.rs:58) already tolerates Int-sorted lengths.
            // Indices into the Array(BV,T) carrier stay BV — length is bridged
            // to BV via `len_as_index_bv` where it meets array select/store.
            // F3 point-interval pin: a Seq whose length is ENTAILED to a
            // concrete literal by this query's own assumption set
            // (`setup.rs::collect_finite_len_pins` — `s == <finite chain>` /
            // `s.len() == N` top-level assumptions) registers the Int LITERAL
            // as its length. No symbolic `__trust_vc_len_*` var is minted and
            // no `>= 0` anchor is asserted: the literal subsumes both, every
            // downstream length consumer constant-folds to ground BV
            // (probe_M2 shape), and no residual ground Int inequality atom is
            // left to trip ay's quantifier lane (F6-class `<= 0 len` poison —
            // docs/probes/2026-07-18-ay-lane/dump-smt2/RESULTS.txt).
            // Unpinned variables keep the incumbent symbolic model verbatim.
            let pinned = matches!(var.ty, crate::ir::TrustVcType::Seq(_))
                .then(|| self.state.pinned_seq_lens.get(&var.name).copied())
                .flatten();
            let len_term = if let Some(value) = pinned {
                self.solver.int_const(value)
            } else {
                let len_name = format!("__trust_vc_len_{}", var.name);
                let len_term = self.solver.declare_const(&len_name, Sort::Int);

                // Assert length >= 0 (Int non-negativity — unbounded nat
                // semantics).
                let zero = self.solver.int_const(0);
                let len_nonneg =
                    self.solver
                        .try_ge(len_term, zero)
                        .map_err(|e| TrustVcError::Encoding {
                            context: "declare variable",
                            detail: format!(
                                "Failed to create length >= 0 constraint for '{}': {}",
                                var.name, e
                            ),
                        })?;
                self.solver
                    .try_assert_term(len_nonneg)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to assert length constraint for '{}': {}",
                            var.name, e
                        ),
                    })?;
                // Vec/slice/array length boundedness: an exec collection has a
                // `usize`-bounded length, so assert `len <= 2^pw-1`. Gated
                // strictly on the per-variable `bounded_len` bit — NEVER emitted
                // for a spec `Seq<T>` (unbounded Int length). See
                // `assert_len_usize_bounded`.
                if var.bounded_len {
                    self.assert_len_usize_bounded(&var.name, len_term)?;
                }
                len_term
            };

            self.collection_lengths.insert(var.name.clone(), len_term);

            if let crate::ir::TrustVcType::Array(_, array_len) = &var.ty {
                self.assert_fixed_array_int_length(&var.name, len_term, *array_len)?;
            }

            if matches!(
                &var.ty,
                crate::ir::TrustVcType::String | crate::ir::TrustVcType::StrSlice
            ) || matches!(
                &var.ty,
                crate::ir::TrustVcType::Seq(elem) if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
            ) {
                self.assert_valid_char_sequence(term, len_term)?;
            }
        }

        #[cfg(feature = "native-strings")]
        if var.ty.is_string_like() {
            let str_len_raw =
                self.solver
                    .try_str_len(term)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to compute str.len for native string '{}': {}",
                            var.name, e
                        ),
                    })?;
            let int_len = self.solver.declare_const(
                &format!("__native_string_len_{}", var.name),
                ay_dpll::api::Sort::Int,
            );
            let len_bridge =
                self.solver
                    .try_eq(int_len, str_len_raw)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to create str.len alias bridge for '{}': {}",
                            var.name, e
                        ),
                    })?;
            self.solver
                .try_assert_term(len_bridge)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!(
                        "Failed to assert str.len alias bridge for '{}': {}",
                        var.name, e
                    ),
                })?;
            let zero = self.solver.int_const(0);
            let len_nonneg =
                self.solver
                    .try_ge(int_len, zero)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to create string length >= 0 for '{}': {}",
                            var.name, e
                        ),
                    })?;
            self.solver
                .try_assert_term(len_nonneg)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!(
                        "Failed to assert string length >= 0 for '{}': {}",
                        var.name, e
                    ),
                })?;
            self.collection_lengths.insert(var.name.clone(), int_len);
        }

        // Under native-seq, Seq variables get an Int-sorted length via an alias
        // variable bridged to seq.len(s). The alias (a plain Int variable) is
        // used everywhere instead of the raw seq.len application so that
        // ay-dpll's model validator can evaluate length terms — the Seq theory
        // unconditionally sets skip_model_eval = true (ay seq.rs:303), so raw
        // seq.len terms cannot be evaluated in models. Part of #2680 Slice 2.
        #[cfg(all(feature = "native-seq", feature = "native-strings"))]
        let needs_native_seq_shadow = matches!(
            var.ty,
            crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _)
        );
        #[cfg(all(feature = "native-seq", not(feature = "native-strings")))]
        let needs_native_seq_shadow = matches!(
            var.ty,
            crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _)
        ) || var.ty.is_string_like();

        #[cfg(feature = "native-seq")]
        if needs_native_seq_shadow {
            let seq_len_raw =
                self.solver
                    .try_seq_len(term)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to compute seq.len for native-seq '{}': {}",
                            var.name, e
                        ),
                    })?;
            // Alias: int_len is a plain Int variable that the model validator
            // can evaluate, bridged to seq.len(s) via equality.
            let int_len = self.solver.declare_const(
                &format!("__native_seq_len_{}", var.name),
                ay_dpll::api::Sort::Int,
            );
            let len_bridge =
                self.solver
                    .try_eq(int_len, seq_len_raw)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to create seq.len alias bridge for '{}': {}",
                            var.name, e
                        ),
                    })?;
            self.solver
                .try_assert_term(len_bridge)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!(
                        "Failed to assert seq.len alias bridge for '{}': {}",
                        var.name, e
                    ),
                })?;
            // Assert int_len >= 0 (ay-seq axioms guarantee this, but be explicit).
            let zero = self.solver.int_const(0);
            let len_nonneg =
                self.solver
                    .try_ge(int_len, zero)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to create seq length >= 0 for '{}': {}",
                            var.name, e
                        ),
                    })?;
            self.solver
                .try_assert_term(len_nonneg)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!("Failed to assert seq length >= 0 for '{}': {}", var.name, e),
                })?;
            // Vec/slice/array length boundedness (native-seq model): mirror the
            // default-model bound. Gated strictly on `bounded_len` — never for a
            // spec `Seq<T>`. See `assert_len_usize_bounded`.
            if var.bounded_len {
                self.assert_len_usize_bounded(&var.name, int_len)?;
            }
            self.collection_lengths.insert(var.name.clone(), int_len);

            if let crate::ir::TrustVcType::Array(_, array_len) = &var.ty {
                self.assert_fixed_array_int_length(&var.name, int_len, *array_len)?;
            }

            let shadow_name = native_seq_shadow_var_name(&var.name);
            let shadow_term = self
                .solver
                .declare_const(&shadow_name, self.solver.term_sort(term));
            let shadow_eq =
                self.solver
                    .try_eq(term, shadow_term)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to create native shadow equality for '{}': {}",
                            var.name, e
                        ),
                    })?;
            self.solver
                .try_assert_term(shadow_eq)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!(
                        "Failed to assert native shadow equality for '{}': {}",
                        var.name, e
                    ),
                })?;
            let shadow_len =
                self.solver
                    .try_seq_len(shadow_term)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to compute native shadow seq.len for '{}': {}",
                            var.name, e
                        ),
                    })?;
            let shadow_len_eq =
                self.solver
                    .try_eq(shadow_len, int_len)
                    .map_err(|e| TrustVcError::Encoding {
                        context: "declare variable",
                        detail: format!(
                            "Failed to create native shadow len bridge for '{}': {}",
                            var.name, e
                        ),
                    })?;
            self.solver
                .try_assert_term(shadow_len_eq)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!(
                        "Failed to assert native shadow len bridge for '{}': {}",
                        var.name, e
                    ),
                })?;
            self.variables.insert(shadow_name.clone(), shadow_term);
            // Register the shadow's type and length so AstExpressionParser::new()
            // pre-populates collection_meta_by_term for the shadow term.
            // Without this, native_seq_len(shadow, None) falls through to
            // a fresh seq.len(shadow) that the solver can't connect to
            // the original length assertions — a soundness gap (#2680).
            self.var_types.insert(shadow_name.clone(), var.ty.clone());
            self.collection_lengths.insert(shadow_name, int_len);

            // For char-bearing sequences (Seq<char>, String, StrSlice), assert
            // the Unicode scalar invariant using seq.nth instead of array select.
            let is_char_seq = matches!(
                &var.ty,
                crate::ir::TrustVcType::Seq(elem) if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
            ) || matches!(
                &var.ty,
                crate::ir::TrustVcType::Array(elem, _) if matches!(elem.as_ref(), crate::ir::TrustVcType::Char)
            );
            if is_char_seq {
                self.assert_valid_char_sequence_native_seq(term, int_len)?;
            }
        }

        // For Map types, create a domain membership array: Array(K, Bool).
        // Tracks which keys have been explicitly inserted. The `{name}_dom`
        // variable is looked up by ContainsKey/Dom/Remove handlers (#1966).
        if let crate::ir::TrustVcType::Map(ref key_ty, _) = var.ty {
            let dom_sort = Sort::Array(Box::new(ArraySort {
                index_sort: sort_for_type(key_ty),
                element_sort: Sort::Bool,
            }));
            let dom_name = format!("{}_dom", var.name);
            let dom_term = self.solver.declare_const(&dom_name, dom_sort);
            self.variables.insert(dom_name, dom_term);
        }

        Ok(())
    }

    /// Asserts `len_term <= 2^pointer_width - 1` (`usize::MAX`) for a variable
    /// whose origin syn type is a `usize`-bounded exec collection (`Vec`/slice/
    /// array). A real `Vec`/slice/array can never hold more than `usize::MAX`
    /// elements, so this is a TRUE fact; it discharges the NC4 carrier-index
    /// representability side condition (`idx <= 2^pw-1`) for length-derived
    /// indices (`v[len-1]`, `v.subrange(len-2, len)`, …).
    ///
    /// SOUNDNESS-CRITICAL: only ever call this when `VariableDecl::bounded_len`
    /// is set — i.e. for a genuine `Vec`/slice/array, NEVER for a spec `Seq<T>`.
    /// Asserting this for an unbounded spec `Seq` would make every
    /// huge-length (`len >= 2^64`) guard's context UNSAT and vacuously verify.
    fn assert_len_usize_bounded(&mut self, name: &str, len_term: Term) -> TrustVcResult<()> {
        let pw = crate::ir::pointer_width();
        let max = (num_bigint::BigInt::from(1u8) << pw) - 1;
        let max_term = self.solver.int_const_bigint(&max);
        let le_max =
            self.solver
                .try_le(len_term, max_term)
                .map_err(|e| TrustVcError::Encoding {
                    context: "declare variable",
                    detail: format!("Failed to create usize length bound for '{name}': {e}"),
                })?;
        self.solver
            .try_assert_term(le_max)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare variable",
                detail: format!("Failed to assert usize length bound for '{name}': {e}"),
            })
    }

    fn assert_fixed_array_int_length(
        &mut self,
        name: &str,
        len_term: Term,
        array_len: usize,
    ) -> TrustVcResult<()> {
        let expected = self
            .solver
            .int_const_bigint(&num_bigint::BigInt::from(array_len));
        let eq = self
            .solver
            .try_eq(len_term, expected)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare variable",
                detail: format!("Failed to create fixed array length equality for '{name}': {e}"),
            })?;
        self.solver
            .try_assert_term(eq)
            .map_err(|e| TrustVcError::Encoding {
                context: "declare variable",
                detail: format!("Failed to assert fixed array length for '{name}': {e}"),
            })
    }

    fn assert_multiset_counts_nonnegative(
        &mut self,
        _name: &str,
        _multiset_term: Term,
        _elem_ty: &crate::ir::TrustVcType,
    ) -> TrustVcResult<()> {
        // Multiset counts are Nat-valued at each operation site. Avoid a
        // global quantified axiom at declaration time because it interacts
        // poorly with the current solver's collection quantifier heuristics.
        Ok(())
    }
}

fn process_memory_limit_bytes(memory_mb: usize) -> Option<usize> {
    if memory_mb == 0 {
        return None;
    }
    let requested = memory_mb.saturating_mul(1024 * 1024);
    let default = ay_sys::default_memory_limit();
    let current_floor = ay_sys::current_rss_bytes().saturating_add(requested);
    let limit = requested.max(default).max(current_floor);
    (limit > 0).then_some(limit)
}

impl Default for AYEncoder {
    fn default() -> Self {
        Self::new()
    }
}

/// Sanitize a name into a valid SMT symbol by replacing non-alphanumeric
/// characters with `_`, collapsing consecutive underscores, and trimming
/// leading/trailing underscores.
///
/// Shared utility for datatype, trait-encoding, and named-assertion symbol
/// generation. Callers that need domain-specific fallbacks for empty results
/// (e.g., "Datatype" or a numeric index) should handle that after calling
/// this function.
pub(crate) fn sanitize_symbol(name: &str) -> String {
    let mut sanitized = String::with_capacity(name.len());
    let mut last_was_underscore = false;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            sanitized.push(ch);
            last_was_underscore = false;
        } else if !last_was_underscore {
            sanitized.push('_');
            last_was_underscore = true;
        }
    }
    while sanitized.ends_with('_') {
        sanitized.pop();
    }
    while sanitized.starts_with('_') {
        sanitized.remove(0);
    }
    sanitized
}

#[cfg(test)]
pub(crate) mod tests;
