//! Encoder state types and supporting data structures.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from `encoder/mod.rs` to keep the main module under 500 lines.
//! Contains the encoder's internal state layout: function context, feature
//! registries, verification state, and batch result types.

use ay_dpll::api::{FuncDecl, Term};

use super::diagnostics;
use super::ground_pool;
use super::polymorphism;
use super::types::VerifyResult;
use crate::ir_lowering::TypeEnv;

/// Maximum broadcast assumptions before falling back to quantifier-only mode.
///
/// At N=30, solver E-matching over 3-hop trigger chains emits O(N²) = 2,700
/// ground instances per new instantiation, and 4-hop emits O(N³) = 108,000.
/// Beyond this threshold, the combinatorial cost exceeds the benefit of ground
/// instantiation. Matches trust_wp's `PRODUCES_GROUND_CAP`. Fixes #2113.
pub(crate) const BROADCAST_INSTANCE_CAP: usize = 30;

#[cfg(feature = "named-assertions")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NamedAssertionKind {
    Assumption,
    NegatedTarget,
}

#[cfg(feature = "named-assertions")]
#[derive(Debug, Clone)]
pub(crate) struct NamedAssertionMeta {
    pub(crate) display_name: String,
    pub(crate) kind: NamedAssertionKind,
}

/// Per-function UF declarations and type metadata.
///
/// Populated by `register_function_context` and consumed by expression encoding
/// and trait dispatch. Part of #2447 Slice 1.
pub(crate) struct EncoderFunctionContext {
    /// Mapping from function names to ay function declarations.
    /// Used for encoding recursive function calls as uninterpreted function applications.
    pub(crate) functions: std::collections::HashMap<String, FuncDecl>,
    /// Mapping from function names to their declared return types.
    /// Used by trigger typed-lowering so function calls infer the right IR type.
    pub(crate) return_types: std::collections::HashMap<String, crate::ir::TrustVcType>,
    /// Per-function parameter types for polymorphic type binding inference.
    /// Populated by `register_function_context`. Part of #2053.
    pub(crate) param_types: std::collections::HashMap<String, Vec<crate::ir::TrustVcType>>,
    /// Per-function type parameter names inferred from TypeParam occurrences
    /// in params/return type. Part of #2053.
    pub(crate) type_params: std::collections::HashMap<String, Vec<String>>,
}

impl EncoderFunctionContext {
    pub(crate) fn new() -> Self {
        Self {
            functions: std::collections::HashMap::new(),
            return_types: std::collections::HashMap::new(),
            param_types: std::collections::HashMap::new(),
            type_params: std::collections::HashMap::new(),
        }
    }
}

/// Feature-specific encoding registries.
///
/// Groups the per-feature UF registries (polymorphism, datatypes, traits,
/// choose, type invariants) that are each accessed only by their own feature
/// module. Part of #2447 Slice 2.
pub(super) struct FeatureRegistries {
    /// Poly/Box/Unbox context for type-erased polymorphism encoding.
    /// Tracks which concrete types have Box_T/Unbox_T functions declared.
    /// Part of #2053.
    pub(crate) poly_context: polymorphism::PolyContext,
    /// Registered datatype UF encodings keyed by canonical TrustVcType name.
    /// Part of #1942 Slice 2, wired into setup in Slice 4.
    pub(crate) datatypes: std::collections::HashMap<String, super::datatype::DatatypeEncoding>,
    /// Registered trait UF encodings keyed by trait name.
    /// Part of #2425 Slice 2.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) trait_encodings:
        std::collections::HashMap<String, super::trait_encoding::TraitEncoding>,
    /// Registry of Skolem functions for `choose!` expressions, keyed by
    /// canonical macro string. Same key within one verification query yields
    /// the same Skolem function for deterministic witness extraction. Part of #2143.
    pub(crate) choose_registry: std::collections::HashMap<String, FuncDecl>,
    /// Registered type invariant UFs keyed by type name. Part of #2419.
    pub(crate) type_invariant_funcs: std::collections::HashMap<String, FuncDecl>,
    /// Well-foundedness size UFs keyed by datatype name. Part of #2421 Slice 4.
    /// Only populated for recursive datatypes.
    pub(crate) dt_size_funcs: std::collections::HashMap<String, FuncDecl>,
    /// Registry of prophecy variables (fresh unconstrained constants) keyed by
    /// prophecy name. Same name within one verification query yields the same
    /// term. Part of #2519.
    pub(crate) prophecy_registry: std::collections::HashMap<String, Term>,
}

impl FeatureRegistries {
    pub(super) fn new() -> Self {
        Self {
            poly_context: polymorphism::PolyContext::new(),
            datatypes: std::collections::HashMap::new(),
            trait_encodings: std::collections::HashMap::new(),
            choose_registry: std::collections::HashMap::new(),
            type_invariant_funcs: std::collections::HashMap::new(),
            dt_size_funcs: std::collections::HashMap::new(),
            prophecy_registry: std::collections::HashMap::new(),
        }
    }
}

/// A live quantified broadcast `forall` premise recorded at encoding time so a
/// candidate SAT counterexample model can be re-validated against it.
///
/// ay's SAT model validation deliberately SKIPS quantified assertions
/// (`ValidationSkipKind::Quantifier`), trusting that E-matching / CEGQI verified
/// them during solving. When E-matching fails to instantiate a broadcast
/// `forall` at the witness a counterexample assigns, the returned model can
/// violate the premise even though `sat_model_validated == true`. Recording the
/// premise body / guard / bound variables lets `verify_assertion_typed`
/// instantiate it at the candidate model's scalar witnesses and reject (or
/// discharge) a model that violates an un-instantiated premise. Soundness fix #1.
///
/// Premises are recorded by the `add_typed_broadcast` quantified branch (live
/// `forall` asserted) AND by the interpreted-op dead-trigger ground-replay
/// branch (no `forall` asserted; the recorded premise restores witness-level
/// instantiation power during model revalidation). Cap-fallback/type-param
/// replays assert their body directly, so ay already validates them.
#[derive(Debug, Clone)]
pub(crate) struct BroadcastForallPremise {
    /// Names of the universally-quantified bound variables.
    pub(crate) bound_vars: Vec<String>,
    /// The quantified body expression (`forall bound_vars. body`).
    pub(crate) body: crate::ir::TrustVcExpr,
    /// Optional `requires!` guard; the published axiom is `guard ==> body`.
    pub(crate) guard: Option<crate::ir::TrustVcExpr>,
}

/// Mutable verification state and caches.
///
/// Groups the per-verification-query state that is mutated during encoding:
/// broadcast counts, ground pool, assumption context, diagnostics, caches.
/// Part of #2447 Slice 3.
pub(crate) struct VerificationState {
    /// Number of broadcast assumptions added to this encoder instance.
    /// When this exceeds `BROADCAST_INSTANCE_CAP`, subsequent broadcast
    /// assumptions are added as ground formulas (no quantification) to
    /// prevent O(N³) E-matching explosion. Fixes #2113.
    pub(crate) broadcast_count: usize,
    /// Live quantified broadcast `forall` premises asserted into this encoder's
    /// solver. Used by `verify_assertion_typed` to re-validate a candidate SAT
    /// counterexample model against premises that ay's model validation skips
    /// (quantified assertions). Soundness fix #1.
    ///
    /// The interpreted-op dead-trigger ground-replay route ALSO records its
    /// premise here even though it never asserts the live `forall`: the
    /// recorded premise lets the same model-revalidation loop instantiate the
    /// lemma at a candidate model's witnesses, upgrading a spurious SAT (one
    /// that violates the un-asserted universal) to Verified — recovering the
    /// proof power the skipped `forall` would have provided at exactly the
    /// witness the model chose. Sound: every instance asserted during
    /// revalidation is a universal instantiation of a conformance-checked
    /// broadcast lemma (see `add_typed_broadcast`).
    pub(crate) broadcast_premises: Vec<BroadcastForallPremise>,
    /// Candidate goal/assumption expressions for the interpreted-op
    /// dead-trigger broadcast ground replay (`add_typed_broadcast`). ay's
    /// E-matcher indexes only uninterpreted function applications, so a
    /// broadcast trigger headed by an interpreted arithmetic/BV op (e.g.
    /// `x * x`) can never fire inside ay; instead trust-vc matches the trigger
    /// pattern against these expressions at the IR level and asserts the
    /// resulting ground instances. Populated by the broadcast setup paths
    /// (`register_setup_broadcasts` / `add_broadcasts_for_inductive_step`)
    /// only when a dead-trigger broadcast is present; empty otherwise.
    pub(crate) broadcast_ground_replay_sources: Vec<crate::ir::TrustVcExpr>,
    /// Number of broadcast lemmas routed through the interpreted-op
    /// dead-trigger ground replay instead of a live `forall` assertion.
    /// Test observability for the routing decision.
    pub(crate) interpreted_trigger_ground_replays: usize,
    /// Persistent ground-term pool for bounded broadcast/body-axiom chaining.
    pub(crate) ground_pool: ground_pool::GroundTermPool,
    /// When true, encoding is for an assumption context. Trigger-less forall
    /// must NOT be Skolemized — use `solver.forall()` to preserve universal
    /// strength. Set by `parse_and_add_assumption()`. #2187.
    pub(crate) in_assumption_context: bool,
    /// When true, a TOP-LEVEL positive assumption existential `exists v. P(v)`
    /// is eager-Skolemized to fresh consts `c` asserting `P(c)` at ENCODE time
    /// (pre-quantifier-loop-watermark), instead of emitting a real `try_exists`
    /// whose Skolem witness is minted DURING solving (post-watermark). This lets
    /// a `no_mbqi` axiom E-match the assumed witness (the `choose` combined
    /// Hilbert axiom). SOUND — an equisatisfiable Skolemization of a
    /// positively-occurring existential with no enclosing universal — and set
    /// ONLY for a literal top-level `Exists` assumption (never a goal/refutation
    /// existential, never one nested under `Not`/`Implies`/`Compare`/`Ite`), so
    /// no negatively-polarized or goal-position existential is ever Skolemized.
    pub(crate) skolemize_top_level_assumption_exists: bool,
    /// When true, quantified assumptions preserve concrete bound-variable
    /// sorts instead of widening integer-like types to Int. Used for scoped
    /// forall-by facts that mention helper UFs over concrete integer sorts.
    /// Part of #2551.
    pub(crate) preserve_assumption_quantifier_sorts: bool,
    /// Solver mode currently being encoded for an assertion or replayed proof
    /// fact. This lets parser-only decisions, such as finite BV quantifier sort
    /// selection, follow the original proof mode across helper encoders.
    /// Part of #2862.
    pub(crate) active_solver_mode: Option<crate::vc::SolverMode>,
    /// Tracks encoding approximations for result demotion. Part of #2224.
    pub(crate) diagnostics: diagnostics::EncodingDiagnostics,
    /// Cached lowering environment for trigger encoding. Synchronized at
    /// `declare_variable` and `register_function_context` mutation points
    /// so `encode_trigger_typed` can borrow instead of rebuilding. Part of #2181.
    pub(crate) lowering_env: TypeEnv,
    /// Cached result of `infer_int_width_from_types`. Invalidated when
    /// `declare_variable` adds new type entries. Uses `Cell` for interior
    /// mutability so `infer_int_width(&self)` can populate the cache without
    /// requiring `&mut self`. Part of #1786.
    pub(crate) cached_int_width: std::cell::Cell<Option<u32>>,
    /// TrustVcExpr-level equality bindings extracted from assumptions.
    /// Used to substitute assumed equalities (e.g., `y == d * q2`) into
    /// assertion expressions before normalization, so that algebraically
    /// equivalent terms produce identical ay terms. Part of #2187.
    pub(crate) equality_assumptions: std::collections::HashMap<String, crate::ir::TrustVcExpr>,
    /// Number of proof assumptions installed in this encoder instance.
    ///
    /// Datatype axioms and other setup facts are not counted here. This lets
    /// constant-false assertion handling preserve scoped contradiction proofs
    /// while still bypassing solver-only unknowns for assumption-free cases.
    pub(crate) assumption_count: usize,
    /// Number of unpruned proof facts available to this verification step.
    ///
    /// Per-assertion pruning can omit a scoped contradiction assumption from
    /// the actual solver frame for literal `false`, because `false` references
    /// no symbols. Keep the pre-pruning count so constant-false fast paths only
    /// run for genuinely assumption-free proof contexts.
    pub(crate) unpruned_proof_fact_count: usize,
    /// Inline spec function bodies for call-site substitution.
    /// Maps function name → (formal param names, formal param TYPES, body
    /// expression). The param types (positionally aligned with the names) carry
    /// the TEMPLATE types (e.g. `Set(TypeParam("A"))`) so a generic inline body
    /// is monomorphized to the call-site instantiation (#2777, `inline_poly`).
    /// Populated during setup from `is_inline` body axioms. Part of #2488.
    pub(crate) inline_bodies: std::collections::HashMap<
        String,
        (
            Vec<String>,
            Vec<crate::ir::TrustVcType>,
            crate::ir::TrustVcExpr,
        ),
    >,
    /// Overflow behavior for the assert+assume pattern. When `should_check()`
    /// is true, `verify_assertion_typed` re-encodes the assertion with overflow
    /// tracking and assumes the predicates hold (they were already verified in
    /// the separate overflow encoder). Part of #2516.
    pub(crate) overflow_behavior: crate::vc::OverflowBehavior,
    /// Division-by-zero checking policy propagated from `VerificationContext`.
    /// Used when constructing `AstExpressionParser` for overflow predicate
    /// collection. Part of #2516.
    pub(crate) div0_behavior: crate::vc::Div0Behavior,
    /// Shift bounds checking policy propagated from `VerificationContext`.
    /// Used when constructing `AstExpressionParser` for overflow predicate
    /// collection. Part of #2516.
    pub(crate) bitshift_behavior: crate::vc::BitshiftBehavior,
    /// False once solver scope management fails for this encoder instance.
    /// Shared-BV reuse must drop the encoder rather than keep reusing a
    /// potentially poisoned incremental solver. Part of #2552.
    pub(crate) reusable_after_scope: bool,
    /// Stable per-query counters for UNSAT-core assertion names. Keeps
    /// duplicate display labels distinct without leaking SMT-safe symbol
    /// mangling into user-facing diagnostics. Part of #2706.
    #[cfg(feature = "named-assertions")]
    pub(crate) named_assertion_counters: std::collections::HashMap<String, usize>,
    /// Mapping from internal SMT-safe assertion names back to report-facing
    /// labels plus attribution category metadata. Part of #2706.
    #[cfg(feature = "named-assertions")]
    pub(crate) named_assertions: std::collections::HashMap<String, NamedAssertionMeta>,
    /// Persistent ground element aliases across AstExpressionParser instances.
    /// Under native-seq, `native_seq_ground_element_alias` creates aliases for
    /// concrete seq.nth applications. These must persist from assumption encoding
    /// to assertion encoding so that bridge axioms (e.g., in `native_seq_last`)
    /// can connect results to known ground values. Part of #2680.
    #[cfg(feature = "native-seq")]
    pub(crate) native_seq_ground_aliases:
        std::collections::HashMap<(ay_dpll::api::Term, i128), ay_dpll::api::Term>,
    /// Persistent fail-closed nat-cast lowering aliases across
    /// `AstExpressionParser` instances within one verification query.
    ///
    /// Keyed by `(source_term, NatCastKind)` → lowered nat term. Carrying these
    /// from assertion encoding into ground-axiom flushing makes a ground
    /// `nat_to_real(expr as nat)` and its definitional axiom instance
    /// `(expr as nat) as real` denote the *same* floor/invalid skolem, so the
    /// def-axiom E-matches on the cast-wrapped argument. See `cast::NatCastKind`.
    pub(crate) nat_cast_aliases: std::collections::HashMap<
        (ay_dpll::api::Term, super::ir_encoder::cast::NatCastKind),
        ay_dpll::api::Term,
    >,
    /// Whether any `map.subset` atom has been emitted in this query. Once set,
    /// `contains_key` reads membership through the native `(map.dom m)`
    /// projection so ay's finite-map theory can decide subset↔key obligations
    /// without MBQI. Persisted across `AstExpressionParser` instances so a subset
    /// assumption switches the membership-read shape for later assertions in the
    /// same query. See `parser_state::AstExpressionParser::map_subset_seen`.
    pub(crate) map_subset_seen: bool,
    /// Persistent `(map.dom m)` projection terms (bridged to each Map's tracked
    /// domain array) across `AstExpressionParser` instances within one query, so
    /// the bridge equality is asserted at most once per Map carrier.
    pub(crate) map_dom_bridges: std::collections::HashMap<ay_dpll::api::Term, ay_dpll::api::Term>,
    /// Persistent memoization of pure spec-collection constructors
    /// (`Set::new`/`Set::map`/`Set::filter`) across `AstExpressionParser`
    /// instances within one verification query, so two syntactically-identical
    /// closed comprehensions in an assumption and a goal denote the *same*
    /// backend array term and connect via E-matching. See
    /// `parser_state::AstExpressionParser::pure_collection_cache`.
    pub(crate) pure_collection_cache: std::collections::HashMap<String, ay_dpll::api::Term>,
    /// F3 point-interval length pins: declared Seq variables whose length is
    /// ENTAILED to a concrete literal by this query's own assumption set
    /// (`setup.rs::collect_finite_len_pins` — top-level `s == <finite chain>`
    /// / `s.len() == N` assumptions). Consumed by `declare_variable`, which
    /// registers the Int literal as the collection length instead of minting
    /// a symbolic `__trust_vc_len_*` var with a `>= 0` anchor — every length
    /// consumer then constant-folds to ground BV (probe_M2 shape) and no
    /// residual ground Int inequality atom is left to trip ay's quantifier
    /// lane (the F6-class `<= 0 len` poison; see
    /// docs/probes/2026-07-18-ay-lane/dump-smt2/RESULTS.txt).
    pub(crate) pinned_seq_lens: std::collections::HashMap<String, i64>,
    /// Length terms that have been asserted `<= 2^pointer_width - 1` because
    /// their variable is a genuinely `usize`-bounded EXEC collection
    /// (`VariableDecl::bounded_len` — a `Vec`/slice/array). Recorded by
    /// [`AYEncoder::assert_len_usize_bounded`](super::AYEncoder), which is the
    /// SOLE emitter of that bound.
    ///
    /// This is the term-level recovery of a bit that is otherwise lost at the
    /// encoder boundary: `TrustVcType` collapses an exec `Vec<T>` and a spec
    /// `Seq<T>` into the same `TrustVcType::Seq(_)` (`ir.rs`), so a downstream
    /// encoding site holding only a length `Term` cannot otherwise tell whether
    /// that length is carrier-representable. Consumers must treat membership as
    /// "in `[0, 2^pw - 1]` by an already-asserted fact" and NON-membership as
    /// "unknown / possibly unbounded" — never the reverse.
    pub(crate) usize_bounded_lens: std::collections::HashSet<ay_dpll::api::Term>,
}

impl VerificationState {
    pub(super) fn new() -> Self {
        Self {
            broadcast_count: 0,
            broadcast_premises: Vec::new(),
            broadcast_ground_replay_sources: Vec::new(),
            interpreted_trigger_ground_replays: 0,
            ground_pool: ground_pool::GroundTermPool::default(),
            in_assumption_context: false,
            skolemize_top_level_assumption_exists: false,
            preserve_assumption_quantifier_sorts: false,
            active_solver_mode: None,
            diagnostics: diagnostics::EncodingDiagnostics::default(),
            lowering_env: TypeEnv::new(),
            cached_int_width: std::cell::Cell::new(None),
            equality_assumptions: std::collections::HashMap::new(),
            assumption_count: 0,
            unpruned_proof_fact_count: 0,
            inline_bodies: std::collections::HashMap::new(),
            overflow_behavior: crate::vc::OverflowBehavior::default(),
            div0_behavior: crate::vc::Div0Behavior::default(),
            bitshift_behavior: crate::vc::BitshiftBehavior::default(),
            reusable_after_scope: true,
            #[cfg(feature = "named-assertions")]
            named_assertion_counters: std::collections::HashMap::new(),
            #[cfg(feature = "named-assertions")]
            named_assertions: std::collections::HashMap::new(),
            #[cfg(feature = "native-seq")]
            native_seq_ground_aliases: std::collections::HashMap::new(),
            nat_cast_aliases: std::collections::HashMap::new(),
            map_subset_seen: false,
            map_dom_bridges: std::collections::HashMap::new(),
            pure_collection_cache: std::collections::HashMap::new(),
            pinned_seq_lens: std::collections::HashMap::new(),
            usize_bounded_lens: std::collections::HashSet::new(),
        }
    }
}

#[cfg(feature = "named-assertions")]
impl VerificationState {
    fn register_named_assertion(
        &mut self,
        prefix: &str,
        display_name: &str,
        kind: NamedAssertionKind,
    ) -> String {
        let sanitized = super::sanitize_symbol(display_name);
        let base = if sanitized.is_empty() {
            prefix.to_string()
        } else {
            format!("{prefix}_{sanitized}")
        };
        let ordinal = self
            .named_assertion_counters
            .entry(base.clone())
            .or_insert(0);
        let solver_name = if *ordinal == 0 {
            base.clone()
        } else {
            format!("{base}_{ordinal}")
        };
        *ordinal += 1;
        self.named_assertions.insert(
            solver_name.clone(),
            NamedAssertionMeta {
                display_name: display_name.to_string(),
                kind,
            },
        );
        solver_name
    }

    pub(crate) fn register_assumption_core_name(&mut self, display_name: &str) -> String {
        self.register_named_assertion("assumption", display_name, NamedAssertionKind::Assumption)
    }

    pub(crate) fn register_negated_target_core_name(&mut self, display_name: &str) -> String {
        self.register_named_assertion(
            "negated_target",
            display_name,
            NamedAssertionKind::NegatedTarget,
        )
    }

    pub(crate) fn used_assumptions_from_core(&self, core: &[String]) -> Vec<String> {
        let mut seen = std::collections::HashSet::new();
        let mut used = Vec::new();
        for name in core {
            let Some(meta) = self.named_assertions.get(name) else {
                continue;
            };
            if meta.kind != NamedAssertionKind::Assumption {
                continue;
            }
            if seen.insert(meta.display_name.clone()) {
                used.push(meta.display_name.clone());
            }
        }
        used
    }
}

/// Result of verifying a single function context in a parallel batch.
///
/// Carries the original index so callers can correlate results with their
/// input order, plus per-function timing for performance analysis.
/// Part of #2647.
#[derive(Debug, Clone)]
#[must_use]
pub struct BatchVerifyResult {
    /// Index into the original `contexts` vector passed to `verify_batch_parallel`.
    pub(crate) index: usize,
    /// Verification result for this function.
    pub(crate) result: VerifyResult,
    /// Wall-clock time spent verifying this function (solver + encoding).
    pub(crate) elapsed: std::time::Duration,
}

impl BatchVerifyResult {
    pub(crate) fn new(index: usize, result: VerifyResult, elapsed: std::time::Duration) -> Self {
        Self {
            index,
            result,
            elapsed,
        }
    }

    #[must_use]
    pub const fn index(&self) -> usize {
        self.index
    }

    pub fn result(&self) -> &VerifyResult {
        &self.result
    }

    #[must_use]
    pub const fn elapsed(&self) -> std::time::Duration {
        self.elapsed
    }
}
