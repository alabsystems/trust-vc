//! Proof obligation data model.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

/// SOUNDNESS-CRITICAL (H7 review round 2). Name prefix stamped by
/// `body_extract` onto a loop obligation emitted INSIDE a closure literal's
/// body whose loop modifies a variable that was already declared when the body
/// visit began — i.e. a symbol the ENCLOSING function can also name.
///
/// The typed lane publishes every VERIFIED `LoopInvariant` (and every verified
/// exit-site `LoopEnsures` copy) as a function-wide post-loop fact over the
/// BARE symbol of each modified variable. For a loop inside a closure body that
/// fact was established over CLOSURE-LOCAL state — the closure need never run —
/// so it must not reach a goal outside the body. The base-case argument that
/// keeps an ordinary in-branch invariant sound ("the enclosing function already
/// implies it") fails exactly here: `|| { x = 0; while x < 10 { invariant!(x <=
/// 10); x += 1 } }` discharges its base case from the closure's own `x = 0`,
/// while the published fact speaks about the outer `x`. Measured `Verified` on
/// `3fab140f` through the postcondition lane, which reads a by-value `mut`
/// parameter's bare symbol and therefore cannot be protected by the
/// after-the-closure capture havoc.
///
/// Suppressing the publication is a pure HYPOTHESIS REMOVAL: the obligation is
/// still checked, in full and unguarded, so nothing can newly verify. The
/// closure's own post-loop reads keep the fact, because a loop whose modified
/// set is entirely closure-local is not stamped (see
/// `ctrl_closure_invariant_used_inside`).
pub(crate) const CLOSURE_SCOPED_OBLIGATION_PREFIX: &str = "closure_scoped__";

/// True for an obligation whose verified predicate must NOT become a
/// function-wide post-loop fact. See `CLOSURE_SCOPED_OBLIGATION_PREFIX`.
pub(crate) fn is_closure_scoped_obligation_name(name: &str) -> bool {
    name.starts_with(CLOSURE_SCOPED_OBLIGATION_PREFIX)
}

/// Proof-step metadata separating internal scope keys from display labels.
///
/// `key` is used for scope-map lookups (`assert_by_scopes`, `forall_bound_vars`).
/// `label` is the user-facing description shown in counterexample diagnostics.
/// Part of #2652.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[must_use]
pub struct ProofStepMeta {
    pub(crate) key: String,
    pub(crate) label: String,
}

impl ProofStepMeta {
    pub(crate) fn new(key: impl Into<String>, label: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            label: label.into(),
        }
    }

    /// Returns the internal scope key used for scope-map lookups.
    #[must_use]
    pub fn key(&self) -> &str {
        &self.key
    }

    /// Returns the user-facing display label shown in diagnostics.
    #[must_use]
    pub fn label(&self) -> &str {
        &self.label
    }
}

/// A guard clause from a broadcast lemma's `requires!` precondition.
///
/// Stored on `ProofObligation` during broadcast registration and lowered
/// into a typed `TrustVcExpr` conjunction at the prepared-context boundary.
/// Part of #2575.
#[derive(Debug, Clone)]
pub(crate) struct BroadcastGuardClause {
    pub(crate) condition: String,
}

/// How an obligation's condition reached the prepared-context boundary.
/// Part of #1830 Slice 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ConditionOrigin {
    /// The condition stayed as source text and is lowered directly from that
    /// text at the prepared boundary.
    LoweredFromCondition,
    /// The condition arrived as a typed TrustVc expression and is not parsed
    /// from source text during preparation.
    TypedTrustVcExpr,
    /// The condition was supplied through the pre-built typed-expression cache.
    PreBuiltExprCache,
    /// Collection fell back to the legacy translation path before preparation.
    LegacyTranslatedString,
}

/// A proof obligation to be verified by ay.
#[derive(Debug, Clone)]
#[must_use = "proof obligations must be added to a context or pipeline"]
pub struct ProofObligation {
    /// Human-readable name for the obligation
    pub(crate) name: String,
    /// The condition that must hold (as a string for now)
    pub(crate) condition: String,
    /// Typed condition payload, when supplied by a native integration.
    ///
    /// `condition` remains a diagnostic/cache label for compatibility, but
    /// prepared-context lowering consumes this expression directly instead of
    /// reparsing source text.
    pub(crate) typed_expr: Option<crate::ir::TrustVcExpr>,
    /// Source location (file:line:col), RENDERED.
    ///
    /// Kept as the diagnostic string channel every existing consumer already
    /// reads. When `source_location` is set this is its
    /// [`crate::SourceLocation::render`] output and the two can never disagree:
    /// [`ProofObligation::with_source_location`] writes both.
    pub(crate) location: Option<String>,
    /// Source location, STRUCTURED — the authority behind `location`.
    ///
    /// The file-context lane (`verify_function_from_file` and everything the
    /// corpus runs through) records this as each obligation is raised, so a
    /// refuted obligation can answer WHERE, not only WHICH. Consumers that need
    /// the line as a NUMBER (the evidence gate's upstream `FAILS`-marker
    /// cross-check) must read this rather than re-parsing the string.
    pub(crate) source_location: Option<crate::SourceLocation>,
    /// Whether this is an assertion (must verify) or assumption (trusted)
    pub(crate) kind: ObligationKind,
    pub(crate) bound_vars: Option<Vec<String>>,
    pub(crate) trigger_patterns: Option<Vec<Vec<String>>>,
    pub(crate) solver_mode: Option<SolverMode>,
    pub(crate) is_opaque: bool,
    pub(crate) is_inline: bool,
    pub(crate) broadcast_group: Option<String>,
    /// Invariant namespace for InvariantOpen/InvariantClose obligations.
    /// Flows through to PreparedObligation for mask enforcement.
    /// Part of #2427 Slice 4.
    pub(crate) invariant_namespace: Option<i64>,
    /// Trigger inference mode set by #[auto_trigger] or #[all_triggers].
    /// None means default (conservative). Part of #2461 Slice 3.
    pub(crate) trigger_inference_mode: Option<crate::trigger_inference::TriggerInferenceMode>,
    /// Guard clauses from broadcast lemma `requires!` preconditions.
    /// When present, the published broadcast axiom becomes `guard ==> body`
    /// instead of bare `body`. Part of #2575.
    pub(crate) broadcast_guard: Option<Vec<BroadcastGuardClause>>,
    /// Provenance for the stored condition payload. Part of #1830 Slice 1.
    pub(crate) condition_origin: ConditionOrigin,
    /// Authenticates the one synthetic marker used to preserve a source spec
    /// function's declared mathematical-`int` result context. This defaults
    /// false and has only a crate-private builder used by the source catalog.
    pub(crate) source_catalog_math_int_context: bool,
    /// Proof-step metadata: separates internal scope key from display label.
    /// When present, the verifier uses `step_meta.label` in user-facing
    /// diagnostics and `step_meta.key` (= `name`) for scope-map lookups.
    /// Part of #2652.
    pub(crate) step_meta: Option<ProofStepMeta>,
    /// User-supplied `#[verifier::proof_note("…")]` / `custom_err` label
    /// (Verus diagnostic parity). When the obligation FAILS, the verifier
    /// reports it through the Verus error channel: `proof_note` appends
    /// "note: {text}" to the primary failure text, `custom_err` replaces the
    /// primary message. Never affects whether an obligation verifies.
    pub(crate) proof_note: Option<crate::proof_note::ProofNoteLabel>,
}

/// A proof obligation whose verifier condition is already a typed TrustVc IR
/// expression.
#[derive(Debug, Clone)]
#[must_use = "typed proof obligations must be added to a context or pipeline"]
pub struct TypedProofObligation {
    name: String,
    expr: crate::ir::TrustVcExpr,
    kind: ObligationKind,
    location: Option<String>,
    source_location: Option<crate::SourceLocation>,
    solver_mode: Option<SolverMode>,
}

impl TypedProofObligation {
    /// Creates a typed proof obligation with the given name, expression, and kind.
    pub fn new(
        name: impl Into<String>,
        expr: crate::ir::TrustVcExpr,
        kind: ObligationKind,
    ) -> Self {
        Self {
            name: name.into(),
            expr,
            kind,
            location: None,
            source_location: None,
            solver_mode: None,
        }
    }

    /// Creates a typed assertion obligation that the solver must verify.
    pub fn assert(name: impl Into<String>, expr: crate::ir::TrustVcExpr) -> Self {
        Self::new(name, expr, ObligationKind::Assert)
    }

    /// Creates a typed assumption obligation.
    pub fn assume(name: impl Into<String>, expr: crate::ir::TrustVcExpr) -> Self {
        Self::new(name, expr, ObligationKind::Assume)
    }

    /// Creates a typed precondition obligation from a `requires` clause.
    pub fn requires(name: impl Into<String>, expr: crate::ir::TrustVcExpr) -> Self {
        Self::new(name, expr, ObligationKind::Requires)
    }

    /// Creates a typed postcondition obligation from an `ensures` clause.
    pub fn ensures(name: impl Into<String>, expr: crate::ir::TrustVcExpr) -> Self {
        Self::new(name, expr, ObligationKind::Ensures)
    }

    /// Creates a typed loop invariant obligation.
    pub fn loop_invariant(name: impl Into<String>, expr: crate::ir::TrustVcExpr) -> Self {
        Self::new(name, expr, ObligationKind::LoopInvariant)
    }

    /// Attaches a source location string (file:line:col) for diagnostics.
    pub fn with_location(mut self, location: impl Into<String>) -> Self {
        self.location = Some(location.into());
        self
    }

    /// Attaches a STRUCTURED source location, and the string rendering with it.
    pub fn with_source_location(mut self, location: crate::SourceLocation) -> Self {
        self.location = Some(location.render());
        self.source_location = Some(location);
        self
    }

    /// Overrides the solver mode.
    pub fn with_solver_mode(mut self, mode: SolverMode) -> Self {
        self.solver_mode = Some(mode);
        self
    }

    /// Returns the human-readable name of this obligation.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the typed condition expression.
    #[must_use]
    pub const fn expr(&self) -> &crate::ir::TrustVcExpr {
        &self.expr
    }

    /// Returns the kind of this obligation.
    #[must_use]
    pub const fn kind(&self) -> ObligationKind {
        self.kind
    }

    /// Returns the source location, if set.
    #[must_use]
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    /// Returns the solver mode override, if set.
    #[must_use]
    pub const fn solver_mode(&self) -> Option<SolverMode> {
        self.solver_mode
    }

    pub(crate) fn into_proof_obligation(self) -> ProofObligation {
        let mut obligation = ProofObligation::new_typed(self.name, self.expr, self.kind);
        if let Some(location) = self.source_location {
            obligation = obligation.with_source_location(location);
        } else if let Some(location) = self.location {
            obligation = obligation.with_location(location);
        }
        if let Some(mode) = self.solver_mode {
            obligation = obligation.with_solver_mode(mode);
        }
        obligation
    }
}

/// The kind of proof obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ObligationKind {
    Assert,
    Assume,
    BroadcastAssume,
    Requires,
    Ensures,
    MeasureNonNegative,
    MeasureDecreases,
    LoopInvariant,
    LoopGuard,
    InvariantExceptBreak,
    LoopEnsures,
    AssertBy,
    Reveal,
    /// Hide: re-opaque a function's defining body from this program point on
    /// (upstream Verus `hide(f)`). Metadata only — carried in the obligation
    /// stream (in body order) so the query-granular `hidden_fns` set can be
    /// derived AND so the `hide!`/`reveal!` interleave soundness guard can see
    /// its body position relative to proof obligations. Part of #2785.
    Hide,
    /// Broadcast-group activation marker (upstream Verus `broadcast use { g }`).
    /// Metadata only — carried in the obligation stream IN BODY ORDER (at the
    /// `broadcast_use!(g)` program point) so a grouped broadcast axiom is gated
    /// FORWARD-ONLY: it is visible only to proof obligations whose body position
    /// is at or after this marker, never to earlier ones (no retroactive
    /// activation). The activated group name is carried in `broadcast_group`.
    /// Mirrors the body-ordered `Reveal`/`Hide` markers. File-path
    /// `broadcast_use!` reinstatement.
    BroadcastUse,
    /// Invariant open: assume predicate holds for a fresh (havocked) inner value.
    /// Used by `open_local_invariant!` — the expr carries the predicate.
    InvariantOpen,
    /// Invariant close: assert predicate still holds after body modifications.
    /// Used by `open_local_invariant!` — the expr carries the predicate.
    InvariantClose,
    /// Soft precondition for spec functions. At body level, assumed (like Requires).
    /// At call sites, violations produce a warning diagnostic, not a verification failure.
    /// Part of #2483.
    Recommends,
    /// Post-loop assumption — a fact about the current (post-loop) state that
    /// should NOT be pre-state-rewritten when post-loop modified vars are active.
    /// Used for auto-generated exit facts like `i == n` after `for i in 0..n`.
    /// Part of #2502.
    PostLoopAssume,
}

/// Invariant mask — specifies which invariant namespaces a function is
/// allowed to open. Used by `#[opens_invariants(...)]` enforcement.
/// Part of #2427 Slice 4.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum InvariantMask {
    /// Function may open any invariant namespace (default).
    #[default]
    Any,
    /// Function may not open any invariant namespace.
    None,
    /// Function may only open invariants in the specified namespaces.
    Namespaces(Vec<i64>),
}

impl InvariantMask {
    /// Returns true if the given namespace is allowed by this mask.
    pub fn allows(&self, namespace: i64) -> bool {
        match self {
            InvariantMask::Any => true,
            InvariantMask::None => false,
            InvariantMask::Namespaces(allowed) => allowed.contains(&namespace),
        }
    }
}

/// Solver strategy to use when discharging a proof obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolverMode {
    /// Standard SMT solving with EUF + LRA theories.
    Default,
    /// Nonlinear integer arithmetic (NIA) theory.
    NonlinearArith,
    /// Bit-vector theory for fixed-width arithmetic.
    BitVector,
    /// Compile-time constant evaluation without SMT.
    Compute,
}

impl ProofObligation {
    /// Creates a new proof obligation with the given name, condition, and kind.
    pub fn new(
        name: impl Into<String>,
        condition: impl Into<String>,
        kind: ObligationKind,
    ) -> Self {
        ProofObligation {
            name: name.into(),
            condition: condition.into(),
            typed_expr: None,
            location: None,
            source_location: None,
            kind,
            bound_vars: None,
            trigger_patterns: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            condition_origin: ConditionOrigin::LoweredFromCondition,
            source_catalog_math_int_context: false,
            step_meta: None,
            proof_note: None,
        }
    }

    /// Creates a proof obligation backed by a typed TrustVc expression.
    pub fn new_typed(
        name: impl Into<String>,
        expr: crate::ir::TrustVcExpr,
        kind: ObligationKind,
    ) -> Self {
        let name = name.into();
        ProofObligation {
            condition: format!("<typed:{name}>"),
            typed_expr: Some(expr),
            name,
            location: None,
            source_location: None,
            kind,
            bound_vars: None,
            trigger_patterns: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            condition_origin: ConditionOrigin::TypedTrustVcExpr,
            source_catalog_math_int_context: false,
            step_meta: None,
            proof_note: None,
        }
    }
    /// Creates an assertion obligation that the solver must verify.
    pub fn assert(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::Assert)
    }
    /// Creates an assumption that the solver treats as a trusted axiom.
    pub fn assume(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::Assume)
    }
    /// Creates a broadcast-group assumption injected by `broadcast_use!`.
    pub fn broadcast_assume(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::BroadcastAssume)
    }
    /// Creates a precondition obligation from a `requires!` clause.
    pub fn requires(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::Requires)
    }
    /// Creates a postcondition obligation from an `ensures!` clause.
    pub fn ensures(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::Ensures)
    }
    /// Creates an obligation asserting a termination measure is non-negative.
    pub fn measure_non_negative(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::MeasureNonNegative)
    }
    /// Creates an obligation asserting a termination measure strictly decreases.
    pub fn measure_decreases(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::MeasureDecreases)
    }
    /// Creates a loop invariant obligation checked at each iteration.
    pub fn loop_invariant(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::LoopInvariant)
    }
    /// Creates a loop guard obligation for the loop entry condition.
    pub fn loop_guard(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::LoopGuard)
    }
    /// Creates an invariant obligation that holds except at `break` exits.
    pub fn invariant_except_break(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::InvariantExceptBreak)
    }
    /// Creates a postcondition obligation for loop ensures clauses.
    pub fn loop_ensures(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::LoopEnsures)
    }
    /// Creates an `assert_by` obligation verified in a separate proof scope.
    pub fn assert_by(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::AssertBy)
    }
    /// Creates an invariant-open obligation that assumes the predicate for a havocked value.
    pub fn invariant_open(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::InvariantOpen)
    }
    /// Creates an invariant-close obligation asserting the predicate still holds after mutation.
    pub fn invariant_close(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::InvariantClose)
    }
    /// Creates a soft precondition obligation that emits a warning instead of a failure.
    pub fn recommends(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::Recommends)
    }
    /// Creates a post-loop assumption not subject to pre-state rewriting.
    pub fn post_loop_assume(name: impl Into<String>, condition: impl Into<String>) -> Self {
        Self::new(name, condition, ObligationKind::PostLoopAssume)
    }
    /// Creates a reveal obligation that makes an opaque function's body visible.
    pub fn reveal(fn_name: impl Into<String>) -> Self {
        ProofObligation {
            name: fn_name.into(),
            condition: String::new(),
            typed_expr: None,
            location: None,
            source_location: None,
            kind: ObligationKind::Reveal,
            bound_vars: None,
            trigger_patterns: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            condition_origin: ConditionOrigin::LoweredFromCondition,
            source_catalog_math_int_context: false,
            step_meta: None,
            proof_note: None,
        }
    }
    /// Creates a hide obligation that re-opaques a function's defining body
    /// from this program point on (upstream Verus `hide(f)`). Metadata only,
    /// carried in body order in the obligation stream. Part of #2785.
    pub fn hide(fn_name: impl Into<String>) -> Self {
        ProofObligation {
            name: fn_name.into(),
            condition: String::new(),
            typed_expr: None,
            location: None,
            source_location: None,
            kind: ObligationKind::Hide,
            bound_vars: None,
            trigger_patterns: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            condition_origin: ConditionOrigin::LoweredFromCondition,
            source_catalog_math_int_context: false,
            step_meta: None,
            proof_note: None,
        }
    }
    /// Creates a body-ordered broadcast-group activation marker (upstream Verus
    /// `broadcast use { group }`). Metadata only, carried in body order in the
    /// obligation stream so grouped broadcast axioms are gated FORWARD-ONLY: the
    /// group is visible only to proof obligations at or after this marker's body
    /// position, never to earlier ones. The group name is carried in BOTH `name`
    /// (for stream identity/ordering) and `broadcast_group` (read by the
    /// position-aware encoder gate). File-path `broadcast_use!` reinstatement.
    pub(crate) fn broadcast_use(group: impl Into<String>) -> Self {
        let group = group.into();
        ProofObligation {
            name: group.clone(),
            condition: String::new(),
            typed_expr: None,
            location: None,
            source_location: None,
            kind: ObligationKind::BroadcastUse,
            bound_vars: None,
            trigger_patterns: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: Some(group),
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            condition_origin: ConditionOrigin::LoweredFromCondition,
            source_catalog_math_int_context: false,
            step_meta: None,
            proof_note: None,
        }
    }
    /// Sets whether the obligation's function body is opaque (hidden from the solver).
    pub fn with_opaque(mut self, opaque: bool) -> Self {
        self.is_opaque = opaque;
        self
    }
    /// Sets whether the obligation's spec function is inlined at call sites.
    pub fn with_inline(mut self, inline: bool) -> Self {
        self.is_inline = inline;
        self
    }
    /// Attaches a source location string (file:line:col) for diagnostics.
    ///
    /// The UNSTRUCTURED channel, kept for callers that already hold a rendered
    /// string (the trust-engine adapter, the proc-macro lane). Prefer
    /// [`Self::with_source_location`], whose line is readable back as a number.
    pub fn with_location(mut self, location: impl Into<String>) -> Self {
        self.location = Some(location.into());
        self
    }
    /// Attaches a STRUCTURED source location, and the string rendering with it.
    ///
    /// Both fields are written together so [`Self::location`] and
    /// [`Self::source_location`] can never name different lines.
    pub fn with_source_location(mut self, location: crate::SourceLocation) -> Self {
        self.location = Some(location.render());
        self.source_location = Some(location);
        self
    }
    /// Attaches `location` only if this obligation carries none.
    ///
    /// This is how the file lane's AMBIENT location is stamped on by
    /// `VerificationContext::push_obligation`: an emission site that already
    /// pinned a more precise span keeps it.
    pub fn or_source_location(self, location: crate::SourceLocation) -> Self {
        if self.location.is_some() || self.source_location.is_some() {
            return self;
        }
        self.with_source_location(location)
    }
    /// Sets the universally quantified bound variables for this obligation.
    pub fn with_bound_vars(mut self, vars: Vec<String>) -> Self {
        self.bound_vars = Some(vars);
        self
    }
    /// Sets the trigger patterns used for quantifier instantiation.
    pub fn with_trigger_patterns(mut self, patterns: Vec<Vec<String>>) -> Self {
        self.trigger_patterns = Some(patterns);
        self
    }
    /// Overrides the solver mode (e.g., bit-vector or nonlinear arithmetic).
    pub fn with_solver_mode(mut self, mode: SolverMode) -> Self {
        self.solver_mode = Some(mode);
        self
    }
    /// Assigns this obligation to a named broadcast group.
    pub fn with_broadcast_group(mut self, group: impl Into<String>) -> Self {
        self.broadcast_group = Some(group.into());
        self
    }
    /// Attaches broadcast `requires`→guard clauses (condition strings). When
    /// present, the published broadcast axiom becomes `guard ==> body` instead of
    /// bare `body`. SOUNDNESS-CRITICAL for file-path `broadcast_use!`: a broadcast
    /// lemma with a `requires` MUST publish the guard, else a caller lacking the
    /// requires proves the conclusion unconditionally. Empty `conditions` is the
    /// identity (an unguarded lemma). Part of the file-path broadcast_use! wiring.
    pub(crate) fn with_broadcast_guard_conditions(mut self, conditions: Vec<String>) -> Self {
        if !conditions.is_empty() {
            self.broadcast_guard = Some(
                conditions
                    .into_iter()
                    .map(|condition| BroadcastGuardClause { condition })
                    .collect(),
            );
        }
        self
    }
    /// Sets the invariant namespace for open/close mask enforcement.
    pub fn with_invariant_namespace(mut self, namespace: i64) -> Self {
        self.invariant_namespace = Some(namespace);
        self
    }
    /// Sets the provenance of how the condition reached the prepared boundary.
    pub fn with_condition_origin(mut self, origin: ConditionOrigin) -> Self {
        self.condition_origin = origin;
        self
    }
    /// Grants the synthetic source-catalog math-int marker capability to this
    /// exact obligation. Crate-private so authored contracts and API consumers
    /// cannot forge the provenance bit.
    pub(crate) fn with_source_catalog_math_int_context(mut self) -> Self {
        self.source_catalog_math_int_context = true;
        self
    }
    /// Attaches proof-step metadata separating the scope key from the display label.
    pub fn with_step_meta(mut self, meta: ProofStepMeta) -> Self {
        self.step_meta = Some(meta);
        self
    }
    /// Attaches an optional `proof_note`/`custom_err` diagnostic label.
    /// `None` is the identity, so callers can thread an optional label
    /// without branching.
    pub fn with_proof_note(mut self, label: Option<crate::proof_note::ProofNoteLabel>) -> Self {
        self.proof_note = label;
        self
    }

    /// Returns the human-readable name of this obligation.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the condition expression that must hold.
    #[must_use]
    pub fn condition(&self) -> &str {
        &self.condition
    }

    /// Returns the typed condition expression, when this obligation was
    /// supplied through the typed API.
    #[must_use]
    pub fn typed_expr(&self) -> Option<&crate::ir::TrustVcExpr> {
        self.typed_expr.as_ref()
    }

    /// Returns the source location (file:line:col), if set.
    #[must_use]
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    /// A copy of this obligation with BOTH location channels cleared.
    ///
    /// For callers that must compare or key on an obligation's SOLVER INPUT:
    /// where an obligation was raised is diagnostic and never changes the query
    /// (`VerificationContext::isolated_query_key`).
    #[must_use = "this returns a copy and does not modify the original obligation"]
    pub fn without_source_location(&self) -> Self {
        let mut copy = self.clone();
        copy.location = None;
        copy.source_location = None;
        copy
    }

    /// Returns the STRUCTURED source location, when one was recorded.
    ///
    /// Read this, not [`Self::location`], whenever the LINE is wanted as a
    /// number — string surgery on the rendering is how a colon-bearing path
    /// silently becomes "no location".
    #[must_use]
    pub fn source_location(&self) -> Option<&crate::SourceLocation> {
        self.source_location.as_ref()
    }

    /// Returns the kind of this obligation (assert, assume, requires, etc.).
    #[must_use]
    pub const fn kind(&self) -> ObligationKind {
        self.kind
    }

    /// Returns the universally quantified bound variables, if any.
    #[must_use]
    pub fn bound_vars(&self) -> Option<&[String]> {
        self.bound_vars.as_deref()
    }

    /// Returns the trigger patterns for quantifier instantiation, if any.
    #[must_use]
    pub fn trigger_patterns(&self) -> Option<&[Vec<String>]> {
        self.trigger_patterns.as_deref()
    }

    /// Returns the solver mode override, if any.
    #[must_use]
    pub fn solver_mode(&self) -> Option<SolverMode> {
        self.solver_mode
    }

    /// Returns whether the obligation's function body is opaque.
    #[must_use]
    pub const fn is_opaque(&self) -> bool {
        self.is_opaque
    }

    /// Returns whether the obligation's spec function is inlined.
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.is_inline
    }

    /// Returns the broadcast group name, if assigned.
    #[must_use]
    pub fn broadcast_group(&self) -> Option<&str> {
        self.broadcast_group.as_deref()
    }

    /// Returns the provenance of the condition payload.
    #[must_use]
    pub const fn condition_origin(&self) -> ConditionOrigin {
        self.condition_origin
    }

    /// Returns the proof-step metadata, if attached.
    #[must_use]
    pub fn step_meta(&self) -> Option<&ProofStepMeta> {
        self.step_meta.as_ref()
    }

    /// Returns the `proof_note`/`custom_err` label, if attached.
    #[must_use]
    pub fn proof_note(&self) -> Option<&crate::proof_note::ProofNoteLabel> {
        self.proof_note.as_ref()
    }
}
