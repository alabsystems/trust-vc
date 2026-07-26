//! Verification context for proof functions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod behaviors;
mod builders;

pub use behaviors::{BitshiftBehavior, Div0Behavior, OverflowBehavior, VerificationMode};

use super::obligation::{InvariantMask, ProofObligation, TypedProofObligation};
use crate::counterexample_names::CounterexampleVarMeta;
use crate::ir::{TraitDecl, TraitImplDecl};
use std::collections::{HashMap, HashSet};

/// Typed helper function signature: (return_type, params, trait_bounds).
pub(crate) type HelperFnSignature = (
    crate::ir::TrustVcType,
    Vec<(String, crate::ir::TrustVcType)>,
    Vec<crate::ir::TraitBound>,
);

/// Inherent-impl method metadata for receiver-method-call lowering:
/// (uf_name, return_type, param_types_excluding_receiver). Keyed by
/// `(self_type_string, method_name)`. Threaded into `TypeEnv` method metadata
/// by `prepare_context`'s `build_type_env` so `recv.method(args)` resolves to a
/// typed `FnCall`. Part of A3 (method/assoc/Self-call return-type registration).
pub(crate) type InherentMethodSignature =
    (String, crate::ir::TrustVcType, Vec<crate::ir::TrustVcType>);

/// How an impl method takes its `self` receiver. Used to decide whether a
/// `recv.method(..)` call can mutate the caller's `recv` binding (the
/// catastrophic struct-mutation frame gap, the user-struct analog of the #62/#63
/// collection loop-mutation gap):
///
/// - `RefMut` (`&mut self`): mutates the caller's binding in place. A later read
///   of `recv` must NOT see the stale entry value (havoc), and `recv` must be in
///   a loop's modified set.
/// - `Ref` (`&self`): pure read — leaves the caller's binding unchanged, so a
///   true fact about `recv` survives the call (must NOT be havocked).
/// - `Value` (`self` / `mut self`): the receiver is moved into the callee; it
///   cannot mutate the *caller's* binding (which is consumed), so reads of the
///   pre-call value are sound — treated as non-mutating for the caller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SelfReceiverKind {
    RefMut,
    Ref,
    Value,
}

/// Context about the function being verified.
#[derive(Debug, Clone)]
pub struct FunctionContext {
    pub(crate) name: String,
    pub(crate) params: Vec<(String, crate::ir::TrustVcType)>,
    pub(crate) return_type: crate::ir::TrustVcType,
    pub(crate) is_recursive: bool,
    pub(crate) mode: crate::mode::FunctionMode,
    pub(crate) trait_bounds: Vec<crate::ir::TraitBound>,
}

impl FunctionContext {
    /// Creates a new function context with the given name, parameters, return type, and mode.
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        params: Vec<(String, crate::ir::TrustVcType)>,
        return_type: crate::ir::TrustVcType,
        mode: crate::mode::FunctionMode,
    ) -> Self {
        Self {
            name: name.into(),
            params,
            return_type,
            is_recursive: false,
            mode,
            trait_bounds: vec![],
        }
    }

    /// Sets whether this function is recursive.
    #[must_use]
    pub fn with_recursive(mut self, is_recursive: bool) -> Self {
        self.is_recursive = is_recursive;
        self
    }

    /// Sets the trait bounds for this function's generic parameters.
    #[must_use]
    pub fn with_trait_bounds(mut self, trait_bounds: Vec<crate::ir::TraitBound>) -> Self {
        self.trait_bounds = trait_bounds;
        self
    }

    /// Returns the function name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the function parameter list as (name, type) pairs.
    #[must_use]
    pub fn params(&self) -> &[(String, crate::ir::TrustVcType)] {
        &self.params
    }

    /// Returns the function's return type.
    #[must_use]
    pub fn return_type(&self) -> &crate::ir::TrustVcType {
        &self.return_type
    }

    /// Returns whether this function is recursive.
    #[must_use]
    pub fn is_recursive(&self) -> bool {
        self.is_recursive
    }

    /// Returns the function's verification mode (exec, proof, or spec).
    #[must_use]
    pub fn mode(&self) -> crate::mode::FunctionMode {
        self.mode
    }

    /// Returns the trait bounds on this function's generic parameters.
    #[must_use]
    pub fn trait_bounds(&self) -> &[crate::ir::TraitBound] {
        &self.trait_bounds
    }
}

/// Configuration for demand-driven body inlining on contract-insufficient retries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct DemandInlineConfig {
    enabled: bool,
    depth_bound: usize,
    max_callees: usize,
}

impl DemandInlineConfig {
    /// Creates a default config: enabled, depth bound 2, max 4 callees.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            enabled: true,
            depth_bound: 2,
            max_callees: 4,
        }
    }

    /// Returns whether demand-inline retry is enabled.
    #[must_use]
    pub const fn enabled(self) -> bool {
        self.enabled
    }

    /// Returns the maximum body-expansion depth for inline retry.
    #[must_use]
    pub const fn depth_bound(self) -> usize {
        self.depth_bound
    }

    /// Returns the maximum number of callees selected per retry round.
    #[must_use]
    pub const fn max_callees(self) -> usize {
        self.max_callees
    }

    /// Returns every verdict-semantic policy component for cache-keying.
    ///
    /// The exhaustive destructure is intentional: adding a policy field must
    /// force callers to decide whether it changes verification semantics.
    pub(crate) const fn cache_key_parts(self) -> (bool, usize, usize) {
        let Self {
            enabled,
            depth_bound,
            max_callees,
        } = self;
        (enabled, depth_bound, max_callees)
    }

    /// Sets whether demand-inline retry is enabled.
    #[must_use]
    pub const fn with_enabled(mut self, enabled: bool) -> Self {
        self.enabled = enabled;
        self
    }

    /// Sets the maximum body-expansion depth.
    #[must_use]
    pub const fn with_depth_bound(mut self, depth_bound: usize) -> Self {
        self.depth_bound = depth_bound;
        self
    }

    /// Sets the maximum number of callees selected per retry round.
    #[must_use]
    pub const fn with_max_callees(mut self, max_callees: usize) -> Self {
        self.max_callees = max_callees;
        self
    }
}

impl Default for DemandInlineConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// The main verification context holding obligations, variables, and configuration.
#[derive(Debug, Clone, Default)]
#[must_use = "verification contexts should be configured or verified, not dropped"]
pub struct VerificationContext {
    pub(crate) obligations: Vec<ProofObligation>,
    /// Non-fatal VERIFIER WARNINGS raised while extracting this unit, in source
    /// order.
    ///
    /// Verus reports these as `MessageLevel::Warning` diagnostics alongside a
    /// SUCCESSFUL verification (`vir/src/well_formed.rs`, `VirErrAs::Warning`);
    /// upstream's harness reads them out of `err.warnings` and its default
    /// `=> Ok(())` arm asserts there are NONE. They carry no proof content — a
    /// warning never changes a verdict — so this channel is purely additive and
    /// cannot affect soundness.
    pub(crate) warnings: Vec<String>,
    pub(crate) variables: Vec<VariableDecl>,
    /// O(1) name→index lookup into `variables`. Maintained by `declare_var*`
    /// and `push_variable`. Part of #1684.
    variable_index: HashMap<String, usize>,
    /// Variables whose Rust source type was an immutable reference erased to
    /// its referent type for verification. This lets lowering accept exactly
    /// one `*x` dereference for shared-reference parameters without making all
    /// dereferences identity.
    pub(crate) erased_shared_ref_vars: HashSet<String>,
    /// Variables whose Rust source type was `Ghost<T>` erased to `T` for SMT.
    /// This lets lowering accept `ghost.view()` as identity without making
    /// ordinary `T::view()` calls identity.
    pub(crate) erased_ghost_vars: HashSet<String>,
    pub(crate) function_context: Option<FunctionContext>,
    pub(crate) verification_mode: VerificationMode,
    pub(crate) overflow_behavior: OverflowBehavior,
    pub(crate) div0_behavior: Div0Behavior,
    pub(crate) bitshift_behavior: BitshiftBehavior,
    overflow_behavior_explicit: bool,
    div0_behavior_explicit: bool,
    bitshift_behavior_explicit: bool,
    pub(crate) broadcast_use_groups: Vec<String>,
    /// Function names hidden via `hide!(f)` in the current proof. A hidden
    /// function's defining body axiom is suppressed for this query (like an
    /// unrevealed `#[trust_vc::opaque]` fn) unless the same proof also
    /// `reveal!`s it — reveal wins over hide. Mirrors Verus `hide(f)` (the
    /// per-function `hidden` list consumed by vir `set_fuel`).
    pub(crate) hidden_fns: HashSet<String>,
    pub(crate) assert_by_scopes: HashMap<String, Vec<ProofObligation>>,
    /// Per-loop-invariant ENTRY assumptions (`i == 0` for loop-modified
    /// let-locals). Fed ONLY to the base-case (entry) check of the invariant via
    /// the scoped slot, so a let-local counter's entry value pins the base case
    /// like a param's `requires`, without leaking into the inductive step or
    /// post-loop (both of which havoc the modified var). Keyed by invariant name.
    pub(crate) loop_entry_scopes: HashMap<String, Vec<ProofObligation>>,
    /// Bound variable declarations scoped to `assert_forall_by` obligations.
    /// These are available only while proving the matching `AssertBy`, not as
    /// globally declared verification variables. Part of #2551.
    pub(crate) forall_bound_vars: HashMap<String, Vec<VariableDecl>>,
    /// Proof-local prophecy bindings available to prepared-context lowering.
    /// Maps local prophecy name -> inner symbolic type. Part of #2549.
    pub(crate) prophecy_bindings: HashMap<String, crate::ir::TrustVcType>,
    /// Source-local type aliases collected from same-file Rust items.
    /// These are copied into `TypeEnv` so contract lowering can resolve alias
    /// names in quantifier binders, spec closures, and explicit type arguments.
    pub(crate) source_type_aliases: HashMap<String, crate::ir::TrustVcType>,
    pub(crate) loop_guards: HashMap<String, String>,
    pub(crate) loop_modified_vars: HashMap<String, Vec<String>>,
    /// Straight-line loop-body state transition for each loop invariant, keyed
    /// by invariant name. Each entry maps a loop-modified variable to the
    /// scoped-value string giving its post-body value expressed over loop-head
    /// (pre-state) variables — e.g. `("i", "(i + 1)")` for a body `i = i + 1`.
    /// Consumed by the frame-condition inductive step to bind the havoc'd
    /// current-state variable to `f(pre-state)` (M4 loop-body transition).
    pub(crate) loop_body_transitions: HashMap<String, Vec<(String, String)>>,
    pub(crate) helper_functions: HashMap<String, String>,
    pub(crate) trait_decls: Vec<TraitDecl>,
    pub(crate) trait_impl_decls: Vec<TraitImplDecl>,
    /// Captured single-pure-return bodies of trait-impl methods, keyed by the
    /// concrete UF name (`Type__method`). Used by the auxiliary conformance pass
    /// to bind the impl method's result to its actual body even when the verified
    /// function never references the impl method (so no body axiom is otherwise
    /// in scope). Populated from source by trait-impl extraction; empty for
    /// directly-constructed contexts (which keep the prior body-axiom path).
    pub(crate) trait_impl_method_bodies: HashMap<String, crate::ir::ConformanceMethodBody>,
    /// The impl method's OWN declared `#[trust_vc::ensures(..)]` postconditions,
    /// keyed by the concrete UF name (`Type__method`). Populated ONLY for
    /// non-exempt impl methods whose single-pure-return body was ALSO captured
    /// (`trait_impl_method_bodies`), so the conformance pass can pin
    /// `result == body` and VERIFY `body ⊨ impl_ensures` before any caller is
    /// allowed to assume the strengthened postcondition. Consumed by the
    /// conformance-extension (assert) and the impl-postcondition propagation
    /// axiom. Empty for impls that declare no own `ensures`. Part of the
    /// impl-ensures conformance-extension + propagation (traits_extend_ensures).
    pub(crate) trait_impl_method_ensures: HashMap<String, Vec<String>>,
    /// Concrete UF names (`Type__method`) of trait-impl methods that are BLOCKED
    /// by a dedicated ill-formedness error — an impl method declaring its own
    /// `requires`, or its own `returns` while the trait also declares `returns`
    /// (the "returns on both" conflict). Such an impl is rejected via that error
    /// when its body is verified directly; the auxiliary conformance pass must
    /// SKIP it so a blocked impl does not also sink the verification of unrelated
    /// functions in the same file. Never used to accept a plain inherited-contract
    /// violation (those still conformance-check and Counterexample).
    pub(crate) conformance_exempt_methods: HashSet<String>,
    /// Typed helper function registry for polymorphic and multi-function proofs.
    /// Maps function name → (return_type, param_types, trait_bounds). Populated
    /// by spec expansion's proof_mode_block so ALL called spec functions are
    /// available in TypeEnv, not just the last-called one (which overwrites
    /// `function_context`). Part of #2431, #2053, #2425.
    pub(crate) helper_functions_typed: HashMap<String, HelperFnSignature>,
    /// Inherent-impl method metadata for `recv.method(args)` lowering, keyed by
    /// `(self_type_string, method_name)`. Populated by inherent-method extraction
    /// and threaded into `TypeEnv` method metadata by `build_type_env`. Part of A3.
    pub(crate) inherent_methods: HashMap<(String, String), InherentMethodSignature>,
    /// How each impl method (inherent OR trait) takes its `self` receiver, keyed
    /// by `(base_self_type_name, method_name)`. Populated from ALL `impl` blocks
    /// in the source file (independent of whether the method's body/return is
    /// modelable), so the body extractor can resolve whether `recv.method(..)`
    /// mutates the caller's `recv` binding. A `(type, method)` absent from this
    /// map is an UNKNOWN signature — treated conservatively (fail-closed havoc)
    /// unless the method is a universally-pure read (`is_known_pure_struct_method`).
    /// The user-struct analog of the collection-mutator detection (#62/#63).
    pub(crate) struct_self_receiver_kinds: HashMap<(String, String), SelfReceiverKind>,
    /// User-defined struct types registered via `#[trust_vc::struct_spec]`.
    /// Each struct is encoded as a single-variant datatype with constructor,
    /// selectors, and tester axioms. Part of #2419 Slice 1.
    pub(crate) struct_types: Vec<crate::ir::StructDef>,
    /// Datatype names (structs AND enums) whose source carried
    /// `#[derive(PartialEq)]` — their `==`/`.eq()` is the structural equality.
    /// Structs also carry this on their `StructDef`; enums (registered as type
    /// aliases, without a `StructDef`) record it only here.
    pub(crate) derived_partial_eq_types: HashSet<String>,
    /// Datatype names whose source carried `#[derive(Clone)]`.
    pub(crate) derived_clone_types: HashSet<String>,
    /// Datatype names with a hand-written (non-derived) `impl PartialEq` in source.
    /// Their EXEC `==` calls a possibly-non-structural custom impl, so the `==`/`!=`
    /// operator on them (or any datatype transitively containing one) must NOT
    /// structural-lower — see `ir_lowering::operators` and `TypeEnv::has_manual_partial_eq`.
    pub(crate) manual_partial_eq_types: HashSet<String>,
    /// Type invariant predicates for struct types. Maps type name → invariant
    /// body expression written in terms of field selectors. Part of #2419 Slice 2.
    pub(crate) type_invariants: HashMap<String, crate::ir::TrustVcExpr>,
    /// Invariant mask specifying which namespaces this function may open.
    /// Set by `#[opens_invariants(...)]`. Defaults to `Any` (unrestricted).
    /// Part of #2427 Slice 4.
    pub(crate) invariant_mask: InvariantMask,
    /// Parameters annotated with `tracked` in proof function signatures.
    /// Recorded for mode checking: tracked params carry proof-mode ownership
    /// and should not be duplicated in spec expressions. Part of #2427 Slice 3.
    pub(crate) tracked_params: HashSet<String>,
    /// Per-function solver timeout override in milliseconds.
    /// When `Some(ms)`, overrides the default 30,000ms solver timeout.
    /// Set by `#[trust_vc::rlimit(N)]`. Part of #2489.
    pub(crate) rlimit_ms: Option<u64>,
    /// Demand-driven body-inlining retry policy for contract-insufficient
    /// assertion recovery. Part of #2655.
    pub(crate) demand_inline: DemandInlineConfig,
    /// Counterexample display metadata keyed by raw solver variable name.
    /// Maps internal helper names to user-facing aliases and visibility.
    /// Part of #2651.
    pub(crate) counterexample_var_meta: HashMap<String, CounterexampleVarMeta>,
    /// Error flag set when `declare_var_typed` detects a duplicate variable.
    /// Checked by `prepare_context` before encoding. Part of #2668.
    pub(crate) duplicate_var_error: Option<String>,
    /// Fail-closed flag set when the verified function constructs a generic
    /// self-recursive datatype at TWO OR MORE distinct concrete instantiations
    /// (e.g. both `GList<i32>` and `GList<bool>`). Such a base cannot be
    /// monomorphized to a single per-instantiation carrier, so its concrete
    /// carrier alias is never registered; the nested-recursion constructor
    /// lowering then mixes a concrete outer carrier (`GList<i32>`) with a
    /// template-sorted recursive tail (`GList`), which the backend rejects as a
    /// sort mismatch deep inside encoding (surfacing as a swallowed
    /// `SolverPanic`). Detecting the conflict here lets `prepare_context` fail
    /// closed CLEANLY — a `VerifyResult::Error`, never a false `Verified` — before
    /// any malformed query reaches the solver. Sound (Verus monomorphizes per
    /// instantiation; we are merely incomplete here), not soundness-relevant.
    pub(crate) generic_instantiation_conflict: Option<String>,
    /// When true, the timeout retry cascade (int-mode + extended-timeout) is
    /// skipped after the initial BV attempt. Tests that accept Unknown can set
    /// this to avoid ~30s of wasted retry per timeout assertion. Part of #2707.
    pub(crate) skip_retry_cascade: bool,
    /// Non-verifying verdict of a spec-carrying `trust_vc::closure!` DEF-SIDE
    /// check discharged during extraction in an ISOLATED child context (see
    /// [`Self::isolated_closure_child`] / [`Self::record_closure_def_side_failure`]).
    ///
    /// SOUNDNESS-CRITICAL (closure def-side isolation): a closure's precondition
    /// `R`, its `result == BODY` binding, and its ensures `E` are discharged as
    /// the INDEPENDENT VC `R ∧ (res == BODY) ⊢ E` in a child context whose
    /// obligation/assumption vectors are DISCARDED — never merged into this
    /// parent — so a contradictory `requires(false)` cannot inject `false` as a
    /// parent hypothesis and vacuously discharge unrelated parent obligations
    /// (the cardinal false-verify this field's mechanism prevents). The child's
    /// FAILING verdict is the ONLY thing that crosses back, recorded here and
    /// surfaced by [`Self::verify`] as this function's result (first failure
    /// wins). `None` for every function without a failing closure def-side
    /// check — a verified or absent closure contributes nothing.
    pub(crate) closure_def_side_failure: Option<crate::VerifyResult>,
}

/// A named variable declaration with its TrustVc type, used in verification contexts.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VariableDecl {
    pub name: String,
    pub ty: crate::ir::TrustVcType,
    /// True IFF this variable's origin *syntactic* type is an exec collection
    /// whose length is `usize`-bounded — a `Vec<T>`, a slice `[T]`, or an array
    /// `[T; N]` (peeling references). Such a collection can never have more than
    /// `usize::MAX` elements, so the encoder is entitled to assert
    /// `len <= 2^pointer_width - 1` at declaration, which discharges the NC4
    /// carrier-index representability side condition for its index reads.
    ///
    /// SOUNDNESS-CRITICAL — this bit MUST stay `false` for a spec `Seq<T>`, whose
    /// length is an unbounded mathematical `Int`. A spec `Seq` and an exec `Vec`
    /// both lower to `TrustVcType::Seq`, so the Vec-vs-Seq provenance is captured
    /// HERE (from the origin syn type string, before the collapse) and nowhere
    /// else. Leaking the bound to a `Seq` would make every huge-length
    /// (`len >= 2^64`) soundness guard's context UNSAT and vacuously "verify"
    /// (the reverted false-verify). Set only at the parameter-typing seam
    /// (`vc_extraction`) via `declare_var_typed_bounded`; defaults `false`
    /// everywhere else.
    pub(crate) bounded_len: bool,
}

impl VariableDecl {
    /// Creates a new variable declaration with the given name and type.
    ///
    /// `bounded_len` defaults to `false` (the fail-closed / spec-`Seq` default).
    #[must_use]
    pub fn new(name: impl Into<String>, ty: crate::ir::TrustVcType) -> Self {
        Self {
            name: name.into(),
            ty,
            bounded_len: false,
        }
    }

    /// Returns the variable name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the variable's TrustVc type.
    #[must_use]
    pub fn ty(&self) -> &crate::ir::TrustVcType {
        &self.ty
    }

    /// Returns whether this variable's length is `usize`-bounded (exec
    /// `Vec`/slice/array origin). See [`Self::bounded_len`].
    #[must_use]
    pub(crate) fn bounded_len(&self) -> bool {
        self.bounded_len
    }
}

impl VerificationContext {
    /// Creates an empty verification context with default configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a context from pre-built variable declarations and proof obligations.
    pub fn from_parts(variables: Vec<VariableDecl>, obligations: Vec<ProofObligation>) -> Self {
        let mut context = Self {
            obligations,
            ..Self::default()
        };
        for variable in variables {
            // Preserve the Vec/slice/array length-boundedness bit through the
            // declaration path — dropping it would silently un-bound a Vec.
            context.declare_var_typed_bounded(&variable.name, variable.ty, variable.bounded_len);
        }
        context
    }

    /// Creates a context from pre-built variable declarations and typed proof
    /// obligations.
    pub fn from_typed_parts(
        variables: Vec<VariableDecl>,
        obligations: Vec<TypedProofObligation>,
    ) -> Self {
        Self::from_parts(
            variables,
            obligations
                .into_iter()
                .map(TypedProofObligation::into_proof_obligation)
                .collect(),
        )
    }

    /// Returns the list of proof obligations registered in this context.
    #[must_use = "obligations should be inspected or iterated, not discarded"]
    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    /// The non-fatal verifier warnings raised while extracting this unit.
    #[must_use]
    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }

    /// Records a non-fatal verifier warning (idempotent per distinct message and
    /// position — Verus emits one warning per offending expression).
    pub(crate) fn push_warning(&mut self, message: impl Into<String>) {
        self.warnings.push(message.into());
    }

    /// Returns the declared verification variables.
    #[must_use]
    pub fn variables(&self) -> &[VariableDecl] {
        &self.variables
    }

    /// Returns the function context, if one has been set.
    #[must_use]
    pub fn function_context(&self) -> Option<&FunctionContext> {
        self.function_context.as_ref()
    }

    /// Returns the current verification mode (body-level or call-site).
    #[must_use]
    pub fn verification_mode(&self) -> VerificationMode {
        self.verification_mode
    }

    /// Returns the arithmetic overflow checking policy.
    #[must_use]
    pub fn overflow_behavior(&self) -> OverflowBehavior {
        self.overflow_behavior
    }

    /// Backward-compatible accessor: true when overflow assertions are enabled.
    #[must_use]
    pub fn check_overflow(&self) -> bool {
        self.overflow_behavior.should_check()
    }

    /// Returns the division-by-zero checking policy.
    #[must_use]
    pub fn div0_behavior(&self) -> Div0Behavior {
        self.div0_behavior
    }

    /// Returns the bitshift bounds checking policy.
    #[must_use]
    pub fn bitshift_behavior(&self) -> BitshiftBehavior {
        self.bitshift_behavior
    }

    /// Returns the demand-driven inline retry configuration.
    #[must_use]
    pub fn demand_inline_config(&self) -> DemandInlineConfig {
        self.demand_inline
    }

    /// Returns the broadcast lemma groups enabled for this context.
    #[must_use]
    pub fn broadcast_use_groups(&self) -> &[String] {
        &self.broadcast_use_groups
    }

    /// Returns the scoped obligation map for `assert_by` proof blocks.
    #[must_use]
    pub fn assert_by_scopes(&self) -> &HashMap<String, Vec<ProofObligation>> {
        &self.assert_by_scopes
    }

    /// Returns the per-loop-invariant ENTRY assumption map (base-case scoped).
    #[must_use]
    pub fn loop_entry_scopes(&self) -> &HashMap<String, Vec<ProofObligation>> {
        &self.loop_entry_scopes
    }

    /// Returns the bound variable declarations scoped to `assert_forall_by` obligations.
    #[must_use]
    pub fn forall_bound_vars(&self) -> &HashMap<String, Vec<VariableDecl>> {
        &self.forall_bound_vars
    }

    /// Returns the loop guard conditions keyed by invariant name.
    #[must_use]
    pub fn loop_guards(&self) -> &HashMap<String, String> {
        &self.loop_guards
    }

    /// Returns the variables modified by each loop, keyed by invariant name.
    #[must_use]
    pub fn loop_modified_vars(&self) -> &HashMap<String, Vec<String>> {
        &self.loop_modified_vars
    }

    /// Resolves how `recv.method(..)` takes its `self` receiver, given the
    /// receiver's base struct/enum type name. `None` means the signature is not
    /// in scope (UNKNOWN — callers fail closed). The user-struct analog of the
    /// collection-mutator detection (#62/#63).
    pub(crate) fn struct_self_receiver_kind(
        &self,
        self_type: &str,
        method: &str,
    ) -> Option<SelfReceiverKind> {
        self.struct_self_receiver_kinds
            .get(&(self_type.to_string(), method.to_string()))
            .copied()
    }

    /// Clones the file-wide impl-method `self`-receiver-kind registry, so the
    /// loop modified-var collector (which runs as a standalone visitor) can
    /// resolve struct receiver-method mutability without borrowing the context.
    pub(crate) fn struct_self_receiver_kinds_clone(
        &self,
    ) -> HashMap<(String, String), SelfReceiverKind> {
        self.struct_self_receiver_kinds.clone()
    }

    /// Returns the loop-body transitions keyed by invariant name. Each value
    /// maps a modified variable to the scoped-value string for its post-body
    /// value over loop-head variables. Part of M4 loop-body transition.
    #[must_use]
    pub fn loop_body_transitions(&self) -> &HashMap<String, Vec<(String, String)>> {
        &self.loop_body_transitions
    }

    /// Returns the string-typed helper function declarations (deprecated path).
    #[must_use]
    pub fn helper_functions(&self) -> &HashMap<String, String> {
        &self.helper_functions
    }

    /// Returns the registered trait declarations.
    #[must_use]
    pub fn trait_decls(&self) -> &[TraitDecl] {
        &self.trait_decls
    }

    /// Returns the registered trait implementation declarations.
    #[must_use]
    pub fn trait_impl_decls(&self) -> &[TraitImplDecl] {
        &self.trait_impl_decls
    }

    /// Appends a proof obligation to this context.
    pub fn push_obligation(&mut self, obligation: ProofObligation) {
        self.obligations.push(obligation);
    }

    /// An ISOLATED child context for a spec-carrying closure's DEF-SIDE check.
    ///
    /// Clones this context's ambient axiom environment — declared variables and
    /// sorts, struct/trait/spec registrations, type invariants, broadcast
    /// groups, mode/overflow settings — but DROPS every parent PROOF obligation
    /// (`obligations`, `assert_by_scopes`) and warnings, and clears any recorded
    /// closure failure. The result is a fresh assumption/assertion vector: the
    /// closure's `R`, `res == BODY`, and `E` are pushed here and discharged as
    /// an independent VC (`R ∧ (res == BODY) ⊢ E`), and this child is DISCARDED
    /// afterward — it is never merged back, so no closure hypothesis can reach
    /// the parent's straight-line context. See `closure_def_side_failure`.
    pub(crate) fn isolated_closure_child(&self) -> Self {
        let mut child = self.clone();
        child.obligations.clear();
        child.assert_by_scopes.clear();
        child.warnings.clear();
        child.closure_def_side_failure = None;
        child
    }

    /// Record a closure DEF-SIDE check's non-verifying verdict so [`Self::verify`]
    /// surfaces it as this function's result. First failure wins — a later
    /// closure never overwrites an earlier failure. Only ever called with a
    /// non-`Verified` result. See `closure_def_side_failure`.
    pub(crate) fn record_closure_def_side_failure(&mut self, result: crate::VerifyResult) {
        if self.closure_def_side_failure.is_none() {
            self.closure_def_side_failure = Some(result);
        }
    }

    /// Appends a typed proof obligation to this context.
    pub fn push_typed_obligation(&mut self, obligation: TypedProofObligation) {
        self.obligations.push(obligation.into_proof_obligation());
    }

    /// Sets the verification mode (body-level or call-site).
    pub fn set_verification_mode(&mut self, mode: VerificationMode) {
        self.verification_mode = mode;
    }

    /// Enables overflow, division-by-zero, and bitshift checking (all set to Error).
    pub fn enable_overflow_checks(&mut self) {
        self.set_overflow_behavior(OverflowBehavior::Error);
        self.set_div0_behavior(Div0Behavior::Error);
        self.set_bitshift_behavior(BitshiftBehavior::Error);
    }

    /// Set the overflow behavior explicitly. Part of #2516.
    pub fn set_overflow_behavior(&mut self, behavior: OverflowBehavior) {
        self.overflow_behavior = behavior;
        self.overflow_behavior_explicit = true;
    }

    /// Set the division-by-zero behavior explicitly. Part of #2516.
    pub fn set_div0_behavior(&mut self, behavior: Div0Behavior) {
        self.div0_behavior = behavior;
        self.div0_behavior_explicit = true;
    }

    /// Set the shift bounds behavior explicitly. Part of #2516.
    pub fn set_bitshift_behavior(&mut self, behavior: BitshiftBehavior) {
        self.bitshift_behavior = behavior;
        self.bitshift_behavior_explicit = true;
    }

    /// Builder variant of `enable_overflow_checks`.
    pub fn with_overflow_checks(mut self) -> Self {
        self.enable_overflow_checks();
        self
    }

    /// Configure all arithmetic checking behaviors from the function's mode.
    /// Exec → Error, Proof/Spec → Allow. Part of #2516.
    pub fn with_mode_overflow(mut self, mode: crate::mode::FunctionMode) -> Self {
        self.set_overflow_behavior(OverflowBehavior::from_mode(mode));
        self.set_div0_behavior(Div0Behavior::from_mode(mode));
        self.set_bitshift_behavior(BitshiftBehavior::from_mode(mode));
        self
    }

    /// Builder variant that sets verification mode to `CallSite`.
    pub fn with_call_site_mode(mut self) -> Self {
        self.set_verification_mode(VerificationMode::CallSite);
        self
    }

    /// Adds a broadcast lemma group name, deduplicating if already present.
    pub fn add_broadcast_use_group(&mut self, group: impl Into<String>) {
        let group = group.into();
        if !self.broadcast_use_groups.contains(&group) {
            self.broadcast_use_groups.push(group);
        }
    }

    /// Hides a function's defining body axiom for this proof (Verus `hide(f)`).
    ///
    /// The function becomes strictly uninterpreted for the query — exactly like
    /// an unrevealed `#[trust_vc::opaque]` fn — unless the same proof also
    /// `reveal!`s it (reveal wins over hide). Called by the expanded `hide!()`
    /// macro via `verify_macro::push_hide`.
    pub fn hide_function(&mut self, name: impl Into<String>) {
        self.hidden_fns.insert(name.into());
    }

    /// Returns the function names hidden via `hide!` in this proof.
    #[must_use]
    pub fn hidden_fns(&self) -> &HashSet<String> {
        &self.hidden_fns
    }

    /// Adds an assertion obligation (deprecated, use `push_obligation`).
    #[deprecated(
        since = "0.1.0",
        note = "use push_obligation(ProofObligation::assert(...))"
    )]
    pub fn add_assert(&mut self, name: &str, condition: &str) {
        self.push_assert(name, condition);
    }

    /// Pushes an assertion obligation without requiring callers to assemble
    /// the `ProofObligation` directly.
    pub fn push_assert(&mut self, name: &str, condition: &str) {
        self.obligations
            .push(ProofObligation::assert(name, condition));
    }

    /// Adds an assumption obligation (deprecated, use `push_obligation`).
    #[deprecated(
        since = "0.1.0",
        note = "use push_obligation(ProofObligation::assume(...))"
    )]
    pub fn add_assume(&mut self, name: &str, condition: &str) {
        self.push_assume(name, condition);
    }

    /// Pushes an assumption obligation without requiring callers to assemble
    /// the `ProofObligation` directly.
    pub fn push_assume(&mut self, name: &str, condition: &str) {
        self.obligations
            .push(ProofObligation::assume(name, condition));
    }
}
