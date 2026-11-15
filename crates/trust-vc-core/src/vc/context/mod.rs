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
use crate::solver_budget::ConflictBudget;
use std::collections::{BTreeSet, HashMap, HashSet};

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
/// - `ValueMutRef` (by-value `self` of an `impl .. for &mut T`): the receiver
///   IS the `&mut T`, so the call mutably reborrows the CALLER's binding
///   exactly like `&mut self` does — but the body extractor POISONS the binding
///   instead of havocking it (review round 2: the havoc REFUTED runtime-true
///   claims about untouched fields, results and postconditions — `s.peek();
///   assert!(s.a == 5u64)` — that HEAD verified; the poison fails them closed
///   as `unresolved variable`). It counts as a mutation for every fail-closed
///   classification (`struct_method_mutates_caller`, the value-lane effect
///   scanner, the `&mut`-struct postcondition reject); the loop / branch
///   modified-set collector leaves it OUT of the modified set, so the region
///   exit re-poisons the receiver (a branch) or refuses the loop instead of
///   framing a havoc that would refute a true claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SelfReceiverKind {
    RefMut,
    Ref,
    Value,
    ValueMutRef,
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

    /// Returns just the parameter NAMES.
    ///
    /// Used by encoder setup to tell a parameter (a value the CALLER built, so
    /// its type invariant may be assumed) from a local (a value this function
    /// built, whose invariant nothing has established).
    pub fn param_names(&self) -> impl Iterator<Item = &str> {
        self.params.iter().map(|(name, _)| name.as_str())
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
    /// ROUND 6 — the exec-container-vs-spec-collection provenance of each
    /// declared variable's ORIGIN SYN SPELLING, recorded at the parameter-typing
    /// seam and nowhere else. See [`CollectionOrigin`].
    ///
    /// Kept as a SIDE TABLE rather than a `VariableDecl` field deliberately: a
    /// missing entry and [`CollectionOrigin::Unknown`] mean the same thing — no
    /// provenance was observed, fail closed — so every `VariableDecl` built
    /// outside the seam (hundreds of them, almost all in tests) keeps meaning
    /// exactly what it meant before, and no construction site can silently
    /// assert a provenance it never measured.
    collection_origins: HashMap<String, CollectionOrigin>,
    /// ROUND 7 — the SAME provenance for a STRUCT FIELD, keyed by
    /// (carrier datatype name, field name) and recorded from the field's own
    /// ORIGIN SYN SPELLING when the source struct is registered
    /// (`vc_extraction::register_struct_defs`). `StructDef` records MODELED
    /// field types only, so without this table a spec `Seq<u64>` field and an
    /// exec `Vec<u64>` field are the same `TrustVcType::Seq` and nothing can
    /// tell them apart — which is how an exec `Vec<int>` FIELD bought the
    /// ghost-closure skip that the PARAMETER seam denies the identical
    /// spelling.
    ///
    /// A SIDE TABLE for the same reason [`Self::collection_origins`] is one: a
    /// missing entry and [`CollectionOrigin::Unknown`] mean the same thing — no
    /// provenance was observed, fail closed — so every `StructDef` built
    /// outside the source-struct seam (the encoder tests, `from_parts`, the IR
    /// lane) keeps meaning exactly what it meant before, and no construction
    /// site can assert a provenance it never measured.
    struct_field_collection_origins: HashMap<(String, String), CollectionOrigin>,
    /// ROUND 7 — the same provenance for a TUPLE COMPONENT of ONE DECLARED
    /// BINDING, keyed by (variable name, component index as written: `"0"`,
    /// `"1"`, …).
    ///
    /// Keyed by the BINDING and not by the carrier, deliberately, and this is a
    /// soundness point rather than a convenience: a tuple's carrier name is
    /// derived from its MODELED element types
    /// ([`crate::ir_expr::tuple_datatype_name`]), so `(Vec<int>, u64)` and
    /// `(Seq<int>, u64)` produce the IDENTICAL carrier name `(Seq<int>,u64)`
    /// after the collapse. A carrier-keyed entry would therefore let one
    /// spelling answer for the other — exactly the confusion this table exists
    /// to end. The binding's own parameter type string is the one place a tuple
    /// component's spelling survives.
    binding_tuple_component_origins: HashMap<(String, String), CollectionOrigin>,
    /// ROUND 10 — the spec-collection / spec-function NAMES this SOURCE FILE
    /// REDEFINES with an item of its own (`type Seq<T> = Vec<T>;`,
    /// `struct Seq { .. }`, `enum Map { .. }`, `type SpecFn = u64;`).
    ///
    /// SOUNDNESS. Every ghost reading in the closure lane keys on a BARE NAME:
    /// the spec-collection type table
    /// (`param_extract::syn_type_string_is_spec_collection`), the ghost
    /// CONSTRUCTOR path (`Seq::new(..)`) and the `SpecFn`/`FnSpec` sink. Round 9
    /// narrowed the first of those to spellings written WITH arguments, which
    /// closed a bare monomorphic alias and left every other shape open.
    /// Measured at `5106f577`, cache off, all `Verified` on bodies that ALWAYS
    /// divide by zero, each against the identical body whose only difference is
    /// the NAME: a generic alias `type Seq<T> = Vec<T>` at a parameter, at a
    /// struct FIELD and at a `let`; the same through a module re-export; a user
    /// `struct Seq` with `Seq::new()`; a monomorphic `type Seq = Vec<u64>` with
    /// `Seq::new()`; the constructor-as-SINK `Seq::build(n, |i| ..)`; and
    /// `SpecFn::new(|x| ..)` over `type SpecFn = u64`.
    ///
    /// A name an item in this file DEFINES is not the spec collection, so every
    /// one of those readings must fall through to `Unknown`/not-ghost, which
    /// fails closed into a definition-site body check. The cost is the file that
    /// defines the ghost types THEMSELVES (vstd's own `seq.rs`): there the
    /// ghost skip is refused, which is the sound direction.
    shadowed_spec_names: HashSet<String>,
    /// Variables whose Rust source type was an immutable reference erased to
    /// its referent type for verification. This lets lowering accept exactly
    /// one `*x` dereference for shared-reference parameters without making all
    /// dereferences identity.
    pub(crate) erased_shared_ref_vars: HashSet<String>,
    /// Variables whose Rust source type was `Ghost<T>` erased to `T` for SMT.
    /// This lets lowering accept `ghost.view()` as identity without making
    /// ordinary `T::view()` calls identity.
    pub(crate) erased_ghost_vars: HashSet<String>,
    /// Name of the return binding a `postcondition` obligation reads (`result`
    /// unless the contract renames it), set by function extraction before the
    /// body is walked. The body walk uses it to check every postcondition at
    /// each explicit `return`, with the returned value substituted, against
    /// only the facts established before that `return`.
    pub(crate) postcondition_result_var: Option<String>,
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
    /// Loop invariants of a loop NESTED in another loop's body (2026-09-10).
    /// Their base (entry) check must not see the function's entry facts about
    /// the vars the nested loop modifies: at a nested entry those vars hold
    /// their site value over the enclosing head (the entry scope binds it),
    /// not their function-entry value. The typed base case filters those
    /// assumptions out for the names here.
    pub(crate) loop_nested_entry_invariants: HashSet<String>,
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
    /// Which LOOP each loop-lane obligation (invariant, except-break invariant,
    /// `loop_ensures`, exit/continue-site check, measure) belongs to, keyed by
    /// obligation name (2026-09-11). An inductive step, measure step, exit
    /// check or normal-exit `loop_ensures` assumes exactly the invariants of
    /// ITS OWN loop at the pre-state — all of them, as Verus does — never
    /// another loop's (an earlier loop's invariant is not a fact at a later
    /// loop's head; assuming it there was a measured false-verify).
    pub(crate) loop_invariant_groups: HashMap<String, usize>,
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
    pub(crate) trait_impl_method_bodies:
        HashMap<crate::ir::ImplMethodKey, crate::ir::ConformanceMethodBody>,
    /// The impl method's OWN declared `#[trust_vc::ensures(..)]` postconditions,
    /// keyed by the concrete UF name (`Type__method`). Populated ONLY for
    /// non-exempt methods of a NON-external impl whose single-pure-return body
    /// was ALSO captured (`trait_impl_method_bodies`), so the conformance pass
    /// can pin `result == body` and VERIFY `body ⊨ impl_ensures` before any
    /// caller is allowed to assume the strengthened postcondition. The clauses
    /// are stored in POSITIONAL canonical form — the i-th non-receiver parameter
    /// spelled `__trust_vc_conf_arg_{i}`, the captured body's numbering — never
    /// in the impl's (or the trait's) parameter names, and a method whose clauses
    /// admit no exact rewrite is not registered at all
    /// (`canonicalize_impl_method_ensures`). Consumed by the
    /// conformance-extension (assert) and the impl-postcondition propagation
    /// axiom. Empty for impls that declare no own `ensures`. Part of the
    /// impl-ensures conformance-extension + propagation (traits_extend_ensures).
    pub(crate) trait_impl_method_ensures: HashMap<crate::ir::ImplMethodKey, Vec<String>>,
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
    /// H10: the declaration-order names of a registered helper's type and const
    /// generic parameters (lifetimes skipped). Recorded ONLY by a registration
    /// that has checked generic carriage
    /// (`spec_function_catalog::check_generic_declaration`), so the call-site
    /// check can map a multi-argument turbofish onto the carrying positions. A
    /// helper without an entry keeps the fail-closed single-argument rule, and
    /// re-declaring a helper clears its entry: a stale order can never describe
    /// a different signature.
    pub(crate) helper_generic_params: HashMap<String, Vec<String>>,
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
    /// How each TRAIT-DECLARED method takes its `self` receiver, keyed by
    /// `(declaring_trait_name, method_name)`. Populated from every `trait` item
    /// in the source file, independent of `#[trust_vc::trait_spec]`.
    ///
    /// SOUNDNESS-CRITICAL. This is the GENERIC-receiver analog of
    /// `struct_self_receiver_kinds`: a receiver whose declared type is a
    /// `TypeParam` (`fn g<T: Tr>(t: &mut T)`, or its `&mut impl Tr` sugar) has
    /// NO `Datatype`, so the struct registry can never classify `t.bump()` and
    /// the receiver was silently left intact across an `&mut self` call — the
    /// two `t.a()` reads around it collapsed to the same `Tr__a(t)` term and a
    /// FALSE claim about the difference verified. Keyed by the DECLARING trait
    /// so a supertrait method resolves through the same closure the caller-side
    /// `requires` discharge uses.
    pub(crate) trait_method_self_receiver_kinds: HashMap<(String, String), SelfReceiverKind>,
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
    /// The operator methods (`add`, `shl`, `shr`) that are the std operator on
    /// a primitive integer in this function's source file: the std trait is in
    /// scope at every call of them there. The lowering refuses any other.
    pub(crate) std_operator_methods: BTreeSet<String>,
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
    /// Per-function WALL-CLOCK backstop override, in milliseconds.
    ///
    /// This is the liveness backstop, NOT the work budget — see
    /// `rlimit_conflicts`. Set by the legacy proc-macro-path
    /// `#[trust_vc::rlimit(N)]` (whose `N` is, and stays, milliseconds —
    /// `spec_expand.rs`, #2489) and raised as a floor by
    /// `#[verifier::rlimit(N)]` so that asking for more work never yields
    /// less wall.
    pub(crate) rlimit_ms: Option<u64>,
    /// Per-function DETERMINISTIC solver work budget, in SAT conflicts.
    ///
    /// `None` means "use the calibrated default"; it does NOT mean "no
    /// budget" (`ConflictBudget::AyDefault` is the explicit spelling for
    /// declining to install one). Set by `#[verifier::rlimit(N)]`.
    pub(crate) rlimit_conflicts: Option<ConflictBudget>,
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
    /// Inconclusive authority verdict from an isolated source-spec termination
    /// check. A recursive defining axiom is never published unless that check is
    /// `Verified`; when AY computed a result but strict proof replay rejected its
    /// evidence, preserve that exact non-verifying verdict instead of discarding
    /// it and later misreporting the now-uninterpreted helper as a counterexample.
    pub(crate) source_catalog_termination_failure: Option<crate::VerifyResult>,
    /// Names of source-catalog definitions whose body axioms passed every
    /// admission gate and were actually published.  For a recursive SCC this
    /// is an unforgeable (crate-private) capability recording that the isolated
    /// `decreases` proof succeeded for the whole cycle.  Demand-inline may use
    /// it when replacing a fully ground recursive call during counterexample
    /// recovery; an authored broadcast with a body-axiom-looking name cannot
    /// manufacture this authority.
    pub(crate) source_catalog_admitted_definitions: HashSet<String>,
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
    /// Why a `Verified` answer for this context cannot be published, when one
    /// cannot. [`Self::verify`] turns a `Verified` result into an `Error`
    /// carrying this message and leaves every other result unchanged. Set by
    /// the file lane for a file whose type spellings need not denote the types
    /// extraction read (`vc_extraction::type_name_rebinding`).
    pub(crate) verified_refusal: Option<String>,
    /// The source file obligations raised in this context belong to, for
    /// DIAGNOSTIC location only.
    ///
    /// Set by the file-context lane (`verify_function_from_file` and the
    /// `cargo trust-vc` scan), which is the only lane that knows a path.
    /// Nothing about verification reads it — it is stamped onto the rendered
    /// `file:line:column` so a refuted obligation can be traced back to a line
    /// of the file the corpus runner scanned.
    pub(crate) diagnostic_source_file: Option<String>,
    /// The source position currently being extracted.
    ///
    /// The file lane raises obligations from deep inside a syn walk, far from
    /// any one place that could attach a span, so the walk parks the enclosing
    /// STATEMENT's position here and [`Self::push_obligation`] stamps it onto
    /// every obligation that does not already carry a more precise one. A
    /// statement is the right granularity because it is what the evidence
    /// gate's span reader expands from: it walks forward from the reported line
    /// until delimiter depth returns to zero, which is exactly the statement
    /// upstream Verus marks with `FAILS`.
    pub(crate) ambient_source_location: Option<crate::SourceLocation>,
}

/// What a variable's ORIGIN SYNTACTIC SPELLING says about whether a collection
/// it models is an EXEC container or a SPEC collection.
///
/// SOUNDNESS-CRITICAL, and the reason this is a TRI-state rather than a bool.
/// `Vec<u64>` and `Seq<u64>` both lower to `TrustVcType::Seq`; `BTreeSet<u64>`
/// and `Set<int>` both lower to `TrustVcType::Set`; `HashMap<u64,u64>` and
/// `Map<int,int>` both lower to `TrustVcType::Map`. After that collapse NOTHING
/// distinguishes an exec container from a spec collection, so the distinction is
/// captured HERE, from the per-binding origin type string, at the
/// parameter-typing seam — and nowhere else.
///
/// BOTH readings are POSITIVE-only. A spelling that matches neither positive
/// table is [`CollectionOrigin::Unknown`], never silently one of the other two:
/// a consumer that needs the distinction must FAIL CLOSED on `Unknown` rather
/// than guess. (Round 6: reading `Unknown` as "spec" is exactly what let an exec
/// `BTreeSet`/`HashSet`/`BTreeMap` buy the ghost-closure skip.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum CollectionOrigin {
    /// The spelling matched neither positive table. FAIL CLOSED.
    #[default]
    Unknown,
    /// An EXEC std container: `Vec`/slice/array, `VecDeque`, `BTreeSet`,
    /// `HashSet`, `BTreeMap`, `HashMap`, `BinaryHeap`, `LinkedList`.
    Exec,
    /// A SPEC collection: `Seq`, `Set`, `Map`, `Multiset`.
    Spec,
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
    ///
    /// NOTE (round 6): a `VariableDecl` carries the `bounded_len` bit but NOT the
    /// [`CollectionOrigin`] side table, so a context rebuilt this way keeps the
    /// Vec-vs-Seq reading and loses the wider exec-vs-spec one. That direction is
    /// FAIL-CLOSED by construction — an unrecorded provenance reads `Unknown`,
    /// which makes a collection receiver UNRESOLVED and its closure body CHECKED
    /// — so the cost is over-rejection, never a skip. Callers that need the
    /// provenance preserved declare through
    /// [`Self::declare_var_typed_origin`] instead (the parameter-typing seam
    /// does, and so do `body_extract`'s dummy-context copies).
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

    /// Returns the invariants whose loop is nested in another loop's body.
    #[must_use]
    pub fn loop_nested_entry_invariants(&self) -> &HashSet<String> {
        &self.loop_nested_entry_invariants
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

    /// Returns the loop group of every loop-lane obligation, keyed by name.
    #[must_use]
    pub fn loop_invariant_groups(&self) -> &HashMap<String, usize> {
        &self.loop_invariant_groups
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

    /// Borrowing view of the file-wide impl-method `self`-receiver-kind
    /// registry, for enumeration by method name.
    pub(crate) fn struct_self_receiver_kinds(
        &self,
    ) -> &HashMap<(String, String), SelfReceiverKind> {
        &self.struct_self_receiver_kinds
    }

    /// Resolves how a TRAIT-DECLARED method takes its `self` receiver.
    /// `None` means the trait/method pair is not declared in scope — callers
    /// must then leave the existing (fail-closed-at-lowering) model alone
    /// rather than invent a mutation model. See
    /// [`Self::trait_method_self_receiver_kinds`].
    pub(crate) fn trait_method_self_receiver_kind(
        &self,
        trait_name: &str,
        method: &str,
    ) -> Option<SelfReceiverKind> {
        self.trait_method_self_receiver_kinds
            .get(&(trait_name.to_string(), method.to_string()))
            .copied()
    }

    /// Clones the file-wide trait-declared `self`-receiver-kind registry, so a
    /// standalone visitor (the loop modified-var collector, the return-render
    /// lane) can classify generic-receiver mutation without borrowing.
    pub(crate) fn trait_method_self_receiver_kinds_clone(
        &self,
    ) -> HashMap<(String, String), SelfReceiverKind> {
        self.trait_method_self_receiver_kinds.clone()
    }

    /// Borrowing view of the same registry, for enumeration on a hot path (the
    /// per-loop/per-branch modified-set rebuild) where a clone would be paid
    /// once per bound.
    pub(crate) fn trait_method_self_receiver_kinds(
        &self,
    ) -> &HashMap<(String, String), SelfReceiverKind> {
        &self.trait_method_self_receiver_kinds
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
    ///
    /// Stamps the ambient source location (see `ambient_source_location`) onto
    /// obligations raised without one. An emission site that pinned its own
    /// span keeps it — `or_source_location` never overwrites.
    pub fn push_obligation(&mut self, obligation: ProofObligation) {
        self.obligations.push(self.locate_obligation(obligation));
    }

    /// Applies this context's ambient location and diagnostic file to
    /// `obligation`, leaving an already-located obligation untouched.
    pub(crate) fn locate_obligation(&self, obligation: ProofObligation) -> ProofObligation {
        // BOTH halves are required. A location of `12:5` with no file names
        // nothing a reader or the evidence gate can open, and the lanes that
        // never set a path (the proc-macro expansion, the in-crate unit tests)
        // are exactly the lanes whose spans come from rebuilt token streams.
        let (Some(ambient), Some(file)) =
            (&self.ambient_source_location, &self.diagnostic_source_file)
        else {
            return obligation;
        };
        obligation.or_source_location(ambient.clone().or_file(file))
    }

    /// Records the operator methods that are the std operator on a primitive
    /// integer in this function's source file.
    pub(crate) fn set_std_operator_methods<'a>(
        &mut self,
        methods: impl IntoIterator<Item = &'a str>,
    ) {
        self.std_operator_methods = methods.into_iter().map(str::to_string).collect();
    }

    /// Records the file obligations raised here should be located in.
    pub fn set_diagnostic_source_file(&mut self, file: impl Into<String>) {
        self.diagnostic_source_file = Some(file.into());
    }

    /// The file obligations raised here are located in, when known.
    #[must_use]
    pub fn diagnostic_source_file(&self) -> Option<&str> {
        self.diagnostic_source_file.as_deref()
    }

    /// Parks `location` as the ambient position and returns the previous one,
    /// which the caller must put back (see `AssertionCollector::visit_stmt`).
    pub fn replace_ambient_source_location(
        &mut self,
        location: Option<crate::SourceLocation>,
    ) -> Option<crate::SourceLocation> {
        std::mem::replace(&mut self.ambient_source_location, location)
    }

    /// The ambient position currently being extracted, when one is parked.
    #[must_use]
    pub fn ambient_source_location(&self) -> Option<&crate::SourceLocation> {
        self.ambient_source_location.as_ref()
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
        child.source_catalog_termination_failure = None;
        child
    }

    /// A child for discharging a `#[trust_vc::broadcast]` lemma's OWN `ensures`
    /// against its declared contract, before that `ensures` is published as a
    /// global `forall` axiom (`collect_source_broadcast_lemmas`).
    ///
    /// Sibling of [`Self::isolated_closure_child`], but deliberately NOT the same:
    /// that one clears EVERY obligation, which would also drop the definitional
    /// spec-fn body axioms (`__body_axiom_*`) the lemma's `ensures` is supposed to
    /// follow FROM. A lemma over a transparent spec fn would then be suppressed —
    /// mass over-rejection wearing the costume of a working soundness fix.
    ///
    /// So this keeps exactly the definitional axioms and drops everything else:
    ///
    /// * **Every `__source_broadcast_*` is dropped.** This is what stops a lemma
    ///   justifying ITSELF, and stops two lemmas justifying EACH OTHER. The
    ///   call-edge SCC in `ill_founded_recursive_function_names` does not cover
    ///   that: lemmas that never call one another can still prove each other
    ///   through published axioms.
    /// * **Retained definitional axioms are REVEALED** (`is_opaque = false`, and
    ///   `hidden_fns` cleared). A body axiom is a TRUE fact about the function;
    ///   opacity is an abstraction/performance control, not a soundness gate, and
    ///   Verus likewise lets a lemma body `reveal(f)` and publish the result.
    ///   Without this, every lemma over an `#[trust_vc::opaque]` spec fn is
    ///   suppressed. Measured, cache-off: an opaque fn's definitional fact is
    ///   `Counterexample` unrevealed and `Verified` revealed.
    /// * **`function_context` is cleared** so acceptance cannot depend on WHICH
    ///   target triggered extraction — a recursive target routes body axioms down
    ///   the fuel path in `setup_broadcasts`, which would otherwise let the same
    ///   lemma be accepted for one function and suppressed for another.
    ///
    /// The child is DISCARDED; only the boolean verdict crosses back.
    /// Retains only the obligations matching `keep`. Used by the session-lane
    /// broadcast suppression pass to drop lemma axioms that failed their own
    /// contract check — equivalent to never having published them.
    pub(crate) fn retain_obligations<F>(&mut self, keep: F)
    where
        F: FnMut(&ProofObligation) -> bool,
    {
        self.obligations.retain(keep);
    }

    pub(crate) fn broadcast_lemma_check_child(&self) -> Self {
        // Mirrors `encoder::verification::body_support::BODY_AXIOM_PREFIX`, which
        // is `pub(super)` to the encoder and so not nameable here.
        const BODY_AXIOM_PREFIX: &str = "__body_axiom_";

        let mut child = self.clone();
        child.assert_by_scopes.clear();
        child.warnings.clear();
        child.closure_def_side_failure = None;
        child.source_catalog_termination_failure = None;
        child.obligations.retain(|obligation| {
            obligation.kind() == crate::vc::ObligationKind::BroadcastAssume
                && obligation.name().starts_with(BODY_AXIOM_PREFIX)
        });
        for obligation in &mut child.obligations {
            obligation.is_opaque = false;
        }
        child.hidden_fns.clear();
        child.function_context = None;
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

    /// Preserve the first inconclusive isolated termination verdict. The
    /// corresponding recursive body axiom remains suppressed; this channel only
    /// prevents a later solver query from fabricating a refutation narrative for
    /// an uninterpreted helper whose definition was withheld for lack of checked
    /// proof authority.
    pub(crate) fn record_source_catalog_termination_failure(
        &mut self,
        result: crate::VerifyResult,
    ) {
        if self.source_catalog_termination_failure.is_none() {
            self.source_catalog_termination_failure = Some(result);
        }
    }

    /// Refuse a `Verified` answer for this context with `message`. The first
    /// message is kept. See `verified_refusal`.
    pub(crate) fn refuse_verified(&mut self, message: String) {
        if self.verified_refusal.is_none() {
            self.verified_refusal = Some(message);
        }
    }

    /// `result`, except that a `Verified` result becomes an `Error` when this
    /// context carries a `verified_refusal`.
    pub(crate) fn apply_verified_refusal(
        &self,
        result: crate::VerifyResult,
    ) -> crate::VerifyResult {
        match (&result, &self.verified_refusal) {
            (crate::VerifyResult::Verified, Some(message)) => crate::VerifyResult::Error {
                message: message.clone(),
            },
            _ => result,
        }
    }

    /// Records that the source catalog actually published this definition after
    /// all opacity/body/termination gates. Crate-private by design: this is proof
    /// provenance, not a public solver-tuning switch.
    pub(crate) fn record_source_catalog_admitted_definition(&mut self, name: impl Into<String>) {
        self.source_catalog_admitted_definitions.insert(name.into());
    }

    /// Appends a typed proof obligation to this context.
    ///
    /// Same ambient-location stamp as [`Self::push_obligation`] — a typed
    /// obligation is no less a statement of the body than a string one.
    pub fn push_typed_obligation(&mut self, obligation: TypedProofObligation) {
        self.push_obligation(obligation.into_proof_obligation());
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
        self.push_obligation(ProofObligation::assert(name, condition));
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
        self.push_obligation(ProofObligation::assume(name, condition));
    }

    /// Canonical, SOLVER-INPUT-COMPLETE cache key for this context.
    ///
    /// Used by the isolated per-edge `decreases` memo
    /// (`spec_function_catalog::verify_isolated_termination_query`), which
    /// discharges a freshly-built `VerificationContext::new()` and reuses the
    /// verdict for a byte-identical repeat. Rendered from the BUILT context, so
    /// it is a same-input/same-output memo key, never a verdict reused across
    /// contexts.
    ///
    /// COMPLETE BY CONSTRUCTION, NOT BY AUDIT (amendment, 2026-08-25). The
    /// destructure below is EXHAUSTIVE and carries NO `..` rest pattern, and
    /// every bound field is rendered. Two consequences, both deliberate:
    ///
    /// * adding a field to `VerificationContext` BREAKS THE BUILD here until
    ///   someone decides how it is keyed — it cannot silently escape the key and
    ///   turn the memo into cross-context verdict reuse (the cardinal
    ///   direction). This is the `DemandInlineConfig::cache_key_parts` rule
    ///   ("adding a policy field must force callers to decide whether it changes
    ///   verification semantics") applied to the whole context;
    /// * a NEW MUTATOR added to a caller — a `register_struct_type`, a
    ///   `source_type_aliases` entry, an `overflow_behavior` — needs no
    ///   follow-up at all: the field it writes is already in the key, so two
    ///   semantically different queries separate instead of colliding.
    ///
    /// `Debug` is used deliberately rather than hand-written renderings: it is
    /// derived throughout, so a field added to `VariableDecl` / `ProofObligation`
    /// / `TrustVcType` enters the key automatically. Hash-ordered containers are
    /// rendered through the local `render_sorted`, which sorts the per-ENTRY renderings,
    /// so `HashMap`/`HashSet` iteration order cannot make an identical context
    /// miss its own entry. A rendering that is nonetheless unstable could only
    /// ever cause a MISS (a fresh solve) — never a false hit, since a hit
    /// requires string equality of the whole 50-field rendering.
    ///
    /// Field separators are `U+0001`, which Rust's `Debug` for `str` escapes as
    /// the six characters `\u{1}`, so no separator can be injected from source
    /// text.
    ///
    /// TARGET POINTER WIDTH is part of the key (SOUNDNESS-CRITICAL) even though
    /// it is not a field. `crate::ir::pointer_width()` is a THREAD-LOCAL
    /// override read at ENCODE time — `encoder::types` builds a `Seq`'s index
    /// sort as `Sort::bitvec(pointer_width())` — so two contexts whose
    /// `TrustVcType`s render IDENTICALLY still produce different solver queries
    /// at 32 and 64 bits, and the dual-width lane runs the same unit at both.
    /// Without this component a `Proven` established at 64 bits could be served
    /// to the 32-bit pass, admitting a body axiom whose measure does not
    /// actually shrink there.
    #[must_use]
    pub(crate) fn isolated_query_key(&self) -> String {
        use std::fmt::Write as _;

        // EXHAUSTIVE — no `..`. See the doc comment above: a new field must
        // break this line, not slip past it.
        let Self {
            obligations,
            warnings,
            variables,
            variable_index,
            collection_origins,
            struct_field_collection_origins,
            binding_tuple_component_origins,
            shadowed_spec_names,
            erased_shared_ref_vars,
            erased_ghost_vars,
            function_context,
            verification_mode,
            overflow_behavior,
            div0_behavior,
            bitshift_behavior,
            overflow_behavior_explicit,
            div0_behavior_explicit,
            bitshift_behavior_explicit,
            broadcast_use_groups,
            hidden_fns,
            assert_by_scopes,
            loop_entry_scopes,
            loop_nested_entry_invariants,
            forall_bound_vars,
            prophecy_bindings,
            source_type_aliases,
            loop_guards,
            loop_modified_vars,
            loop_invariant_groups,
            loop_body_transitions,
            helper_functions,
            trait_decls,
            trait_impl_decls,
            trait_impl_method_bodies,
            trait_impl_method_ensures,
            conformance_exempt_methods,
            helper_functions_typed,
            helper_generic_params,
            inherent_methods,
            struct_self_receiver_kinds,
            trait_method_self_receiver_kinds,
            struct_types,
            derived_partial_eq_types,
            derived_clone_types,
            manual_partial_eq_types,
            std_operator_methods,
            type_invariants,
            invariant_mask,
            tracked_params,
            rlimit_ms,
            rlimit_conflicts,
            demand_inline,
            counterexample_var_meta,
            duplicate_var_error,
            generic_instantiation_conflict,
            source_catalog_termination_failure,
            source_catalog_admitted_definitions,
            skip_retry_cascade,
            closure_def_side_failure,
            verified_refusal,
            diagnostic_source_file,
            ambient_source_location,
            postcondition_result_var,
        } = self;

        // DIAGNOSTIC ONLY, and deliberately absent from the key: neither names
        // a hypothesis, an obligation or a solver setting, so two contexts that
        // differ only in where their obligations were read from are the same
        // query. The obligations' own recorded locations are absent too — see
        // `unlocated_obligations` below, which strips BOTH location channels,
        // so an obligation moved to another line IS served its old verdict.
        // That is intended: the key's contract is SOLVER-INPUT-COMPLETE, and
        // the only consumer (`TERMINATION_QUERY_MEMO`) stores a location-free
        // `TerminationCheck`, so a stale location can never reach a caller.
        let _ = (diagnostic_source_file, ambient_source_location);

        /// Renders a hash-ordered container canonically: each entry is rendered
        /// with `Debug` and the resulting strings are sorted, so iteration order
        /// cannot change the key.
        fn render_sorted<T: std::fmt::Debug>(
            out: &mut String,
            label: &str,
            items: impl IntoIterator<Item = T>,
        ) {
            let mut rendered: Vec<String> =
                items.into_iter().map(|item| format!("{item:?}")).collect();
            rendered.sort_unstable();
            let _ = write!(out, "{label}={rendered:?}\u{1}");
        }

        let mut key = String::with_capacity(4096);
        // Not a field: read at ENCODE time, soundness-critical. See above.
        let _ = write!(key, "pointer_width={}\u{1}", crate::ir::pointer_width());

        // Ordered containers and scalars: `Debug` directly.
        // Rendered WITHOUT their source locations. This key's contract is
        // SOLVER-INPUT-COMPLETE (see the doc above), and a location is
        // diagnostic: two contexts whose obligations differ only in which line
        // raised them present the solver with the identical query, so they must
        // share a verdict. Leaving locations in would also have silently
        // narrowed the cache the moment the file lane started recording them —
        // every ported function would have got its own entry.
        let unlocated_obligations = obligations
            .iter()
            .map(ProofObligation::without_source_location)
            .collect::<Vec<_>>();
        let _ = write!(key, "obligations={unlocated_obligations:?}\u{1}");
        let _ = write!(key, "warnings={warnings:?}\u{1}");
        let _ = write!(key, "variables={variables:?}\u{1}");
        let _ = write!(key, "function_context={function_context:?}\u{1}");
        let _ = write!(key, "verification_mode={verification_mode:?}\u{1}");
        let _ = write!(key, "overflow_behavior={overflow_behavior:?}\u{1}");
        let _ = write!(key, "div0_behavior={div0_behavior:?}\u{1}");
        let _ = write!(key, "bitshift_behavior={bitshift_behavior:?}\u{1}");
        let _ = write!(
            key,
            "overflow_behavior_explicit={overflow_behavior_explicit:?}\u{1}"
        );
        let _ = write!(
            key,
            "div0_behavior_explicit={div0_behavior_explicit:?}\u{1}"
        );
        let _ = write!(
            key,
            "bitshift_behavior_explicit={bitshift_behavior_explicit:?}\u{1}"
        );
        let _ = write!(key, "broadcast_use_groups={broadcast_use_groups:?}\u{1}");
        let _ = write!(key, "trait_decls={trait_decls:?}\u{1}");
        let _ = write!(key, "trait_impl_decls={trait_impl_decls:?}\u{1}");
        let _ = write!(key, "struct_types={struct_types:?}\u{1}");
        let _ = write!(key, "invariant_mask={invariant_mask:?}\u{1}");
        let _ = write!(key, "rlimit_ms={rlimit_ms:?}\u{1}");
        // Semantically load-bearing, exactly like `rlimit_ms`: the conflict
        // budget decides where the solver gives up, so a verdict established
        // under one budget must not be served to a query running another.
        let _ = write!(key, "rlimit_conflicts={rlimit_conflicts:?}\u{1}");
        let _ = write!(
            key,
            "demand_inline={:?}\u{1}",
            demand_inline.cache_key_parts()
        );
        let _ = write!(key, "duplicate_var_error={duplicate_var_error:?}\u{1}");
        let _ = write!(
            key,
            "generic_instantiation_conflict={generic_instantiation_conflict:?}\u{1}"
        );
        let _ = write!(
            key,
            "source_catalog_termination_failure={source_catalog_termination_failure:?}\u{1}"
        );
        let _ = write!(key, "skip_retry_cascade={skip_retry_cascade:?}\u{1}");
        let _ = write!(
            key,
            "closure_def_side_failure={closure_def_side_failure:?}\u{1}"
        );
        let _ = write!(key, "verified_refusal={verified_refusal:?}\u{1}");
        let _ = write!(
            key,
            "postcondition_result_var={postcondition_result_var:?}\u{1}"
        );

        // Hash-ordered containers: canonicalised.
        render_sorted(&mut key, "variable_index", variable_index);
        // IN THE KEY, deliberately. `collection_origins` is read during
        // EXTRACTION rather than at encode time, so an argument could be made
        // that the obligations it produced already distinguish the two contexts.
        // It rides here anyway because it is cheap and because the failure it
        // would otherwise admit is a false `Verified`: a context whose exec
        // `BTreeSet` provenance was not yet recorded produces FEWER obligations
        // than the same context with it, and those two renderings must never
        // share a cache entry.
        render_sorted(&mut key, "collection_origins", collection_origins);
        // IN THE KEY for the same reason, and the reason is the same shape as
        // the one above: a context in which a field's provenance has NOT been
        // recorded reads that field `Unknown` and produces FEWER obligations
        // than the same context with it recorded (`Unknown` fails closed into a
        // definition-site check only where the receiver is not positively
        // ghost; where it IS recorded `Spec`, the skip applies and the check
        // disappears). A context with fewer obligations must never share a
        // cache entry with one that has more, in either direction.
        render_sorted(
            &mut key,
            "struct_field_collection_origins",
            struct_field_collection_origins,
        );
        render_sorted(
            &mut key,
            "binding_tuple_component_origins",
            binding_tuple_component_origins,
        );
        // IN THE KEY for the same reason as the three tables above, and with
        // the same direction of failure: a context that has NOT recorded this
        // file's shadowing reads `Seq<u64>` as a spec collection and produces
        // FEWER obligations (the ghost skip applies) than the same context with
        // it recorded. The two renderings must never share a cache entry.
        render_sorted(&mut key, "shadowed_spec_names", shadowed_spec_names);
        render_sorted(&mut key, "erased_shared_ref_vars", erased_shared_ref_vars);
        render_sorted(&mut key, "erased_ghost_vars", erased_ghost_vars);
        render_sorted(&mut key, "hidden_fns", hidden_fns);
        render_sorted(&mut key, "assert_by_scopes", assert_by_scopes);
        render_sorted(&mut key, "loop_entry_scopes", loop_entry_scopes);
        render_sorted(
            &mut key,
            "loop_nested_entry_invariants",
            loop_nested_entry_invariants,
        );
        render_sorted(&mut key, "forall_bound_vars", forall_bound_vars);
        render_sorted(&mut key, "prophecy_bindings", prophecy_bindings);
        render_sorted(&mut key, "source_type_aliases", source_type_aliases);
        render_sorted(&mut key, "loop_guards", loop_guards);
        render_sorted(&mut key, "loop_modified_vars", loop_modified_vars);
        render_sorted(&mut key, "loop_invariant_groups", loop_invariant_groups);
        render_sorted(&mut key, "loop_body_transitions", loop_body_transitions);
        render_sorted(&mut key, "helper_functions", helper_functions);
        render_sorted(
            &mut key,
            "trait_impl_method_bodies",
            trait_impl_method_bodies,
        );
        render_sorted(
            &mut key,
            "trait_impl_method_ensures",
            trait_impl_method_ensures,
        );
        render_sorted(
            &mut key,
            "conformance_exempt_methods",
            conformance_exempt_methods,
        );
        render_sorted(&mut key, "helper_functions_typed", helper_functions_typed);
        render_sorted(&mut key, "helper_generic_params", helper_generic_params);
        render_sorted(&mut key, "inherent_methods", inherent_methods);
        render_sorted(
            &mut key,
            "struct_self_receiver_kinds",
            struct_self_receiver_kinds,
        );
        render_sorted(
            &mut key,
            "trait_method_self_receiver_kinds",
            trait_method_self_receiver_kinds,
        );
        render_sorted(
            &mut key,
            "derived_partial_eq_types",
            derived_partial_eq_types,
        );
        render_sorted(&mut key, "derived_clone_types", derived_clone_types);
        render_sorted(&mut key, "manual_partial_eq_types", manual_partial_eq_types);
        render_sorted(&mut key, "std_operator_methods", std_operator_methods);
        render_sorted(&mut key, "type_invariants", type_invariants);
        render_sorted(&mut key, "tracked_params", tracked_params);
        render_sorted(&mut key, "counterexample_var_meta", counterexample_var_meta);
        render_sorted(
            &mut key,
            "source_catalog_admitted_definitions",
            source_catalog_admitted_definitions,
        );
        key
    }
}
