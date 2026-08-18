//! Prepared verification context for typed-condition execution.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides the preparation boundary between string-based
//! `VerificationContext` and the typed verification pipeline. `prepare_context`
//! parses and lowers all obligation conditions to `TrustVcExpr`, producing a
//! `PreparedVerificationContext` that the encoder operates on directly.

use std::collections::{HashMap, HashSet};

#[cfg(test)]
use self::expr_repair::fix_fn_call_return_types;
pub(crate) use self::obligation::{PreparedObligation, PreparedTrigger};
pub(crate) use self::type_env::build_type_env;

use crate::counterexample_names::CounterexampleVarMeta;
use crate::error::TrustVcError;
use crate::ir::{StructDef, TraitDecl, TraitImplDecl, TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};
use crate::ir_lowering::TypeEnv;
use crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX;
use crate::vc::{
    BitshiftBehavior, DemandInlineConfig, Div0Behavior, FunctionContext, InvariantMask,
    ObligationKind, OverflowBehavior, VariableDecl, VerificationContext, VerificationMode,
};

mod expr_repair;
mod obligation;
mod type_env;
pub(crate) mod validation;

#[derive(Debug, Clone, Default)]
pub(crate) struct PreparedVerificationContext {
    pub obligations: Vec<PreparedObligation>,
    pub variables: Vec<VariableDecl>,
    pub function_context: Option<FunctionContext>,
    pub trait_decls: Vec<TraitDecl>,
    pub trait_impl_decls: Vec<TraitImplDecl>,
    /// Captured single-pure-return bodies of trait-impl methods, keyed by the
    /// concrete UF name (`Type__method`). Threaded from `VerificationContext` so
    /// the auxiliary conformance pass can bind an impl method's result to its
    /// actual body even when the verified function never references it. Part of
    /// the trait-conformance generic-result over-rejection fix.
    pub trait_impl_method_bodies: HashMap<String, crate::ir::ConformanceMethodBody>,
    /// Impl methods' OWN declared `ensures` postconditions, keyed by concrete UF
    /// name. Threaded from `VerificationContext`; populated only for non-exempt
    /// impl methods with a captured body. The conformance pass VERIFIES
    /// `body ⊨ impl_ensures`; the encoder propagates it to callers only after.
    pub trait_impl_method_ensures: HashMap<String, Vec<String>>,
    /// Concrete UF names of trait-impl methods the conformance pass must SKIP
    /// because they are blocked by a dedicated ill-formedness error (own
    /// `requires`, or a `returns`-on-both conflict). Threaded from
    /// `VerificationContext`. Skipping prevents a blocked impl from sinking
    /// unrelated functions; the impl is still rejected via its own error.
    pub conformance_exempt_methods: HashSet<String>,
    pub verification_mode: VerificationMode,
    pub overflow_behavior: OverflowBehavior,
    pub div0_behavior: Div0Behavior,
    pub bitshift_behavior: BitshiftBehavior,
    pub broadcast_use_groups: HashSet<String>,
    pub assert_by_scopes: HashMap<String, Vec<PreparedObligation>>,
    /// Per-loop-invariant ENTRY assumptions (loop-modified let-local pre-loop
    /// values), prepared. Passed as the base-case scoped slice so they reach only
    /// the invariant's entry check. Keyed by invariant name.
    pub loop_entry_scopes: HashMap<String, Vec<PreparedObligation>>,
    /// Functions revealed by a `reveal!(f)` INSIDE an `assert … by { .. }` proof
    /// block, keyed by the assert_by obligation name. Only entries with a
    /// non-empty set are present.
    ///
    /// SOUNDNESS-CRITICAL (#34, upstream `assert_forall_by.rs::test_assertby1_fail2`):
    /// Verus scopes a by-block's `reveal` to the block — the block's CONCLUSION
    /// persists as a fact afterwards, but `f` is opaque again for every later
    /// statement. These names are therefore deliberately NOT merged into the
    /// query-level [`Self::revealed_fns`]; the verifier unions them in only while
    /// verifying that one scope (its inner assertions and its conclusion). A leak
    /// into `revealed_fns` would expose `f`'s body to obligations Verus checks
    /// with `f` opaque — the cardinal proves-more-than-Verus direction.
    pub assert_by_scope_revealed_fns: HashMap<String, HashSet<String>>,
    /// Typed forall-by bound variables keyed by the corresponding assert_by
    /// obligation name. These are declared only while verifying that scope.
    /// Part of #2551.
    pub forall_bound_vars: HashMap<String, Vec<VariableDecl>>,
    pub loop_guards: HashMap<String, String>,
    pub loop_modified_vars: HashMap<String, Vec<String>>,
    /// Straight-line loop-body state transitions keyed by invariant name. Each
    /// value maps a loop-modified variable to the scoped-value string for its
    /// post-body value over loop-head variables. Consumed by the
    /// frame-condition inductive step (M4 loop-body transition).
    pub loop_body_transitions: HashMap<String, Vec<(String, String)>>,
    /// True when any variable or obligation in this context references
    /// collections (Seq/Set/Map). Used to widen the confirmation check gate
    /// so that non-collection assertions in mixed contexts still get
    /// double-checked against ay-dpll non-determinism. Part of #2354.
    pub has_collection_context: bool,
    /// Pre-computed set of function names from Reveal obligations.
    /// Avoids O(total_obligations) linear scan per encoder setup in
    /// `setup_from_prepared` and `add_broadcasts_for_inductive_step`.
    /// Part of #1786.
    pub revealed_fns: HashSet<String>,
    /// Function names hidden via `hide!` in this query. A hidden function's
    /// defining body axiom is suppressed (like an unrevealed opaque fn) unless
    /// the same query also `reveal!`s it — reveal wins over hide, matching the
    /// net effect of upstream Verus's flow-ordered `hide(f); …; reveal(f)`
    /// under trust-vc's query-granular reveal model. Mirrors Verus `hide(f)`
    /// (vir set_fuel `hidden` list). Session (proc-macro) path only; the file
    /// path keeps failing closed on `hide!` in `vc_extraction`.
    pub hidden_fns: HashSet<String>,
    /// Source definitions whose body axioms were admitted and published by the
    /// catalog, including termination-proven recursive SCC members.
    pub source_catalog_admitted_definitions: HashSet<String>,
    /// Typed helper function contexts for multi-function proofs.
    /// Each entry is a FunctionContext that should be registered as a ay UF
    /// in addition to the primary `function_context`. Part of #2431.
    pub helper_function_contexts: Vec<FunctionContext>,
    /// Registered struct types for struct invariant verification.
    /// Part of #2419 Slice 1.
    pub struct_types: Vec<StructDef>,
    /// Type invariant predicates for struct types. Maps type name → invariant
    /// body expression. Part of #2419 Slice 2.
    pub type_invariants: HashMap<String, TrustVcExpr>,
    /// Invariant mask specifying which namespaces this function may open.
    /// Defaults to `Any` (unrestricted). Controlled by `#[opens_invariants]`.
    /// Part of #2427 Slice 4.
    pub invariant_mask: InvariantMask,
    /// Parameters annotated with `tracked` in the proof function signature.
    /// Metadata for mode checking — tracked params carry proof-mode ownership.
    /// Part of #2427 Slice 3.
    pub tracked_params: HashSet<String>,
    /// Per-function solver timeout override in milliseconds.
    /// When `Some(ms)`, overrides the default 30,000ms solver timeout.
    /// Set by `#[trust_vc::rlimit(N)]`. Part of #2489.
    pub rlimit_ms: Option<u64>,
    /// Demand-driven body-inlining retry policy copied from the unprepared
    /// verification context. Part of #2655.
    pub demand_inline: DemandInlineConfig,
    /// Counterexample display metadata keyed by raw solver variable name.
    /// Threaded from VerificationContext for model rendering. Part of #2651.
    pub counterexample_var_meta: HashMap<String, CounterexampleVarMeta>,
    /// When true, the timeout retry cascade (int-mode + extended-timeout) is
    /// skipped. Threaded from VerificationContext. Part of #2707.
    pub skip_retry_cascade: bool,
}

impl PreparedVerificationContext {
    /// Backward-compatible accessor: true when overflow assertions are enabled.
    #[must_use]
    pub fn check_overflow(&self) -> bool {
        self.overflow_behavior.should_check()
    }
}

// All methods that were here (to_legacy_context, condition_map) have been
// removed as part of #2219 — the typed verification path operates directly
// on PreparedVerificationContext fields without legacy round-trips.

fn has_collection_context(
    variables: &[VariableDecl],
    obligations: &[PreparedObligation],
    assert_by_scopes: &HashMap<String, Vec<PreparedObligation>>,
    forall_bound_vars: &HashMap<String, Vec<VariableDecl>>,
) -> bool {
    variables.iter().any(|variable| variable.ty.is_collection())
        || forall_bound_vars
            .values()
            .flatten()
            .any(|variable| variable.ty.is_collection())
        || obligations
            .iter()
            .any(|obligation| obligation.expr.references_collection())
        || assert_by_scopes.values().any(|scope| {
            scope
                .iter()
                .any(|obligation| obligation.expr.references_collection())
        })
}

fn env_with_scoped_variables(base_env: &TypeEnv, scoped_variables: &[VariableDecl]) -> TypeEnv {
    let mut env = base_env.clone();
    for variable in scoped_variables {
        env.insert(variable.name.clone(), variable.ty.clone());
    }
    env
}

fn revealed_function_names(obligations: &[PreparedObligation]) -> HashSet<String> {
    obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, ObligationKind::Reveal))
        .map(|obligation| obligation.name.clone())
        .collect()
}

/// Per-scope `reveal!` sets collected from the obligations of each
/// `assert … by { .. }` proof block.
///
/// Kept SEPARATE from the query-level reveal set on purpose: Verus scopes a
/// by-block's reveal to that block. See
/// [`PreparedVerificationContext::assert_by_scope_revealed_fns`]. Scopes with no
/// `reveal!` are omitted so the common case allocates nothing and the verifier
/// can take its byte-identical unscoped path. Part of #34.
fn assert_by_scope_reveals(
    assert_by_scopes: &HashMap<String, Vec<PreparedObligation>>,
) -> HashMap<String, HashSet<String>> {
    assert_by_scopes
        .iter()
        .map(|(scope_name, scope)| (scope_name.clone(), revealed_function_names(scope)))
        .filter(|(_, revealed)| !revealed.is_empty())
        .collect()
}

/// Fail closed on a `hide!(f)` inside an `assert … by { .. }` proof block.
///
/// A scoped `Hide` obligation is not part of any visibility set trust-vc
/// computes (`hidden_fns` is query-level and derives from the TOP-LEVEL stream),
/// so it would be a silent no-op: `f`'s body would stay visible while verifying
/// the block, where Verus re-opaques it — proving MORE than Verus. Rejecting the
/// query is the fail-closed answer until block-scoped hiding is modeled. Part of
/// #34, layered on the #2785 interleave guard.
fn reject_hide_inside_assert_by_scope(
    assert_by_scopes: &HashMap<String, Vec<PreparedObligation>>,
) -> Result<(), crate::error::TrustVcError> {
    let mut offenders: Vec<(&str, &str)> = assert_by_scopes
        .iter()
        .flat_map(|(scope_name, scope)| {
            scope
                .iter()
                .filter(|obligation| matches!(obligation.kind, ObligationKind::Hide))
                .map(move |obligation| (scope_name.as_str(), obligation.name.as_str()))
        })
        .collect();
    offenders.sort_unstable();
    let Some((scope_name, hidden)) = offenders.first() else {
        return Ok(());
    };
    Err(crate::error::TrustVcError::Encoding {
        context: "prepare verification context",
        detail: format!(
            "hide!({hidden}) inside the proof block of `{scope_name}` is not supported: \
             trust-vc's hidden-function set is query-level, so a block-scoped hide would \
             silently do nothing and the body would stay visible where Verus re-opaques \
             it. Rejected fail-closed for soundness. Part of #34."
        ),
    })
}

/// Shared `reveal!`/`hide!` typo guard: the target must name a known function,
/// verbatim or by the trailing `::` segment of a fully-qualified cross-crate
/// spec. Without it, `reveal!(typo)` silently does nothing (#2473).
fn validate_visibility_target(
    target: &str,
    known_function_names: &HashSet<String>,
    macro_name: &str,
) -> Result<(), crate::error::TrustVcError> {
    let matches_known = known_function_names.contains(target)
        || known_function_names.iter().any(|known| {
            known
                .rsplit_once("::")
                .is_some_and(|(_, leaf)| leaf == target)
        });
    if matches_known {
        return Ok(());
    }
    let mut available: Vec<_> = known_function_names.iter().cloned().collect();
    available.sort();
    Err(crate::error::TrustVcError::Encoding {
        context: "prepare verification context",
        detail: format!(
            "{macro_name}!({target}) references unknown function. \
             Available functions: [{}]",
            available.join(", "),
        ),
    })
}

/// Function names hidden via `hide!` obligations carried in the stream (file
/// path). Mirrors [`revealed_function_names`] for the `Hide` kind so the
/// query-granular `hidden_fns` set is populated identically to how the
/// session (proc-macro) path populates `ctx.hidden_fns` via `hide_function`.
/// Part of #2785.
fn hidden_function_names(obligations: &[PreparedObligation]) -> HashSet<String> {
    obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, ObligationKind::Hide))
        .map(|obligation| obligation.name.clone())
        .collect()
}

/// True for obligation kinds that Verus DISCHARGES (proves), as opposed to
/// assumes or treats as metadata. Used by the `hide!`/`reveal!` interleave
/// guard: only a checked obligation positioned inside a Verus-hidden window can
/// prove more than Verus. Conservative (the complement — assumptions/metadata):
/// over-classifying a kind as "checked" only ever fails the guard closed, which
/// is sound. Part of #2785.
fn is_checked_proof_obligation(kind: ObligationKind) -> bool {
    !matches!(
        kind,
        ObligationKind::Assume
            | ObligationKind::PostLoopAssume
            | ObligationKind::BroadcastAssume
            | ObligationKind::LoopGuard
            | ObligationKind::Reveal
            | ObligationKind::Hide
            | ObligationKind::BroadcastUse
            | ObligationKind::InvariantOpen
    )
}

/// Fail closed on the one `hide!`/`reveal!` interleave the query-granular
/// visibility model cannot represent soundly.
///
/// trust-vc models reveal/hide as query-level sets (`revealed_fns`/`hidden_fns`)
/// with reveal winning over hide — NOT flow-ordered fuel like Verus. That is
/// verdict-equivalent EXCEPT when a checked proof obligation sits at a program
/// point where Verus has `f` re-opaqued (textually after a `hide!(f)` and
/// before the next `reveal!(f)`) while `f` is ALSO revealed somewhere in the
/// query (so the reveal-wins set still exposes `f`'s body at that earlier
/// point). Verifying such an obligation with `f`'s body visible proves MORE
/// than Verus (which checks it with `f` hidden) — the cardinal
/// proves-more-than-Verus direction. We reject those queries fail-closed.
///
/// The complementary cases stay sound WITHOUT a guard: a `hide!(f)` with NO
/// reveal anywhere hides `f` for the whole query (proves LESS = sound
/// incompleteness); a checked obligation BEFORE a `hide!(f)`, or AFTER the
/// closing `reveal!(f)`, sees `f` visible in both models. Obligations are in
/// body order (built by `prepare` from `ctx.obligations`), so a linear scan
/// with the closing-reveal lookup is exact. Part of #2785.
fn reject_unsound_hide_reveal_interleave(
    obligations: &[PreparedObligation],
) -> Result<(), crate::error::TrustVcError> {
    let revealed: HashSet<&str> = obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Reveal))
        .map(|o| o.name.as_str())
        .collect();
    // No reveal anywhere ⇒ every hidden fn stays hidden query-wide ⇒ the model
    // only ever proves LESS ⇒ sound, nothing to reject.
    if revealed.is_empty() {
        return Ok(());
    }

    for (hide_idx, hide) in obligations.iter().enumerate() {
        if !matches!(hide.kind, ObligationKind::Hide) {
            continue;
        }
        // A `hide!(f)` that is never revealed keeps `f` hidden query-wide
        // (proves LESS) — sound, no window.
        if !revealed.contains(hide.name.as_str()) {
            continue;
        }
        // Verus re-opaques `f` from this `hide!(f)` until the NEXT `reveal!(f)`
        // (or end of body if none follows — the reveal is earlier, but
        // reveal-wins still exposes `f` here, so the window runs to the end).
        let close = obligations
            .iter()
            .enumerate()
            .skip(hide_idx + 1)
            .find(|(_, o)| matches!(o.kind, ObligationKind::Reveal) && o.name == hide.name)
            .map_or(obligations.len(), |(idx, _)| idx);
        let brackets_checked = obligations[hide_idx..close]
            .iter()
            .any(|o| is_checked_proof_obligation(o.kind));
        if brackets_checked {
            return Err(crate::error::TrustVcError::Encoding {
                context: "prepare verification context",
                detail: format!(
                    "hide!({name}) brackets a checked proof obligation before its \
                     reveal!({name}): trust-vc's query-granular reveal model would \
                     expose {name}'s body at that obligation, proving more than \
                     Verus's flow-ordered fuel. Rejected fail-closed for soundness. \
                     Part of #2785.",
                    name = hide.name,
                ),
            });
        }
    }
    Ok(())
}

fn build_helper_function_contexts(ctx: &VerificationContext) -> Vec<FunctionContext> {
    let primary_fn_name = ctx.function_context.as_ref().map(|fc| fc.name.as_str());

    ctx.helper_functions_typed
        .iter()
        .filter(|(name, _)| Some(name.as_str()) != primary_fn_name)
        .map(|(name, (return_ty, params, bounds))| FunctionContext {
            name: name.clone(),
            params: params.clone(),
            return_type: return_ty.clone(),
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: bounds.clone(),
        })
        .collect()
}

#[derive(Default)]
struct CollectionConstructorCollector {
    constructors: HashMap<String, crate::ir::TrustVcType>,
}

impl TrustVcExprVisitor for CollectionConstructorCollector {
    fn visit_expr(&mut self, expr: &TrustVcExpr) {
        if let TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } = expr
        {
            if args.is_empty() && name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX) {
                self.constructors
                    .entry(name.clone())
                    .or_insert_with(|| return_ty.clone());
            }
        }

        walk_expr(self, expr);
    }
}

fn collect_collection_constructor_contexts(
    obligations: &[PreparedObligation],
    assert_by_scopes: &HashMap<String, Vec<PreparedObligation>>,
    known_function_names: &HashSet<String>,
) -> Vec<FunctionContext> {
    let mut collector = CollectionConstructorCollector::default();
    for obligation in obligations {
        collector.visit_expr(&obligation.expr);
    }
    for scoped_obligations in assert_by_scopes.values() {
        for obligation in scoped_obligations {
            collector.visit_expr(&obligation.expr);
        }
    }

    let mut contexts: Vec<_> = collector
        .constructors
        .into_iter()
        .filter(|(name, _)| !known_function_names.contains(name))
        .map(|(name, return_type)| FunctionContext {
            name,
            params: vec![],
            return_type,
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        })
        .collect();
    contexts.sort_by_key(|context| context.name.clone());
    contexts
}

/// Re-resolve an `Opaque` trait-impl concrete type against the registered
/// source struct definitions so it becomes a `Datatype` carrying an ay sort.
///
/// The proc-macro `parse_trait_impl_decl` resolves the impl's `self` type
/// WITHOUT the `SourceStructRegistry`, so a user struct (`impl T for Counter`,
/// `struct Counter;`) reaches the prepared context as `Opaque("Counter")` even
/// though the struct IS registered in `struct_types`. Left opaque, every
/// downstream consumer (`synthesize_impl_method_contexts`, the setup linking
/// axioms, and `verify_trait_conformance`) silently SKIPS the impl via
/// `contains_opaque()`, which means trait-impl conformance is never checked for
/// user-struct concrete types — unlike Verus, which checks conformance for
/// every impl. Resolving to the registered `Datatype` (whose `to_type_string()`
/// is identical to the `Opaque` name, so receiver-keyed metadata is unchanged)
/// lets conformance actually RUN and discharge. Faithfulness fix layered on
/// #2425.
fn resolve_trait_impl_concrete_types(
    impl_decls: &[TraitImplDecl],
    struct_types: &[StructDef],
) -> Vec<TraitImplDecl> {
    impl_decls
        .iter()
        .map(|impl_decl| {
            // Resolve a struct self type whether it arrived as `Opaque("S")` or as
            // `TypeParam("S")` — a single-uppercase struct name (`impl T for S`) is
            // heuristically classified `TypeParam` at macro-expand time (no struct
            // registry there), so BOTH forms name the same concrete struct. A
            // genuine blanket-impl type param (`impl<A> T for A`) has a name absent
            // from `struct_types`, so it falls through unchanged (fail-closed).
            let (TrustVcType::Opaque(name) | TrustVcType::TypeParam(name)) =
                &impl_decl.concrete_type
            else {
                return impl_decl.clone();
            };
            let Some(struct_def) = struct_types.iter().find(|def| &def.name == name) else {
                return impl_decl.clone();
            };
            let datatype = struct_def.to_datatype_type();
            // Only resolve to a fully concrete datatype (no opaque field types);
            // otherwise the encoder still has no ay sort and we must keep the
            // impl on the skip path to fail closed rather than encode garbage.
            if datatype.contains_opaque() {
                return impl_decl.clone();
            }
            let mut resolved = impl_decl.clone();
            resolved.concrete_type = datatype;
            resolved
        })
        .collect()
}

/// Synthesize FunctionContext entries for concrete impl methods referenced
/// by TraitImplDecl.method_bindings. These must be registered as ay UFs
/// before register_trait_impl can emit linking axioms. Part of #2425.
fn synthesize_impl_method_contexts(
    ctx: &VerificationContext,
    impl_decls: &[TraitImplDecl],
) -> Vec<FunctionContext> {
    let primary_fn_name = ctx.function_context.as_ref().map(|fc| fc.name.as_str());
    let mut seen = HashSet::new();
    let mut contexts = Vec::new();
    for impl_decl in impl_decls {
        // Skip impls with Opaque concrete types — no ay sort for the self
        // param. Matches the guard in setup_from_prepared. Part of #2425.
        if impl_decl.concrete_type.contains_opaque() {
            continue;
        }
        let trait_decl = ctx
            .trait_decls
            .iter()
            .find(|td| td.name == impl_decl.trait_name);
        let Some(trait_decl) = trait_decl else {
            continue;
        };

        for (trait_method_name, concrete_fn_name) in &impl_decl.method_bindings {
            // Skip if already registered in helper_functions_typed.
            if ctx.helper_functions_typed.contains_key(concrete_fn_name) {
                continue;
            }
            // Skip if same name as primary function (matches build_helper_function_contexts).
            if Some(concrete_fn_name.as_str()) == primary_fn_name {
                continue;
            }
            // Skip if already synthesized (multiple impls can bind the same fn).
            if !seen.insert(concrete_fn_name.clone()) {
                continue;
            }
            let Some(method) = trait_decl
                .methods
                .iter()
                .find(|m| m.name == *trait_method_name)
            else {
                continue;
            };

            // Instantiate a parameterized trait's type params at the impl's
            // trait type args (`impl T<u64> for S` → `A := u64`): this context
            // stands for the CONCRETE impl method, whose written signature is
            // the instantiated one. Substitution only for a full arity match
            // with fully-concrete args; otherwise declared types remain and
            // fail closed downstream (mirrors `ContractBindings::new`).
            let generic_bindings: Vec<(String, crate::ir::TrustVcType)> =
                if !trait_decl.generics.is_empty()
                    && trait_decl.generics.len() == impl_decl.trait_type_args.len()
                    && impl_decl
                        .trait_type_args
                        .iter()
                        .all(crate::trait_instantiation::is_fully_concrete)
                {
                    trait_decl
                        .generics
                        .iter()
                        .cloned()
                        .zip(impl_decl.trait_type_args.iter().cloned())
                        .collect()
                } else {
                    Vec::new()
                };
            let bind_ty = |ty: &crate::ir::TrustVcType| {
                crate::ir_lowering::substitute_type_params(
                    &impl_decl.resolve_assoc_projections(ty),
                    &generic_bindings,
                )
            };

            let mut params = Vec::with_capacity(method.params.len() + 1);
            params.push(("self".to_string(), impl_decl.concrete_type.clone()));
            // Normalize `Self::X` associated-type projections in the trait
            // method signature to the impl's `type X = T` binding: the trait
            // declares the ABSTRACT signature, but this context stands for the
            // CONCRETE impl method. An unresolved projection stays Opaque and
            // is rejected fail-closed by record_function_context_metadata.
            params.extend(
                method
                    .params
                    .iter()
                    .map(|(param_name, param_ty)| (param_name.clone(), bind_ty(param_ty))),
            );

            contexts.push(FunctionContext {
                name: concrete_fn_name.clone(),
                params,
                return_type: bind_ty(&method.return_type),
                is_recursive: false,
                mode: crate::mode::FunctionMode::Spec,
                trait_bounds: vec![],
            });
        }
    }
    contexts
}

pub(crate) fn prepare_context(
    ctx: &VerificationContext,
) -> Result<PreparedVerificationContext, TrustVcError> {
    if let Some(ref err) = ctx.duplicate_var_error {
        return Err(TrustVcError::Encoding {
            context: "prepare verification context",
            detail: err.clone(),
        });
    }
    // Fail closed CLEANLY on a generic-datatype multi-instantiation conflict
    // (e.g. a function building both `GList<i32>` and `GList<bool>`). The base
    // cannot be monomorphized to one carrier, so emitting the obligations would
    // mix a concrete outer carrier with a template-sorted recursive tail and trip
    // a backend sort mismatch (swallowed as a `SolverPanic`). Surface a clean
    // `VerifyResult::Error` instead — sound (never `Verified`), just incomplete.
    if let Some(ref detail) = ctx.generic_instantiation_conflict {
        return Err(TrustVcError::Encoding {
            context: "prepare verification context",
            detail: detail.clone(),
        });
    }
    let env = build_type_env(ctx)?;
    let mut obligations = Vec::with_capacity(ctx.obligations.len());
    for obligation in &ctx.obligations {
        let scoped_env;
        let obligation_env = if matches!(obligation.kind(), ObligationKind::AssertBy) {
            if let Some(scoped_variables) = ctx.forall_bound_vars.get(obligation.name()) {
                scoped_env = env_with_scoped_variables(&env, scoped_variables);
                &scoped_env
            } else {
                &env
            }
        } else {
            &env
        };
        obligations.push(PreparedObligation::from_legacy(obligation, obligation_env)?);
    }

    let mut assert_by_scopes = HashMap::with_capacity(ctx.assert_by_scopes.len());
    for (scope_name, scope_obligations) in &ctx.assert_by_scopes {
        let scoped_env;
        let scope_env = if let Some(scoped_variables) = ctx.forall_bound_vars.get(scope_name) {
            scoped_env = env_with_scoped_variables(&env, scoped_variables);
            &scoped_env
        } else {
            &env
        };
        let prepared_scope = scope_obligations
            .iter()
            .map(|obligation| PreparedObligation::from_legacy(obligation, scope_env))
            .collect::<Result<Vec<_>, _>>()?;
        assert_by_scopes.insert(scope_name.clone(), prepared_scope);
    }

    // Prepare per-loop-invariant ENTRY scopes (loop-modified let-local pre-loop
    // values) — same lowering as assert_by scopes, over the base env (no forall
    // binders). Passed to the invariant's BASE-CASE check only.
    let mut loop_entry_scopes = HashMap::with_capacity(ctx.loop_entry_scopes.len());
    for (inv_name, entry_obligations) in &ctx.loop_entry_scopes {
        let prepared = entry_obligations
            .iter()
            .map(|obligation| PreparedObligation::from_legacy(obligation, &env))
            .collect::<Result<Vec<_>, _>>()?;
        loop_entry_scopes.insert(inv_name.clone(), prepared);
    }

    // Resolve user-struct concrete types (Opaque -> registered Datatype) up
    // front so EVERY downstream consumer — synthesized impl-method contexts,
    // the setup linking axioms, and trait-impl conformance — sees the same
    // ay-encodable self sort. Faithfulness fix layered on #2425.
    let resolved_trait_impl_decls =
        resolve_trait_impl_concrete_types(&ctx.trait_impl_decls, &ctx.struct_types);

    let mut helper_function_contexts = build_helper_function_contexts(ctx);
    helper_function_contexts.extend(synthesize_impl_method_contexts(
        ctx,
        &resolved_trait_impl_decls,
    ));
    let mut known_function_names: HashSet<_> = helper_function_contexts
        .iter()
        .map(|func_ctx| func_ctx.name.clone())
        .collect();
    // Include string-based helper functions in the known set. These are
    // registered via declare_helper_function() (non-typed path) and are valid
    // reveal targets even though they lack typed parameter info. (#2473)
    known_function_names.extend(ctx.helper_functions.keys().cloned());
    if let Some(function_context) = &ctx.function_context {
        known_function_names.insert(function_context.name.clone());
    }
    helper_function_contexts.extend(collect_collection_constructor_contexts(
        &obligations,
        &assert_by_scopes,
        &known_function_names,
    ));

    // Validate that every revealed function name matches a known function.
    // Without this, reveal!(typo_name) silently does nothing — the function
    // stays opaque, producing confusing Unknown/Counterexample results. (#2473)
    // A `reveal!` target matches a known function either verbatim or — for a
    // cross-crate dependency spec registered under its fully-qualified name
    // (e.g. `trust_vc_std::arithmetic::mul`) — by the trailing `::` segment
    // (leaf), since `reveal!` only accepts a bare identifier. This mirrors the
    // broadcast-setup reveal gate (`opaque_body_axiom_revealed`), so a bare
    // `reveal!(mul)` both passes this typo guard and discloses the imported
    // body axiom. The guard still fails closed on a name that matches no known
    // function (verbatim or by leaf). Part of #2473, #2778.
    let revealed_fns = revealed_function_names(&obligations);
    for revealed_name in &revealed_fns {
        validate_visibility_target(revealed_name, &known_function_names, "reveal")?;
    }

    // Scoped `reveal!`s (inside an `assert … by { .. }` proof block) get the SAME
    // typo guard — a scoped `reveal!(typo)` must not silently do nothing — but
    // are deliberately kept OUT of the query-level `revealed_fns`. Part of #34.
    let assert_by_scope_revealed_fns = assert_by_scope_reveals(&assert_by_scopes);
    for scoped_reveals in assert_by_scope_revealed_fns.values() {
        for revealed_name in scoped_reveals {
            validate_visibility_target(revealed_name, &known_function_names, "reveal")?;
        }
    }

    // SOUNDNESS-CRITICAL (#34): a `hide!` inside a by-block would be a silent
    // no-op under the query-level hidden set — reject it fail-closed.
    reject_hide_inside_assert_by_scope(&assert_by_scopes)?;

    // Validate hide! targets exactly like reveal! targets: hide!(typo_name)
    // would silently do nothing (the function stays visible), masking the
    // intended re-opaquing — fail closed instead. Same verbatim-or-leaf
    // matching as the reveal guard. Part of #2473.
    // Session (proc-macro) path supplies `ctx.hidden_fns` via `hide_function`;
    // the file path carries `hide!` as `Hide` obligations in the stream. Union
    // both so the query-granular hidden set is identical regardless of front
    // end. Part of #2785.
    let mut hidden_fns: HashSet<String> = ctx.hidden_fns.iter().cloned().collect();
    hidden_fns.extend(hidden_function_names(&obligations));
    for hidden_name in &hidden_fns {
        validate_visibility_target(hidden_name, &known_function_names, "hide")?;
    }

    // SOUNDNESS-CRITICAL (#2785): reject fail-closed the one `hide!`/`reveal!`
    // interleave the query-granular visibility model cannot represent without
    // proving MORE than Verus.
    reject_unsound_hide_reveal_interleave(&obligations)?;

    Ok(PreparedVerificationContext {
        has_collection_context: has_collection_context(
            &ctx.variables,
            &obligations,
            &assert_by_scopes,
            &ctx.forall_bound_vars,
        ),
        revealed_fns,
        hidden_fns,
        source_catalog_admitted_definitions: ctx.source_catalog_admitted_definitions.clone(),
        helper_function_contexts,
        obligations,
        variables: ctx.variables.clone(),
        function_context: ctx.function_context.clone(),
        trait_decls: ctx.trait_decls.clone(),
        trait_impl_decls: resolved_trait_impl_decls,
        trait_impl_method_bodies: ctx.trait_impl_method_bodies.clone(),
        trait_impl_method_ensures: ctx.trait_impl_method_ensures.clone(),
        conformance_exempt_methods: ctx.conformance_exempt_methods.clone(),
        verification_mode: ctx.verification_mode,
        overflow_behavior: ctx.overflow_behavior,
        div0_behavior: ctx.div0_behavior,
        bitshift_behavior: ctx.bitshift_behavior,
        broadcast_use_groups: ctx.broadcast_use_groups.iter().cloned().collect(),
        assert_by_scopes,
        loop_entry_scopes,
        assert_by_scope_revealed_fns,
        forall_bound_vars: ctx.forall_bound_vars.clone(),
        loop_guards: ctx.loop_guards.clone(),
        loop_modified_vars: ctx.loop_modified_vars.clone(),
        loop_body_transitions: ctx.loop_body_transitions.clone(),
        struct_types: ctx.struct_types.clone(),
        type_invariants: ctx.type_invariants.clone(),
        invariant_mask: ctx.invariant_mask.clone(),
        tracked_params: ctx.tracked_params.clone(),
        rlimit_ms: ctx.rlimit_ms,
        demand_inline: ctx.demand_inline,
        counterexample_var_meta: ctx.counterexample_var_meta.clone(),
        skip_retry_cascade: ctx.skip_retry_cascade,
    })
}

#[cfg(test)]
#[path = "prepared_context_tests.rs"]
mod tests;
