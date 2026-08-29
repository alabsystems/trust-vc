// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::calc_parser::{parse_calc, transitive_op, CalcOp};
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{DatatypeVariant, StructDef, TrustVcType};
use crate::ir_expr::TUPLE_VARIANT_NAME;
use crate::vc::{
    ObligationKind, ProofObligation, ProofStepMeta, SelfReceiverKind, SolverMode,
    VerificationContext,
};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use quote::ToTokens;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use syn::{
    parse::Parser,
    punctuated::Punctuated,
    visit::{self, Visit},
    visit_mut::VisitMut,
    BinOp, Expr, Item, ItemMacro, Macro, Pat, Stmt, Token,
};

/// Extracts assertions from a function body.
///
/// Uses a structural AST visitor so new expression forms do not need bespoke
/// recursion arms to avoid silently dropping nested assertions.
/// Post-body two-state summary for scalar `&mut` parameters.
///
/// The string-substitution body model resolves a *bare* reference to a `&mut`
/// scalar parameter `P` in a **postcondition** to its FINAL (post-body) value,
/// matching Verus' two-state semantics (`design-new-mut-ref.md`: the bare
/// binding `P` in a postcondition denotes `*final(P)`). This summary carries the
/// facts the postcondition rewriter (`vc_extraction.rs`) needs to do that
/// soundly:
///
/// - `clean_finals` — for each `&mut` scalar param cleanly tracked through to the
///   single fall-through exit, its final scoped-value string. Substituting this
///   for the bare param in a postcondition is exact.
/// - `has_early_exit` — the body has a non-fall-through normal exit (`return` or
///   `?`). The fall-through final value need not hold on those paths, so a
///   postcondition over a `&mut` param must fail closed.
/// - `mutated_in_body` — the `&mut` scalar params that are the target of a
///   deref-assignment (`*P = ..`, `*P op= ..`) anywhere in the body. A param
///   referenced in a postcondition but NOT in `clean_finals` is safe to read as
///   its entry value ONLY when it is neither mutated nor escaped (definitely
///   unchanged: e.g. a pure `*P` read); a mutated-but-untracked param has an
///   uncertain final value (havoced by a branch/loop join) → fail closed.
#[derive(Debug, Default, Clone)]
pub(super) struct MutRefPostState {
    pub(super) clean_finals: BTreeMap<String, String>,
    pub(super) has_early_exit: bool,
    pub(super) mutated_in_body: BTreeSet<String>,
    /// `&mut` scalar params whose *reference* is used bare in the body (passed to
    /// a call/method, moved into an alias binding, or reborrowed) rather than
    /// only being read/written through `*P`. The callee/alias may mutate the
    /// referent invisibly to the caller's value-numbering, so the tracked
    /// scoped value can be stale — a postcondition over such a param fails
    /// closed even when `clean_finals` holds a value.
    pub(super) escapes_in_body: BTreeSet<String>,
}

/// The caller-supplied state an `AssertionCollector` needs BEYOND what
/// `AssertionCollector::new` establishes — the seed that the IN-BODY obligation
/// lane and the RETURN-VALUE render lane must apply IDENTICALLY.
///
/// SOUNDNESS-CRITICAL, and it exists because forgetting one of these fields in
/// the return lane has now been a cardinal false verify TWICE.
///
/// `4ee6d1d4` fixed the return lane's throwaway `VerificationContext` (it
/// carried the struct registry and nothing else, so every mutation test
/// answered "unknown" for a parameter). It seeded the CONTEXT and left the
/// COLLECTOR at `AssertionCollector::new(..)` defaults, so `mut_ref_call_args`
/// stayed empty and `havoc_mut_ref_call_arg_referents` — which opens with
/// `if self.mut_ref_call_args.is_empty() { return }` — never fired in the
/// return lane. One hop away from the receiver call it had just fixed:
///
///     pub fn bump(c: &mut C) { c.n = c.n + 1; }
///     #[requires(t.n == 0)] pub fn g(t: &mut C) { bump(t); assert!(t.n == 0); }   // refuted
///     #[requires(t.n == 0)] #[ensures(result == 0)]
///     pub fn g(t: &mut C) -> u64 { bump(t); t.n }                                 // VERIFIED, false
///
/// Both lanes now go through [`AssertionCollector::apply_lane_seed`] with a
/// value of THIS type, and this type is constructed only by exhaustive struct
/// literal (no `Default`, no `..rest`), so adding a fourth seeded field is a
/// COMPILE ERROR at every construction site rather than a silent third
/// instalment. The lanes are NOT identical — see
/// [`CollectorLaneSeed::return_lane_view`] for the one field the return lane
/// deliberately withholds — but the difference is written down in one place and
/// a new field cannot dodge it.
///
/// WHAT IS DELIBERATELY *NOT* HERE, and why the return lane does not need it —
/// the full audit of everything `AssertionCollector::new` leaves defaulted:
///
/// * `helper_contracts` / `trait_method_contracts` / `concrete_method_contracts`
///   — a resolved contract only ever ADDS facts: a callee `ensures` assumption
///   over the post-call state, and `requires` obligations that this throwaway
///   collector discards (only its rendered STRING escapes). Absent, the havoc'd
///   root simply stays unconstrained, which is strictly WEAKER — an
///   over-rejection, never a false `Verified`. They are also `&'a`-borrowed from
///   the caller's own maps, so threading them is a lifetime change, not a seed.
///   Sound to omit; a capability opportunity, not a hole.
/// * `ambient_solver_mode` / `next_assertion_index` — both name or route
///   OBLIGATIONS, and this lane's obligations are thrown away with its context.
///   No effect on the rendered value.
/// * `next_struct_havoc_index` — deliberately caller-controlled, not seeded:
///   `extract_scoped_return_expression` sets it from `havoc_index_base` so two
///   renders combined into one model cannot mint the same name for two
///   unrelated arbitrary states.
/// * every remaining field (`scopes`, `path_conditions`, `loop_contexts`, the
///   depth counters, the dedup/journal sets, `pre_havoc_call_args`,
///   `exec_closure_defs`, `closure_reflection_contracts`, `loop_body_havoc`, …)
///   is per-visit working state whose correct initial value IS the default:
///   seeding them from another visit would import a foreign scope stack.
pub(super) struct CollectorLaneSeed<'s> {
    /// `&mut` scalar parameters with a clean erased-reference target. Seeds
    /// scope 0's `erased_mut_ref_aliases` / `erased_mut_ref_targets`.
    ///
    /// IN-BODY LANE ONLY — see [`CollectorLaneSeed::return_lane_view`] for the
    /// measured reason and the test that pins it. This is not framing state: it
    /// changes how `*p` is ERASED, and granting it to the return lane cost a
    /// fail-closed rejection without buying any soundness.
    pub(super) supported_mut_ref_param_targets: &'s BTreeSet<String>,
    /// Callee-signature `&mut` argument positions per free-call symbol. THE
    /// field whose omission was the false verify: it is the sole enable of
    /// `havoc_mut_ref_call_arg_referents`, and it is also what keeps that havoc
    /// PRECISE — a `&`-shared read (`read(v)`) is spelled identically at the
    /// call site and must NOT havoc.
    pub(super) mut_ref_call_args: &'s BTreeMap<String, Vec<bool>>,
    /// Per-ARGUMENT `&mut` positions of every method NAME the file declares
    /// (receiver excluded). `mut_ref_call_args` is keyed on `ExprCall` symbols
    /// and structurally cannot see `h.hit(t)`, so a `&mut` NON-self parameter of
    /// an inherent or trait method was framed nowhere. Same lane discipline as
    /// `mut_ref_call_args`: seeded into BOTH lanes.
    pub(super) method_arg_mut_flags: &'s BTreeMap<String, Vec<bool>>,
    /// Bindings of the function under extraction whose own type is `&mut T`.
    /// The fallback that makes an UNRESOLVABLE callee fail closed instead of
    /// reading as "no mutable arguments" — see
    /// `super::mut_ref_reborrowable_bindings`. Seeded into BOTH lanes.
    pub(super) mut_ref_reborrowable_bindings: &'s BTreeSet<String>,
    /// `Fn`-bound `SpecFn` value parameters. Gates a conditional call-site
    /// ASSUME, so omitting it is weaker (sound); seeded for lane parity.
    pub(super) fn_bound_spec_fn_params: &'s BTreeSet<String>,
}

impl CollectorLaneSeed<'_> {
    /// The seed for a lane that has no caller state to supply — the
    /// definitional-body-axiom / conformance-capture renders, which run over a
    /// SIBLING's body rather than the function under extraction.
    ///
    /// READ THIS BEFORE REUSING IT. An empty seed here is NOT self-evidently
    /// safe, and assuming it was is how a second false verify got written into
    /// this fix's first draft. Those lanes drop their axiom on a non-empty
    /// `havoc_dependencies`, and it is tempting to argue that an empty seed can
    /// only produce FEWER havocs and therefore never publishes an axiom the
    /// populated seed would have dropped. That argument is exactly backwards:
    /// fewer havocs means fewer dependencies means the drop does NOT fire, and
    /// `fn via(mut c: C) -> u64 { bump(&mut c); c.n }` published `via(c) == c.n`
    /// against the ENTRY `c` — a false premise (probed: `via(C{n:0})` proved
    /// `result == 0`; every execution returns 1).
    ///
    /// What actually makes these lanes safe is a GATE AT THE PUBLISHER
    /// (`body_has_unframeable_mutation`, applied by both
    /// `SiblingHelperDef::from_item_fn_with_name` and
    /// `InherentMethodDef::from_impl_method`), which drops the axiom when the
    /// body passes a `&mut` argument or calls a `&mut self` method. Seeding the
    /// render could not have fixed it: the body's own PARAMETERS are declared in
    /// neither this throwaway scope stack nor the target's context, so
    /// `havoc_mut_ref_call_arg_referents` has no tracked root to rebind.
    /// `{sibling_helper,inherent_method}_body_axiom_is_dropped_when_*` in
    /// `crates/trust-vc/tests/mut_ref_free_call_return_lane.rs` pin both
    /// directions, with `a_pure_*_keeps_its_body_axiom` as the narrowness pins.
    pub(super) const EMPTY: CollectorLaneSeed<'static> = CollectorLaneSeed {
        supported_mut_ref_param_targets: &BTreeSet::new(),
        mut_ref_call_args: &BTreeMap::new(),
        method_arg_mut_flags: &BTreeMap::new(),
        mut_ref_reborrowable_bindings: &BTreeSet::new(),
        fn_bound_spec_fn_params: &BTreeSet::new(),
    };

    /// The subset of this seed that the RETURN-VALUE render lane applies.
    ///
    /// There is exactly ONE deliberate difference between the lanes, and it is
    /// here rather than at the call site so that it is reviewed rather than
    /// forgotten: the exhaustive destructure below means a future seed field
    /// cannot compile until someone decides, in writing, which lanes get it.
    /// That is the whole point of routing both lanes through one type — the two
    /// cardinal false verifies in this area were both "the return lane was given
    /// SOME of the caller's state and nobody noticed which".
    ///
    /// `supported_mut_ref_param_targets` is WITHHELD. It is not framing state:
    /// it installs scope-0 erased-reference TARGETS, which change how `*p` is
    /// ERASED in the rendered value — a modelling change, not a mutation-framing
    /// one. Measured consequence of granting it:
    /// `#[trust_vc::spec] fn f(x: &mut u64) -> u64 { *old(x) }` stopped failing
    /// closed on "Unsupported old-state expression `old(...)`" and instead
    /// reached the solver with no obligations at all
    /// ("nothing to prove") — pinned by
    /// `mut_refs_old_rs_snapshot_boundaries_fail_closed_from_file`, which the
    /// granting version turned red. Both outcomes are Errors, so nothing became
    /// unsound, but the render lost a rejection it is supposed to make, and this
    /// field's absence is fail-closed by construction (an unresolved `*p` simply
    /// does not render). The two fields that DO decide whether a call may have
    /// changed a binding — `mut_ref_call_args` and `fn_bound_spec_fn_params` —
    /// are granted, and `mut_ref_call_args` is the one this whole fix is about.
    fn return_lane_view(&self) -> CollectorLaneSeed<'_> {
        let CollectorLaneSeed {
            supported_mut_ref_param_targets: _withheld,
            mut_ref_call_args,
            method_arg_mut_flags,
            mut_ref_reborrowable_bindings,
            fn_bound_spec_fn_params,
        } = self;
        CollectorLaneSeed {
            supported_mut_ref_param_targets: &EMPTY_MUT_REF_PARAM_TARGETS,
            mut_ref_call_args,
            method_arg_mut_flags,
            mut_ref_reborrowable_bindings,
            fn_bound_spec_fn_params,
        }
    }
}

/// Backing storage for [`CollectorLaneSeed::return_lane_view`]'s withheld field.
static EMPTY_MUT_REF_PARAM_TARGETS: BTreeSet<String> = BTreeSet::new();

pub(super) fn extract_body_assertions_with_mut_ref_param_targets(
    block: &syn::Block,
    vc: &mut VerificationContext,
    ambient_solver_mode: Option<SolverMode>,
    seed: &CollectorLaneSeed<'_>,
) -> TrustVcResult<MutRefPostState> {
    let supported_mut_ref_param_targets = seed.supported_mut_ref_param_targets;
    let mut collector = AssertionCollector::new(vc, 0, ambient_solver_mode);
    collector.apply_lane_seed(seed);
    let clean_finals = collector.visit_function_body_capturing_mut_ref_finals(block);
    collector.finish()?;
    Ok(MutRefPostState {
        clean_finals,
        has_early_exit: body_has_early_exit(block),
        mutated_in_body: mut_ref_params_mutated_in_body(block, supported_mut_ref_param_targets),
        escapes_in_body: mut_ref_params_escaping_in_body(block, supported_mut_ref_param_targets),
    })
}

/// Extracts body assertions while discharging BOTH path-form sibling-helper
/// call contracts and generic trait-bounded method-call `requires` contracts.
///
/// Either map may be empty. The trait-method map keys are `(type_param,
/// method)` and supply caller-side `requires` obligations at `z.f(args)` where
/// `z: TypeParam(P)` and `P: T` (unit 1 of the trait-`requires` discharge).
pub(super) fn extract_body_assertions_with_helper_and_trait_method_contracts(
    block: &syn::Block,
    vc: &mut VerificationContext,
    ambient_solver_mode: Option<SolverMode>,
    helper_contracts: Option<&BTreeMap<String, HelperCallContract>>,
    trait_method_contracts: Option<&BTreeMap<(String, String), TraitMethodCallContract>>,
    concrete_method_contracts: Option<&BTreeMap<(String, String), TraitMethodCallContract>>,
    seed: &CollectorLaneSeed<'_>,
) -> TrustVcResult<MutRefPostState> {
    let supported_mut_ref_param_targets = seed.supported_mut_ref_param_targets;
    let mut collector = AssertionCollector::new_with_helper_and_trait_method_contracts(
        vc,
        0,
        ambient_solver_mode,
        helper_contracts,
        trait_method_contracts,
        concrete_method_contracts,
    );
    collector.apply_lane_seed(seed);
    let clean_finals = collector.visit_function_body_capturing_mut_ref_finals(block);
    collector.finish()?;
    Ok(MutRefPostState {
        clean_finals,
        has_early_exit: body_has_early_exit(block),
        mutated_in_body: mut_ref_params_mutated_in_body(block, supported_mut_ref_param_targets),
        escapes_in_body: mut_ref_params_escaping_in_body(block, supported_mut_ref_param_targets),
    })
}

/// Extracts assertions from expressions (looking for assertion-like macros).
/// Only used by tests — production code enters via `extract_body_assertions`.
#[cfg(test)]
pub(super) fn extract_expr_assertions(
    expr: &Expr,
    vc: &mut VerificationContext,
    stmt_index: usize,
) -> TrustVcResult<()> {
    let mut collector = AssertionCollector::new(vc, stmt_index, None);
    collector.visit_expr(expr);
    collector.finish()
}

/// Outcome of a scoped return-value render.
///
/// `rendered` is `None` when the collector could not locate the target
/// expression (or hit a parse error first) — nothing was rewritten, so the
/// caller's raw-source fallback is as good a model as it ever was.
///
/// `havoc_dependencies` are the fresh symbols an UNMODELLED-MUTATION havoc
/// minted that the rendered value actually READS (`t.bump(); t.a()` renders
/// `t__havoc_0.a()`). They are minted inside this render's throwaway context, so
/// a caller that uses `rendered` MUST declare them in its own context — binding
/// `result` to an expression over an undeclared symbol is not a model. A caller
/// that cannot declare them (a definitional body axiom, whose binder set is
/// fixed) must drop its axiom instead.
///
/// Emitting them rather than declining is what keeps this fix from being a
/// blanket rejection: the fresh symbol is exactly "arbitrary post-mutation
/// state", so `fn g(t: &mut impl Ctr) -> int { t.bump(); t.a() }` still proves
/// `result >= 2` from the trait's `ensures` (which holds of EVERY receiver)
/// while `result == 0` is refuted with a model.
pub(super) struct ScopedReturnRender {
    pub(super) rendered: Option<String>,
    pub(super) havoc_dependencies: Vec<(String, TrustVcType)>,
    /// One past the highest havoc index this render consumed. Feed it back as
    /// the next render's `havoc_index_base` when two renders of the SAME body
    /// are combined into one model (the `let … else` then/else pair), so the two
    /// cannot mint the same name for two different arbitrary states. Identifying
    /// them would remove models in which they differ, which NARROWS the value
    /// bound to `result` — the unsound direction.
    pub(super) next_havoc_index: usize,
    /// SOUNDNESS-CRITICAL: the caller MUST NOT substitute a raw token rendering
    /// of the return expression when `rendered` is `None`.
    ///
    /// `scoped_return_expression` in the parent module used to do exactly that —
    /// `render.rendered.unwrap_or_else(|| extract_expr_string(return_expr))` —
    /// which threw away every fail-closed decision this render made and put back
    /// the very string the decision rejected. That is how
    /// `fn a1(f: bool, t: &mut C) -> u64 { if f { bump(t); t.n } else { bump(t); t.n } }`
    /// kept proving `result == 0`: the collector correctly declined, and the
    /// caller silently answered for it with the raw tokens, in which the encoder
    /// has no statement semantics and reads each branch tail against the ENTRY
    /// state.
    ///
    /// Set when a raw rendering of THIS return expression would drop a
    /// statement-position mutation (see
    /// [`AssertionCollector::raw_fallback_dropped_mutations`]) — narrow on
    /// purpose, so the long-standing benign uses of that fallback (a target the
    /// walk simply did not reach, in a body with nothing to drop) are untouched.
    pub(super) raw_fallback_unsound: bool,
}

/// SOUNDNESS-CRITICAL (return-lane mutation framing). The `ctx` seed is
/// load-bearing, not a convenience.
///
/// This render runs on its OWN collector over a throwaway context. That context
/// used to carry the struct-type registry and nothing else — no variable
/// declarations, no receiver-kind registries, no function context — so every
/// mutation-framing test the collector performs answered "unknown" for a
/// PARAMETER: `receiver_struct_type_name` and `receiver_is_collection_like` both
/// read declared types, and both were `None`. The result was that the in-body
/// lane correctly havoced `t` across `t.bump()` and fail-closed an
/// `assert!(t.n == 0)`, while the RETURN lane rendered the very same body's tail
/// `t.n` against the ENTRY symbol and false-`Verified` `ensures(result == 0)`.
/// The two lanes must see the same facts or they decide the same program
/// differently.
pub(super) fn extract_scoped_return_expression(
    block: &syn::Block,
    return_expr: &Expr,
    struct_types: &[StructDef],
    ctx: Option<&VerificationContext>,
    havoc_index_base: usize,
    seed: &CollectorLaneSeed<'_>,
) -> ScopedReturnRender {
    // SOUNDNESS-CRITICAL (returned owned-local field write): the scoped
    // return-expression render threads straight-line field writes via
    // `assign_direct_field_expr`, which needs the OWNING struct/enum `Datatype`
    // to build the functional update — resolved through `self.vc.struct_types`.
    // A fresh empty `VerificationContext` has NO registered struct types, so an
    // owned local `let mut s = S { a: 0 }; s.a = 5; s.a` could not resolve `S`
    // and silently dropped the `s.a = 5` write — the returned `s.a` then read
    // the construction value, a real `result == 0` false `Verified`. Seed the
    // dummy with the caller's struct registry so the returned field projection
    // observes the write. (Tuple-struct constructors `Pair(..)` are recognized
    // by `expr_struct_type_name` only against this same registry, so the tuple
    // and nested forms are covered too.)
    let mut dummy = VerificationContext::new();
    for def in struct_types {
        dummy.register_struct_type(def.clone());
    }
    if let Some(ctx) = ctx {
        // Declared types: what `receiver_struct_type_name` /
        // `receiver_is_collection_like` classify a PARAMETER receiver by.
        for decl in ctx.variables() {
            dummy.declare_var_typed_bounded(&decl.name, decl.ty.clone(), decl.bounded_len);
        }
        // The two receiver-kind registries. Seeding these is what keeps the
        // framing PRECISE rather than blanket: a `&self` reader resolves to
        // `Ref` and is left alone, so `let n = t.peek(); n` still renders.
        for ((self_type, method), kind) in ctx.struct_self_receiver_kinds_clone() {
            dummy.register_struct_self_receiver_kind(self_type, method, kind);
        }
        for ((trait_name, method), kind) in ctx.trait_method_self_receiver_kinds_clone() {
            dummy.register_trait_method_self_receiver_kind(trait_name, method, kind);
        }
        // Trait bounds + declarations: the generic-receiver classifier resolves
        // a `TypeParam` receiver through the function context's bounds and the
        // supertrait closure.
        if let Some(function_context) = ctx.function_context() {
            dummy.set_function_context(function_context.clone());
        }
        for decl in ctx.trait_decls() {
            dummy.register_trait_decl(decl.clone());
        }
    }
    let mut collector = AssertionCollector::new(&mut dummy, 0, None);
    // SOUNDNESS-CRITICAL: the SAME seed the in-body obligation lane applies.
    // Seeding the CONTEXT (above) and leaving the COLLECTOR at its defaults is
    // exactly how the free-call `&mut`-argument havoc went missing here —
    // `havoc_mut_ref_call_arg_referents` returns immediately on an empty
    // `mut_ref_call_args`, so `bump(t); t.n` rendered `t`'s ENTRY symbol and
    // `ensures(result == 0)` false-`Verified` while the identical body's
    // `assert!(t.n == 0)` was correctly refuted. See [`CollectorLaneSeed`].
    collector.apply_lane_seed(&seed.return_lane_view());
    collector.next_struct_havoc_index = havoc_index_base;
    let rendered = collector.scoped_return_expression(block, return_expr);
    // Report ONLY the havoc symbols the rendered value actually reads, so a body
    // that mutates a binding it does not return (`t.bump(); 42`) costs nothing.
    let havoc_dependencies = match &rendered {
        Some(rendered) => collector
            .havoc_minted_symbols
            .iter()
            .filter(|symbol| string_contains_whole_word(rendered, symbol))
            .filter_map(|symbol| {
                collector
                    .vc
                    .get_variable_type(symbol)
                    .map(|ty| (symbol.clone(), ty.clone()))
            })
            .collect(),
        None => Vec::new(),
    };
    let raw_fallback_unsound = rendered.is_none()
        && !collector
            .raw_fallback_dropped_mutations(return_expr)
            .is_empty();
    ScopedReturnRender {
        rendered,
        havoc_dependencies,
        next_havoc_index: collector.next_struct_havoc_index,
        raw_fallback_unsound,
    }
}

/// The match condition for the TAIL `let PAT = SCRUTINEE else { return … };` of
/// `block` (`local`), rendered in the same scoped-value vocabulary as
/// [`extract_scoped_return_expression`]. `None` means "not modelable".
///
/// SOUNDNESS-CRITICAL. The caller's `ReturnValue::Conditional` model is
/// `if COND { then } else { else }`. A `COND` of `"true"` for a REFUTABLE
/// pattern makes the ELSE value unreachable and discharges the postcondition
/// against the then-value alone — a cardinal false verify (`enum E { V{a}, W }`,
/// `let E::V { a } = e else { return 0 }; 7` proved `result == 7`). `"false"` is
/// exactly as wrong in the other direction: it would drop the THEN value. There
/// is no safe placeholder, so an unmodelable pattern returns `None` and the
/// caller must DECLINE the conditional model entirely. An unmodelled return
/// leaves `result` unconstrained, which is an over-rejection — a capability
/// cost, not a hole.
///
/// This deliberately routes to the obligation collector's OWN let-else handler
/// ([`AssertionCollector::local_let_else_match_condition`] ->
/// [`pattern_match_condition_for_scoped_value`]) instead of re-deriving the
/// condition. The return lane previously carried a hand-copied predicate that
/// had drifted away from this one on every axis that matters: it returned a bare
/// `String` whose unrecognized arms all yielded `"true"`, it applied the
/// `Some`/`None` spelling without checking the type was an `Option`, and it had
/// neither the `Pat::Struct` refutability gate nor the refinement-drop guards.
/// Deriving the condition in one place is what keeps the two lanes from drifting
/// again.
///
/// `ctx` is the caller's verification context, needed for the scrutinee's TYPE:
/// the declared variable types decide whether a variant tester is even
/// applicable, and `Option`'s `Some`/`None` spell differently from a user enum's
/// same-named variants. Pass `None` only where no context exists (the
/// conformance-method-body capture); the resolution then fails and the caller
/// declines, which is sound.
pub(super) fn extract_tail_let_else_match_condition(
    block: &syn::Block,
    local: &syn::Local,
    ctx: Option<&VerificationContext>,
) -> Option<String> {
    let mut dummy = VerificationContext::new();
    if let Some(ctx) = ctx {
        for def in &ctx.struct_types {
            dummy.register_struct_type(def.clone());
        }
        for (name, ty) in ctx.source_type_aliases() {
            dummy.register_source_type_alias(name, ty.clone());
        }
        for decl in ctx.variables() {
            dummy.declare_var_typed_bounded(&decl.name, decl.ty.clone(), decl.bounded_len);
        }
    }
    let mut collector = AssertionCollector::new(&mut dummy, 0, None);
    collector.tail_let_else_match_condition(block, local)
}

/// The WRITTEN contract of a known local `trust_vc::closure!` literal, keyed by
/// its binding name, retained so a later `f.requires(..)`/`f.ensures(..)`
/// REFLECTION (Phase C) can be discharged with a GROUND definitional fact
/// (`f.requires((a,)) == R[p:=a]`) at the exact use site — no quantifier, no
/// BV-vs-Int sort tension, and clean Verified/Counterexample verdicts (a live
/// universal axiom would leave un-instantiated instances that the ay soundness
/// gate fails closed to `Unknown`). The reflection UF stays OPAQUE and DISJOINT;
/// each ground fact is a conservative extension that says nothing about the
/// closure's real behaviour, so it can neither poison nor rescue the parent.
#[derive(Clone)]
struct ClosureReflectionContract {
    /// Closure parameter names, positionally matched to the reflection args tuple.
    params: Vec<String>,
    /// Modelable parameter sorts (arity check; the UF signature comes from `f`'s
    /// `SpecFn` type at lowering).
    arg_tys: Vec<TrustVcType>,
    /// The WRITTEN `requires` clause, or `None` (reflected requires is `true`).
    requires: Option<Expr>,
    /// The WRITTEN `ensures` clause as `(result_binder_name, clause)`, or `None`
    /// (no ensures ⇒ `f.ensures(..)` reflection fails closed).
    ensures: Option<(String, Expr)>,
}

struct AssertionCollector<'a> {
    vc: &'a mut VerificationContext,
    next_assertion_index: usize,
    next_helper_call_contract_index: usize,
    parse_error: Option<TrustVcError>,
    scopes: Vec<BTreeMap<String, String>>,
    concrete_scoped_values: Vec<BTreeSet<String>>,
    /// Scoped names whose bound value models an immutable ghost collection
    /// (`Set`/`Seq`/`Map`/`Multiset`), inferred at bind time from ghost
    /// constructors and pure-combinator chains (GAP2). Used only to TARGET the
    /// receiver-preservation relaxation in `visit_expr_method_call`; soundness
    /// does not rest on it (see `method_call_preserves_receiver`).
    ghost_collection_scopes: Vec<BTreeSet<String>>,
    scoped_struct_types: Vec<BTreeMap<String, String>>,
    erased_shared_ref_aliases: Vec<BTreeSet<String>>,
    erased_mut_ref_aliases: Vec<BTreeSet<String>>,
    erased_mut_ref_targets: Vec<BTreeMap<String, ErasedMutRefTarget>>,
    supported_mut_ref_param_targets: BTreeSet<String>,
    /// Per-call `&mut`-argument positions for free functions called in the body,
    /// keyed by the call symbol (`call_function_symbol`), value a positional
    /// `is_mut_ref_param` flag vector. Populated from callee signatures by the
    /// caller (`collect_referenced_sibling_mut_ref_call_args`). SOUNDNESS-CRITICAL
    /// (free-call `&mut`-argument framing): an opaque free call `push_helper(v)`
    /// mutates `v` through its `&mut` argument, so the referent must be havoced;
    /// a `&`-shared read (`read_helper(v)`) is syntactically identical at the call
    /// site, so the callee signature carried here is what tells the two apart and
    /// keeps the havoc free of over-rejection.
    mut_ref_call_args: BTreeMap<String, Vec<bool>>,
    /// Per-ARGUMENT `&mut` positions of every method NAME the file declares
    /// (receiver EXCLUDED, so positions align with `ExprMethodCall::args`).
    /// SOUNDNESS-CRITICAL and the METHOD-call twin of `mut_ref_call_args`:
    /// `impl H { fn hit(&self, c: &mut C) }` called `h.hit(t)` never reached the
    /// `ExprCall` havoc at all, so the mutation of `t` was dropped outright.
    /// Absence means the file declares no method of that name — an UNKNOWN, which
    /// routes to `mut_ref_reborrowable_bindings` rather than to a silent "no".
    method_arg_mut_flags: BTreeMap<String, Vec<bool>>,
    /// Bindings whose OWN declared type is `&mut T` (the enclosing function's
    /// `&mut` parameters and a `&mut self` receiver).
    ///
    /// SOUNDNESS-CRITICAL — this is the answer for a callee the file cannot
    /// resolve. Passing one of these bare REBORROWS the mutable reference into
    /// the call, so whoever the callee is may write through it; no resolution is
    /// required to know that. It is consulted ONLY when the callee is
    /// unresolved: a resolved signature is authoritative and can legitimately say
    /// NO (`read(c: &C)` called `read(t)` with `t: &mut C` is a reborrow-coercion
    /// to `&C` and must not havoc — `shared_ref_argument_does_not_havoc_the_return_value`).
    mut_ref_reborrowable_bindings: BTreeSet<String>,
    unsupported_index_receivers: Vec<BTreeSet<String>>,
    local_macros: Vec<BTreeMap<String, LocalMacroDefinition>>,
    macro_expansion_depth: usize,
    loop_contexts: Vec<LoopExtractionContext>,
    /// Nesting depth of loop BODIES currently being traversed, counting every
    /// loop form uniformly: `while`, `for`, bare `loop`, and `while let`. Unlike
    /// `loop_contexts` (pushed only for a boolean-guard `while`, to carry the
    /// single-iteration transition), this is incremented around the body visit of
    /// EVERY loop form. It is the signal used to fail-close a loop-body call's
    /// `ensures` ASSUMPTION (see `add_helper_contract_obligations`): a body that
    /// may run zero times must not leak a call postcondition into the surrounding
    /// straight-line context. Mirrors the arithmetic-safety / `.set` loop-body
    /// deferrals, which key off `loop_contexts` but only need the `while` form.
    loop_body_depth: usize,
    /// Stack of branch path-condition strings (already scope-substituted) for the
    /// `if`/`else` arms currently being traversed. A body `assert(P)` inside
    /// `if c { … }` is the Verus obligation `c ==> P`, not the unconditional `P`:
    /// the assert is only reached when the guard holds. `add_assertion` wraps each
    /// emitted obligation in `!(c1) || !(c2) || … || (P)`. This is the branch-guard
    /// path condition that lets, e.g., `if m.len() != 0 { assert(m.count(m.choose())
    /// > 0) }` discharge via the multiset choose-positivity axiom (#2779 Feature B).
    /// >    It only ever guards an assert with a true hypothesis, so it can turn a
    /// >    spurious dead-branch counterexample into a verification but never makes a
    /// >    reachable false assert pass.
    path_conditions: Vec<String>,
    /// SOUNDNESS-CRITICAL (match-arm assume leak): depth counter raised while
    /// visiting a `match` arm whose "this arm is selected" path condition cannot
    /// be soundly rendered (an opaque/unknown pattern, or any earlier arm whose
    /// selection condition could not be rendered, so a later arm cannot exclude
    /// it). A bare `assume!`/call-`ensures` in such an arm must be DROPPED rather
    /// than leak its raw hypothesis past the match (mirroring the loop-body
    /// `assume!`/call-`ensures` drop). `assert!`/arithmetic obligations are left
    /// emitted but UNGUARDED (sound, possibly over-rejecting), never made vacuous.
    match_arm_unguardable_depth: usize,
    /// SOUNDNESS-CRITICAL (short-circuit condition-position call-`ensures`
    /// leak, slice-D remediation p8/p8b): depth counter raised while visiting
    /// the RIGHT operand of a short-circuit `&&` / `||`. That operand is
    /// CONDITIONALLY EVALUATED (the left operand short-circuits it), and the
    /// conditionality is NOT on the `path_conditions` stack — so a
    /// state-transition hypothesis established there (`__call_ensures_*` of a
    /// `&mut`-arg call, a bare `assume!`, a post-loop exit fact) would be
    /// assumed UNCONDITIONALLY over the surrounding straight-line context even
    /// on the real execution where the operand never ran (`if c &&
    /// add1b(&mut v) {} assert!(v == 6)` false-`Verified` for `c == false`).
    /// While raised, those assumes are DROPPED, mirroring the loop-body /
    /// unguardable-match-arm drops. PROVEN obligations (call-site `requires`,
    /// `assert!`, arithmetic safety) are untouched — over-rejection is
    /// fail-closed — and the `&mut`-arg havoc stays (over-havoc is sound).
    /// The LEFT operand is always evaluated and is visited OUTSIDE the raise.
    short_circuit_rhs_depth: usize,
    /// SOUNDNESS-CRITICAL (slice-C remediation: control-flow deref-write
    /// drop). Depth counter raised around the calc!/assert-by PROOF-block
    /// visits, where a deref write cannot be modeled at all (proof context
    /// must not mutate exec state; the visit is snapshot-discarded) and must
    /// fail closed with the VERBATIM pre-existing rejection
    /// (`unsupported_deref_assignment_error`). Exec control-flow regions are
    /// handled elsewhere: branch/match/nested-block/closure regions by
    /// `deref_written_region_roots` (exact in-region modeling + exit havoc);
    /// LOOP bodies keep base's plain-single-write modeling with the slice-C
    /// capabilities (compound desugar, sequential repins) switched off via
    /// `loop_body_depth` (their SSA chain would read the previous VISIT's
    /// value, not the previous ITERATION's) plus the same exit havoc.
    deref_write_rollback_depth: usize,
    /// SOUNDNESS-CRITICAL (slice-C remediation, sibling of
    /// `deref_write_rollback_depth`): stack of deref-written ROOT names, one
    /// set per active rollback/conditional region (`if`/`else` branch pair,
    /// whole `match` arm sweep, nested `{ .. }` block, value-path block
    /// evaluation, closure body, loop condition+body). Deref writes are
    /// EXCLUDED from
    /// `external_assignments` (the deliberate #83 deref-aliasing skip), so
    /// the region's snapshot-restore silently rolls them back and the join
    /// merge/havoc never covers the root — a post-region read then saw the
    /// PRE-region value and proved wrong facts (`if c { *x += 1; }
    /// assert!(*x == 5)` false-`Verified` for `c`; `{ *x += 1; }
    /// assert!(*x == 10)` false on EVERY path; both probed firsthand, and
    /// both ALSO reachable on base 2fdd181 with a single first write). Every
    /// deref write records its root in the TOP set; at region exit the set is
    /// popped, each root is HAVOCKED (fresh unconstrained symbol; its aliases
    /// invalidated) and the roots propagate into the ENCLOSING region's set
    /// so each outer join re-havocs after its own restore. In-region reads
    /// keep exact SSA semantics (a write + assert inside one branch/block is
    /// modeled precisely — the manifest-pinned mut_refs control-flow ports);
    /// post-region reads see arbitrary state (counterexample-able, sound:
    /// havoc can only lose provability, never prove wrong facts). Empty stack
    /// = straight-line function body: no recording, no havoc.
    deref_written_region_roots: Vec<BTreeSet<String>>,
    /// Roots havocked by [`Self::exit_deref_write_region_and_havoc`] whose
    /// FINAL value is therefore unresolved for the callee-side `ensures`
    /// resolver: `capture_mut_ref_param_finals` must OMIT them (the
    /// pre-existing "postcondition over an unresolvable final fails closed"
    /// path — an `Error`, not a `Counterexample` against a spurious havoc
    /// model). A later STRAIGHT-LINE deref write re-establishes exact
    /// tracking and removes the root again (the region stack is empty exactly
    /// in the straight-line body).
    deref_region_havoced_roots: BTreeSet<String>,
    ambient_solver_mode: Option<SolverMode>,
    helper_contracts: Option<&'a BTreeMap<String, HelperCallContract>>,
    recorded_helper_contract_call_sites: BTreeSet<usize>,
    /// Dedup set for the Phase C part 2 direct-application seam
    /// (`record_closure_application_obligations`), keyed by call-site pointer.
    /// The seam runs only from `visit_expr_call`, but the guard keeps the
    /// call-site contract obligations emitted exactly ONCE even if a node is
    /// revisited (mirrors `recorded_helper_contract_call_sites`).
    recorded_closure_application_call_sites: BTreeSet<usize>,
    /// Pre-havoc renderings of a free call's arguments, keyed by call-site
    /// pointer. Snapshotted in `visit_expr_call` BEFORE
    /// `havoc_mut_ref_call_arg_referents` rebinds `&mut`-passed roots, so the
    /// call-site `requires` obligation is checked against the state the callee
    /// actually receives (the PRE-call state). Without this, the `requires`
    /// substitution rendered `p` as the fresh post-call `p__havoc_0` and a
    /// satisfied precondition was wrongly counterexampled (refs
    /// `test_mut_ref_forward` regression, root cause d568e2e's free-call `&mut`
    /// havoc). The `ensures` assumption deliberately KEEPS the post-havoc
    /// rendering — it constrains the fresh post-call value.
    pre_havoc_call_args: HashMap<usize, Vec<String>>,
    /// `syn::ExprReference` nodes (ptr-keyed) that are literal `&mut v` call
    /// arguments whose referent the `&mut`-call-arg havoc ALREADY rebound to a
    /// fresh post-call symbol. `visit_expr_reference`'s general
    /// mutable-borrow-escape invalidation skips exactly these nodes (consuming
    /// the entry), so the fresh binding — the post-call model the call's
    /// `ensures` constrains — survives argument visiting. Any OTHER `&mut v`
    /// node (a `let r = &mut v;` alias, an unhandled call shape) still
    /// invalidates fail-closed.
    mut_ref_call_arg_reference_havocs: BTreeSet<usize>,
    trait_method_contracts: Option<&'a BTreeMap<(String, String), TraitMethodCallContract>>,
    recorded_trait_method_contract_call_sites: BTreeSet<usize>,
    /// Caller-side `requires` contracts for CONCRETE-receiver trait-method calls
    /// `s.f(args)` where `s: S` and `impl T for S` (unit 2). Keyed by the
    /// concrete type name (`receiver_ty.to_type_string()`). Shares the
    /// `next_helper_call_contract_index` counter with the path-form and generic
    /// trait-method maps so obligation names never collide.
    concrete_method_contracts: Option<&'a BTreeMap<(String, String), TraitMethodCallContract>>,
    recorded_concrete_method_contract_call_sites: BTreeSet<usize>,
    /// Caller-side `requires` contracts for QUALIFIED-UFCS trait-function calls
    /// `<S as T>::f(s, args)` (unit 4). These reuse the SAME `(type_name,
    /// method)`-keyed `concrete_method_contracts` table — the concrete type is
    /// named explicitly by the qualified-path `qself` rather than resolved from
    /// a receiver variable — and share the `next_helper_call_contract_index`
    /// counter so obligation names never collide with the other forms. A qself
    /// call recorded here must NOT consume the helper-call dedup set, so this
    /// keeps an independent dedup table keyed on the `ExprCall` pointer.
    recorded_qualified_trait_fn_call_sites: BTreeSet<usize>,
    /// Monotonic counter for fresh havoc-symbol names introduced when a struct/
    /// enum receiver is mutated in place by a `&mut self` (or unresolved non-pure)
    /// method call. See `havoc_struct_receiver`.
    next_struct_havoc_index: usize,
    /// Every fresh symbol minted by an UNMODELLED-MUTATION havoc
    /// (`havoc_struct_receiver` / `havoc_declared_binding_to_fresh`). Each one
    /// means "arbitrary post-mutation state of this binding".
    ///
    /// Read only by the return-value render lane
    /// ([`extract_scoped_return_expression`]), which reports the ones the
    /// rendered value actually READS as that render's `havoc_dependencies` so the
    /// caller can declare them. Recording is unconditional (the in-body lane
    /// simply never reads the set) so the two lanes cannot drift apart about
    /// which calls mutate.
    havoc_minted_symbols: BTreeSet<String>,
    /// Exec closures bound to a local (`let g = |..| ..;`), keyed by the local
    /// name. At an exec call site `g(args)` (or an immediately-invoked
    /// `(|..| ..)(args)`), the closure body's checked arithmetic / index accesses
    /// are instantiated (params substituted by the call arguments) and pinned via
    /// the SAME arith-safety / index-bounds obligations Verus checks at the call —
    /// closing the invoked-exec-closure-body panic-freedom hole (`let g = |x, y| x
    /// / y; g(a, b)` had its divide-by-zero unchecked).
    ///
    /// SOUNDNESS-CRITICAL discrimination (exec vs spec): only a closure that is
    /// BOUND TO A LOCAL and then CALLED as `g(args)` is instrumented. A SPEC
    /// closure passed inline to `Seq::new`/`map`/`filter`/`fold`/`forall`/`SpecFn`
    /// is an argument, never a `let`-bound-then-called local, so its ghost body is
    /// never instrumented — no false multiplication/overflow counterexample on
    /// valid ghost code (the cardinal `Seq::new(n, |i| ((i + 1) as i32) * 10)`
    /// surface still verifies). Snapshotted with the scope stack so an
    /// isolated-scope definition does not leak, and cleared on
    /// invalidate/shadow/rebind so a reassigned `g` cannot carry a stale body.
    exec_closure_defs: HashMap<String, syn::ExprClosure>,
    /// ACTIVE WRITTEN contracts of known local `trust_vc::closure!` literals,
    /// keyed by binding name, for Phase C reflection ground-fact emission. See
    /// [`ClosureReflectionContract`]. Mutations are journaled in
    /// `closure_reflection_contract_changes`, so a nested ordinary binding hides
    /// an outer closure contract and leaving the scope restores it. This is
    /// soundness-critical for pass-site linkage: a contract from a closure that
    /// has left lexical scope must never authorize a later bare-ident argument.
    closure_reflection_contracts: HashMap<String, ClosureReflectionContract>,
    /// Per-lexical-scope undo journal for `closure_reflection_contracts`. The
    /// first mutation of a name in a scope records its previously active value;
    /// `pop_scope` restores exactly that value. Included in `ScopeSnapshot` so
    /// proof/temporary extraction cannot publish a closure contract into its
    /// parent context.
    closure_reflection_contract_changes: Vec<HashMap<String, Option<ClosureReflectionContract>>>,
    /// INCREMENT 2a (Fn-bound closure dispatch, callee-side obligation model):
    /// the NAMES of value parameters `f: F` whose `F: Fn(A) -> B` bound Increment 1
    /// typed as a first-class `SpecFn` value (`fn_bound_spec_fn_param_types`). At a
    /// direct application `f(a)` of such a parameter,
    /// [`Self::emit_fn_bound_param_application_obligations`] emits the SOUND
    /// call-site conditional assume `call_requires%(f, a) ==> call_ensures%(f, a,
    /// f(a))` over the OPAQUE reflection UFs. Gating on this explicit set — rather
    /// than on "any `SpecFn`-typed variable" — confines the seam to genuine
    /// Fn-bound PARAMETERS (never a `closure!` literal, a bare closure, or a ghost
    /// `SpecFn<A,B>` param), matching the universally-quantified-closure soundness
    /// argument exactly.
    fn_bound_spec_fn_params: BTreeSet<String>,
    /// INCREMENT 2b (Fn-bound closure dispatch, pass-site linkage) re-entrancy
    /// guard: set only while rendering a pass-site linkage ground fact, whose
    /// substituted result term can itself be a contracted helper call `g(c, 5)`.
    /// Rendering that term routes through `format_call_expr`, which normally
    /// re-invokes `record_helper_contract_call`; because the substituted call node
    /// has a fresh pointer it escapes the call-site dedup and would recurse
    /// forever. While this flag is set, `record_helper_contract_call` returns
    /// immediately — the term is a REFERENCE to the already-processed call's
    /// result, not a new call occurrence, so it must emit no obligations.
    suppress_helper_contract_recording: bool,
    /// Scope stack (mirrors `scopes`) recording the declared/inferred modeled
    /// scalar type (bool/integer) of each `let`-local. Function PARAMETERS carry
    /// their type in the VC variable table (`get_variable_type`), but `let`-locals
    /// are deliberately NOT in that table (see `local_pattern_base`), so this is
    /// the only place a local's scalar type is available. Used to mint a
    /// correctly-typed fresh symbol for a loop-modified local when havocing the
    /// loop-body entry state for exec arithmetic-safety (see
    /// `push_loop_body_havoc`) and to materialize immutable snapshots of
    /// loop-modified values.
    scoped_local_types: Vec<HashMap<String, TrustVcType>>,
    /// Stack of loop-body havoc maps (one per active `while`-loop body being
    /// instrumented for arithmetic safety), each mapping a loop-MODIFIED scalar
    /// variable name to a fresh, unconstrained, SMT-declared symbol that models
    /// its arbitrary value at loop-body entry. SOUNDNESS-CRITICAL: a loop-body
    /// arithmetic-safety obligation (`x += 100` ⇒ overflow) must be checked
    /// against this HAVOC'd entry state (the var is arbitrary after any number of
    /// iterations), NOT the function-entry value — checking the entry value
    /// misses an overflow that only manifests after iterations. Consulted by
    /// `lookup_scoped` only while `render_loop_body_havoc` is set, so the havoc
    /// is confined to arithmetic-safety obligation rendering and never perturbs
    /// the loop invariant / post-loop / M4-transition value-numbering.
    loop_body_havoc: Vec<HashMap<String, String>>,
    /// When set, `lookup_scoped` resolves a loop-modified scalar variable to its
    /// fresh loop-body havoc symbol (from `loop_body_havoc`) instead of its
    /// ordinary scoped value. Toggled ON only transiently inside the
    /// arithmetic-safety / index-bounds emit helpers (`render_with_loop_body_havoc`),
    /// so the havoc rendering is invisible to every other extraction path.
    render_loop_body_havoc: bool,
    /// Stack of loop-body reachability guard strings (the loop GUARD and each
    /// loop INVARIANT, rendered over the fresh havoc symbols). A loop-body exec
    /// arithmetic-safety obligation is the Verus check "the body arithmetic does
    /// not panic GIVEN the guard and the invariant hold at body entry", so each
    /// emitted reflexive obligation is weakened to `!(guard) || !(inv) || (goal)`
    /// (see `guard_arith_obligation`). This is LOCAL to the arithmetic obligation
    /// — body `assert!`s are NOT weakened by it — so it cannot vacuously discharge
    /// a real assertion the way a global `assume(guard)` could when the guard is
    /// unsatisfiable (e.g. `i < n` with `n == 0`, the zero-trip case).
    loop_body_arith_guards: Vec<String>,
}

#[derive(Clone)]
struct LocalMacroDefinition {
    body: TokenStream,
}

const LOCAL_MACRO_EXPANSION_LIMIT: usize = 16;

/// Verbatim Verus warning (`vir/src/well_formed.rs`, `ExprX::AssertBy`).
///
/// Fires for a top-level `==>` in an `assert forall|..| .. by { .. }` body,
/// whose by-block — unlike the `implies` keyword's — does NOT assume the
/// antecedent. Upstream `assert_forall_by.rs::test_forallstmt_implies` asserts
/// the message text.
const ASSERT_FORALL_IMPLIES_ARROW_WARNING: &str =
    "using ==> in `assert forall` does not currently assume the antecedent in the body; \
     consider using `implies` instead of `==>`";

/// True when `expr` is the `__trust_vc_implies!(P, Q)` marker that
/// `chained_comparisons` lowers a top-level `==>` into.
fn expr_is_implies_marker(expr: &Expr) -> bool {
    let Expr::Macro(mac) = expr else {
        return false;
    };
    mac.mac
        .path
        .get_ident()
        .is_some_and(|ident| ident == crate::chained_comparisons::IMPLIES_MARKER_MACRO)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ErasedMutRefTarget {
    Local(String),
    Field { owner: String, member: String },
    Index { owner: String, index: String },
}

impl ErasedMutRefTarget {
    fn root_name(&self) -> &str {
        match self {
            ErasedMutRefTarget::Local(name) => name,
            ErasedMutRefTarget::Field { owner, .. } => owner,
            ErasedMutRefTarget::Index { owner, .. } => owner,
        }
    }
}

#[derive(Clone)]
struct ScopeSnapshot {
    scopes: Vec<BTreeMap<String, String>>,
    concrete_scoped_values: Vec<BTreeSet<String>>,
    ghost_collection_scopes: Vec<BTreeSet<String>>,
    scoped_struct_types: Vec<BTreeMap<String, String>>,
    erased_shared_ref_aliases: Vec<BTreeSet<String>>,
    erased_mut_ref_aliases: Vec<BTreeSet<String>>,
    erased_mut_ref_targets: Vec<BTreeMap<String, ErasedMutRefTarget>>,
    unsupported_index_receivers: Vec<BTreeSet<String>>,
    local_macros: Vec<BTreeMap<String, LocalMacroDefinition>>,
    exec_closure_defs: HashMap<String, syn::ExprClosure>,
    closure_reflection_contracts: HashMap<String, ClosureReflectionContract>,
    closure_reflection_contract_changes: Vec<HashMap<String, Option<ClosureReflectionContract>>>,
    scoped_local_types: Vec<HashMap<String, TrustVcType>>,
}

#[derive(Clone)]
struct LoopExtractionContext {
    modified_vars: Vec<String>,
    guard: String,
    /// Per-invariant ENTRY bindings `(var, pre-loop-value)` for loop-modified
    /// LET-LOCALS declared at the loop head. Registered against each invariant as
    /// a SCOPED assumption (`var == value`) that reaches ONLY the base-case
    /// (entry) check — never the inductive step or post-loop lanes — so a
    /// `let mut i = 0` counter's entry value pins the base case exactly as a
    /// param's `requires` would, without tripping the current-state vacuity
    /// precheck against the negated-guard exit fact. Empty for param-only loops.
    entry_bindings: Vec<(String, String)>,
    /// Names of the LoopInvariant/InvariantExceptBreak obligations emitted while
    /// this loop body is being visited. The single-iteration body transition
    /// captured for this loop is registered against each of these invariant
    /// names so the inductive step can bind modified vars to `f(pre-state)`.
    /// Part of M4 loop-body transition.
    invariant_names: Vec<String>,
    /// Single-measure `loop_decreases!` bindings emitted inside this (`while`,
    /// boolean-guarded) loop body. After the body visit, each measure's decrease
    /// AND non-negativity obligations are registered like an invariant — with the
    /// loop's modified set (extended by the measure's entry variable), guard, and
    /// the captured single-iteration transition (extended by the entry-binding
    /// `entry_var == measure[pre-state]`) — so the strict-descent obligation
    /// `measure < entry_var` (WF2) verifies as a frame-condition inductive step
    /// and the non-negativity floor `measure >= 0` (WF1) lands in the
    /// `loop_measures` lane. Only populated when an active loop context exists
    /// (bare `loop{}` / `for` leave it empty ⇒ free entry var ⇒ fail-closed
    /// Counterexample). Part of the file-path `loop_decreases!` wiring.
    measure_decreases: Vec<crate::decreases_runtime::LoopDecreaseBinding>,
}

#[derive(Clone)]
pub(super) struct HelperCallContract {
    pub(super) params: Vec<String>,
    pub(super) erased_shared_ref_params: Vec<bool>,
    /// Per-param: `&mut <bool/integer>` positions (slice D caller-side
    /// two-state). At the call site these params substitute VALUE (referent)
    /// renderings: the PRE-call rendering into `requires` and `old(P)` forms,
    /// the POST-havoc fresh symbol into bare `P` in `ensures`; `*P` is erased
    /// to the substituted value (the substitution values are referent values,
    /// never references).
    pub(super) mut_ref_scalar_params: Vec<bool>,
    pub(super) return_binding: String,
    pub(super) requires: Vec<HelperContractClause>,
    pub(super) ensures: Vec<HelperContractClause>,
    pub(super) allow_in_spec: bool,
}

#[derive(Clone)]
pub(super) struct HelperContractClause {
    pub(super) condition: Expr,
    pub(super) solver_mode: Option<SolverMode>,
    /// The callee clause's `#[verifier::proof_note("…")]`/`custom_err` label.
    /// For a `requires` clause it is attached to the caller-side
    /// `__call_requires_*` discharge obligation, so a caller that violates a
    /// LABELED precondition reports through the Verus error channel with the
    /// callee's label (upstream `test_requires2` / `test_proof_note_on_requires`).
    pub(super) proof_note: Option<crate::proof_note::ProofNoteLabel>,
}

/// Caller-side contract for a generic trait-bounded method call `z.f(args)`
/// where `z: TypeParam(P)` and `P: T`. Carries only the `requires` clauses (as
/// raw source strings, exactly as stored on `TraitMethodDecl`) that the caller
/// must discharge at the call site. The matching `ensures` is supplied globally
/// by the trait postcondition axiom (`assert_trait_postconditions`), so it is
/// deliberately NOT carried here — this is requires-only.
#[derive(Clone)]
pub(super) struct TraitMethodCallContract {
    /// The receiver binding name used inside the requires clauses (`self`,
    /// i.e. the trait receiver name). Substituted by the actual receiver.
    pub(super) receiver_binding: String,
    /// The trait method's declared parameter names (excluding `self`), in
    /// order, substituted positionally by the call arguments.
    pub(super) param_names: Vec<String>,
    /// The trait method's `requires` clauses, raw source strings.
    pub(super) requires: Vec<String>,
    /// The uninterpreted-function prefix `{trait_name}__{method}` used to name
    /// the emitted obligations (shares the call-index counter with the
    /// path-form helper contracts so names never collide).
    pub(super) uf_prefix: String,
}

impl<'a> AssertionCollector<'a> {
    fn new(
        vc: &'a mut VerificationContext,
        next_assertion_index: usize,
        ambient_solver_mode: Option<SolverMode>,
    ) -> Self {
        Self::new_inner(
            vc,
            next_assertion_index,
            ambient_solver_mode,
            None,
            None,
            None,
        )
    }

    fn new_with_helper_and_trait_method_contracts(
        vc: &'a mut VerificationContext,
        next_assertion_index: usize,
        ambient_solver_mode: Option<SolverMode>,
        helper_contracts: Option<&'a BTreeMap<String, HelperCallContract>>,
        trait_method_contracts: Option<&'a BTreeMap<(String, String), TraitMethodCallContract>>,
        concrete_method_contracts: Option<&'a BTreeMap<(String, String), TraitMethodCallContract>>,
    ) -> Self {
        Self::new_inner(
            vc,
            next_assertion_index,
            ambient_solver_mode,
            helper_contracts,
            trait_method_contracts,
            concrete_method_contracts,
        )
    }

    /// Apply the caller-state seed. THE single place either lane installs it —
    /// see [`CollectorLaneSeed`] for why "either lane" is soundness-critical and
    /// for the per-field audit of what is deliberately left at its default.
    ///
    /// Destructured exhaustively on purpose: a new seed field is a compile error
    /// here until it is actually installed, not a silently-dropped one.
    fn apply_lane_seed(&mut self, seed: &CollectorLaneSeed<'_>) {
        let CollectorLaneSeed {
            supported_mut_ref_param_targets,
            mut_ref_call_args,
            method_arg_mut_flags,
            mut_ref_reborrowable_bindings,
            fn_bound_spec_fn_params,
        } = seed;
        self.method_arg_mut_flags = (*method_arg_mut_flags).clone();
        self.mut_ref_reborrowable_bindings = (*mut_ref_reborrowable_bindings).clone();
        self.supported_mut_ref_param_targets = (*supported_mut_ref_param_targets).clone();
        // Scope 0 is the collector's outermost scope and is present from
        // construction, so this installs the erased-reference targets exactly
        // where `new_inner` used to.
        self.erased_mut_ref_aliases[0] = (*supported_mut_ref_param_targets).clone();
        self.erased_mut_ref_targets[0] = supported_mut_ref_param_targets
            .iter()
            .map(|name| (name.clone(), ErasedMutRefTarget::Local(name.clone())))
            .collect();
        self.mut_ref_call_args = (*mut_ref_call_args).clone();
        self.fn_bound_spec_fn_params = (*fn_bound_spec_fn_params).clone();
    }

    fn new_inner(
        vc: &'a mut VerificationContext,
        next_assertion_index: usize,
        ambient_solver_mode: Option<SolverMode>,
        helper_contracts: Option<&'a BTreeMap<String, HelperCallContract>>,
        trait_method_contracts: Option<&'a BTreeMap<(String, String), TraitMethodCallContract>>,
        concrete_method_contracts: Option<&'a BTreeMap<(String, String), TraitMethodCallContract>>,
    ) -> Self {
        // The `&mut`-param targets are no longer a construction argument: they
        // are part of `CollectorLaneSeed` and are installed by `apply_lane_seed`
        // so the return lane cannot get a differently-seeded collector than the
        // in-body lane. Construction starts them empty.
        Self {
            vc,
            next_assertion_index,
            next_helper_call_contract_index: 0,
            parse_error: None,
            scopes: vec![BTreeMap::new()],
            concrete_scoped_values: vec![BTreeSet::new()],
            ghost_collection_scopes: vec![BTreeSet::new()],
            scoped_struct_types: vec![BTreeMap::new()],
            erased_shared_ref_aliases: vec![BTreeSet::new()],
            erased_mut_ref_aliases: vec![BTreeSet::new()],
            erased_mut_ref_targets: vec![BTreeMap::new()],
            supported_mut_ref_param_targets: BTreeSet::new(),
            mut_ref_call_args: BTreeMap::new(),
            method_arg_mut_flags: BTreeMap::new(),
            mut_ref_reborrowable_bindings: BTreeSet::new(),
            unsupported_index_receivers: vec![BTreeSet::new()],
            local_macros: vec![BTreeMap::new()],
            macro_expansion_depth: 0,
            loop_contexts: Vec::new(),
            loop_body_depth: 0,
            path_conditions: Vec::new(),
            match_arm_unguardable_depth: 0,
            short_circuit_rhs_depth: 0,
            deref_write_rollback_depth: 0,
            deref_written_region_roots: Vec::new(),
            deref_region_havoced_roots: BTreeSet::new(),
            ambient_solver_mode,
            helper_contracts,
            recorded_helper_contract_call_sites: BTreeSet::new(),
            recorded_closure_application_call_sites: BTreeSet::new(),
            pre_havoc_call_args: HashMap::new(),
            mut_ref_call_arg_reference_havocs: BTreeSet::new(),
            trait_method_contracts,
            recorded_trait_method_contract_call_sites: BTreeSet::new(),
            concrete_method_contracts,
            recorded_concrete_method_contract_call_sites: BTreeSet::new(),
            recorded_qualified_trait_fn_call_sites: BTreeSet::new(),
            next_struct_havoc_index: 0,
            havoc_minted_symbols: BTreeSet::new(),
            exec_closure_defs: HashMap::new(),
            closure_reflection_contracts: HashMap::new(),
            closure_reflection_contract_changes: vec![HashMap::new()],
            fn_bound_spec_fn_params: BTreeSet::new(),
            suppress_helper_contract_recording: false,
            scoped_local_types: vec![HashMap::new()],
            loop_body_havoc: Vec::new(),
            render_loop_body_havoc: false,
            loop_body_arith_guards: Vec::new(),
        }
    }

    fn finish(self) -> TrustVcResult<()> {
        match self.parse_error {
            Some(err) => Err(err),
            None => Ok(()),
        }
    }

    /// Visits the function body exactly as `visit_block` does (a single pushed
    /// scope around the statements), but snapshots the final scoped value of
    /// every cleanly-tracked scalar `&mut` parameter **before** the body scope
    /// is popped. That snapshot is the FINAL (post-body) value at the
    /// fall-through exit — what a bare `&mut` parameter denotes in a Verus
    /// postcondition. The value-numbering is the same machinery that makes a
    /// body-level `assert!(*x == ..)` see the current value, so the captured
    /// value is exact whenever the parameter is still tracked at exit (i.e. it
    /// was not havoced by a branch/loop join). A param that was havoced — or
    /// never assigned — is simply absent from the returned map; the caller
    /// resolves that case using `MutRefPostState::appears_in_body`.
    fn visit_function_body_capturing_mut_ref_finals(
        &mut self,
        block: &syn::Block,
    ) -> BTreeMap<String, String> {
        self.push_scope();
        for stmt in &block.stmts {
            self.visit_stmt(stmt);
        }
        let finals = self.capture_mut_ref_param_finals();
        self.pop_scope();
        finals
    }

    /// Snapshots `lookup_scoped` for each supported `&mut` scalar param that is
    /// still bound in the current scope stack. A param bound to a non-trivial
    /// scoped value (i.e. assigned and not later havoced) yields its final
    /// value; an unbound param is omitted (entry == final, or havoced — the
    /// caller disambiguates). Nothing is captured on a pending parse error,
    /// since the partial scope state is meaningless once extraction has failed.
    fn capture_mut_ref_param_finals(&self) -> BTreeMap<String, String> {
        let mut finals = BTreeMap::new();
        if self.parse_error.is_some() {
            return finals;
        }
        for name in &self.supported_mut_ref_param_targets {
            // Slice-C remediation: a root havocked at a deref-write region
            // exit (branch/match/block/closure write) has NO resolvable final
            // — reporting the fresh havoc symbol would turn the contract path
            // into a counterexample against a spurious model. Omit it so the
            // resolver keeps the pre-existing fail-closed behavior (a later
            // straight-line write clears the mark and restores the clean
            // final).
            if self.deref_region_havoced_roots.contains(name) {
                continue;
            }
            if self.has_scoped_name(name) {
                finals.insert(name.clone(), self.lookup_scoped(name));
            }
        }
        finals
    }

    fn scoped_return_expression(
        &mut self,
        block: &syn::Block,
        return_expr: &Expr,
    ) -> Option<String> {
        let result = self.find_target_return_in_block(block, return_expr);
        if self.parse_error.is_some() {
            None
        } else {
            result
        }
    }

    fn find_target_return_in_block(&mut self, block: &syn::Block, target: &Expr) -> Option<String> {
        self.push_scope();
        for stmt in &block.stmts {
            if self.parse_error.is_some() {
                break;
            }
            if let Some(result) = self.find_target_return_in_stmt(stmt, target) {
                self.pop_scope();
                return Some(result);
            }
            self.visit_stmt(stmt);
        }
        self.pop_scope();
        None
    }

    fn find_target_return_in_stmt(&mut self, stmt: &Stmt, target: &Expr) -> Option<String> {
        let saved_scopes = self.scope_snapshot();
        let result = match stmt {
            Stmt::Local(local) => local.init.as_ref().and_then(|init| {
                self.find_target_return_in_expr(&init.expr, target)
                    .or_else(|| {
                        init.diverge.as_ref().and_then(|(_, diverge)| {
                            self.find_target_return_in_expr(diverge, target)
                        })
                    })
            }),
            Stmt::Expr(expr, _) => self.find_target_return_in_expr(expr, target),
            Stmt::Macro(_) | Stmt::Item(_) => None,
        };
        if result.is_none() {
            self.restore_scope_snapshot(saved_scopes);
        }
        result
    }

    fn find_target_return_in_expr(&mut self, expr: &Expr, target: &Expr) -> Option<String> {
        let saved_scopes = self.scope_snapshot();
        let result = self.find_target_return_in_expr_inner(expr, target);
        if result.is_none() {
            self.restore_scope_snapshot(saved_scopes);
        }
        result
    }

    fn find_target_return_in_expr_inner(&mut self, expr: &Expr, target: &Expr) -> Option<String> {
        if std::ptr::eq(expr, target) {
            return Some(self.expr_to_scoped_string(expr));
        }

        match expr {
            Expr::Return(ret) => ret.expr.as_ref().and_then(|inner| {
                if std::ptr::eq(inner.as_ref(), target) {
                    Some(self.expr_to_scoped_string(inner))
                } else {
                    self.find_target_return_in_expr(inner, target)
                }
            }),
            Expr::Block(block) => {
                let saved_scopes = self.scope_snapshot();
                let result = self.find_target_return_in_block(&block.block, target);
                self.restore_scope_snapshot(saved_scopes);
                result
            }
            Expr::If(expr_if) => self.find_target_return_in_if(expr_if, target),
            _ => None,
        }
    }

    fn find_target_return_in_if(&mut self, expr_if: &syn::ExprIf, target: &Expr) -> Option<String> {
        let saved_before_if = self.scope_snapshot();
        let then_bindings = if let Expr::Let(expr_let) = &*expr_if.cond {
            if let Some(result) = self.find_target_return_in_expr(&expr_let.expr, target) {
                return Some(result);
            }
            self.visit_expr(&expr_let.expr);
            bound_idents_from_pat(&expr_let.pat)
        } else {
            if let Some(result) = self.find_target_return_in_expr(&expr_if.cond, target) {
                return Some(result);
            }
            self.visit_expr(&expr_if.cond);
            BTreeSet::new()
        };
        let after_cond = self.scope_snapshot();

        self.restore_scope_snapshot(after_cond.clone());
        let then_result = {
            let saved = self.scope_snapshot();
            self.shadow_names(&then_bindings);
            let result = self.find_target_return_in_block(&expr_if.then_branch, target);
            self.restore_scope_snapshot(saved);
            result
        };
        if then_result.is_some() {
            return then_result;
        }

        if let Some((_, else_branch)) = &expr_if.else_branch {
            self.restore_scope_snapshot(after_cond);
            let else_result = {
                let saved = self.scope_snapshot();
                let result = self.find_target_return_in_expr(else_branch, target);
                self.restore_scope_snapshot(saved);
                result
            };
            if else_result.is_some() {
                return else_result;
            }
        }

        self.restore_scope_snapshot(saved_before_if);
        None
    }

    /// Add an assertion with an optional `proof_note`/`custom_err` label
    /// attached to the emitted obligation (Verus diagnostic parity: a labeled
    /// FAILING assert reports through the error channel).
    fn add_assertion_noted(
        &mut self,
        condition: String,
        note: Option<crate::proof_note::ProofNoteLabel>,
    ) {
        let name = format!("assertion_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        let condition = self.guard_with_path_conditions(&condition);
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assert(&name, &condition))
                .with_proof_note(note),
        );
    }

    /// Wrap an obligation condition string in the enclosing branch path
    /// conditions, yielding `(p1 && p2 && …) ==> condition` rendered as
    /// `!(p1) || !(p2) || … || (condition)`. With no enclosing branch this is the
    /// bare condition. Part of #2779 Feature B (branch-guarded asserts).
    fn guard_with_path_conditions(&self, condition: &str) -> String {
        if self.path_conditions.is_empty() {
            return condition.to_string();
        }
        let mut guarded = format!("({condition})");
        for path in self.path_conditions.iter().rev() {
            guarded = format!("!({path}) || ({guarded})");
        }
        guarded
    }

    /// Emit an arithmetic-safety obligation for a discarded-result exec
    /// arithmetic site (a `let` initializer or a scalar assignment RHS).
    ///
    /// Verus checks integer overflow / divide-by-zero / remainder at every
    /// exec arithmetic site, even when the result is bound to a fresh local or
    /// discarded. trust-vc's overflow checks are derived from each obligation's
    /// expression, so a site whose value never reaches an assertion would carry
    /// no obligation and go unchecked. We pin the scoped value into a reflexive
    /// `(v) == (v)` obligation: the equality is trivially Verified, but the
    /// overflow precheck fires on the arithmetic inside `v`. Gated on
    /// `check_overflow()` (exec functions only) so spec/proof bodies are
    /// unaffected. Part of #2778.
    fn maybe_emit_exec_arith_overflow_check(&mut self, rhs: &Expr, scoped_value: &str) {
        if !self.vc.check_overflow() {
            return;
        }
        // Scalar `+ - * / %` and bit-shifts (`<< >>`) both carry an exec
        // arithmetic-safety obligation that Verus checks at every site,
        // result-discarded or not. The shift obligation is the bit-shift-bounds
        // check (`0 <= b < width`, plus unsigned over-shift), which the encoder
        // emits unconditionally for a shift expression — wrapping the scoped
        // value in the reflexive `(z) == (z)` goal fires it the same way it
        // fires arithmetic overflow for `+`. This makes a bare `let z = x << y;`
        // faithful (surrogate-free) to upstream `bit_shift_*`. Part of #2778.
        if !rhs_is_checked_scalar_arithmetic(rhs) && !rhs_is_checked_bit_shift(rhs) {
            return;
        }
        // SOUNDNESS-CRITICAL (loop-body exec arithmetic safety): inside a havoc'd
        // loop body the obligation must be checked against the HAVOC'd
        // loop-body-entry state — a modified scalar is arbitrary after any number
        // of iterations (`x += 100` overflows u8 once x reaches 200, even though x
        // started at 200). Re-render `rhs` with loop-body havoc resolution active
        // so a modified scalar resolves to its fresh, unconstrained symbol (rather
        // than the function-entry value the caller pre-rendered in
        // `scoped_value`). `guard_arith_obligation` then weakens the goal by the
        // loop guard + invariant (over those same fresh symbols), the Verus
        // "panic-free GIVEN the guard and invariant hold at body entry" rule. When
        // no havoc frame is active (outside a loop, or a loop form that does not
        // set one up) the passed `scoped_value` is reused verbatim and there are
        // no arith guards, so behavior is byte-for-byte unchanged.
        let scoped = if self.has_active_loop_body_havoc() {
            self.render_with_loop_body_havoc(|c| c.expr_to_scoped_string(rhs))
        } else {
            scoped_value.to_string()
        };
        // Branch/arm-guard the reflexive arithmetic-safety obligation with the
        // enclosing path conditions (an `if` condition, a `match`-arm
        // pattern+guard, or a short-circuit `&&`/`||` reachability guard). The
        // encoder's overflow-check guarding (`encode_with_overflow_guard`) then
        // weakens the overflow / divide-by-zero / shift-bounds precheck to fire
        // only on the taken path, so a conditionally-evaluated arithmetic site
        // (`match sel { _ => a / sel }`, `if sel != 0 { a / sel }`, `b != 0 && a /
        // b`) that is SAFE under its guard no longer yields a spurious
        // entry-context counterexample, while an UNGUARDED top-level site (empty
        // `path_conditions`) is unchanged. Part of the match-arm arithmetic safety
        // fix (P0-B) and the short-circuit right-operand fix.
        let condition = self.guard_arith_obligation(&format!("({scoped}) == ({scoped})"));
        if self.loop_body_obligation_renders_inconsistently(&condition) {
            return;
        }
        let name = format!("overflow_check_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assert(&name, &condition)),
        );
    }

    /// SOUNDNESS-CRITICAL (exec array/slice OOB panic-freedom) — the index-bounds
    /// sibling of [`Self::maybe_emit_exec_arith_overflow_check`].
    ///
    /// Verus checks `0 <= i < len` at EVERY exec `a[i]` access, including ones
    /// whose value is discarded or never observed by an assertion. trust-vc's
    /// index-bounds obligation is derived from the obligation EXPRESSION (the
    /// encoder fires `add_seq_index_bounds_check` while resolving an index
    /// access), so a site whose value never reaches an assertion carried NO
    /// obligation and silently `Verified` despite a runtime OOB panic — UNLIKE
    /// the per-site scalar-arithmetic path. We pin the scoped index access into a
    /// reflexive `(a[i]) == (a[i])` obligation: the equality is trivially
    /// `Verified`, but resolving `a[i]` fires the index bound (`may_emit_overflow_checks`
    /// reports `Index` unconditionally, so the precheck runs even for a pure,
    /// arithmetic-free access). Resolving the OUTERMOST access also fires the
    /// bound for every nested index in its receiver/index position (e.g.
    /// `a[a[0]]` checks both `0 < len` and `a[0] < len`).
    ///
    /// Gated on `check_overflow()` (exec functions only — spec/proof bodies emit
    /// nothing) and DEFERRED inside loop bodies EXACTLY as the arithmetic path is:
    /// trust-vc's loop encoding does not yet route the guard/invariant into
    /// body-site obligations, so an in-loop bound would be solved in the
    /// function-entry context and yield a spurious counterexample. The accepted,
    /// sound incompleteness mirrors the arithmetic deferral. Part of #81.
    /// Whether an index ACCESS rooted at variable `root` is faithfully modeled,
    /// and so safe to instrument with a synthetic bounds obligation.
    ///
    /// A function PARAMETER is not held in the local scope (it is declared by the
    /// encoder from the signature), so it is modelable. A local bound to a real
    /// value (an array literal, an `update`-chain, a `Vec::new()`, …) is
    /// modelable. The ONE non-modelable case is a local bound to its OWN bare name
    /// `(root)` — the fallback the extractor uses when it cannot model the
    /// initializer (e.g. `let (left, right) = v.split_at_mut(..)` with an
    /// unsupported `split_at_mut`). Such a receiver is NOT declared in the
    /// encoder, so a bounds obligation over it would be an un-lowerable
    /// `unresolved variable` error; the unsupported feature already fails the
    /// function closed, so we skip emission rather than perturb that (sound)
    /// outcome. Part of #81.
    fn index_receiver_is_modelable(&self, root: &str) -> bool {
        !(self.has_scoped_name(root) && self.lookup_scoped(root) == format!("({root})"))
    }

    fn maybe_emit_exec_index_bounds_check(&mut self, scoped_access: &str) {
        if !self.vc.check_overflow() {
            return;
        }
        if !self.loop_contexts.is_empty() {
            return;
        }
        // Branch/arm-guard the reflexive index-bounds obligation with the enclosing
        // path conditions, the index-access sibling of the arithmetic-safety guard:
        // a conditionally-evaluated `a[i]` whose bound holds under its guard no
        // longer over-rejects (top-level access unchanged — empty path conditions).
        let condition =
            self.guard_with_path_conditions(&format!("({scoped_access}) == ({scoped_access})"));
        let name = format!("index_bounds_check_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assert(&name, &condition)),
        );
    }

    /// Pin an index-bounds obligation (via [`Self::maybe_emit_exec_index_bounds_check`])
    /// for every value-position array/slice/map index ACCESS reachable in `expr`
    /// — an exec `let` initializer, a scalar-assignment RHS, a bare expression
    /// statement, or an index-write RHS. The accesses are isolated to the bare
    /// `a[i]` term (looking through transparent value wrappers, additive operands,
    /// and the unconditionally-evaluated aggregate / call sub-positions —
    /// tuple/array/struct-literal elements and call/method arguments) rather than
    /// the whole expression, so an un-modelable surrounding method call cannot
    /// demote a genuine bound, yet an access nested in an aggregate or argument is
    /// no longer silently skipped (the narrower residual of #81). Deduplicated so
    /// a repeated access (`a[i] + a[i]`) pins one obligation.
    fn emit_exec_index_bounds_checks_in_expr(&mut self, expr: &Expr) {
        if !self.vc.check_overflow() || !self.loop_contexts.is_empty() {
            return;
        }
        let mut accesses = Vec::new();
        collect_value_position_index_exprs(expr, &mut accesses);
        let mut seen = BTreeSet::new();
        for access in accesses {
            // NOTE (deliberate divergence from the #81 compound-write side-effect
            // gate): a side-effecting index/receiver is NOT skipped here. The READ
            // bound is a throwaway reflexive `(a[i]) == (a[i])` — it pins NOTHING
            // into the persistent scope, so re-rendering the (already-resolved)
            // index does not duplicate the effect the way the compound-write
            // `update()`-chain does. Crucially, a side-effecting index whose value
            // is unbounded (e.g. `a[{ j = i; j }]` with `i` unbounded) is a genuine
            // OOB; skipping the bound would falsely `Verified` it, whereas pinning
            // the bound correctly fails it closed (and a provably-bounded
            // side-effecting index still verifies — no over-rejection). This is the
            // pre-existing top-level read-path behavior (which never gated on side
            // effects); the recursion simply applies it to nested positions too.
            //
            // Only instrument an access rooted at a declared variable. An access
            // whose root is anonymous or not a known scoped name (e.g. `left`
            // bound by an unsupported `split_at_mut`) cannot be faithfully
            // modeled; the unsupported feature already fails the function closed,
            // and emitting an un-lowerable obligation would only obscure that.
            match index_access_root_ident(access) {
                Some(root) if self.index_receiver_is_modelable(&root) => {}
                _ => continue,
            }
            let scoped = self.expr_to_scoped_string(access);
            if seen.insert(scoped.clone()) {
                self.maybe_emit_exec_index_bounds_check(&scoped);
            }
        }
    }

    /// SOUNDNESS-CRITICAL (exec scalar arithmetic panic-freedom) — the
    /// arithmetic-safety sibling of [`Self::emit_exec_index_bounds_checks_in_expr`].
    ///
    /// Pin an arithmetic-safety obligation (via
    /// [`Self::maybe_emit_exec_arith_overflow_check`], a reflexive
    /// `(v) == (v)` whose overflow / divide-by-zero / shift-bounds precheck fires
    /// on the arithmetic inside `v`) for every value-position checked-arithmetic
    /// or bit-shift expression reachable in `expr` — an exec `let` initializer, a
    /// scalar-assignment RHS, a bare expression statement, or a compound-assignment
    /// RHS. The top-level-only [`Self::maybe_emit_exec_arith_overflow_check`] saw
    /// ONLY a checked-arith RHS at the outermost position, so an arithmetic site
    /// nested in a tuple / array / struct literal or a call argument
    /// (`let _ = (a / b, 0);`, `f(a / b);`, `[a / b]`, `S { x: a / b }`) — and a
    /// bare arithmetic statement (`a / b;`) — carried NO obligation and silently
    /// `Verified` despite a guaranteed runtime panic. Deduplicated so a repeated
    /// site (`a / b + a / b`, which the collector pushes as one outer `+`) pins one
    /// obligation. Gated on `check_overflow()` and deferred inside loop bodies
    /// EXACTLY as the index-bounds / scalar-arithmetic paths are (the loop encoding
    /// owns body-site obligations).
    fn emit_exec_arith_safety_checks_in_expr(&mut self, expr: &Expr) {
        if !self.vc.check_overflow() {
            return;
        }
        let mut sites = Vec::new();
        let mut guards = Vec::new();
        collect_value_position_arith_exprs(expr, &mut guards, &mut sites);
        let mut seen = BTreeSet::new();
        for ArithSite { site, guards } in sites {
            // Render the site (the dedup key) over the fresh loop-body havoc
            // symbols inside a loop body, matching the rendering
            // `maybe_emit_exec_arith_overflow_check` re-derives; outside a loop
            // body this is the ordinary scoped rendering.
            let scoped = self.render_with_loop_body_havoc(|c| c.expr_to_scoped_string(site));
            // Render each enclosing short-circuit guard into a path-condition
            // string (the left-operand condition, negated for the `||` right
            // operand). The emitter then pushes these onto `path_conditions` so
            // `maybe_emit_exec_arith_overflow_check`'s `guard_with_path_conditions`
            // wraps the reflexive obligation as `!(guard) || ((v) == (v))`, and the
            // encoder's `encode_logic` overflow-guard fires the right operand's
            // precheck only on its reachable path. Rendered over the havoc symbols
            // too (a `b != 0` reachability guard for a havoc'd `b` must reference
            // the same fresh symbol the `a / b` site does).
            let guard_strs: Vec<String> = guards
                .iter()
                .map(|g| {
                    let rendered =
                        self.render_with_loop_body_havoc(|c| c.expr_to_scoped_string(g.cond));
                    if g.negate {
                        format!("!({rendered})")
                    } else {
                        rendered
                    }
                })
                .collect();
            // Dedup on the FULL (scoped site, guard stack) key: two sites with the
            // same scoped string but DIFFERENT reachability guards are distinct
            // obligations (e.g. one unconditional — the strictly stronger check —
            // and one guarded), so both must be emitted; identical site+guard pairs
            // collapse to one. Deduping on the scoped string alone could drop a
            // stronger unconditional check in favor of a weaker guarded one.
            if !seen.insert((scoped.clone(), guard_strs.clone())) {
                continue;
            }
            let pushed = guard_strs.len();
            for guard in guard_strs {
                self.path_conditions.push(guard);
            }
            self.maybe_emit_exec_arith_overflow_check(site, &scoped);
            for _ in 0..pushed {
                self.path_conditions.pop();
            }
        }
    }

    /// Pin a compound-assignment element-safety obligation `(value) == (value)`
    /// for an exec `a[i] OP= rhs` write, where `value` is the synthesized updated
    /// element `(a[i] OP rhs)`. The single reflexive obligation fires BOTH the
    /// write-index bound (resolving the old element `a[i]` runs
    /// `add_seq_index_bounds_check`, the same `i < len` precondition the discarded
    /// `update` would carry) AND the element arithmetic / shift overflow check
    /// Verus applies to `a[i] OP rhs` — plus any index bound nested in the index
    /// or RHS, which are subterms of `value`. `emit_overflow_check` is `false` on
    /// the value-computation path (`eval_scoped_stmts`), which must not emit
    /// obligations. Gated on `check_overflow()` and deferred inside loop bodies,
    /// mirroring the read / scalar-arithmetic paths. Part of #81.
    fn maybe_emit_exec_compound_element_safety(&mut self, value: &str, emit_overflow_check: bool) {
        if !emit_overflow_check || !self.vc.check_overflow() || !self.loop_contexts.is_empty() {
            return;
        }
        // Branch/arm-guard the compound element-safety obligation (see
        // `maybe_emit_exec_arith_overflow_check`): a compound write under an `if`/
        // arm guard is checked only on its taken path. Top-level writes are
        // unchanged (empty path conditions).
        let condition = self.guard_with_path_conditions(&format!("({value}) == ({value})"));
        let name = format!("overflow_check_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assert(&name, &condition)),
        );
    }

    /// Pin the SCALAR compound-assignment element-safety obligation `(value) ==
    /// (value)` for an exec `a OP= rhs` scalar write, where `value` is the
    /// synthesized updated value `(old_a) OP (rhs)` ALREADY rendered over the
    /// loop-body havoc symbols by the caller. Unlike the array-element sibling
    /// [`Self::maybe_emit_exec_compound_element_safety`] (which stays deferred
    /// inside a loop body — the `update()`-chain value is reused as the stored
    /// scoped value and would otherwise embed a fresh havoc symbol into the
    /// persistent state), the scalar value is throwaway, so it is emitted inside
    /// loop bodies too — weakened by the loop guard + invariant via
    /// `guard_arith_obligation`. This is the obligation that closes the loop-body
    /// `x += 100` overflow hole. Outside a loop body `guard_arith_obligation`
    /// reduces to `guard_with_path_conditions` and `value` is the ordinary
    /// rendering, so behavior is unchanged.
    fn maybe_emit_exec_scalar_compound_safety(&mut self, value: &str) {
        if !self.vc.check_overflow() {
            return;
        }
        let condition = self.guard_arith_obligation(&format!("({value}) == ({value})"));
        if self.loop_body_obligation_renders_inconsistently(&condition) {
            return;
        }
        let name = format!("overflow_check_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assert(&name, &condition)),
        );
    }

    /// Record (or clear) the exec-closure body bound to a local `name`.
    ///
    /// A `let g = |..| ..;` initializer that is a bare closure literal (looking
    /// through transparent paren/group wrappers) is recorded keyed by `g`; any
    /// other initializer — or `None` — clears a stale entry so a rebinding of `g`
    /// to a non-closure cannot be instrumented at a later `g(args)` call site.
    /// Part of #2778 invoked-exec-closure body arith.
    fn record_or_clear_exec_closure_def(&mut self, name: &str, init: Option<&Expr>) {
        match init.map(strip_paren_group_expr) {
            Some(Expr::Closure(closure)) => {
                self.exec_closure_defs
                    .insert(name.to_string(), closure.clone());
            }
            _ => {
                self.exec_closure_defs.remove(name);
            }
        }
    }

    /// SOUNDNESS-CRITICAL (invoked-exec-closure body panic-freedom): instrument the
    /// body of an EXEC closure that is actually CALLED in exec position.
    ///
    /// At `g(args)` where `g` was bound by `let g = |params| body;` — or at an
    /// immediately-invoked closure literal `(|params| body)(args)` — Verus checks
    /// the closure body's integer overflow / divide-by-zero / shift-bounds / array
    /// index bounds at the call, but trust-vc's isolated-scope closure visit drops
    /// the body's effects, so a `let g = |x, y| x / y; g(a, b)` silently `Verified`
    /// a divide-by-zero. We instantiate the body by substituting each closure
    /// parameter with the corresponding call ARGUMENT expression, then pin the same
    /// reflexive arith-safety / index-bounds obligations the straight-line paths
    /// use. The args resolve in the caller's scope, so a SAFE call (a `requires`
    /// precondition or bounded args, e.g. `requires(b != 0)`) still verifies — no
    /// over-rejection.
    ///
    /// EXEC-vs-SPEC discrimination: only a LOCAL-bound, then-CALLED closure reaches
    /// here. A SPEC closure handed inline to `Seq::new`/`map`/`fold`/… is an
    /// argument, never a `let`-bound-then-called local, so its ghost body is never
    /// instrumented (the cardinal `Seq::new(n, |i| ((i + 1) as i32) * 10)` surface
    /// keeps verifying). Gated on `check_overflow()` (exec only) and deferred
    /// inside loop bodies, exactly as the other arith-safety paths are.
    fn maybe_emit_invoked_exec_closure_arith_safety(&mut self, call: &syn::ExprCall) {
        if !self.vc.check_overflow() || !self.loop_contexts.is_empty() {
            return;
        }
        let closure = match strip_paren_group_expr(&call.func) {
            Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
                let name = path.path.segments[0].ident.to_string();
                match self.exec_closure_defs.get(&name) {
                    Some(closure) => closure.clone(),
                    None => return,
                }
            }
            Expr::Closure(closure) => closure.clone(),
            _ => return,
        };
        // Only simple-ident params with matching arity are instrumented; bail
        // (sound — leaves the body unchecked) on a destructuring/ref/typed-subpat
        // param or an arity mismatch so substitution stays exact.
        let mut param_names = Vec::with_capacity(closure.inputs.len());
        for input in &closure.inputs {
            match closure_param_simple_ident(input) {
                Some(name) => param_names.push(name),
                None => return,
            }
        }
        if param_names.len() != call.args.len() {
            return;
        }
        // Shadowing-safety: if the body re-binds a parameter name (a nested `let`,
        // closure param, or match binder of the same name), a flat substitution
        // could rewrite the inner binding's occurrence — bail to avoid pinning a
        // spurious site (no over-rejection). Mirrors `scoped_closure_string`.
        let body_bound = closure_body_bound_idents(&closure.body);
        if param_names.iter().any(|name| body_bound.contains(name)) {
            return;
        }
        let subst: HashMap<String, Expr> = param_names
            .into_iter()
            .zip(call.args.iter().cloned())
            .collect();
        if subst.is_empty() {
            // A zero-arg closure body still carries its own (capture-only)
            // arithmetic; instrument the body directly.
            let body = (*closure.body).clone();
            self.emit_exec_arith_safety_checks_in_expr(&body);
            self.emit_exec_index_bounds_checks_in_expr(&body);
            return;
        }
        let mut body = (*closure.body).clone();
        substitute_param_idents(&mut body, &subst);
        self.emit_exec_arith_safety_checks_in_expr(&body);
        self.emit_exec_index_bounds_checks_in_expr(&body);
    }

    /// Verify a `trust_vc::closure!(|p: T, …| requires(R) ensures(|r: U| E) BODY)`
    /// DEF-SIDE as an INDEPENDENT VC discharged in an ISOLATED child context.
    ///
    /// Over FRESH declared symbols, the child assumes `R`, binds the result to
    /// `BODY`, and asserts `E` — i.e. it discharges `R ∧ (res == BODY) ⊢ E` in a
    /// [`VerificationContext::isolated_closure_child`] whose own
    /// assumption/assertion vectors are DISCARDED before returning. The parent
    /// collector receives ZERO closure conjuncts: this method makes NO
    /// `add_assumption`/`add_assertion` call on `self`, so a contradictory
    /// `requires(false)` cannot inject `false` as a parent hypothesis and
    /// vacuously discharge unrelated parent obligations (the cardinal
    /// false-verify — a parent `assert!(false)` alongside a never-called
    /// `requires(false)` closure still Counterexamples). Only a NON-verifying
    /// child verdict crosses back, via
    /// [`VerificationContext::record_closure_def_side_failure`], to fail this
    /// function closed.
    ///
    /// The closure VALUE is never modeled — the assume-leak discipline: a
    /// passing def-side check never licenses call-site trust of the closure's
    /// ensures, so any call site `f(args)`, `f.requires`/`f.ensures` reflection,
    /// or capture stays fail-closed ("unknown return type for function 'f'").
    ///
    /// Fails closed (records `parse_error`, discharges nothing) on: a token
    /// parse error, a contract-less closure, a CAPTURED outer variable in
    /// R/BODY/E (the mutation-capture false-verify — an ensures proven against a
    /// capture's definition-time value must never be trusted later), a param or
    /// result type with no modelable sort, or a non-value (block/control-flow)
    /// body. Part of the file-path closure! wiring.
    ///
    /// `binding` is the bound name of a `let f = trust_vc::closure!(..)` literal
    /// (`None` for an anonymous / `let _ =` closure). When present AND the closure
    /// spec is fully modelable, Phase C reflection axioms defining
    /// `call_requires%`/`call_ensures%` over `f` are co-emitted (see
    /// [`Self::emit_closure_reflection_axioms`]) — a conservative extension over a
    /// disjoint UF that cannot poison the parent.
    fn emit_closure_def_side_obligation(&mut self, mac: &Macro, binding: Option<&str>) {
        if self.parse_error.is_some() {
            return;
        }
        let contract: BodyOptionClosureContract = match syn::parse2(mac.tokens.clone()) {
            Ok(contract) => contract,
            Err(source) => {
                self.parse_error = Some(TrustVcError::Parse {
                    context: "parse closure! contract",
                    source,
                });
                return;
            }
        };
        if !contract.has_contract_clause() {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract closure contract",
                detail: "closure!() without a requires or ensures clause is not supported".into(),
            });
            return;
        }

        // Body: unwrap a trailing `return <expr>` (a corpus shape); a
        // block/control-flow body is not a pure value and is not modelable here.
        let body_expr = match &contract.body {
            Expr::Return(ret) => match ret.expr.as_deref() {
                Some(expr) => expr.clone(),
                None => {
                    self.parse_error = Some(TrustVcError::Encoding {
                        context: "extract closure contract",
                        detail: "closure!() with a bare `return` (no value) is not supported"
                            .into(),
                    });
                    return;
                }
            },
            other => other.clone(),
        };
        if matches!(
            body_expr,
            Expr::Block(_)
                | Expr::ForLoop(_)
                | Expr::While(_)
                | Expr::Loop(_)
                | Expr::Match(_)
                | Expr::If(_)
                | Expr::Unsafe(_)
                | Expr::TryBlock(_)
                | Expr::Async(_)
                | Expr::Let(_)
                | Expr::Closure(_)
        ) {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract closure contract",
                detail: "closure!() with a non-value (block/control-flow) body is not supported"
                    .into(),
            });
            return;
        }

        // CAPTURE GUARD (the mutation-capture false-verify): reject any free
        // identifier in R ∪ BODY ∪ E that resolves to a DECLARED outer variable.
        // Such a capture would be proven at the closure's definition-time value
        // and could be trusted after it changed. (Function/type/method idents are
        // not declared VARIABLES, so this does not over-reject a pure call.)
        let mut bound: BTreeSet<String> =
            contract.params.iter().map(|p| p.name.to_string()).collect();
        if let Some(ensures) = &contract.ensures {
            bound.insert(ensures.result_name.to_string());
        }
        let mut referenced = BTreeSet::new();
        if let Some(requires) = &contract.requires {
            collect_token_stream_idents(requires.to_token_stream(), &mut referenced);
        }
        collect_token_stream_idents(contract.body.to_token_stream(), &mut referenced);
        if let Some(ensures) = &contract.ensures {
            collect_token_stream_idents(ensures.expr.to_token_stream(), &mut referenced);
        }
        for name in &referenced {
            if bound.contains(name) {
                continue;
            }
            // A free ident that is an in-scope `let`-local (tracked in
            // `scoped_local_types`) or a declared VC variable/param is a CAPTURE.
            // The `scoped_local_types` check is load-bearing: a `let c = …` local
            // is registered there but is NOT yet in the VC var table at
            // closure-definition time, so the var-table check alone misses it (the
            // mutation-capture / #74-contamination false-verify — a `requires(c ==
            // 5)` over a capture would leak a definition-time hypothesis about the
            // outer `c`). A pure spec-fn / const reference is neither a local nor a
            // VC var, so this does not over-reject those.
            let is_capture = self
                .scoped_local_types
                .iter()
                .any(|scope| scope.contains_key(name))
                || self.vc.get_variable_type(name).is_some();
            if is_capture {
                self.parse_error = Some(TrustVcError::Encoding {
                    context: "extract closure contract",
                    detail: format!(
                        "closure!() capturing outer variable `{name}` is not supported \
                         (its requires/ensures would leak a definition-time hypothesis \
                         about `{name}` into the enclosing verification context)"
                    ),
                });
                return;
            }
        }

        // Phase C reflection (co-located with, and guarded by, the same capture
        // guard and def-side obligation). Emitted AFTER the capture guard so no
        // axiom can ever mention a captured outer var, and BEFORE the no-ensures
        // early return so a bare-`requires` closure still publishes its
        // `call_requires%` definition. The axioms are DEFINITIONAL equalities over
        // the DISJOINT `call_requires%`/`call_ensures%` UF symbols — a conservative
        // extension that says nothing about whether the body establishes the
        // ensures (the def-side obligation independently forces that), so it can
        // neither poison nor rescue the parent context.
        if let Some(binding) = binding {
            self.emit_closure_reflection_axioms(binding, &contract);
        }

        // No ensures ⇒ no postcondition to prove ⇒ the def-side check is
        // vacuously valid (a bare `requires` need not be satisfiable, exactly as
        // upstream). Nothing is discharged and nothing leaks — return.
        let Some(ensures) = &contract.ensures else {
            return;
        };

        // Mint a fresh, declared, uniquely-named symbol per param + result, and
        // build the param/result → fresh rename map. `fresh_loop_body_symbol`
        // declares each in the parent VC var table (referenced by no parent
        // obligation, so inert there); the clone below carries them into the
        // isolated child, which is where they are actually constrained.
        let mut substitutions: BTreeMap<String, Expr> = BTreeMap::new();
        for param in &contract.params {
            let Some(ty) = closure_modelable_type(&param._ty) else {
                self.parse_error = Some(TrustVcError::Encoding {
                    context: "extract closure contract",
                    detail: format!(
                        "closure!() parameter `{}` has a type with no modelable sort",
                        param.name
                    ),
                });
                return;
            };
            let fresh = self.fresh_loop_body_symbol(&format!("closure_{}", param.name), ty);
            let Ok(fresh_expr) = syn::parse_str::<Expr>(&fresh) else {
                self.parse_error = Some(closure_internal_error("fresh param symbol"));
                return;
            };
            substitutions.insert(param.name.to_string(), fresh_expr);
        }

        let result_ty = ensures
            ._result_ty
            .clone()
            .or_else(|| contract._return_ty.clone());
        let Some(result_ty) = result_ty.as_ref().and_then(closure_modelable_type) else {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract closure contract",
                detail: "closure!() ensures result type has no modelable sort".into(),
            });
            return;
        };
        let fresh_result = self.fresh_loop_body_symbol("closure_result", result_ty);
        let Ok(result_expr) = syn::parse_str::<Expr>(&fresh_result) else {
            self.parse_error = Some(closure_internal_error("fresh result symbol"));
            return;
        };

        // Render the closure's conjuncts over the fresh symbols. Rendering uses
        // the PARENT scopes/registrations (to resolve spec-fns / consts), but the
        // results are strings referencing only the fresh closure symbols — they
        // are pushed as obligations onto the ISOLATED child, NEVER onto `self`.
        let requires_str = contract
            .requires
            .as_ref()
            .map(|requires| self.render_closure_clause(requires, &substitutions));
        let body_str = self.render_closure_clause(&body_expr, &substitutions);
        let mut ensures_subst = substitutions.clone();
        ensures_subst.insert(ensures.result_name.to_string(), result_expr);
        let ensures_str = self.render_closure_clause(&ensures.expr, &ensures_subst);

        // Build the isolated child context (its own obligation/assumption
        // vectors; the parent's proof obligations dropped) and discharge the
        // def-side VC `R ∧ (res == BODY) ⊢ E` there. The child is DISCARDED; only
        // a non-verifying verdict is recorded back on the parent.
        let mut child = self.vc.isolated_closure_child();
        if let Some(requires_str) = requires_str {
            child.push_obligation(self.with_ambient_solver_mode(ProofObligation::assume(
                "closure_def_side_requires",
                requires_str,
            )));
        }
        child.push_obligation(self.with_ambient_solver_mode(ProofObligation::assume(
            "closure_def_side_result",
            format!("{fresh_result} == ({body_str})"),
        )));
        child.push_obligation(self.with_ambient_solver_mode(ProofObligation::assert(
            "closure_def_side_ensures",
            ensures_str,
        )));
        let child_result = child.verify();
        // A contradictory antecedent (`requires(false)`, `requires(y==2 && y==3)`,
        // …) makes the def-side VC `R ∧ (res == BODY) ⊢ E` VACUOUSLY VALID: the
        // solver reports the unsatisfiable assumption set as
        // `Unknown{VacuousTruth}` rather than `Verified`, but a never-callable,
        // contradictory-precondition closure IS trivially def-side-valid (`false
        // ⇒ E` holds). Treating it as a PASS is soundness-CRITICAL for the poison
        // probe: it must NOT be recorded as a parent failure, so the parent's own
        // `assert!(false)` still surfaces its Counterexample. (The result binding
        // `res == BODY` over a fresh `res` is always satisfiable, so VacuousTruth
        // here can only come from an unsatisfiable `R`.) The closure value stays
        // unmodeled regardless, so a vacuous def-side pass never licenses call-site
        // trust. Every other non-`Verified` verdict (Counterexample, NotProved,
        // timeout/other Unknown, Error) fails this function CLOSED.
        let vacuously_valid = matches!(
            &child_result,
            crate::VerifyResult::Unknown {
                category: crate::encoder::UnknownCategory::VacuousTruth,
                ..
            }
        );
        if !child_result.is_verified() && !vacuously_valid {
            self.vc.record_closure_def_side_failure(child_result);
        }
    }

    /// Render a closure clause expression to a scoped condition string after
    /// substituting the closure's param/result idents with their fresh declared
    /// symbols. `ContractExprSubstituter` is a flat (non-scoped) ident rewriter.
    fn render_closure_clause(
        &mut self,
        expr: &Expr,
        substitutions: &BTreeMap<String, Expr>,
    ) -> String {
        let mut rewritten = expr.clone();
        let erased_shared_ref_params = BTreeSet::new();
        let old_substitutions = BTreeMap::new();
        let erased_mut_ref_value_params = BTreeSet::new();
        ContractExprSubstituter {
            substitutions,
            erased_shared_ref_params: &erased_shared_ref_params,
            old_substitutions: &old_substitutions,
            erased_mut_ref_value_params: &erased_mut_ref_value_params,
            binder_scopes: Vec::new(),
            unscopable_binder: false,
        }
        .visit_expr_mut(&mut rewritten);
        self.expr_to_scoped_string(&rewritten)
    }

    /// Phase C reflection, definition side: register the WRITTEN contract of a
    /// known local closure literal `let f = trust_vc::closure!(..)` so a later
    /// `f.requires(..)`/`f.ensures(..)` reflection can be discharged with a GROUND
    /// definitional fact at its use site (see
    /// [`Self::emit_reflection_ground_facts_in_expr`]).
    ///
    /// This ONLY declares `f : SpecFn(arg_tys, ret_ty)` (so the reflection surface
    /// lowers against a real term) and stashes the written clauses; it publishes
    /// NO axiom here. The opaque, DISJOINT reflection UFs `call_requires%` /
    /// `call_ensures%` never connect to a real return value (direct application is
    /// deferred), so each later ground fact is a CONSERVATIVE EXTENSION: it can
    /// neither introduce inconsistency (`requires(false)` yields
    /// `f.requires((a,)) == false`, the constant-false predicate, NOT the bare
    /// hypothesis `false`) nor let a caller read a false ensures as an ESTABLISHED
    /// fact (the equality fixes the UF's VALUE, saying nothing about the closure's
    /// real behaviour). The independent def-side obligation forces the body to
    /// back the ensures, so a lying closure still fails the whole function.
    ///
    /// Fails closed (registers nothing, leaves `f` unmodeled → later reflection
    /// fails to resolve) when any parameter or the result type has no modelable
    /// sort. The capture guard has already run in the caller, so no stored clause
    /// can mention a captured outer variable.
    fn emit_closure_reflection_axioms(
        &mut self,
        binding: &str,
        contract: &BodyOptionClosureContract,
    ) {
        // Modelable arg/result sorts, or fail closed (leave `f` unmodeled).
        let mut arg_tys = Vec::with_capacity(contract.params.len());
        for param in &contract.params {
            let Some(ty) = closure_modelable_type(&param._ty) else {
                return;
            };
            arg_tys.push(ty);
        }
        let ret_ty_syn = contract
            .ensures
            .as_ref()
            .and_then(|ensures| ensures._result_ty.clone())
            .or_else(|| contract._return_ty.clone());
        let Some(ret_ty) = ret_ty_syn.as_ref().and_then(closure_modelable_type) else {
            return;
        };

        // Register `f : SpecFn(arg_tys, ret_ty)` — a declared SMT const of the
        // uninterpreted `SpecFn{N}To{ret}` sort (via `build_type_env` → the
        // lowering `TypeEnv`) AND a scoped-local type entry so a later closure
        // capturing `f` fails closed. Direct application `f(..)` still fails closed
        // (dispatch/calls.rs).
        let spec_fn_ty = TrustVcType::SpecFn(arg_tys.clone(), Box::new(ret_ty));
        // This is a real Rust `let` binding, so it must participate in the same
        // value-scope shadowing as every generic local. Without the identity entry
        // an outer scalar model named `f` remains visible through `lookup_scoped`,
        // and the inner closure's reflection/pass-site terms are lowered as that
        // scalar (for example, `.requires()` on `u64`). `shadow_name` also hides
        // any active outer closure contract; the journal below restores it when
        // this lexical scope exits.
        self.shadow_name(binding);
        self.vc.declare_var_typed(binding, spec_fn_ty.clone());
        if let Some(scope) = self.scoped_local_types.last_mut() {
            scope.insert(binding.to_string(), spec_fn_ty);
        }

        // Stash the written clauses for use-site ground-fact emission. The
        // replacement is journaled so lexical/snapshot scope exit restores the
        // previously active binding (or removes this one if there was none).
        self.replace_closure_reflection_contract(
            binding.to_string(),
            ClosureReflectionContract {
                params: contract.params.iter().map(|p| p.name.to_string()).collect(),
                arg_tys,
                requires: contract.requires.clone(),
                ensures: contract
                    .ensures
                    .as_ref()
                    .map(|ensures| (ensures.result_name.to_string(), ensures.expr.clone())),
            },
        );
    }

    /// Phase C reflection, use side: for every `f.requires((a..))` /
    /// `f.ensures((a..), r)` REFLECTION over a registered closure literal appearing
    /// in `expr` (an assert!/assume! condition), emit the GROUND definitional
    /// assumption `f.requires((a..)) == R[p:=a]` / `f.ensures((a..), r) ==
    /// E[p:=a, result:=r]`. No quantifier is introduced, so a caller's reflection
    /// discharges (or counterexamples) cleanly. Emission is via
    /// [`Self::add_assumption_noted`], so the loop-body / unguardable-match-arm /
    /// short-circuit DROPs and the branch path-condition guard apply uniformly —
    /// an in-loop reflection read cannot be discharged from a dropped fact (fail
    /// closed, no verified-by-leak).
    fn emit_reflection_ground_facts_in_expr(&mut self, expr: &Expr) {
        if self.closure_reflection_contracts.is_empty() {
            return;
        }
        let uses = {
            let mut collector = ReflectionUseCollector {
                contracts: &self.closure_reflection_contracts,
                uses: Vec::new(),
            };
            syn::visit::Visit::visit_expr(&mut collector, expr);
            collector.uses
        };
        for mc in uses {
            self.emit_closure_reflection_ground_fact(&mc);
        }
    }

    /// Emit the single GROUND definitional fact for one reflection method call
    /// over a registered closure literal. Fails closed (emits nothing) on any
    /// arity/shape mismatch or a `f.ensures(..)` over a closure with no ensures —
    /// the caller's reflection then stays unprovable (fail closed).
    fn emit_closure_reflection_ground_fact(&mut self, mc: &syn::ExprMethodCall) {
        let Some(binding) = expr_path_ident(&mc.receiver) else {
            return;
        };
        let Some(contract) = self.closure_reflection_contracts.get(&binding).cloned() else {
            return;
        };
        let is_ensures = mc.method == "ensures";
        let expected_args = if is_ensures { 2 } else { 1 };
        if mc.args.len() != expected_args {
            return;
        }
        let Expr::Tuple(tuple) = strip_paren_group_expr(&mc.args[0]) else {
            return;
        };
        if tuple.elems.len() != contract.arg_tys.len() {
            return;
        }

        // param → actual-arg-expr substitution for the WRITTEN clause.
        let mut subst: BTreeMap<String, Expr> = contract
            .params
            .iter()
            .cloned()
            .zip(tuple.elems.iter().cloned())
            .collect();

        let rhs = if is_ensures {
            let Some((result_name, ensures_expr)) = contract.ensures.as_ref() else {
                // `f.ensures(..)` on a closure with no ensures: fail closed.
                return;
            };
            subst.insert(result_name.clone(), mc.args[1].clone());
            self.render_closure_clause(ensures_expr, &subst)
        } else {
            match contract.requires.as_ref() {
                Some(requires) => self.render_closure_clause(requires, &subst),
                None => "true".to_string(),
            }
        };

        // LHS renders through the SAME method-call renderer the assert uses, so the
        // ground fact's UF application is the identical term the reflection assert
        // encodes.
        let lhs = self.expr_to_scoped_string(&Expr::MethodCall(mc.clone()));
        self.add_assumption_noted(format!("{lhs} == ({rhs})"), None);
    }

    /// INCREMENT 2b (Fn-bound closure dispatch, cross-boundary PASS-SITE linkage):
    /// at a helper call `g(c, 5)` whose callee contract REFLECTS an Fn-bound value
    /// parameter (`requires f.requires((a,))` / `ensures f.ensures((a,), result)`),
    /// bridge the callee's OPAQUE reflection UFs to the passed closure literal's
    /// OWN concrete spec by emitting the definitional ground facts
    ///
    ///     call_requires%(c, <subst args>)            == R[c][params := subst args]
    ///     call_ensures%(c, <subst args>, <result>)   == E[c][params := subst args,
    ///                                                          result := <result>]
    ///
    /// where `c` is the passed `closure!` literal (`substitutions[f]`), the args
    /// are the callee's reflection arguments after call-site substitution (`a := 5`),
    /// and `<result>` is the substituted return binding (`g(c, 5)`). The callee's
    /// substituted `f.requires((a,))` / `f.ensures((a,), result)` reflection calls
    /// become `c.requires((5,))` / `c.ensures((5,), g(c, 5))` — the IDENTICAL UF
    /// applications this call's prove-`requires` obligation asserts and its
    /// assume-`ensures` binds — so the ground fact pins exactly those terms.
    ///
    /// SOUNDNESS.
    /// * GATE — emits ONLY for a bare-ident argument present in
    ///   `closure_reflection_contracts` (enforced by
    ///   [`Self::emit_closure_reflection_ground_fact`], which looks the receiver up
    ///   there). Registration ⇔ `emit_closure_reflection_axioms` ran ⇔ the closure's
    ///   independent def-side obligation was emitted at its `let c = …`. So the
    ///   linkage is BACKED by a checked def-side: a lying closure sinks the DEFINING
    ///   function at `record_closure_def_side_failure` (short-circuited in
    ///   `vc/verify.rs`), independent of this call site — 2b needs no separate
    ///   def-side check and cannot mask that failure. An Fn-bound PARAMETER
    ///   re-passed as an argument (`g(f, 5)`) is NOT in the map ⇒ NO ground fact ⇒
    ///   the callee's opaque `requires` stays undischargeable ⇒ FAILS CLOSED. This
    ///   is the identical invariant the direct-application literal seam relies on.
    /// * CONSERVATIVE — each fact FIXES the value of the opaque UF (never injects a
    ///   raw hypothesis `false`), so it can neither poison the context nor let an
    ///   unchecked ensures through; the def-side independently forces `c`'s body to
    ///   back the ensures.
    /// * A requires-violation (`g(c, 50)`) pins `call_requires%(c, (50,)) == (50 <
    ///   10) == false`, making the prove-`requires` obligation false ⇒ Counterexample.
    ///
    /// `requires` clauses substitute the PRE-call map, `ensures` the POST-havoc map
    /// (the same split the two obligations below use), so the linked terms are
    /// byte-for-byte the obligations' terms. A no-op when no closure literal is in
    /// scope.
    fn emit_closure_pass_site_linkage_facts(
        &mut self,
        contract: &HelperCallContract,
        substitutions: &BTreeMap<String, Expr>,
        requires_substitutions: &BTreeMap<String, Expr>,
        erased_shared_ref_params: &BTreeSet<String>,
        old_substitutions: &BTreeMap<String, Expr>,
        erased_mut_ref_value_params: &BTreeSet<String>,
    ) {
        if self.parse_error.is_some() || self.closure_reflection_contracts.is_empty() {
            return;
        }
        // Clone the clause expressions so the immutable borrow of `contract` does
        // not overlap the `&mut self` reflection-fact emission below.
        let requires_clauses: Vec<Expr> = contract
            .requires
            .iter()
            .map(|c| c.condition.clone())
            .collect();
        let ensures_clauses: Vec<Expr> = contract
            .ensures
            .iter()
            .map(|c| c.condition.clone())
            .collect();
        // Re-entrancy guard (see `suppress_helper_contract_recording`): the ground
        // fact renders substituted result terms that may be contracted helper
        // calls; suppress recursive helper-contract recording while doing so.
        let previously_suppressed = self.suppress_helper_contract_recording;
        self.suppress_helper_contract_recording = true;
        for condition in &requires_clauses {
            self.emit_pass_site_reflection_facts_for_clause(
                condition,
                requires_substitutions,
                erased_shared_ref_params,
                old_substitutions,
                erased_mut_ref_value_params,
            );
        }
        for condition in &ensures_clauses {
            self.emit_pass_site_reflection_facts_for_clause(
                condition,
                substitutions,
                erased_shared_ref_params,
                old_substitutions,
                erased_mut_ref_value_params,
            );
        }
        self.suppress_helper_contract_recording = previously_suppressed;
    }

    /// Substitute one callee contract clause with the call-site map, then emit a
    /// pass-site linkage ground fact for every `c.requires(..)` / `c.ensures(..)`
    /// reflection over a REGISTERED closure literal it now contains. Reuses the
    /// exact substituter the prove-`requires`/assume-`ensures` obligations use and
    /// the exact ground-fact renderer the intra-function reflection surface uses,
    /// so the linked UF application is byte-for-byte the obligation's term.
    fn emit_pass_site_reflection_facts_for_clause(
        &mut self,
        condition: &Expr,
        substitutions: &BTreeMap<String, Expr>,
        erased_shared_ref_params: &BTreeSet<String>,
        old_substitutions: &BTreeMap<String, Expr>,
        erased_mut_ref_value_params: &BTreeSet<String>,
    ) {
        let mut rewritten = condition.clone();
        ContractExprSubstituter {
            substitutions,
            erased_shared_ref_params,
            old_substitutions,
            erased_mut_ref_value_params,
            binder_scopes: Vec::new(),
            unscopable_binder: false,
        }
        .visit_expr_mut(&mut rewritten);
        // Collect `.requires`/`.ensures` reflection uses over REGISTERED closure
        // literals only — a bare-ident receiver present in
        // `closure_reflection_contracts` (the soundness gate). `uses` is owned, so
        // the immutable borrow is released before the `&mut self` emission loop.
        let uses = {
            let mut collector = ReflectionUseCollector {
                contracts: &self.closure_reflection_contracts,
                uses: Vec::new(),
            };
            syn::visit::Visit::visit_expr(&mut collector, &rewritten);
            collector.uses
        };
        for mc in uses {
            self.emit_closure_reflection_ground_fact(&mc);
        }
    }

    fn add_assumption(&mut self, condition: String) {
        self.add_assumption_noted(condition, None);
    }

    /// [`Self::add_assumption`] with an optional `proof_note`/`custom_err`
    /// label attached. An assume never fails in normal verification (the
    /// label is inert here); it is carried so the obligation metadata is
    /// complete rather than silently dropped.
    fn add_assumption_noted(
        &mut self,
        condition: String,
        note: Option<crate::proof_note::ProofNoteLabel>,
    ) {
        // SOUNDNESS-CRITICAL (loop-body assume! leak): a bare `assume!(P)` inside
        // ANY loop body (`while` / `for` / bare `loop` / `while let`) must NOT
        // contribute `P` as an assumption to the surrounding straight-line
        // context. The body may execute zero times, so the assume may never run;
        // trust-vc's loop encoding does not route a body assumption through the
        // loop's zero-trip / havoc model, so a body `assume!` would otherwise
        // survive as a flat, unconditional hypothesis PAST the (possibly skipped)
        // loop — a catastrophic false `Verified` (e.g. a post-loop
        // `assert!(x == 7)`, or a function postcondition, proven by a loop-body
        // `assume!(x == 7)` that never ran). Fail closed by DROPPING the assume
        // here, EXACTLY mirroring the loop-body call-`ensures` drop
        // (`add_helper_contract_obligations`) and the arithmetic-safety loop-body
        // deferral (`maybe_emit_exec_arith_overflow_check`). The accepted, sound
        // incompleteness: code that RELIES on a loop-body `assume!` (within or
        // after the loop) will not discharge from it. In-loop OBLIGATIONS
        // (`assert!`) are emitted elsewhere and are untouched — NOT made vacuous —
        // so an `assert!(false)` in a loop is STILL a counterexample.
        // `loop_body_depth` covers every loop form uniformly; `loop_contexts` is
        // OR'd for the boolean-guard `while` form for defense in depth. Dropped
        // before consuming a program-point index (mirrors the call-`ensures` drop).
        if self.loop_body_depth > 0 || !self.loop_contexts.is_empty() {
            return;
        }
        // SOUNDNESS-CRITICAL (match-arm assume leak): drop a bare `assume!` in a
        // `match` arm whose selection path condition could not be soundly rendered
        // (see `match_arm_unguardable_depth`). Without a guard the raw hypothesis
        // would leak past the match into sibling arms / straight-line code; we
        // cannot guard it, so we drop it (sound — removes a hypothesis). Dropped
        // before consuming a program-point index (mirrors the loop-body drop).
        if self.match_arm_unguardable_depth > 0 {
            return;
        }
        // SOUNDNESS-CRITICAL (short-circuit RHS assume leak): a bare `assume!`
        // inside the conditionally-evaluated RHS of `&&` / `||` (e.g.
        // `c && { assume!(P); true }`) may never run, and its conditionality is
        // not on the path-condition stack — drop it, exactly mirroring the
        // loop-body / unguardable-match-arm drops above (sound: removes a
        // hypothesis; in-RHS `assert!` obligations are untouched).
        if self.short_circuit_rhs_depth > 0 {
            return;
        }
        let name = format!("assumption_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        // SOUNDNESS-CRITICAL: branch-guard the assumption with its enclosing path
        // conditions, exactly as `add_assertion` does. A branch-local `assume!(P)`
        // under guard `G` is lowered to `G ==> P` (rendered `!(G) || (P)`), so it
        // holds UNCONDITIONALLY in the guarded form and cannot leak its raw `P`
        // into a sibling `else`, into post-branch code, or out as a function
        // postcondition. A statically-dead `if false { assume!(P) }` becomes
        // `!(false) || (P)` = `true`, i.e. no effect. Without this wrapping the
        // assumption was injected as a flat, unguarded global hypothesis — a
        // branch-local assume could prove a false whole-function contract.
        // The `assumption_{N}` name additionally carries the program point used
        // for forward-only ordering (see `verify_regular_assertions`).
        let condition = self.guard_with_path_conditions(&condition);
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assume(&name, &condition))
                .with_proof_note(note),
        );
    }

    fn add_loop_obligation(&mut self, kind: ObligationKind, prefix: &str, condition: String) {
        let name = format!("{}_{}", prefix, self.next_assertion_index);
        self.next_assertion_index += 1;
        let obligation = match kind {
            ObligationKind::LoopInvariant => ProofObligation::loop_invariant(&name, &condition),
            ObligationKind::InvariantExceptBreak => {
                ProofObligation::invariant_except_break(&name, &condition)
            }
            ObligationKind::LoopEnsures => ProofObligation::loop_ensures(&name, &condition),
            _ => ProofObligation::assert(&name, &condition),
        };
        self.vc
            .push_obligation(self.with_ambient_solver_mode(obligation));

        if matches!(
            kind,
            ObligationKind::LoopInvariant | ObligationKind::InvariantExceptBreak
        ) {
            // Record this invariant's name in the active loop context so the
            // body transition captured after the body visit can be registered
            // against it (M4), and propagate the modified-var/guard metadata.
            let context_data = self.loop_contexts.last_mut().map(|context| {
                context.invariant_names.push(name.clone());
                (
                    context.modified_vars.clone(),
                    context.guard.clone(),
                    context.entry_bindings.clone(),
                )
            });
            if let Some((modified_vars, guard, entry_bindings)) = context_data {
                self.vc.set_loop_modified_vars(&name, modified_vars);
                self.vc.add_loop_guard(&name, &guard);
                // Register the loop-modified let-locals' pre-loop values as SCOPED
                // entry assumptions for THIS invariant — reaches only the base-case
                // check (see set_loop_entry_scope / the typed base case). Empty for
                // param-only loops (no behavior change there).
                if !entry_bindings.is_empty() {
                    let entry_scope: Vec<ProofObligation> = entry_bindings
                        .iter()
                        .map(|(var, value)| {
                            ProofObligation::assume(
                                format!("{name}__entry_{var}"),
                                format!("{var} == ({value})"),
                            )
                        })
                        .collect();
                    self.vc.set_loop_entry_scope(&name, entry_scope);
                }
            }
        }
    }

    fn add_post_loop_assumption(&mut self, condition: String) {
        // SOUNDNESS-CRITICAL (post-loop normal-exit leak): the auto-generated
        // negated-guard exit fact (`!(guard)`) of a side-effect-free `while` must
        // be both (a) branch-guarded and (b) forward-ordered, exactly like a body
        // `assume!` / a call's `ensures`.
        //
        // (a) Branch-guard with the enclosing path conditions. A loop nested in a
        // branch (`if c { while g {..} }`) reaches its normal-exit point only when
        // the branch is taken, so the fact is lowered to `G ==> !(guard)` (rendered
        // `!(G) || (!(guard))`). Without this, the raw `!(guard)` leaked into a
        // sibling `else` (`else { assert!(!guard-implied) }`) and out as a function
        // postcondition established under a conditional loop — a false `Verified`.
        // A top-level (straight-line) loop has EMPTY path conditions, so this is a
        // no-op there and the genuine straight-line exit fact is unchanged.
        //
        // (b) Reserve ONE straight-line program point for the exit fact and stamp
        // it into a `post_loop_assumption_pp{N}` name that `body_program_point`
        // parses (mirroring `__call_ensures_pp{N}`). `forward_visible_assumptions`
        // then hides this current-state fact from any body `assert!` at an EARLIER
        // point, so an `assert!(!guard-implied)` textually BEFORE the loop is NOT
        // retroactively satisfied by the loop's exit fact. A post-loop `assert!`
        // (after the loop) has a strictly-later point and still sees the fact, so
        // the legitimate straight-line case keeps verifying.
        // SOUNDNESS-CRITICAL (short-circuit RHS exit-fact leak): a loop nested
        // in the conditionally-evaluated RHS of `&&` / `||` may never run, so
        // its negated-guard exit fact must not leak unconditionally (the RHS
        // conditionality is not on the path-condition stack). Drop it —
        // sibling of the `add_assumption_noted` short-circuit drop.
        if self.short_circuit_rhs_depth > 0 {
            return;
        }
        let program_point = self.next_assertion_index;
        self.next_assertion_index += 1;
        let name = format!("post_loop_assumption_pp{program_point}");
        let condition = self.guard_with_path_conditions(&condition);
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::post_loop_assume(&name, &condition)),
        );
    }

    fn add_option_closure_requires(&mut self, method: &str, condition: String) {
        let name = format!(
            "__option_{method}_closure_requires_{}",
            self.next_assertion_index
        );
        self.next_assertion_index += 1;
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assert(name, condition)),
        );
    }

    fn add_option_closure_ensures(&mut self, method: &str, condition: String) {
        let name = format!(
            "__option_{method}_closure_ensures_{}",
            self.next_assertion_index
        );
        self.next_assertion_index += 1;
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::ensures(name, condition)),
        );
    }

    fn with_ambient_solver_mode(&self, obligation: ProofObligation) -> ProofObligation {
        match self.ambient_solver_mode {
            Some(mode) => obligation.with_solver_mode(mode),
            None => obligation,
        }
    }

    fn visit_assertion_macro(&mut self, mac: &Macro) {
        self.visit_assertion_macro_with_attrs(mac, &[]);
    }

    /// Like [`Self::visit_assertion_macro`], but with the STATEMENT-level
    /// attributes of the enclosing `Stmt::Macro`/`Expr::Macro` node, so a
    /// `#[verifier::proof_note("…")] assert!(…);` label is pooled with any
    /// expression-level label inside the macro tokens (upstream
    /// `builtin_macros` moves statement attrs INSIDE onto the argument
    /// expression, so both positions form ONE pool).
    fn visit_assertion_macro_with_attrs(&mut self, mac: &Macro, stmt_attrs: &[syn::Attribute]) {
        if self.parse_error.is_some() {
            return;
        }

        match self.parse_assertion_obligations(mac, stmt_attrs) {
            Ok(conditions) => {
                for (condition, note) in conditions {
                    self.add_assertion_noted(condition, note);
                }
            }
            Err(err) => self.parse_error = Some(err),
        }
    }

    fn parse_assertion_obligations(
        &mut self,
        mac: &Macro,
        stmt_attrs: &[syn::Attribute],
    ) -> TrustVcResult<Vec<(String, Option<crate::proof_note::ProofNoteLabel>)>> {
        let Some(name) = super::path_last_segment(&mac.path) else {
            return Err(unsupported_macro_error(mac));
        };

        match name.as_str() {
            "assert" | "trust_vc_assert" => {
                if is_verus_assert_forall_by(&mac.tokens) {
                    self.add_assert_forall_by_macro(mac, &name)?;
                    return Ok(Vec::new());
                }

                let mut assertion_expr =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
                        .map_err(|source| TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "Failed to parse {}!() expression — this would silently drop the assertion: {}",
                                name, source
                            ),
                        })?;
                // Pool statement-level and expression-level proof-note labels
                // and enforce the upstream at-most-one rule at extraction
                // (translation) time — it fires even when the assert would
                // verify, exactly as upstream.
                let mut labels = crate::proof_note::proof_note_labels_from_attrs(stmt_attrs)?;
                labels.extend(crate::proof_note::take_leading_proof_note_labels(
                    &mut assertion_expr,
                )?);
                let note = crate::proof_note::at_most_one_proof_note(labels)?;
                // Phase C reflection: emit the GROUND definitional facts for any
                // `f.requires(..)`/`f.ensures(..)` in this assert BEFORE rendering
                // it, so the reflection assert can discharge/counterexample cleanly.
                self.emit_reflection_ground_facts_in_expr(&assertion_expr);
                // Phase C part 2: emit the call-site prove-requires + assume-ensures
                // for any DIRECT APPLICATION `f(arg)` of a registered closure literal
                // embedded in this assert, BEFORE the assert obligation is pushed so
                // the assume forward-dominates it.
                self.emit_closure_application_obligations_in_expr(&assertion_expr);
                let condition = self.expr_to_scoped_string(&assertion_expr);
                self.invalidate_expr_side_effects(&assertion_expr);
                Ok(vec![(condition, note)])
            }
            "assume" | "trust_vc_assume" => {
                let mut assumption_expr =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
                        .map_err(|source| TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "Failed to parse {}!() expression — this would silently drop the assumption: {}",
                                name, source
                            ),
                        })?;
                let mut labels = crate::proof_note::proof_note_labels_from_attrs(stmt_attrs)?;
                labels.extend(crate::proof_note::take_leading_proof_note_labels(
                    &mut assumption_expr,
                )?);
                let note = crate::proof_note::at_most_one_proof_note(labels)?;
                // Phase C reflection: emit GROUND definitional facts for any
                // `f.requires(..)`/`f.ensures(..)` reflected in this assume.
                self.emit_reflection_ground_facts_in_expr(&assumption_expr);
                // Phase C part 2: emit the call-site obligations for any DIRECT
                // APPLICATION `f(arg)` of a registered closure literal in this assume.
                self.emit_closure_application_obligations_in_expr(&assumption_expr);
                let condition = self.expr_to_scoped_string(&assumption_expr);
                self.invalidate_expr_side_effects(&assumption_expr);
                self.add_assumption_noted(condition, note);
                Ok(Vec::new())
            }
            "reveal" | "trust_vc_reveal" => {
                let path = syn::parse2::<syn::Path>(mac.tokens.clone()).map_err(|source| {
                    TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!(
                            "Failed to parse {}!() target — this would silently drop reveal metadata: {}",
                            name, source
                        ),
                    }
                })?;
                if path.segments.is_empty() {
                    return Err(TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!("{}!() requires a function path", name),
                    });
                }
                let Some(target_name) = reveal_target_name(&path) else {
                    return Err(TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!(
                            "{}!() supports only unqualified function names, optionally with generic arguments; got {}",
                            name,
                            path.to_token_stream()
                        ),
                    });
                };
                self.vc
                    .push_obligation(ProofObligation::reveal(target_name));
                Ok(Vec::new())
            }
            "hide" | "trust_vc_hide" => {
                // Mirror `reveal`: parse the target function path and push a
                // body-ordered Hide obligation. `prepare()` derives `hidden_fns`
                // from these (re-opaquing the body, like an unrevealed opaque
                // fn) and runs `reject_unsound_hide_reveal_interleave` to fail
                // closed on any `hide!(f) … reveal!(f)` that brackets a checked
                // obligation. Part of #2785.
                let path = syn::parse2::<syn::Path>(mac.tokens.clone()).map_err(|source| {
                    TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!(
                            "Failed to parse {}!() target — this would silently drop hide metadata: {}",
                            name, source
                        ),
                    }
                })?;
                if path.segments.is_empty() {
                    return Err(TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!("{}!() requires a function path", name),
                    });
                }
                let Some(target_name) = reveal_target_name(&path) else {
                    return Err(TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!(
                            "{}!() supports only unqualified function names, optionally with generic arguments; got {}",
                            name,
                            path.to_token_stream()
                        ),
                    });
                };
                self.vc.push_obligation(ProofObligation::hide(target_name));
                Ok(Vec::new())
            }
            "broadcast_use" | "trust_vc_broadcast_use" => {
                // Verus `broadcast use { g1, g2 }`: activate each named broadcast
                // group. SOUNDNESS-CRITICAL (forward-only, non-retroactive): push
                // a BODY-ORDERED `BroadcastUse` marker obligation at THIS program
                // point — mirroring how `reveal!`/`hide!` push body-ordered
                // markers — rather than folding activation into the
                // function-global `broadcast_use_groups` set. The position-aware
                // gate (`active_broadcast_groups_before`, consumed by
                // `setup_broadcasts.rs` / `invariants/mod.rs`) then admits a
                // grouped `BroadcastAssume` axiom only for proof obligations at or
                // after the marker, so a group activated here is NEVER visible to
                // an assertion that textually precedes it. Part of the file-path
                // `broadcast_use!` reinstatement.
                let groups = <syn::punctuated::Punctuated<syn::Path, syn::Token![,]>>::parse_terminated
                    .parse2(mac.tokens.clone())
                    .map_err(|source| TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!(
                            "Failed to parse {}!() group list — this would silently drop broadcast activation: {}",
                            name, source
                        ),
                    })?;
                if groups.is_empty() {
                    return Err(TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!("{}!() requires at least one broadcast group name", name),
                    });
                }
                for path in groups {
                    let Some(group) = path.segments.last().map(|s| s.ident.to_string()) else {
                        return Err(TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "{}!() group must be a name; got {}",
                                name,
                                path.to_token_stream()
                            ),
                        });
                    };
                    self.vc
                        .push_obligation(ProofObligation::broadcast_use(group));
                }
                Ok(Vec::new())
            }
            "invariant" | "trust_vc_invariant" => {
                let invariant_expr =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
                        .map_err(|source| TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "Failed to parse {}!() expression — this would silently drop the loop invariant: {}",
                                name, source
                            ),
                        })?;
                let condition = self.expr_to_scoped_string(&invariant_expr);
                self.invalidate_expr_side_effects(&invariant_expr);
                self.add_loop_obligation(
                    ObligationKind::LoopInvariant,
                    "loop_invariant",
                    condition,
                );
                Ok(Vec::new())
            }
            "invariant_except_break" | "trust_vc_invariant_except_break" => {
                let invariant_expr =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
                        .map_err(|source| TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "Failed to parse {}!() expression — this would silently drop the loop invariant: {}",
                                name, source
                            ),
                        })?;
                let condition = self.expr_to_scoped_string(&invariant_expr);
                self.invalidate_expr_side_effects(&invariant_expr);
                self.add_loop_obligation(
                    ObligationKind::InvariantExceptBreak,
                    "loop_invariant_except_break",
                    condition,
                );
                Ok(Vec::new())
            }
            "loop_ensures" | "trust_vc_loop_ensures" => {
                let ensures_expr =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
                        .map_err(|source| TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "Failed to parse {}!() expression — this would silently drop the loop ensures clause: {}",
                                name, source
                            ),
                        })?;
                let condition = self.expr_to_scoped_string(&ensures_expr);
                self.invalidate_expr_side_effects(&ensures_expr);
                self.add_loop_obligation(ObligationKind::LoopEnsures, "loop_ensures", condition);
                Ok(Vec::new())
            }
            "loop_decreases" | "trust_vc_loop_decreases" => {
                // Loop termination measure. Route through the SAME obligation
                // builder the runtime path uses (`build_loop_decreases_obligations`)
                // so the two paths cannot drift, then register the single-measure
                // decrease + non-negativity obligations as loop-inductive against
                // the active loop context (below). The measure is scoped exactly
                // like the loop `invariant!` above, so its variables share the
                // loop var's namespace and the captured single-iteration
                // transition applies.
                let measure_expr =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
                        .map_err(|source| TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "Failed to parse {}!() expression — this would silently drop the loop decreases measure: {}",
                                name, source
                            ),
                        })?;
                let measure = self.expr_to_scoped_string(&measure_expr);
                self.invalidate_expr_side_effects(&measure_expr);
                match crate::decreases_runtime::build_loop_decreases_obligations(
                    &mut self.vc,
                    measure,
                    None,
                ) {
                    Ok(Some(binding)) => {
                        // Only a `while` with a boolean guard pushes a loop
                        // context (see the while-loop visit). Bare `loop{}` / `for`
                        // leave `loop_contexts` empty here, so the decrease keeps
                        // its free entry variable and fails closed as a
                        // Counterexample — the continue-boundary / for-loop cases.
                        if let Some(context) = self.loop_contexts.last_mut() {
                            context.measure_decreases.push(binding);
                        }
                    }
                    // Lexicographic (tuple) measures and runtime idempotency
                    // re-entries return `None`: no inductive binding, so the
                    // decrease stays fail-closed on the file path.
                    Ok(None) => {}
                    // A present-but-unconstructible measure (invalid component or
                    // uninferable type) must FAIL CLOSED here — a silent drop
                    // under an `#[ensures(true)]` body would be a spurious
                    // Verified.
                    Err(err) => {
                        return Err(TrustVcError::Encoding {
                            context: "extract body assertions",
                            detail: format!(
                                "{}!() measure could not be constructed ({:?}); refusing to drop the termination obligation",
                                name, err
                            ),
                        });
                    }
                }
                Ok(Vec::new())
            }
            "assert_eq" => self
                .parse_binary_assert_macro(mac, &name, "==")
                .map(|c| vec![(c, None)]),
            "assert_ne" => self
                .parse_binary_assert_macro(mac, &name, "!=")
                .map(|c| vec![(c, None)]),
            "assert_seqs_equal" => self
                .parse_assert_seqs_equal_macro(mac, &name)
                .map(|c| vec![(c, None)]),
            "calc" => self
                .parse_calc_macro(mac, &name)
                .map(|cs| cs.into_iter().map(|c| (c, None)).collect()),
            "assert_forall_by" => {
                self.add_assert_forall_by_macro(mac, &name)?;
                Ok(Vec::new())
            }
            "assert_by_nonlinear" => {
                self.add_solver_mode_assert_macro(
                    mac,
                    &name,
                    SolverMode::NonlinearArith,
                    "assert_by_nonlinear",
                )?;
                Ok(Vec::new())
            }
            "assert_by_bit_vector" => {
                self.add_solver_mode_assert_macro(
                    mac,
                    &name,
                    SolverMode::BitVector,
                    "assert_by_bit_vector",
                )?;
                Ok(Vec::new())
            }
            "assert_by_compute" => {
                self.add_solver_mode_assert_macro(
                    mac,
                    &name,
                    SolverMode::Compute,
                    "assert_by_compute",
                )?;
                Ok(Vec::new())
            }
            "assert_by_contradiction" => {
                self.add_assert_by_contradiction_macro(mac, &name)?;
                Ok(Vec::new())
            }
            "assert_by" | "trust_vc_assert_by" => {
                self.add_assert_by_macro(mac, &name)?;
                Ok(Vec::new())
            }
            "debug_assert" | "debug_assert_eq" | "debug_assert_ne" => Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Unsupported {}!() in vc_extraction — debug-only assertions are rejected \
                     to avoid silently dropping proof obligations",
                    name
                ),
            }),
            "proof_block" | "trust_vc_proof_block" => {
                self.extract_exec_proof_block(mac, &name)?;
                Ok(Vec::new())
            }
            _ => Err(unsupported_macro_error(mac)),
        }
    }

    /// Lower a statement-position `proof_block!({ ... })` inside an **exec**
    /// function as a ghost-code mutation site (#2778, upstream `overflow.rs`
    /// `test_overflow_spec_*` / `proof_in_spec.rs`).
    ///
    /// Verus's `proof { ... }` block in exec code runs ghost statements whose
    /// assignments to ghost locals (e.g. `let ghost mut j; proof { j = add(j, 2); }`)
    /// are visible to the surrounding ghost state afterward, and whose arithmetic
    /// is unbounded (no exec overflow / div0 / bitshift obligation — proof code is
    /// not bound-checked). We faithfully reproduce both:
    ///
    /// * **Mutation propagation**: the block is visited under a single pushed
    ///   scope, so `assign_scoped` updates an *existing* outer ghost local in its
    ///   home scope (e.g. `j`) while any proof-local `let` stays scoped to the
    ///   block. This is the surrogate-free lowering that makes the literal
    ///   upstream body verify — the encoder-level truncating-`add` model
    ///   (`overflow_spec_add.rs`) then decides `j == add(a, 2)`.
    /// * **No exec arithmetic obligation**: overflow/div0/bitshift behaviors are
    ///   set to `Allow` for the duration of the block, so a ghost `j = j + 2`
    ///   never acquires the exec `+` overflow check, matching Verus's unbounded
    ///   ghost arithmetic.
    ///
    /// **Soundness scope.** This is supported *only* when the enclosing function
    /// is exec (`check_overflow()` true). Proof blocks inside spec/proof functions
    /// — and proof blocks used as value expressions (`let x = { proof { } v };`) —
    /// remain rejected as `Unsupported proof_block!()`, exactly matching the
    /// fail-closed upstream cases (`proof_in_spec.rs::{nonrecursive,recursive}_…`,
    /// `…_assignment_…`, `…_return_…`), because those route through spec/proof
    /// classification where `check_overflow()` is false. A `return` inside the
    /// block is also rejected (Verus: "return is not allowed inside proof"); a
    /// `return` would otherwise silently escape the ghost block.
    fn extract_exec_proof_block(&mut self, mac: &Macro, name: &str) -> TrustVcResult<()> {
        // Gate strictly on exec mode. In spec/proof functions `check_overflow()`
        // is false; we defer to the unsupported-macro rejection there so the
        // fail-closed `proof_in_spec.rs` cases keep their exact diagnostic.
        if !self.vc.check_overflow() {
            return Err(unsupported_macro_error(mac));
        }

        let block = syn::parse2::<syn::Block>(mac.tokens.clone()).map_err(|source| {
            TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {name}!() block — this would silently drop the ghost \
                     proof statements: {source}"
                ),
            }
        })?;

        // Verus forbids `return` inside a proof block; reject rather than let a
        // control-flow construct we do not model silently escape the ghost scope.
        if block.stmts.iter().any(stmt_contains_return) {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Unsupported `return` inside {name}!() — Verus does not allow return \
                     inside a proof block"
                ),
            });
        }

        // Ghost/proof arithmetic is unbounded: suppress exec overflow / div0 /
        // bitshift obligations for the duration of the block, then restore the
        // enclosing exec behaviors so downstream exec sites are still checked.
        let saved_overflow = self.vc.overflow_behavior();
        let saved_div0 = self.vc.div0_behavior();
        let saved_bitshift = self.vc.bitshift_behavior();
        self.vc
            .set_overflow_behavior(crate::vc::OverflowBehavior::Allow);
        self.vc.set_div0_behavior(crate::vc::Div0Behavior::Allow);
        self.vc
            .set_bitshift_behavior(crate::vc::BitshiftBehavior::Allow);

        // Visit under a single pushed scope so proof-local `let`s are block-scoped
        // while assignments to existing outer ghost locals propagate to their home
        // scope via `assign_scoped`.
        self.push_scope();
        for stmt in &block.stmts {
            if self.parse_error.is_some() {
                break;
            }
            self.visit_stmt(stmt);
        }
        self.pop_scope();

        self.vc.set_overflow_behavior(saved_overflow);
        self.vc.set_div0_behavior(saved_div0);
        self.vc.set_bitshift_behavior(saved_bitshift);

        match self.parse_error.take() {
            Some(err) => Err(err),
            None => Ok(()),
        }
    }

    /// Lower `assert_by!(condition, { proof_block })` — upstream Verus's
    /// `assert(condition) by { .. }` — on the FILE path (#34,
    /// `assert_forall_by.rs::test_assertby1`).
    ///
    /// Semantics reproduced (identical model to the SESSION/proc-macro path,
    /// which drains proof-block obligations into `assert_by_scopes`):
    ///
    /// * the proof block's statements (`assert!`, `assume!`, `reveal!`, `let`)
    ///   become the SCOPED obligations of the by-block;
    /// * the scoped assertions are proven under the scoped assumptions, then the
    ///   `condition` is proven under those established facts (`typed.rs`);
    /// * the proven CONCLUSION is exported to later obligations
    ///   (`verified_assert_by`) — upstream `test_assertby1`, where the fact
    ///   persists after the block;
    /// * a `reveal!(f)` inside the block is SCOPED to the block (see
    ///   `prepared_context::assert_by_scope_revealed_fns`): `f` stays opaque for
    ///   every obligation outside it — upstream `test_assertby1_fail2`. A leak
    ///   would prove MORE than Verus.
    ///
    /// Block-local `let`s are confined to the block by the scope snapshot in
    /// [`Self::extract_scoped_proof_block`].
    ///
    /// Only the two-argument Verus form is accepted; the single-argument
    /// `assert_by!(cond)` / `assert_by!({ lets; cond })` proc-macro shorthand
    /// has no Verus counterpart and is rejected fail-closed on the file path.
    fn add_assert_by_macro(&mut self, mac: &Macro, name: &str) -> TrustVcResult<()> {
        let crate::AssertByParsed::WithProofBlock {
            condition,
            proof_block,
        } = crate::parse_assert_by(mac.tokens.clone())
        else {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Unsupported {name}!() form in vc_extraction — the file path supports only the \
                     Verus-style two-argument form {name}!(condition, {{ proof_block }})"
                ),
            });
        };

        let condition_expr = crate::chained_comparisons::parse_expr_tokens_with_chains(condition)
            .map_err(|source| TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {name}!() condition — this would silently drop the assertion: {source}"
                ),
            })?;
        let condition = self.expr_to_scoped_string(&condition_expr);
        self.invalidate_expr_side_effects(&condition_expr);

        let assert_index = self.next_assertion_index;
        self.next_assertion_index += 1;
        let scoped = self.extract_scoped_proof_block(&proof_block, name)?;

        self.vc
            .add_assert_by(&format!("assert_by_{assert_index}"), &condition, scoped);
        if let Some(mode) = self.ambient_solver_mode {
            if let Some(last) = self.vc.obligations.last_mut() {
                last.solver_mode = Some(mode);
            }
        }
        Ok(())
    }

    fn add_assert_by_contradiction_macro(&mut self, mac: &Macro, name: &str) -> TrustVcResult<()> {
        let crate::AssertByParsed::WithProofBlock {
            condition,
            proof_block,
        } = crate::parse_assert_by(mac.tokens.clone())
        else {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {}!() block — expected assert_by_contradiction!(condition, {{ proof_block }})",
                    name
                ),
            });
        };

        let condition_expr =
            crate::chained_comparisons::parse_expr_tokens_with_chains(condition.clone()).map_err(
                |source| TrustVcError::Encoding {
                    context: "extract body assertions",
                    detail: format!(
                        "Failed to parse {}!() condition — this would silently drop the contradiction proof obligation: {}",
                        name, source
                    ),
                },
            )?;
        let condition = self.expr_to_scoped_string(&condition_expr);
        self.invalidate_expr_side_effects(&condition_expr);

        let assert_index = self.next_assertion_index;
        self.next_assertion_index += 1;
        let mut scoped = vec![ProofObligation::assume(
            format!("assert_by_contradiction_{assert_index}_assume_negated_goal"),
            format!("!({condition})"),
        )];
        scoped.extend(self.extract_assert_by_contradiction_proof_block(&proof_block)?);

        self.vc.add_assert_by(
            &format!("assert_by_contradiction_{assert_index}"),
            &condition,
            scoped,
        );
        Ok(())
    }

    fn add_solver_mode_assert_macro(
        &mut self,
        mac: &Macro,
        name: &str,
        solver_mode: SolverMode,
        obligation_prefix: &str,
    ) -> TrustVcResult<()> {
        // Verus parity (#2778, upstream nonlinear.rs
        // `test_assert_nonlinear_by_in_nonlinear`): a `#[verifier(nonlinear)]`
        // function IS one whole-function nonlinear query; a nested solver-mode
        // assert-by query inside it is rejected by Verus at the VIR level. The
        // diagnostic below deliberately contains the upstream message
        // verbatim. Fail-closed: rejecting the program can never wrongly
        // verify anything.
        if self.ambient_solver_mode == Some(SolverMode::NonlinearArith)
            && matches!(
                solver_mode,
                SolverMode::NonlinearArith | SolverMode::BitVector
            )
        {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "{name}!(): assert_by_query not allowed in #[verifier::nonlinear] functions"
                ),
            });
        }
        let parsed = crate::parse_solver_mode_assert(mac.tokens.clone()).map_err(|source| {
            TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {}!() expression — this would silently drop the assertion: {}",
                    name, source
                ),
            }
        })?;
        if parsed.compute_only && solver_mode != SolverMode::Compute {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "`compute_only` is only supported by assert_by_compute!(), not {}!()",
                    name
                ),
            });
        }
        if !parsed.requires.is_empty() && solver_mode == SolverMode::Compute {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: "`requires` clauses are not supported by assert_by_compute!()".to_string(),
            });
        }
        // Verus parity (upstream bitvector.rs::test_old_not_supported): the
        // `old` two-state operator is rejected inside a `by(bit_vector)` assert
        // at the VIR level ("`old` is not supported in `bit_vector` assert").
        // The bit-vector solver query has no entry-vs-current two-state model,
        // so `old` is unsupported there regardless of whether the surrounding
        // property happens to hold — the port's `*old(x) == *x` is even *true*
        // with no mutation, yet Verus still rejects it. trust-vc DOES model
        // `old()` soundly elsewhere (mut-ref two-state slice B — verified by
        // probe: `*x = 5; *old(x) == *x` correctly refutes with the entry
        // value), so this is a deliberate faithful restriction to Verus's
        // supported surface, not a soundness limitation. Fail-closed: rejecting
        // the program can never wrongly verify. Scoped strictly to BitVector to
        // leave the (unaffected) nonlinear/compute query modes untouched.
        if solver_mode == SolverMode::BitVector
            && (expr_uses_old_call(&parsed.condition)
                || parsed.requires.iter().any(expr_uses_old_call)
                || parsed.body.as_ref().is_some_and(block_uses_old_call))
        {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!("{name}!(): `old` is not supported in `bit_vector` assert"),
            });
        }
        // Verus-style scoped proof block (#2778, upstream nonlinear.rs test5 /
        // test_unexpected_vars). Extract the body assert expressions (only
        // plain `assert!(..)` statements are supported — fail-closed
        // otherwise) after enforcing the Verus query-interface scope rule.
        let body_asserts = match &parsed.body {
            Some(block) => {
                if solver_mode == SolverMode::Compute {
                    return Err(TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: "proof blocks are not supported by assert_by_compute!()"
                            .to_string(),
                    });
                }
                // Extract (and shape-check) the body FIRST so unsupported
                // statement forms get the capability diagnostic, then run the
                // Verus scope rule on the supported shape.
                let asserts = solver_mode_body_assert_exprs(block, name)?;
                self.check_solver_mode_body_scope(&parsed, block, name)?;
                asserts
            }
            None => Vec::new(),
        };

        let condition = self.expr_to_scoped_string(&parsed.condition);
        let assertion_index = self.next_assertion_index;
        let scoped_requires = parsed
            .requires
            .iter()
            .enumerate()
            .map(|(index, requires)| {
                ProofObligation::requires(
                    format!("{obligation_prefix}_{assertion_index}_requires_{index}"),
                    self.expr_to_scoped_string(requires),
                )
            })
            .collect::<Vec<_>>();

        let name = format!("{obligation_prefix}_{assertion_index}");
        self.next_assertion_index += 1;

        // Each proof-block assert is checked as its OWN scoped query under the
        // same scoped requires (strictly no weaker than Verus, which also
        // allows earlier body facts as hypotheses — proving from fewer
        // hypotheses can only fail more often, never wrongly verify), and the
        // established facts then join the goal query's hypotheses. Adding an
        // established fact as an extra `requires` of the goal is sound in both
        // roles of a scoped requires: as a hypothesis it was just proven from
        // the original requires, and as an enclosing-context obligation it
        // holds because the original requires do (the enclosing context
        // discharges them) and entail it.
        let mut goal_requires = scoped_requires.clone();
        for (body_index, body_expr) in body_asserts.iter().enumerate() {
            let body_condition = self.expr_to_scoped_string(body_expr);
            let body_name = format!("{name}_body_{body_index}");
            self.vc.add_assert_by_with_solver_mode(
                &body_name,
                &body_condition,
                scoped_requires.clone(),
                Some(solver_mode),
            );
            goal_requires.push(ProofObligation::requires(
                format!("{name}_body_fact_{body_index}"),
                body_condition,
            ));
        }

        self.vc
            .add_assert_by_with_solver_mode(&name, &condition, goal_requires, Some(solver_mode));
        Ok(())
    }

    /// Verus query-interface scope rule for solver-mode assert proof blocks
    /// (#2778, upstream nonlinear.rs `test_unexpected_vars`): every variable
    /// mentioned in the proof-block body must be mentioned in the query's
    /// interface — its goal (the `ensures` of the query) or its scoped
    /// `requires`. Verus rejects the query at the VIR level otherwise; the
    /// diagnostic below deliberately contains the upstream message
    /// ("not mentioned in requires/ensures") verbatim.
    ///
    /// The interface ident set is collected syntactically from the goal and
    /// requires expressions (including block-local `let` names, which only
    /// widens the set). Widening the allowed set can only ACCEPT more
    /// programs — never wrongly verify one, since every body fact is still
    /// proven as its own scoped query. (Body-local `let`s never reach this
    /// check: `solver_mode_body_assert_exprs` rejects them fail-closed
    /// first.)
    fn check_solver_mode_body_scope(
        &self,
        parsed: &crate::SolverModeAssertInput,
        block: &syn::Block,
        macro_name: &str,
    ) -> TrustVcResult<()> {
        use syn::visit::Visit;

        struct IdentCollector {
            idents: std::collections::BTreeSet<String>,
        }
        impl Visit<'_> for IdentCollector {
            fn visit_expr_path(&mut self, path: &syn::ExprPath) {
                if path.qself.is_none() {
                    if let Some(ident) = path.path.get_ident() {
                        self.idents.insert(ident.to_string());
                    }
                }
                syn::visit::visit_expr_path(self, path);
            }
            fn visit_pat_ident(&mut self, pat: &syn::PatIdent) {
                self.idents.insert(pat.ident.to_string());
                syn::visit::visit_pat_ident(self, pat);
            }
            fn visit_macro(&mut self, mac: &syn::Macro) {
                if let Ok(expr) =
                    crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
                {
                    self.visit_expr(&expr);
                }
                syn::visit::visit_macro(self, mac);
            }
        }

        let mut interface = IdentCollector {
            idents: std::collections::BTreeSet::new(),
        };
        interface.visit_expr(&parsed.condition);
        for requires in &parsed.requires {
            interface.visit_expr(requires);
        }

        let mut body = IdentCollector {
            idents: std::collections::BTreeSet::new(),
        };
        body.visit_block(block);

        for ident in &body.idents {
            if !interface.idents.contains(ident) {
                return Err(TrustVcError::Encoding {
                    context: "extract body assertions",
                    detail: format!(
                        "{macro_name}!() proof block: variable `{ident}` is \
                         not mentioned in requires/ensures of the scoped query"
                    ),
                });
            }
        }
        Ok(())
    }

    fn add_assert_forall_by_macro(&mut self, mac: &Macro, name: &str) -> TrustVcResult<()> {
        let parsed = crate::parse_assert_forall_by(mac.tokens.clone()).map_err(|source| {
            TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {}!() expression — this would silently drop the assertion: {}",
                    name, source
                ),
            }
        })?;

        let source_names = parsed
            .bound_vars
            .iter()
            .map(|var| var.name.clone())
            .collect::<Vec<_>>();
        // CAPTURE-AVOIDING RENAME. An `assert forall|i: int| …` binder is a BOUND
        // variable: it shadows any program variable of the same name. But the
        // encoder declares the function's params/locals and the quantifier's
        // bound vars into ONE flat solver namespace (`setup.rs` chains
        // `ctx.variables` with `extra_variables`), so a binder that reuses a
        // param name used to hard-error with "Variable 'i' already declared" —
        // rejecting a perfectly legal program (upstream `test_scope`, whose
        // `scope(b: bool, i: u64)` quantifies over `|i: int|`).
        //
        // Alpha-rename such binders to a fresh symbol and render the body,
        // triggers and proof block against the fresh name. Renaming a bound
        // variable is meaning-preserving, and it can only ever DISAMBIGUATE: the
        // binder can no longer be conflated with the outer program variable, so
        // the quantified fact stays about a genuinely universally-quantified
        // symbol. The outer `i` remains reachable to nothing inside the binder's
        // scope, exactly as Verus scopes it.
        let renames = self.fresh_assert_forall_binder_renames(&source_names);
        let bound_names = source_names
            .iter()
            .map(|name| renames.get(name).cloned().unwrap_or_else(|| name.clone()))
            .collect::<Vec<_>>();
        let (condition, trigger_patterns) = self.with_temporary_scopes(|collector| {
            collector.push_scope();
            for name in &source_names {
                let target = renames.get(name).map_or(name.as_str(), String::as_str);
                collector.shadow_name_as(name, target);
            }
            let condition = collector.expr_to_scoped_string(&parsed.closure.body);
            let trigger_patterns = parsed
                .trigger_patterns
                .iter()
                .map(|group| {
                    group
                        .iter()
                        .map(|trigger| collector.expr_to_scoped_string(trigger))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            collector.pop_scope();
            (condition, trigger_patterns)
        });
        // Verus `assert forall|x| A implies B by { .. }`: the by-block ASSUMES
        // the antecedent `A` (Verus keeps it in `AssertBy { require, .. }` and
        // emits it as an assumption of the forall's proof block). The `==>`
        // surface does NOT — see the warning below. The GOAL is `A ==> B` either
        // way, so this assumption is confined to the block: it is the standard
        // "fix an arbitrary x, assume A(x), prove B(x)" step, and it never
        // reaches any obligation outside the scope (`scoped_assumptions` in
        // `encoder/verification/typed.rs` is local to this assert-by).
        let mut scoped = Vec::new();
        if let Some(require) = &parsed.require {
            let antecedent = self.with_temporary_scopes(|collector| {
                collector.push_scope();
                for name in &source_names {
                    let target = renames.get(name).map_or(name.as_str(), String::as_str);
                    collector.shadow_name_as(name, target);
                }
                let rendered = collector.expr_to_scoped_string(require);
                collector.pop_scope();
                rendered
            });
            scoped.push(ProofObligation::assume(
                format!(
                    "assert_forall_by_{}_implies_antecedent",
                    self.next_assertion_index
                ),
                antecedent,
            ));
        } else if expr_is_implies_marker(&parsed.closure.body) {
            // Verus `vir/src/well_formed.rs` (`ExprX::AssertBy`, non-empty
            // `vars`): a top-level `==>` in an `assert forall` body warns,
            // because — unlike `implies` — its by-block does NOT assume the
            // antecedent. Verbatim upstream text; upstream
            // `assert_forall_by.rs::test_forallstmt_implies` asserts it.
            self.vc.push_warning(ASSERT_FORALL_IMPLIES_ARROW_WARNING);
        }
        scoped.extend(self.extract_assert_forall_by_proof_block(
            &parsed.proof_block,
            &source_names,
            &renames,
        )?);

        // Counterexample models still display the SOURCE binder name, so a
        // renamed binder reports `i = -1`, not `i__afb0 = -1`.
        for (source, fresh) in &renames {
            self.vc.register_counterexample_alias(fresh, source, true);
        }

        let owned_bound_vars = parsed
            .bound_vars
            .iter()
            .zip(bound_names.iter())
            .map(|(var, bound_name)| {
                (
                    bound_name.clone(),
                    crate::ir::TrustVcType::parse_or_opaque(&super::extract_type_name(&var.ty)),
                )
            })
            .collect::<Vec<_>>();
        let bound_vars = owned_bound_vars
            .iter()
            .map(|(var_name, ty)| (var_name.as_str(), ty.clone()))
            .collect::<Vec<_>>();

        let obligation_name = format!("assert_forall_by_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        self.vc.add_assert_forall_by_typed_with_trigger_patterns(
            &obligation_name,
            &condition,
            bound_vars,
            scoped,
            trigger_patterns,
        );
        if let Some(mode) = self.ambient_solver_mode {
            if let Some(last) = self.vc.obligations.last_mut() {
                last.solver_mode = Some(mode);
            }
        }
        Ok(())
    }

    fn parse_binary_assert_macro(
        &mut self,
        mac: &Macro,
        name: &str,
        op: &str,
    ) -> TrustVcResult<String> {
        let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
        let args = parser
            .parse2(mac.tokens.clone())
            .map_err(|source| TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {}!() arguments — this would silently drop the assertion: {}",
                    name, source
                ),
            })?;

        if args.len() < 2 {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "{}!() requires two expression arguments before any optional message",
                    name
                ),
            });
        }

        let Some(lhs_expr) = args.first() else {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!("{}!() requires a left-hand expression argument", name),
            });
        };
        let Some(rhs_expr) = args.iter().nth(1) else {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!("{}!() requires a right-hand expression argument", name),
            });
        };
        let lhs = self.expr_to_scoped_string(lhs_expr);
        self.invalidate_expr_side_effects(lhs_expr);
        let rhs = self.expr_to_scoped_string(rhs_expr);
        self.invalidate_expr_side_effects(rhs_expr);
        Ok(format!("{lhs} {op} {rhs}"))
    }

    fn parse_assert_seqs_equal_macro(&mut self, mac: &Macro, name: &str) -> TrustVcResult<String> {
        let parsed = crate::parse_assert_seqs_equal(mac.tokens.clone()).map_err(|source| {
            TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {}!() expression — this would silently drop the assertion: {}",
                    name, source
                ),
            }
        })?;

        let lhs = self.expr_to_scoped_string(&parsed.lhs);
        self.invalidate_expr_side_effects(&parsed.lhs);
        let rhs = self.expr_to_scoped_string(&parsed.rhs);
        self.invalidate_expr_side_effects(&parsed.rhs);
        Ok(format!("ext_eq!({lhs}, {rhs})"))
    }

    fn bind_local(&mut self, local: &syn::Local) {
        let value = self.local_init_scoped_value(local);
        let erased_mut_ref_target = self.local_mut_reference_target(local);
        let scoped_struct_type =
            self.local_scoped_struct_type_name(local, erased_mut_ref_target.as_ref());
        let concrete_value = self.local_init_is_concrete(local);
        self.bind_local_with_value(
            local,
            value,
            erased_mut_ref_target,
            concrete_value,
            scoped_struct_type,
        );
    }

    fn bind_local_with_value(
        &mut self,
        local: &syn::Local,
        value: Option<String>,
        erased_mut_ref_target: Option<ErasedMutRefTarget>,
        concrete_value: bool,
        scoped_struct_type: Option<String>,
    ) {
        // Verus-parity diagnostics (choose.rs #2777): reject a parenthesized
        // `forall(..)`/`exists(..)`/`choose(..)` binder and a `choose_tuple(..)`
        // whose binder tuple type mismatches the ascription. Placed at this common
        // chokepoint (both `bind_local` and the `AssertionCollector` statement
        // walk reach it) so it fires for tuple-destructure AND simple `let`s.
        // Fail-closed: surfacing the error before binding can only reject.
        if self.parse_error.is_none() {
            if let Some(err) =
                choose_binder_paren_error(local).or_else(|| choose_tuple_wrong_type_error(local))
            {
                self.parse_error = Some(err);
                return;
            }
        }
        if self.bind_destructuring_local(local) {
            return;
        }
        let Some(name) = local_ident(&local.pat) else {
            self.shadow_pat_bindings(&local.pat);
            return;
        };
        // Track / clear an exec-closure body bound to this local (`let g = |..|
        // ..;`) for the invoked-exec-closure body arith-safety instrumentation. A
        // closure initializer is recorded; any other rebinding clears a stale
        // entry so a later `g(args)` cannot instrument the wrong body. Part of
        // #2778 invoked-exec-closure body arith.
        self.record_or_clear_exec_closure_def(
            &name,
            local.init.as_ref().map(|init| init.expr.as_ref()),
        );
        let indexed_mut_ref_alias =
            local_pat_is_mut_reference(&local.pat) || local_init_is_mut_reference(local);
        let erased_mut_ref_alias = self.local_init_erases_mut_reference_alias(local);
        let erased_shared_ref_alias = local.init.as_ref().is_some_and(|init| {
            self.is_erased_shared_ref_expr(&init.expr)
                || (local_pat_is_shared_reference(&local.pat) && expr_is_call_result(&init.expr))
                || self.helper_call_returns_erased_shared_ref(&init.expr)
        });
        let Some(value) = value else {
            self.shadow_name(&name);
            if indexed_mut_ref_alias {
                self.mark_unsupported_index_receiver(&name);
            }
            if erased_mut_ref_alias {
                self.mark_erased_mut_ref_alias(&name);
                if let Some(target) = erased_mut_ref_target {
                    self.set_erased_mut_ref_target_current(&name, target);
                }
            }
            return;
        };
        // GAP2: infer whether the bound value models an immutable ghost
        // collection BEFORE inserting `name` (the inference inspects the init's
        // free names, not `name` itself).
        let models_ghost_collection = local
            .init
            .as_ref()
            .is_some_and(|init| self.expr_models_ghost_collection(&init.expr));
        self.current_scope_mut().insert(name.clone(), value);
        self.record_local_scalar_type(&name, local);
        self.set_concrete_scoped_current(&name, concrete_value);
        self.set_ghost_collection_current(&name, models_ghost_collection);
        if let Some(struct_type) = scoped_struct_type {
            self.set_struct_type_current(&name, struct_type);
        } else {
            self.clear_struct_type_current(&name);
        }
        if indexed_mut_ref_alias {
            self.mark_unsupported_index_receiver(&name);
        }
        if erased_mut_ref_alias {
            self.mark_erased_mut_ref_alias(&name);
            if let Some(target) = erased_mut_ref_target {
                self.set_erased_mut_ref_target_current(&name, target);
            } else {
                self.clear_erased_mut_ref_target_current(&name);
            }
        } else {
            self.unmark_erased_mut_ref_alias_current(&name);
        }
        if erased_shared_ref_alias {
            self.mark_erased_shared_ref_alias(&name);
        } else {
            self.unmark_erased_shared_ref_alias_current(&name);
        }
    }

    /// Record the declared / inferred modeled scalar type of `let`-local `name`
    /// in the current scope, for loop-body havoc and immutable-snapshot typing.
    /// Bool/integer scalars are modelable; other or un-inferable locals are not
    /// recorded.
    fn record_local_scalar_type(&mut self, name: &str, local: &syn::Local) {
        if let Some(ty) = self.local_declared_scalar_type(local) {
            if let Some(scope) = self.scoped_local_types.last_mut() {
                scope.insert(name.to_string(), ty);
            }
        }
    }

    /// The modeled scalar type of a `let`-local, taken from an explicit `: T`
    /// annotation when present, else inferred from a suffixed-literal,
    /// referenced-variable, or dereference initializer. `None` for non-scalar or
    /// un-inferable locals (`String::from(..)`, an unsuffixed-literal-free call, …).
    fn local_declared_scalar_type(&self, local: &syn::Local) -> Option<TrustVcType> {
        if let Pat::Type(pat_type) = &local.pat {
            let ty = TrustVcType::parse_or_opaque(&super::extract_type_name(&pat_type.ty));
            if matches!(ty, TrustVcType::Bool) || ty.is_integer() {
                return Some(ty);
            }
        }
        let init = local.init.as_ref()?;
        self.infer_scalar_type_from_init(&init.expr)
    }

    fn infer_scalar_type_from_init(&self, expr: &Expr) -> Option<TrustVcType> {
        if let Expr::Unary(unary) = strip_place_wrappers(expr) {
            if matches!(unary.op, syn::UnOp::Deref(_)) {
                let referenced = expr_path_ident(&unary.expr)?;
                return self.modified_var_scalar_type(&referenced);
            }
        }
        match crate::local_vars_helpers::infer_type_from_expr(expr) {
            crate::local_vars_helpers::TypeInference::Inferred(name) => {
                let ty = TrustVcType::parse_or_opaque(&name);
                (matches!(ty, TrustVcType::Bool) || ty.is_integer()).then_some(ty)
            }
            crate::local_vars_helpers::TypeInference::InferFromRef(referenced) => {
                self.modified_var_scalar_type(&referenced)
            }
            _ => None,
        }
    }

    /// The modeled scalar type of a loop-modifiable variable: a function
    /// parameter via the VC variable table, else a `let`-local via the scoped
    /// type stack. `None` (skip havoc) for non-scalar or untyped variables.
    fn modified_var_scalar_type(&self, name: &str) -> Option<TrustVcType> {
        if let Some(ty) = self.vc.get_variable_type(name) {
            return (matches!(ty, TrustVcType::Bool) || ty.is_integer()).then(|| ty.clone());
        }
        self.scoped_local_types
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .cloned()
    }

    /// Mint a fresh, unconstrained, SMT-declared symbol of `ty` modelling the
    /// arbitrary loop-body-entry value of modified scalar `name`.
    fn fresh_loop_body_symbol(&mut self, name: &str, ty: TrustVcType) -> String {
        let mut fresh = format!("{name}__loopbody_{}", self.next_struct_havoc_index);
        self.next_struct_havoc_index += 1;
        while self.vc.get_variable_type(&fresh).is_some() {
            fresh = format!("{name}__loopbody_{}", self.next_struct_havoc_index);
            self.next_struct_havoc_index += 1;
        }
        self.vc.declare_var_typed(&fresh, ty);
        fresh
    }

    /// Freeze visible scalar aliases whose values depend on a variable modified
    /// by the upcoming loop.
    ///
    /// Straight-line extraction normally substitutes an immutable local with its
    /// initializer: `let start = *x` makes `start` render as `x`. That ceases to
    /// be exact once a loop modifies `x`; without materialization,
    /// `invariant!(*x == start)` collapses to the tautology `x == x`. Each such
    /// local is therefore rebound to a fresh, framed scalar with an exact
    /// loop-entry binding. The regular assumption preserves the snapshot for
    /// later straight-line obligations, while the returned binding is scoped
    /// directly into the invariant base case.
    fn materialize_loop_snapshot_aliases(
        &mut self,
        modified: &BTreeSet<String>,
    ) -> Vec<(String, String)> {
        let mut seen = BTreeSet::new();
        let mut visible = Vec::new();
        for scope in self.scopes.iter().rev() {
            for (name, value) in scope {
                if seen.insert(name.clone()) {
                    visible.push((name.clone(), value.clone()));
                }
            }
        }

        let mut entry_bindings = Vec::new();
        for (name, value) in visible {
            if modified.contains(&name)
                || self.is_erased_shared_ref_name(&name)
                || self.is_erased_mut_ref_name(&name)
            {
                continue;
            }
            if !modified
                .iter()
                .any(|source| super::condition_references_word(&value, source))
            {
                continue;
            }
            let Some(ty) = self.modified_var_scalar_type(&name) else {
                continue;
            };

            let fresh = self.fresh_loop_body_symbol(&format!("{name}__loop_snapshot"), ty);
            self.add_assumption(format!("{fresh} == ({value})"));
            self.assign_scoped(&name, fresh.clone());
            self.set_concrete_scoped_nearest(&name, false);
            entry_bindings.push((fresh, value));
        }
        entry_bindings
    }

    /// Push a loop-body havoc frame for `modified_vars`. Every modified
    /// scalar variable is mapped to a fresh, unconstrained, declared
    /// symbol (its arbitrary value at loop-body entry); a modified var with no
    /// determinable scalar type is omitted (it then resolves to its ordinary
    /// scoped value — for an undeclared local an unresolved name that fails the
    /// arithmetic obligation CLOSED, never a false Verified). Tear down with
    /// `pop_loop_body_havoc`.
    fn push_loop_body_havoc(&mut self, modified_vars: &BTreeSet<String>) {
        let mut map = HashMap::new();
        for name in modified_vars {
            if let Some(ty) = self.modified_var_scalar_type(name) {
                let fresh = self.fresh_loop_body_symbol(name, ty);
                map.insert(name.clone(), fresh);
            }
        }
        self.loop_body_havoc.push(map);
    }

    fn pop_loop_body_havoc(&mut self) {
        self.loop_body_havoc.pop();
    }

    /// True iff the innermost loop-body havoc frame havoced at least one var (so
    /// loop-body arithmetic obligations are worth emitting / guarding).
    fn loop_body_has_havoc(&self) -> bool {
        self.loop_body_havoc
            .last()
            .is_some_and(|map| !map.is_empty())
    }

    /// True iff ANY active loop-body havoc frame havoced a var — the signal that
    /// an arithmetic obligation should be re-rendered over the fresh symbols
    /// (covers reads of an outer loop's modified var from an inner loop body).
    fn has_active_loop_body_havoc(&self) -> bool {
        self.loop_body_havoc.iter().any(|map| !map.is_empty())
    }

    /// Render `f` with loop-body havoc resolution active, so `lookup_scoped`
    /// resolves a modified scalar to its fresh havoc symbol. Used ONLY around
    /// arithmetic / index obligation rendering.
    fn render_with_loop_body_havoc<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let previous = self.render_loop_body_havoc;
        self.render_loop_body_havoc = true;
        let result = f(self);
        self.render_loop_body_havoc = previous;
        result
    }

    /// Render the loop GUARD (if any) and every top-level loop INVARIANT in
    /// `body` over the fresh havoc symbols, pushing each onto
    /// `loop_body_arith_guards`. Returns how many were pushed (to pop after the
    /// body visit). The havoc frame must already be pushed; when it havoced
    /// nothing, no guards are pushed (no arithmetic obligation will be emitted
    /// against a havoc symbol anyway).
    fn push_loop_body_arith_guards(&mut self, guard: Option<&Expr>, body: &syn::Block) -> usize {
        if !self.loop_body_has_havoc() {
            return 0;
        }
        let mut pushed = 0;
        if let Some(guard) = guard {
            let rendered = self.render_with_loop_body_havoc(|c| c.expr_to_scoped_string(guard));
            self.loop_body_arith_guards.push(rendered);
            pushed += 1;
        }
        for invariant in collect_loop_invariant_exprs(body) {
            let rendered =
                self.render_with_loop_body_havoc(|c| c.expr_to_scoped_string(&invariant));
            self.loop_body_arith_guards.push(rendered);
            pushed += 1;
        }
        pushed
    }

    fn pop_loop_body_arith_guards(&mut self, count: usize) {
        for _ in 0..count {
            self.loop_body_arith_guards.pop();
        }
    }

    /// Weaken a loop-body arithmetic-safety obligation by the active loop-body
    /// reachability guards (the loop guard + invariants, over the fresh havoc
    /// symbols): `!(g1) || !(g2) || (path-guarded condition)`. Outside a loop
    /// body `loop_body_arith_guards` is empty, so this is exactly
    /// `guard_with_path_conditions`.
    fn guard_arith_obligation(&self, condition: &str) -> String {
        let mut guarded = self.guard_with_path_conditions(condition);
        for guard in self.loop_body_arith_guards.iter().rev() {
            guarded = format!("!({guard}) || ({guarded})");
        }
        guarded
    }

    /// SOUNDNESS-CRITICAL: true iff `condition` (a fully-rendered loop-body
    /// arithmetic obligation) still mentions a HAVOC'd variable by its BARE name —
    /// the fresh symbol's value-numbered alias has not reached every occurrence.
    ///
    /// This happens when the obligation references a modified scalar INDIRECTLY:
    /// through a body-local that captured it before the havoc rename (`let k = i;
    /// k += 1`), or through a branch path condition rendered over the bare name
    /// (`if i > 5 { x += 100 }`). In those cases the guard speaks of `i__loopbody_N`
    /// while the site/condition speaks of bare `i` — two DIFFERENT symbols — so the
    /// obligation is inconsistent: the solver can satisfy the (unrelated) guard and
    /// vacuously discharge a real overflow, or reject a safe site against the
    /// stale function-entry value. Rather than emit an unsound / over-rejecting
    /// obligation we DEFER it (skip emission), exactly the pre-existing loop-body
    /// behavior for that site — closing the DIRECT-arithmetic hole (`x += 100`,
    /// `i += 1`, …) while leaving the narrower indirect/branch-conditional residual
    /// deferred (no new false-`Verified`, no over-rejection). Only consulted while
    /// a havoc frame is active.
    fn loop_body_obligation_renders_inconsistently(&self, condition: &str) -> bool {
        if !self.has_active_loop_body_havoc() {
            return false;
        }
        self.loop_body_havoc
            .iter()
            .flat_map(|map| map.keys())
            .any(|name| string_contains_whole_word(condition, name))
    }

    fn bind_destructuring_local(&mut self, local: &syn::Local) -> bool {
        if local_ident(&local.pat).is_some() {
            return false;
        }
        let Some(init) = local.init.as_ref() else {
            return false;
        };
        // Tuple-of-idents destructured from a branch of tuple literals
        // (#2778, upstream nonlinear.rs test_complex_vars):
        // `let (b1, b2) = if c { (a1, a2) } else { (a2, a1) };` binds each
        // component to the componentwise conditional
        // `bi = if c { theni } else { elsei }` — exact semantics when the
        // scrutinee is a pure expression (enforced by a purity whitelist,
        // fail-closed otherwise via the normal unresolved-variable error).
        if let Some(bindings) = self.tuple_conditional_destructure_bindings(local, init) {
            for (name, value) in bindings {
                self.current_scope_mut().insert(name.clone(), value);
                self.set_concrete_scoped_current(&name, false);
                self.set_ghost_collection_current(&name, false);
                self.clear_struct_type_current(&name);
                self.unmark_erased_shared_ref_alias_current(&name);
                self.unmark_erased_mut_ref_alias_current(&name);
                self.clear_erased_mut_ref_target_current(&name);
            }
            return true;
        }
        // Plain tuple pattern `let (a, b, ..) = <tuple expr>;` (non-conditional
        // init): bind each PLAIN-IDENT element to the corresponding tuple field
        // projection `.i` of the init. Tuple field access (`t.0`) is already a
        // supported term, so this is a faithful desugar — `a` binds to the
        // SCOPED value of `(init).i`, never a free/havoc variable. Fail closed
        // (fall through to the normal unresolved-variable path) on nested / rest
        // (`..`) / ref / mut sub-patterns so no element is silently mis-bound.
        if let syn::Pat::Tuple(pat_tuple) = &local.pat {
            // NO-ascription tuple whose type is recoverable from a multi-binder
            // `choose!(|i: T0, j: T1| ..)` init: route through a typed synthetic
            // local (projecting off the raw macro does not resolve — the tuple
            // elements would be left havoc). A plain-local init infers no type
            // here and falls through to the ordinary field-projection path below.
            if let Some(ty) = self.infer_untyped_tuple_local_type(&init.expr) {
                if self.bind_tuple_via_synthetic_local(pat_tuple, &ty, &init.expr) {
                    return true;
                }
            }
            if let Some(bindings) = self.tuple_pattern_field_bindings(pat_tuple, &init.expr) {
                for (name, value) in bindings {
                    self.current_scope_mut().insert(name.clone(), value);
                    self.set_concrete_scoped_current(&name, false);
                    self.set_ghost_collection_current(&name, false);
                    self.clear_struct_type_current(&name);
                    self.unmark_erased_shared_ref_alias_current(&name);
                    self.unmark_erased_mut_ref_alias_current(&name);
                    self.clear_erased_mut_ref_target_current(&name);
                }
                return true;
            }
        }
        let Some((base, base_ty)) = self.local_pattern_base(&init.expr) else {
            // The init has no resolvable projection base (e.g. a `choose!` macro
            // whose multi-binder form yields a tuple). A TYPED tuple pattern
            // `let (a, b): (T0, T1) = <init>;` can still be bound by routing the
            // init through a fresh typed local (the proven whole-tuple path).
            return self.bind_typed_tuple_via_synthetic_local(local, init);
        };
        let Some(bindings) = pattern_bindings_for_scoped_value(&local.pat, &base, &base_ty) else {
            return false;
        };
        if bindings.is_empty() {
            self.shadow_pat_bindings(&local.pat);
            return true;
        }
        for (name, value) in bindings {
            self.current_scope_mut().insert(name.clone(), value);
            self.set_concrete_scoped_current(&name, false);
            self.set_ghost_collection_current(&name, false);
            self.clear_struct_type_current(&name);
            self.unmark_erased_shared_ref_alias_current(&name);
            self.unmark_erased_mut_ref_alias_current(&name);
            self.clear_erased_mut_ref_target_current(&name);
        }
        true
    }

    /// Last-resort binding for a TYPED tuple pattern `let (a, b, ..): (T0, T1,
    /// ..) = <init>;` whose init is NOT a resolvable projection base — e.g. a
    /// `trust_vc::choose!(|i, j| ..)` macro whose multi-binder form yields a
    /// tuple. Such a pattern parses as `Pat::Type(Pat::Tuple, ty)`, which reaches
    /// neither the bare-`Pat::Tuple` projection path nor `local_pattern_base`
    /// (a macro init has no path ident), so without this the elements are left
    /// UNBOUND and any use fails closed as an unresolved variable.
    ///
    /// Bind the init to a fresh local of the annotated tuple type — the ordinary
    /// typed-local path, exactly as the user-written whole-tuple form
    /// `let t: (T0, T1) = <init>; t.0` (which verifies) — then project each
    /// element off that local's scoped value (`(src).i`, a supported tuple
    /// selector). Faithful desugar: every element binds to a field access of the
    /// same scoped value, never a free/havoc variable. Returns false (fall
    /// through to the fail-closed unresolved path) for any non-typed / non-tuple
    /// pattern, or a pattern element the projection path rejects.
    fn bind_typed_tuple_via_synthetic_local(
        &mut self,
        local: &syn::Local,
        init: &syn::LocalInit,
    ) -> bool {
        let syn::Pat::Type(pat_type) = &local.pat else {
            return false;
        };
        let syn::Pat::Tuple(pat_tuple) = pat_type.pat.as_ref() else {
            return false;
        };
        self.bind_tuple_via_synthetic_local(pat_tuple, pat_type.ty.as_ref(), &init.expr)
    }

    /// Bind a tuple pattern by routing `init_expr` through a fresh local of tuple
    /// type `ty` (the proven whole-tuple path `let t: ty = init; t.0`), then
    /// projecting each element off that local's scoped value. Shared by the
    /// ascribed-type path (`let (a, b): (T0, T1) = ..`) and the
    /// no-ascription-but-inferable path (`let (a, b) = choose!(|i: T0, j: T1| ..)`,
    /// whose tuple type is recovered from the choose binders). Returns false
    /// (fall through to the fail-closed path) if the projection rejects any
    /// element.
    fn bind_tuple_via_synthetic_local(
        &mut self,
        pat_tuple: &syn::PatTuple,
        ty: &syn::Type,
        init_expr: &Expr,
    ) -> bool {
        let src = format!("__tuple_src_{}", self.next_struct_havoc_index);
        self.next_struct_havoc_index += 1;
        let src_ident = syn::Ident::new(&src, proc_macro2::Span::call_site());
        let synth_stmt: Stmt = syn::parse_quote!(let #src_ident: #ty = #init_expr;);
        let Stmt::Local(synth) = synth_stmt else {
            return false;
        };
        self.bind_local(&synth);
        let src_base: Expr = syn::parse_quote!(#src_ident);
        let Some(bindings) = self.tuple_pattern_field_bindings(pat_tuple, &src_base) else {
            return false;
        };
        for (name, value) in bindings {
            self.current_scope_mut().insert(name.clone(), value);
            self.set_concrete_scoped_current(&name, false);
            self.set_ghost_collection_current(&name, false);
            self.clear_struct_type_current(&name);
            self.unmark_erased_shared_ref_alias_current(&name);
            self.unmark_erased_mut_ref_alias_current(&name);
            self.clear_erased_mut_ref_target_current(&name);
        }
        true
    }

    /// Recover the tuple type of a NO-ascription tuple local from a multi-binder
    /// `choose!(|i: T0, j: T1| ..)` macro initializer: `(T0, T1)`. Returns `None`
    /// unless `init` is a `choose!` macro whose closure has at least two
    /// fully-typed binders — so a single-binder choose, an untyped binder, or any
    /// non-choose / plain-local init falls through to the ordinary
    /// field-projection path (#2777 `test1_choose_tuple_no_ascription_...`).
    fn infer_untyped_tuple_local_type(&self, init: &Expr) -> Option<syn::Type> {
        let Expr::Macro(macro_expr) = init else {
            return None;
        };
        if super::path_last_segment(&macro_expr.mac.path).as_deref() != Some("choose") {
            return None;
        }
        let closure: syn::ExprClosure = syn::parse2(macro_expr.mac.tokens.clone()).ok()?;
        if closure.inputs.len() < 2 {
            return None;
        }
        let mut elems: Vec<syn::Type> = Vec::with_capacity(closure.inputs.len());
        for input in &closure.inputs {
            let syn::Pat::Type(pat_type) = input else {
                return None;
            };
            elems.push((*pat_type.ty).clone());
        }
        Some(syn::parse_quote!((#(#elems),*)))
    }

    /// `let (b1, .., bn) = if c { (t1, .., tn) } else { (e1, .., en) };` →
    /// componentwise scoped bindings `bi = if c { ti } else { ei }` (#2778,
    /// upstream nonlinear.rs test_complex_vars / test_requires_no_block).
    ///
    /// Exactness conditions (all required, else `None` → the normal
    /// fail-closed unbound-variable path):
    /// * the pattern is a tuple of plain idents;
    /// * the initializer (paren-stripped) is an `if` whose two branches are
    ///   statement-free blocks with tuple-literal tails of the same arity
    ///   (no `else if` chains);
    /// * the condition and every tuple element pass a strict purity
    ///   whitelist (paths, literals, unary/binary operators, parens, casts,
    ///   field accesses), so duplicating the condition across components
    ///   cannot duplicate effects;
    /// * no `let`-`else` diverge arm.
    fn tuple_conditional_destructure_bindings(
        &mut self,
        local: &syn::Local,
        init: &syn::LocalInit,
    ) -> Option<Vec<(String, String)>> {
        if init.diverge.is_some() {
            return None;
        }
        let syn::Pat::Tuple(pat_tuple) = &local.pat else {
            return None;
        };
        let names: Vec<String> = pat_tuple
            .elems
            .iter()
            .map(|pat| match pat {
                syn::Pat::Ident(ident) if ident.subpat.is_none() => Some(ident.ident.to_string()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        if names.is_empty() {
            return None;
        }

        fn strip(expr: &Expr) -> &Expr {
            match expr {
                Expr::Paren(p) => strip(&p.expr),
                Expr::Group(g) => strip(&g.expr),
                _ => expr,
            }
        }
        fn block_tuple_tail(block: &syn::Block, arity: usize) -> Option<Vec<Expr>> {
            let [Stmt::Expr(tail, None)] = block.stmts.as_slice() else {
                return None;
            };
            let Expr::Tuple(tuple) = strip(tail) else {
                return None;
            };
            if tuple.elems.len() != arity {
                return None;
            }
            Some(tuple.elems.iter().cloned().collect())
        }
        fn expr_is_pure(expr: &Expr) -> bool {
            match expr {
                Expr::Path(_) | Expr::Lit(_) => true,
                Expr::Paren(p) => expr_is_pure(&p.expr),
                Expr::Group(g) => expr_is_pure(&g.expr),
                Expr::Unary(u) => expr_is_pure(&u.expr),
                Expr::Binary(b) => expr_is_pure(&b.left) && expr_is_pure(&b.right),
                Expr::Cast(c) => expr_is_pure(&c.expr),
                Expr::Field(f) => expr_is_pure(&f.base),
                _ => false,
            }
        }

        let Expr::If(if_expr) = strip(&init.expr) else {
            return None;
        };
        if !expr_is_pure(&if_expr.cond) {
            return None;
        }
        let then_elems = block_tuple_tail(&if_expr.then_branch, names.len())?;
        let (_, else_expr) = if_expr.else_branch.as_ref()?;
        let Expr::Block(else_block) = strip(else_expr) else {
            return None;
        };
        let else_elems = block_tuple_tail(&else_block.block, names.len())?;
        if !then_elems.iter().chain(else_elems.iter()).all(expr_is_pure) {
            return None;
        }

        let mut bindings = Vec::with_capacity(names.len());
        for (index, name) in names.iter().enumerate() {
            let cond = &if_expr.cond;
            let then_i = &then_elems[index];
            let else_i = &else_elems[index];
            let value_expr: Expr = syn::parse_quote!(if #cond { #then_i } else { #else_i });
            let value = self.expr_to_scoped_string(&value_expr);
            bindings.push((name.clone(), value));
        }
        Some(bindings)
    }

    /// Field-projection bindings for a plain tuple pattern `let (a, b, ..) = t;`.
    /// Each PLAIN-IDENT element `elem_i` binds to the SCOPED value of `(t).i`
    /// (a supported tuple field access); a NESTED tuple element recurses on the
    /// projected base `(t).i`; wildcards are skipped. A trailing rest `..` is
    /// allowed (it just ignores the remaining fields — the bound elements before
    /// it keep their known indices). Returns `None` (fail closed) if any element
    /// is NOT a plain by-value ident / wildcard / nested tuple, or if a BINDING
    /// element follows the rest (its index would need the tuple's arity, which
    /// the pattern alone does not give) — so no element is bound to a wrong or
    /// ambiguous projection.
    fn tuple_pattern_field_bindings(
        &mut self,
        pat_tuple: &syn::PatTuple,
        init: &Expr,
    ) -> Option<Vec<(String, String)>> {
        let mut bindings = Vec::new();
        self.collect_tuple_pattern_bindings(&pat_tuple.elems, init, &mut bindings)?;
        (!bindings.is_empty()).then_some(bindings)
    }

    fn collect_tuple_pattern_bindings(
        &mut self,
        elems: &Punctuated<Pat, Token![,]>,
        base: &Expr,
        out: &mut Vec<(String, String)>,
    ) -> Option<()> {
        let mut index = 0usize;
        let mut seen_rest = false;
        for elem in elems {
            if matches!(elem, syn::Pat::Rest(_)) {
                if seen_rest {
                    return None; // two rests: invalid pattern, fail closed
                }
                seen_rest = true;
                continue;
            }
            if seen_rest {
                // After `..` the index is unknown (would need the tuple arity), so
                // only IGNORABLE wildcards are admissible; a real binding fails closed.
                if matches!(elem, syn::Pat::Wild(_)) {
                    continue;
                }
                return None;
            }
            let idx = syn::Index::from(index);
            match elem {
                syn::Pat::Ident(id)
                    if id.by_ref.is_none() && id.mutability.is_none() && id.subpat.is_none() =>
                {
                    let field_expr: Expr = syn::parse_quote!((#base).#idx);
                    let value = self.expr_to_scoped_string(&field_expr);
                    out.push((id.ident.to_string(), value));
                }
                syn::Pat::Wild(_) => {}
                syn::Pat::Tuple(inner) => {
                    let inner_base: Expr = syn::parse_quote!((#base).#idx);
                    self.collect_tuple_pattern_bindings(&inner.elems, &inner_base, out)?;
                }
                _ => return None,
            }
            index += 1;
        }
        Some(())
    }

    fn local_pattern_base(&mut self, expr: &Expr) -> Option<(String, TrustVcType)> {
        let name = expr_path_ident(expr)?;
        // Parameters (and other declared variables) carry their datatype in the
        // VC variable table, so resolve that first.
        if let Some(ty) = self.vc.get_variable_type(&name) {
            let ty = ty.clone();
            return Some((self.lookup_scoped(&name), ty));
        }
        // #102: let-locals are NOT in the VC variable table. When such a local
        // carries an inferred scoped struct/enum type name (e.g. it was bound
        // from a `Pair { .. }` literal or a `TupleThing(..)` tuple-struct
        // constructor), recover the SAME base `Datatype` the parameter path
        // would have produced from the registered struct/enum definitions. This
        // adds no new assumption: the destructure binds each pattern variable to
        // a field projection of the local's own scoped value, exactly as for a
        // parameter of that type.
        let type_name = self.scoped_struct_type_name(&name)?;
        let ty = self.datatype_for_scoped_type_name(&type_name)?;
        Some((self.lookup_scoped(&name), ty))
    }

    /// Resolves an inferred scoped struct/enum type-name string (which may carry
    /// a turbofish suffix or module path, e.g. `Pair :: < bool , bool >`) to the
    /// base `Datatype` registered for that user type. Structs come from
    /// [`VerificationContext::struct_types`]; enums fall back to the registered
    /// source type aliases.
    fn datatype_for_scoped_type_name(&self, type_name: &str) -> Option<TrustVcType> {
        let base = scoped_struct_type_base_name(type_name);
        if let Some(def) = self.vc.struct_types.iter().find(|def| def.name == base) {
            return Some(def.to_datatype_type());
        }
        match self.vc.source_type_aliases().get(&base) {
            Some(ty @ TrustVcType::Datatype { .. }) => Some(ty.clone()),
            _ => None,
        }
    }

    fn local_let_else_match_condition(&mut self, local: &syn::Local) -> Option<String> {
        let init = local.init.as_ref()?;
        init.diverge.as_ref()?;
        // An IRREFUTABLE binder matches every scrutinee, so its condition is
        // `true` regardless of the scrutinee's shape or whether its type
        // resolves. Answering that before `local_pattern_base` keeps a
        // `let x = f() else { … }` (non-path scrutinee, hence no resolvable
        // base) modelable instead of needlessly declining. `pattern_is_
        // irrefutable_binder` is the SAME predicate the type-aware arms below
        // reduce to, so this is a short-circuit, not a second opinion.
        if pattern_is_irrefutable_binder(&local.pat) {
            return Some("true".to_string());
        }
        let (base, base_ty) = self.local_pattern_base(&init.expr)?;
        pattern_match_condition_for_scoped_value(&local.pat, &base, &base_ty)
    }

    /// Walks `block` up to the tail let-else statement `local` so every binding
    /// introduced BEFORE it is in scope, then defers to
    /// [`Self::local_let_else_match_condition`]. The let-else statement itself is
    /// deliberately NOT visited: the match condition is evaluated in the state
    /// before the pattern binds.
    fn tail_let_else_match_condition(
        &mut self,
        block: &syn::Block,
        local: &syn::Local,
    ) -> Option<String> {
        self.push_scope();
        let mut condition = None;
        for stmt in &block.stmts {
            if self.parse_error.is_some() {
                break;
            }
            if let Stmt::Local(candidate) = stmt {
                if std::ptr::eq(candidate, local) {
                    condition = self.local_let_else_match_condition(local);
                    break;
                }
            }
            self.visit_stmt(stmt);
        }
        self.pop_scope();
        if self.parse_error.is_some() {
            return None;
        }
        condition
    }

    fn local_init_scoped_value(&mut self, local: &syn::Local) -> Option<String> {
        let init = local.init.as_ref()?;
        // Declared-width preservation (#2778 bit-shift parity). A
        // `let v: <intty> = <bare int literal>;` binding const-substitutes `v`
        // into later expressions as the literal's bare digits. Without a suffix
        // the re-lowered literal defaults to the signed `i32` placeholder and
        // DROPS `v`'s declared width, so an unsigned over-shift `x >> v`
        // (e.g. upstream `bit_shift_overflow`: `let y: u16 = 16; x >> y`) loses
        // the width that decides the over-shift: the amount routes to the signed
        // `bit shift underflow/overflow` path, and when the shifted LHS is itself
        // a substituted bare literal the bound is checked against width 32, so a
        // genuine `>= 16` over-shift verifies spuriously. Re-attaching the
        // local's DECLARED type suffix keeps the substituted value at its true
        // width; `coerce_unsuffixed_literal` then propagates that width to a
        // peer bare-literal LHS, so the shift routes to the unsigned over-shift
        // path where the empty-model counterexample reclassification fires.
        //
        // Soundness: the suffix is the local's DECLARED type taken verbatim from
        // the `let` annotation (never inferred/guessed), so no width is
        // mis-attributed; `usize`/`isize` are kept as-spelled so a
        // `global size_of usize` directive is still honored at re-lowering. A
        // value that does not fit the declared type is the same literal-range
        // error Rust/Verus raise. Suffixed source literals (`16u16`) and
        // non-literal initializers are left untouched (return `None`).
        if let Some(value) = declared_width_int_literal_scoped_value(local) {
            return Some(value);
        }
        if let Some(value) = typed_empty_std_collection_scoped_value(local, &init.expr) {
            return Some(value);
        }
        if let Some(value) = typed_tuple_default_scoped_value(local, &init.expr) {
            return Some(value);
        }
        if let Some(value) = scoped_option_none_value(local, &init.expr) {
            return Some(value);
        }
        if self.local_init_erases_mut_reference_alias(local) {
            self.mutable_reference_referent_scoped_string(&init.expr)
                .or_else(|| Some(self.expr_to_scoped_string(&init.expr)))
        } else {
            Some(self.expr_to_scoped_string(&init.expr))
        }
    }

    fn assign_expr(
        &mut self,
        assign: &syn::ExprAssign,
        direct_deref_target: Option<ErasedMutRefTarget>,
        right_mut_ref_target: Option<ErasedMutRefTarget>,
        emit_overflow_check: bool,
    ) -> bool {
        // FAITHFULNESS + SOUNDNESS: a destructuring-assignment LHS previously
        // fell through every assign sub-path silently — the assignment was
        // DROPPED from the model (`(a, b) = (1, 2); assert!(a == 0)` verified
        // against the stale value). Verus rejects the feature outright; so do
        // we, at the single funnel shared by the obligation and value walks.
        if let Some(err) = destructuring_assignment_error(assign.left.as_ref()) {
            self.parse_error = Some(err);
            return false;
        }
        // SOUNDNESS-CRITICAL (slice-C remediation: control-flow deref-write
        // drop). A deref write inside a calc!/assert-by PROOF block
        // (`deref_write_rollback_depth`, see the field doc) cannot be
        // modeled — proof context must not mutate exec state, and the visit
        // is snapshot-discarded. Fail closed with the VERBATIM pre-existing
        // rejection before any state or obligation is touched. This single
        // funnel check covers the direct-target, alias, and unsupported-shape
        // branches below, and the compound desugar
        // (`assign_deref_compound_expr`) that re-enters here. Exec
        // branch/match/block/closure/loop regions are instead handled by
        // exact in-region modeling + region-exit havoc
        // (`deref_written_region_roots`), with the slice-C compound /
        // sequential capabilities switched off inside loop bodies
        // (`loop_body_depth`).
        if self.deref_write_rollback_depth > 0 && is_deref_assignment_target(assign.left.as_ref()) {
            self.parse_error = Some(unsupported_deref_assignment_error(assign.left.as_ref()));
            return false;
        }
        if let Some(target) = direct_deref_target {
            self.emit_deref_write_rhs_safety_checks(&assign.right, emit_overflow_check);
            return self.assign_mut_ref_target(&target, &assign.right, None);
        }
        if let Some(alias) = deref_assignment_target_alias(assign.left.as_ref()) {
            let Some(target) = self.erased_mut_ref_target_name(&alias) else {
                self.parse_error = Some(unsupported_deref_assignment_error(assign.left.as_ref()));
                return false;
            };
            self.emit_deref_write_rhs_safety_checks(&assign.right, emit_overflow_check);
            return self.assign_mut_ref_target(&target, &assign.right, Some(&alias));
        }
        if is_deref_assignment_target(assign.left.as_ref()) {
            self.parse_error = Some(unsupported_deref_assignment_error(assign.left.as_ref()));
            return false;
        }
        if let Some(result) = self.assign_indexed_tuple_field_expr(assign) {
            return result;
        }
        if let Some(result) = self.assign_mut_ref_field_expr(assign) {
            return result;
        }
        if let Some(result) = self.assign_direct_field_expr(assign) {
            return result;
        }
        if let Some(name) = expr_path_ident(&assign.left) {
            let erased_shared_ref_alias = self.is_erased_shared_ref_expr(&assign.right);
            let erased_mut_ref_alias = expr_is_mut_reference(&assign.right);
            let value = if expr_is_mut_reference(&assign.right) {
                self.mutable_reference_referent_scoped_string(&assign.right)
                    .unwrap_or_else(|| self.expr_to_scoped_string(&assign.right))
            } else {
                self.expr_to_scoped_string(&assign.right)
            };
            let concrete_value = self.expr_is_concrete(&assign.right);
            let struct_type = self.expr_struct_type_name(&assign.right);
            if emit_overflow_check {
                self.maybe_emit_exec_arith_overflow_check(&assign.right, &value);
                // SOUNDNESS (#81): a scalar-target assign `x = a[i];` reads an
                // array/slice access whose bound otherwise never reaches an
                // assertion. When the RHS is not a top-level checked-arith/shift
                // expression (which already pins a reflexive over the whole RHS),
                // pin the bound on each value-position index access in it.
                if !rhs_is_checked_scalar_arithmetic(&assign.right)
                    && !rhs_is_checked_bit_shift(&assign.right)
                {
                    self.emit_exec_index_bounds_checks_in_expr(&assign.right);
                    // SOUNDNESS-CRITICAL (exec scalar arithmetic): mirror the
                    // `let`-init nested-site pin. An arithmetic site nested in a
                    // non-arith RHS (`x = f(a / b);`) is not seen by the top-level
                    // `maybe_emit_exec_arith_overflow_check` above; pin each.
                    self.emit_exec_arith_safety_checks_in_expr(&assign.right);
                }
            }
            self.invalidate_mut_ref_aliases_targeting(&name);
            self.assign_scoped(&name, value);
            self.set_concrete_scoped_nearest(&name, concrete_value);
            if let Some(struct_type) = struct_type {
                self.set_struct_type_nearest(&name, struct_type);
            } else {
                self.clear_struct_type_nearest(&name);
            }
            if erased_shared_ref_alias {
                self.mark_erased_shared_ref_alias_nearest(&name);
            } else {
                self.unmark_erased_shared_ref_alias_nearest(&name);
            }
            if erased_mut_ref_alias {
                self.mark_erased_mut_ref_alias_nearest(&name);
                if let Some(target) = right_mut_ref_target {
                    self.set_erased_mut_ref_target_nearest(&name, target);
                } else {
                    self.clear_erased_mut_ref_target_nearest(&name);
                }
            } else {
                self.unmark_erased_mut_ref_alias_nearest(&name);
            }
            return true;
        }

        let Expr::Index(index_target) = strip_place_wrappers(assign.left.as_ref()) else {
            return false;
        };
        if let Some(result) = self.assign_struct_field_index_expr(assign, index_target) {
            return result;
        }
        if let Some(result) = self.assign_nested_index_expr(assign, index_target) {
            return result;
        }
        let Some(name) = expr_path_ident(&index_target.expr) else {
            return false;
        };
        let index = self.expr_to_scoped_string(&index_target.index);
        let value = self.expr_to_scoped_string(&assign.right);
        if self.assign_mut_ref_alias_index(&name, &index, &value) {
            return true;
        }
        if self.is_unsupported_index_receiver(&name) {
            self.parse_error = Some(unsupported_reference_index_assignment_error(
                assign.left.as_ref(),
            ));
            return false;
        }
        if !self
            .externally_assigned_in_expr(&index_target.index)
            .is_empty()
        {
            self.invalidate_scoped(&name);
            return true;
        }

        let receiver = self.lookup_scoped(&name);
        if let (Some(len), Some(index)) = (
            scoped_vec_literal_len(&receiver),
            literal_usize_index_expr(&index_target.index),
        ) {
            if index >= len {
                self.parse_error = Some(out_of_bounds_vec_literal_index_assignment_error(
                    assign.left.as_ref(),
                    index,
                    len,
                ));
                return false;
            }
        }
        self.assign_scoped(&name, format!("{receiver}.update({index}, {value})"));
        true
    }

    fn assign_struct_field_index_expr(
        &mut self,
        assign: &syn::ExprAssign,
        index_target: &syn::ExprIndex,
    ) -> Option<bool> {
        let (owner, member) = struct_field_index_assignment_target(&index_target.expr)?;
        if self.is_erased_mut_ref_name(&owner)
            || self.is_erased_shared_ref_name(&owner)
            || self.is_unsupported_index_receiver(&owner)
        {
            self.parse_error = Some(unsupported_reference_index_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        }
        let Some(struct_type) = self.struct_type_name_for_direct_owner(&owner) else {
            return Some(false);
        };
        if !self
            .externally_assigned_in_expr(&index_target.index)
            .is_empty()
            || !self.externally_assigned_in_expr(&assign.right).is_empty()
        {
            self.parse_error = Some(unsupported_index_assignment_error(assign.left.as_ref()));
            return Some(false);
        }

        let receiver_concrete = self.is_concrete_scoped_name(&owner);
        let concrete_value = receiver_concrete
            && self.expr_is_concrete(&index_target.index)
            && self.expr_is_concrete(&assign.right);
        let receiver = self.lookup_scoped(&owner);
        let index = self.expr_to_scoped_string(&index_target.index);
        let value = self.expr_to_scoped_string(&assign.right);
        let field_update = format!("({receiver}).{member}.update({index}, {value})");
        let updated = format!("{struct_type} {{ {member}: {field_update}, ..{receiver} }}");

        self.assign_scoped(&owner, updated);
        self.set_concrete_scoped_nearest(&owner, concrete_value);
        self.set_struct_type_nearest(&owner, struct_type);
        Some(true)
    }

    fn assign_nested_index_expr(
        &mut self,
        assign: &syn::ExprAssign,
        index_target: &syn::ExprIndex,
    ) -> Option<bool> {
        let (name, outer_index_expr, inner_index_expr) =
            nested_index_assignment_target(index_target)?;
        if self.is_erased_mut_ref_name(&name)
            || self.is_erased_shared_ref_name(&name)
            || self.is_unsupported_index_receiver(&name)
        {
            self.parse_error = Some(unsupported_reference_index_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        }

        let mut assignments = self.externally_assigned_in_expr(outer_index_expr);
        assignments.extend(self.externally_assigned_in_expr(inner_index_expr));
        assignments.extend(self.externally_assigned_in_expr(&assign.right));
        if !assignments.is_empty() {
            self.parse_error = Some(unsupported_index_assignment_error(assign.left.as_ref()));
            return Some(false);
        }

        let receiver = self.lookup_scoped(&name);
        let outer_index = self.expr_to_scoped_string(outer_index_expr);
        let inner_index = self.expr_to_scoped_string(inner_index_expr);
        let value = self.expr_to_scoped_string(&assign.right);
        let inner_receiver = format!("({receiver})[{outer_index}]");
        let updated_inner = format!("{inner_receiver}.update({inner_index}, {value})");
        self.assign_scoped(
            &name,
            format!("{receiver}.update({outer_index}, {updated_inner})"),
        );
        Some(true)
    }

    fn struct_type_name_for_direct_owner(&self, owner: &str) -> Option<String> {
        if let Some(struct_type) = self.scoped_struct_type_name(owner) {
            return Some(struct_type);
        }
        if self.has_scoped_name(owner) {
            return None;
        }
        match self.vc.get_variable_type(owner)? {
            crate::ir::TrustVcType::Datatype { name, .. } => Some(name.clone()),
            _ => None,
        }
    }

    /// The base struct/enum (`Datatype`) type-name backing `name`, when it
    /// denotes a user struct/enum value. Used to resolve whether a method call
    /// `name.method(..)` mutates the caller's binding (the user-struct analog of
    /// the #62/#63 collection loop-mutation gap). Resolves an inferred scoped
    /// struct type first, then the variable's declared `Datatype` type, so it
    /// works for both let-locals and parameters.
    fn receiver_struct_type_name(&self, name: &str) -> Option<String> {
        if let Some(struct_type) = self.scoped_struct_type_name(name) {
            return Some(struct_type);
        }
        match self.vc.get_variable_type(name) {
            Some(TrustVcType::Datatype { name, .. }) => Some(name.clone()),
            _ => None,
        }
    }

    /// The struct/enum type-NAME of a FIELD-PROJECTION method receiver place
    /// `root.f.g` — the declared `Datatype` of the leaf sub-field, walked from the
    /// root binding's own `Datatype` through the registered struct/enum field
    /// lists. Returns `None` when the receiver is the bare root (a DIRECT receiver,
    /// classified by the root type itself), the root has no resolvable `Datatype`,
    /// or the projection cannot be followed to a struct sub-field (a tuple field /
    /// index / scalar leaf) — the caller then falls back to the conservative
    /// pure-name classification. This lets a laundered `o.inner.method()` be
    /// classified by the SAME receiver-kind registry as a direct `o.method()`, so
    /// a pure `&self` getter on the sub-field is recognized by its RESOLVED
    /// signature rather than its NAME (no over-rejection of a custom-named getter).
    fn projected_receiver_struct_type(&self, receiver: &Expr) -> Option<String> {
        let (root, path) = receiver_field_projection_path(receiver)?;
        let root_ty = self.owner_struct_datatype(&root)?;
        projected_field_struct_type(&root_ty, &path)
    }

    /// True when `recv.method(..)` — where `recv` is a user struct/enum binding of
    /// type `struct_type` — may mutate the CALLER's `recv` binding, so a later
    /// read of `recv` must not see the stale entry value (havoc), and `recv` must
    /// join a loop's modified set. This is the user-struct analog of the
    /// collection-mutator detection that closed the #62/#63 false-`Verified` gap.
    ///
    /// SOUNDNESS (fail-closed): resolves the method's `self` receiver kind from
    /// the file's impls (`struct_self_receiver_kind`). `&mut self` → mutates;
    /// `&self` → pure; by-value `self` → a move that cannot mutate the caller's
    /// binding → pure (matches the existing by-value inherent-method semantics).
    /// An UNKNOWN signature (no in-scope impl) is treated as POSSIBLY mutating
    /// unless it is a universally-pure read (`is_known_pure_struct_method`), so a
    /// method we cannot resolve never silently preserves a stale receiver.
    fn struct_method_mutates_caller(&self, struct_type: &str, method: &str) -> bool {
        match self.vc.struct_self_receiver_kind(struct_type, method) {
            Some(SelfReceiverKind::RefMut) => true,
            Some(SelfReceiverKind::Ref | SelfReceiverKind::Value) => false,
            None => !is_known_pure_struct_method(method),
        }
    }

    /// SOUNDNESS-CRITICAL (generic-receiver mutation framing). True when
    /// `recv.method(..)` — where `recv`'s DECLARED type is a bare type parameter
    /// (`fn g<T: Tr>(t: &mut T)`, or its `fn g(t: &mut impl Tr)` sugar, which
    /// desugars to exactly that) — is resolved to a `&mut self` trait method and
    /// therefore mutates the caller's binding.
    ///
    /// This is the shape `struct_method_mutates_caller` structurally cannot
    /// reach: a `TypeParam` receiver has no `Datatype`, so
    /// `receiver_struct_type_name` is `None` and the struct branch never fires.
    /// Before this, `t.bump()` on such a receiver was a NO-OP — the two `t.a()`
    /// reads bracketing it lowered to the SAME `Tr__a(t)` term (the trait-bound
    /// method UF is a function OF the receiver term), so `y - x == 0` verified
    /// even though every real impl with a mutating `bump` refutes it.
    ///
    /// Resolution reuses the SAME start-first supertrait BFS that registers the
    /// bound methods (`supertrait_closure_methods`) so the mutation classifier
    /// and the method-resolution closure cannot drift, and additionally consults
    /// the DIRECT bound so a trait declared without `#[trust_vc::trait_spec]`
    /// (absent from `trait_decls`) is still classified.
    ///
    /// FAIL DIRECTION (no over-rejection): an UNRESOLVED `(trait, method)` pair
    /// returns `false` and leaves the receiver intact. That is safe here — and
    /// only here — because a method that resolves to no in-scope trait
    /// declaration also gets no bound-method registration, so a call on it
    /// cannot be lowered at all and already fails closed. A `&self` / by-value
    /// trait method resolves to `Ref`/`Value` and is likewise left alone, so a
    /// true fact carried across a pure generic read still verifies.
    fn type_param_method_mutates_caller(&self, name: &str, method: &str) -> bool {
        // A scoped struct-type inference wins over the declared type (the struct
        // branch already handled that case); only classify a receiver whose
        // declared type is a bare type parameter.
        if self.scoped_struct_type_name(name).is_some() {
            return false;
        }
        let Some(TrustVcType::TypeParam(type_param)) = self.vc.get_variable_type(name) else {
            return false;
        };
        self.type_param_mut_self_methods(&type_param.clone())
            .contains(method)
    }

    /// Every method name a `TypeParam`-typed receiver bound by `type_param` can
    /// be called with that the in-scope trait declarations resolve to
    /// `&mut self`. The single authority behind both consumers of the
    /// generic-receiver mutation framing: the straight-line havoc
    /// ([`Self::type_param_method_mutates_caller`]) and the loop / branch
    /// modified-set collector, which must agree or a receiver havoced in one
    /// lane stays frame-pinned in the other.
    fn type_param_mut_self_methods(&self, type_param: &str) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let Some(function_context) = self.vc.function_context() else {
            return out;
        };
        let trait_decls = self.vc.trait_decls();
        for bound in function_context.trait_bounds() {
            if bound.type_param != type_param {
                continue;
            }
            // The bound trait itself, plus every (transitive) supertrait, via the
            // SAME start-first BFS that registers the callable bound methods —
            // so the mutation classifier and the method-resolution closure cannot
            // drift. `supertrait_closure_methods` applies Rust's shadowing rule,
            // so the nearest declaration of a name wins.
            let mut declaring: Vec<(String, String)> = Vec::new();
            for (declaring_trait, decl) in
                crate::vc_extraction::trait_contracts::supertrait_closure_methods(
                    trait_decls,
                    &bound.trait_name,
                )
            {
                declaring.push((declaring_trait, decl.name.clone()));
            }
            // Also consult the DIRECT bound by name, so a trait declared without
            // `#[trust_vc::trait_spec]` (absent from `trait_decls`, hence from the
            // closure above) is still classified.
            for (trait_name, method) in self.vc.trait_method_self_receiver_kinds().keys() {
                if trait_name == &bound.trait_name {
                    declaring.push((trait_name.clone(), method.clone()));
                }
            }
            for (trait_name, method) in declaring {
                if self
                    .vc
                    .trait_method_self_receiver_kind(&trait_name, &method)
                    == Some(SelfReceiverKind::RefMut)
                {
                    out.insert(method);
                }
            }
        }
        out
    }

    /// Per-receiver `&mut self` method names for every declared `TypeParam`
    /// binding, in the shape the loop / branch modified-set collector consumes.
    ///
    /// SOUNDNESS-CRITICAL (generic receiver × loop frame). The modified-set
    /// collector classifies a method receiver through `struct_receivers` (a
    /// `Datatype` map) and `collection_receivers`; a `TypeParam` receiver is in
    /// NEITHER, so `t.bump()` inside a loop body left `t` out of the modified
    /// set, the loop frame pinned `t == t_pre`, and a FALSE invariant about
    /// `t.a()` was trivially "preserved" — the loop sibling of the straight-line
    /// hole, live on its own.
    fn type_param_mut_methods_by_receiver(&self) -> BTreeMap<String, BTreeSet<String>> {
        let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        if self.vc.function_context().is_none() {
            return out;
        }
        for decl in self.vc.variables() {
            let TrustVcType::TypeParam(type_param) = &decl.ty else {
                continue;
            };
            // A nearer `let` binding of the same name may shadow the declared
            // parameter, exactly as `struct_typed_receiver_names` handles.
            if self.has_scoped_name(&decl.name) {
                continue;
            }
            let methods = self.type_param_mut_self_methods(type_param);
            if !methods.is_empty() {
                out.insert(decl.name.clone(), methods);
            }
        }
        out
    }

    /// Havocs a struct/enum receiver after an in-place mutation by a `&mut self`
    /// (or unresolved non-pure) method call: rebinds `name`'s scoped value to a
    /// FRESH, unconstrained variable of the same `Datatype` type. Subsequent reads
    /// of `name`/`name.field` then resolve to the fresh symbol, which carries no
    /// constraints, so a later `assert!`/`ensures` that reads the stale pre-call
    /// value can no longer be discharged (fail-closed) — closing the straight-line
    /// user-struct sibling of the #62/#63 collection-mutation false-`Verified`.
    ///
    /// This is the in-body two-state model for a struct receiver: because the
    /// method's post-state effect on the receiver is not threaded (we have no
    /// `ensures` to recover field values), the only sound model after the call is
    /// "arbitrary". A pure `&self`/by-value reader never reaches here, so a true
    /// fact about an only-read struct still verifies (NO over-rejection). When the
    /// receiver's `Datatype` type cannot be resolved we conservatively forget the
    /// scoped binding (`invalidate_scoped`), which the caller already did.
    fn havoc_struct_receiver(&mut self, name: &str) {
        let ty = self.vc.get_variable_type(name).cloned();
        let Some(ty @ TrustVcType::Datatype { .. }) = ty else {
            return;
        };
        let TrustVcType::Datatype {
            name: struct_type, ..
        } = &ty
        else {
            return;
        };
        let struct_type = struct_type.clone();
        let mut fresh = format!("{name}__post_mut_{}", self.next_struct_havoc_index);
        self.next_struct_havoc_index += 1;
        while self.vc.get_variable_type(&fresh).is_some() {
            fresh = format!("{name}__post_mut_{}", self.next_struct_havoc_index);
            self.next_struct_havoc_index += 1;
        }
        self.vc.declare_var_typed(&fresh, ty);
        self.havoc_minted_symbols.insert(fresh.clone());
        // Rebind `name` (and any mut-ref aliases pointing at it) to the fresh,
        // unconstrained symbol so later reads see arbitrary state.
        self.assign_scoped(name, fresh.clone());
        self.set_concrete_scoped_nearest(name, false);
        self.set_struct_type_nearest(name, struct_type.clone());
        for alias_name in
            self.erased_mut_ref_aliases_targeting(&ErasedMutRefTarget::Local(name.to_string()))
        {
            self.assign_scoped(&alias_name, fresh.clone());
            self.set_concrete_scoped_nearest(&alias_name, false);
            self.set_struct_type_nearest(&alias_name, struct_type.clone());
        }
    }

    /// Havocs a struct/enum `name` that was assigned (a field/direct write) on
    /// only SOME branches of an `if`/`match`, or to DIFFERING values — i.e. a
    /// name in the branch-join's `assigned_outer` that the common-value merge did
    /// NOT keep. Rebinds it to a FRESH unconstrained value of its `Datatype` type
    /// (resolved via `owner_struct_datatype`, so it covers owned locals as well as
    /// `&mut`/owned params).
    ///
    /// SOUNDNESS (round-2 audit P0-A): `assign_direct_field_expr` records a field
    /// write `s.x = v` as a scoped functional-update on the ROOT `s`. At a branch
    /// join `invalidate_scoped` drops that override, but for a `&mut`/owned PARAM
    /// the read then falls back to the ENTRY value — so a conditional `s.x = 99`
    /// silently reverts `s` to its entry state and a post-join `assert!(s.x == 5)`
    /// (the entry/`requires` value) is wrongly discharged. Havocing instead models
    /// the conditional write as "arbitrary", closing the false-`Verified`.
    fn havoc_assigned_struct_at_join(&mut self, name: &str) {
        let Some(ty) = self.owner_struct_datatype(name) else {
            return;
        };
        let TrustVcType::Datatype {
            name: struct_type, ..
        } = &ty
        else {
            return;
        };
        let struct_type = struct_type.clone();
        let mut fresh = format!("{name}__post_join_{}", self.next_struct_havoc_index);
        self.next_struct_havoc_index += 1;
        while self.vc.get_variable_type(&fresh).is_some() {
            fresh = format!("{name}__post_join_{}", self.next_struct_havoc_index);
            self.next_struct_havoc_index += 1;
        }
        self.vc.declare_var_typed(&fresh, ty.clone());
        self.invalidate_mut_ref_aliases_targeting(name);
        self.assign_scoped(name, fresh.clone());
        self.set_concrete_scoped_nearest(name, false);
        self.set_struct_type_nearest(name, struct_type.clone());
        for alias_name in
            self.erased_mut_ref_aliases_targeting(&ErasedMutRefTarget::Local(name.to_string()))
        {
            self.assign_scoped(&alias_name, fresh.clone());
            self.set_concrete_scoped_nearest(&alias_name, false);
            self.set_struct_type_nearest(&alias_name, struct_type.clone());
        }
    }

    /// Havocs an un-merged branch-assigned `name` at an `if`/`match` join,
    /// dispatching on its modeled kind: a struct/enum (incl. an owned local whose
    /// type is inferred from a constructor literal) uses the functional-update
    /// `Datatype` havoc; any other DECLARED binding (collection / scalar / param)
    /// is freshened generically. Closes the branch-join sibling of the loop-frame
    /// leak for collection and scalar `&mut`-arguments mutated on only some
    /// branches (`if b { push_helper(v); }`), where the struct-only havoc was a
    /// no-op and the binding wrongly reverted to its entry value.
    fn havoc_unmerged_assigned_at_join(&mut self, name: &str) {
        if self.owner_struct_datatype(name).is_some() {
            self.havoc_assigned_struct_at_join(name);
            return;
        }
        if !self.havoc_declared_binding_to_fresh(name) {
            // Undeclared scoped-only local: the caller's `invalidate_scoped_names`
            // already dropped any rewrite, which is the sound fail-closed model.
            self.invalidate_scoped(name);
        }
    }

    /// Opens a deref-write rollback/conditional region (see
    /// [`deref_written_region_roots`](Self::deref_written_region_roots)):
    /// deref writes visited until the matching
    /// [`Self::exit_deref_write_region_and_havoc`] record their root here.
    fn enter_deref_write_region(&mut self) {
        self.deref_written_region_roots.push(BTreeSet::new());
    }

    /// Records the ROOT of a deref write into the innermost active region (a
    /// no-op in the straight-line function body, where writes persist and the
    /// SSA chain is exact).
    fn record_deref_written_root(&mut self, root: &str) {
        if let Some(region) = self.deref_written_region_roots.last_mut() {
            region.insert(root.to_string());
        }
    }

    /// Closes a deref-write region: every root deref-written inside it was
    /// ROLLED BACK by the region's snapshot-restore (deref LHSes are excluded
    /// from `external_assignments` by the #83 skip, so no join merge/havoc
    /// covers them) — havoc each root so a post-region read sees ARBITRARY
    /// state instead of the stale pre-region value (the false-`Verified`
    /// class this remediation closes). Mechanics, per root:
    /// 1. `havoc_unmerged_assigned_at_join` rebinds the root to a FRESH
    ///    unconstrained symbol of its declared type (or fail-closes an
    ///    undeclared local), so a post-region root read is counterexample-able
    ///    but never provably stale. Havoc is one-directional: a fresh symbol
    ///    can only LOSE provability, never prove wrong facts.
    /// 2. The root is recorded in `deref_region_havoced_roots` so the
    ///    callee-side `ensures` resolver treats its final as UNRESOLVED
    ///    (fail-closed `Error`, the pre-existing branch-havoc contract path)
    ///    rather than a spurious havoc-model counterexample; a later
    ///    straight-line write re-establishes the clean final.
    /// 3. Every alias whose NEAREST resolution roots at this root has its
    ///    scoped VALUE refreshed to the same fresh symbol (or dropped when
    ///    the root fail-closed) — a stale in-region snapshot must not survive
    ///    in an alias — while its alias->target MAPPING is kept: the aliasing
    ///    relationship is a static fact, and stripping it would spuriously
    ///    reject a later re-processing of the same syntax (the #83
    ///    index-block fold evaluates its block twice). Shadowed same-name
    ///    bindings rooted elsewhere are never touched (nearest filter).
    /// 4. The roots propagate into the ENCLOSING region's set: the outer
    ///    join's own snapshot-restore reverts this havoc, so the outer exit
    ///    must re-havoc (`if a { if b { *x = 1; } } assert!(*x == 0)`).
    fn exit_deref_write_region_and_havoc(&mut self) {
        let Some(roots) = self.deref_written_region_roots.pop() else {
            return;
        };
        for root in &roots {
            // This root's aliases, captured with their FULL targets BEFORE
            // the havoc (whose internal `invalidate_scoped` /
            // `invalidate_mut_ref_aliases_targeting` strips both the value
            // bindings and the MAPPINGS). Nearest-filtered here, while the
            // frame state is intact: a shadowed same-name binding rooted
            // elsewhere is never touched.
            let aliases: Vec<(String, ErasedMutRefTarget)> = self
                .erased_mut_ref_targets
                .iter()
                .flat_map(|targets| {
                    targets.iter().filter_map(|(alias, alias_target)| {
                        (alias_target.root_name() == root && alias != root).then(|| alias.clone())
                    })
                })
                .collect::<BTreeSet<_>>()
                .into_iter()
                .filter_map(|alias| {
                    self.erased_mut_ref_target_name(&alias)
                        .filter(|t| t.root_name() == root)
                        .map(|t| (alias, t))
                })
                .collect();
            self.havoc_unmerged_assigned_at_join(root);
            self.deref_region_havoced_roots.insert(root.clone());
            // A PARAM root's seeded self-mapping may have been stripped (the
            // havoc invalidation) — re-pin it at the fresh binding so a
            // subsequent STRAIGHT-LINE `*x = ..` write regains exact tracking
            // instead of spuriously failing closed.
            if self.supported_mut_ref_param_targets.contains(root) {
                self.set_erased_mut_ref_target_nearest(
                    root,
                    ErasedMutRefTarget::Local(root.clone()),
                );
                self.mark_erased_mut_ref_alias_nearest(root);
            }
            let fresh = self.has_scoped_name(root).then(|| self.lookup_scoped(root));
            for (alias, alias_target) in aliases {
                match &fresh {
                    Some(value) => {
                        // Refresh the alias's VALUE to the root's fresh havoc
                        // symbol — a stale in-region snapshot must not
                        // survive in an alias.
                        self.assign_scoped(&alias, value.clone());
                        self.set_concrete_scoped_nearest(&alias, false);
                        self.clear_struct_type_nearest(&alias);
                    }
                    None => {
                        // Root fail-closed (undeclared local): drop the
                        // alias's VALUE bindings so a post-region read fails
                        // closed too.
                        for scope in &mut self.scopes {
                            scope.remove(&alias);
                        }
                        for concrete in &mut self.concrete_scoped_values {
                            concrete.remove(&alias);
                        }
                        for struct_types in &mut self.scoped_struct_types {
                            struct_types.remove(&alias);
                        }
                    }
                }
                // Restore the alias->target MAPPING the havoc invalidation
                // stripped: the aliasing relationship is a static fact, and
                // losing it would spuriously reject a later write through the
                // alias or a re-processing of the same syntax (the #83
                // index-block fold evaluates its block twice). Safe: the
                // nearest filter above proved this name's nearest meaning IS
                // this root.
                self.set_erased_mut_ref_target_nearest(&alias, alias_target);
                self.mark_erased_mut_ref_alias_nearest(&alias);
            }
        }
        if let Some(parent) = self.deref_written_region_roots.last_mut() {
            parent.extend(roots);
        }
    }

    /// Havocs a loop-modified DECLARED variable at the join of a NO-invariant
    /// loop (`while`/`for`): rebinds `name`'s scoped value to a FRESH,
    /// unconstrained variable of its declared type, so a post-loop (or, when
    /// applied at the body head, an in-body) read sees ARBITRARY state.
    ///
    /// SOUNDNESS (loop-frame leak): the previous post-loop model was only
    /// `invalidate_scoped` — it dropped the scoped value-numbering but, for a
    /// function PARAMETER (or any declared var), the read then fell back to the
    /// ENTRY symbol, which is still pinned by `requires`/`assume`/a call
    /// `ensures`. A no-invariant loop that mutates such a variable would then
    /// falsely retain the entry value across the loop, so a post-loop
    /// `assert!`/`ensures` reading the stale value wrongly `Verified`. A
    /// no-invariant loop is semantically `invariant!(true)`: every modified
    /// variable is arbitrary after the loop (and on every iteration), so the
    /// only sound model is to forget its entry facts by minting a fresh symbol.
    ///
    /// Only DECLARED variables (params / declared outer locals, whose bare
    /// symbol carries entry facts) are freshened. An UNDECLARED scoped-only
    /// local (`let mut b = ..` mutated in the loop) has no entry-pinned bare
    /// symbol; `invalidate_scoped` leaves it resolving to an unresolved bare
    /// name (fail-closed), which is already sound, so it is left untouched here.
    ///
    /// When a loop HAS an invariant, the encoder's `loop_modified_vars`
    /// machinery performs the post-loop havoc and the post-loop read must see
    /// the bare (invariant-constrained) symbol — so this helper is NOT used in
    /// that case (`invalidate_scoped` is kept), avoiding over-rejection of a
    /// correct invariant-based loop.
    fn havoc_modified_var_at_loop_join(&mut self, name: &str) {
        if !self.havoc_declared_binding_to_fresh(name) {
            // Undeclared scoped-only local: keep the existing fail-closed model.
            self.invalidate_scoped(name);
        }
    }

    /// Rebinds a DECLARED variable `name`'s scoped value to a FRESH, unconstrained
    /// variable of its declared type, forgetting every entry fact about it (a later
    /// read resolves to arbitrary state). Returns `true` when `name` was a declared
    /// variable (and was freshened), `false` when it is undeclared (caller decides
    /// the fail-closed fallback). Generic over scalars / structs / collections —
    /// shared by the no-invariant loop-frame havoc and the mutable-reborrow havoc.
    fn havoc_declared_binding_to_fresh(&mut self, name: &str) -> bool {
        let Some(ty) = self.vc.get_variable_type(name).cloned() else {
            return false;
        };
        let mut fresh = format!("{name}__havoc_{}", self.next_struct_havoc_index);
        self.next_struct_havoc_index += 1;
        while self.vc.get_variable_type(&fresh).is_some() {
            fresh = format!("{name}__havoc_{}", self.next_struct_havoc_index);
            self.next_struct_havoc_index += 1;
        }
        self.vc.declare_var_typed(&fresh, ty.clone());
        self.havoc_minted_symbols.insert(fresh.clone());
        // Forget every auxiliary scoped fact about `name` (struct type, ghost
        // collection, mut-ref aliases, concrete flag, ...) exactly as the
        // invalidate path does, then rebind the scoped value to the fresh,
        // unconstrained symbol so later reads resolve to arbitrary state.
        self.invalidate_scoped(name);
        self.assign_scoped(name, fresh.clone());
        self.set_concrete_scoped_nearest(name, false);
        if let TrustVcType::Datatype {
            name: struct_type, ..
        } = &ty
        {
            self.set_struct_type_nearest(name, struct_type.clone());
        }
        true
    }

    /// Re-applies the `exec_closure_defs` entry for every outer-assigned name
    /// that BOTH branches of an `if`/`else` rebind to the SAME closure body, so a
    /// post-join call instruments the (unambiguous) rebound body. See the
    /// soundness note at the `visit_expr_if` call site (round-8 finding 13b).
    fn reapply_common_branch_exec_closure_rebinds(
        &mut self,
        assigned_outer: &BTreeSet<String>,
        then_snapshot: &ScopeSnapshot,
        else_snapshot: Option<&ScopeSnapshot>,
    ) {
        let Some(else_snapshot) = else_snapshot else {
            return;
        };
        for name in assigned_outer {
            let (Some(then_def), Some(else_def)) = (
                then_snapshot.exec_closure_defs.get(name),
                else_snapshot.exec_closure_defs.get(name),
            ) else {
                continue;
            };
            // Compare the closure bodies by their token rendering — only an
            // identical rebind on both arms yields an unambiguous post-join body.
            if then_def.to_token_stream().to_string() == else_def.to_token_stream().to_string() {
                self.exec_closure_defs
                    .insert(name.clone(), then_def.clone());
            }
        }
    }

    /// SOUNDNESS-CRITICAL (free-call `&mut`-argument framing): havoc the
    /// referent of every argument passed at a `&mut` parameter position of a free
    /// `call`. A contract-less `push_helper(v: &mut Vec<u64>) { v.push(1) }`
    /// mutates `v` through the `&mut` argument, so after the call the caller's `v`
    /// is arbitrary; the previous model dropped the effect and a post-call read of
    /// `v` saw the stale entry snapshot (a real false `Verified`). The `&mut`
    /// positions come from the CALLEE SIGNATURE (`mut_ref_call_args`), so a
    /// `&`-shared read (`read_helper(v: &Vec<u64>)`) — syntactically identical at
    /// the call site — is left untouched (no over-rejection). The havoc runs
    /// BEFORE the helper-contract recording so a contracted helper's `ensures`
    /// (a `&mut`-param two-state postcondition like `ensures(v.len() == 5)`) is
    /// threaded over the FRESH post-call symbol — pinning the post-state instead
    /// of the dropped entry value. Only the root binding of a place argument (`v`,
    /// `*v`, `&mut v`, `&mut *v`, `&mut o.f`) is havoced.
    ///
    /// Fires inside loop bodies too: the loop's single-iteration body transition
    /// is built from these straight-line scope mutations, so havocing the `&mut`
    /// referent here is what makes a loop invariant referencing the argument
    /// genuinely NON-inductive across the call (e.g. `bump_scalar(x)` under
    /// `invariant!(*x == start)`). The complementary `ExternalAssignmentCollector`
    /// signal adds the same root to the loop-frame / if-join MODIFIED set so the
    /// head/join havoc is applied as well.
    /// True when this call resolves to a declared helper contract with at least
    /// one `requires` OR `ensures` clause. The pre-havoc argument snapshot is
    /// consumed by BOTH the call-site `requires` substitution and (slice D) the
    /// `old(P)` bindings of the `ensures` assumption, so an ensures-only callee
    /// needs the snapshot too — without it, `old(P)` would silently bind to the
    /// post-havoc fresh symbol (the directionality inversion).
    fn call_has_helper_contract(&self, call: &syn::ExprCall) -> bool {
        let Some(helper_contracts) = self.helper_contracts else {
            return false;
        };
        let Some(helper_name) = super::call_function_symbol(call) else {
            return false;
        };
        helper_contracts
            .get(&helper_name)
            .is_some_and(|contract| !contract.requires.is_empty() || !contract.ensures.is_empty())
    }

    /// The `&mut`-SCALAR param flags of the resolved helper contract for this
    /// call (empty when the call has no helper contract). Positions align with
    /// the call arguments; used to render `&mut v` arguments as referent VALUES
    /// for the contract substitution.
    fn helper_contract_mut_ref_scalar_flags(&self, call: &syn::ExprCall) -> Vec<bool> {
        let Some(helper_contracts) = self.helper_contracts else {
            return Vec::new();
        };
        let Some(helper_name) = super::call_function_symbol(call) else {
            return Vec::new();
        };
        helper_contracts
            .get(&helper_name)
            .map(|contract| contract.mut_ref_scalar_params.clone())
            .unwrap_or_default()
    }

    /// True when `havoc_mut_ref_call_arg_referents` would rebind at least one
    /// argument root for this call — i.e. the callee takes a `&mut` parameter
    /// bound to a tracked local/param here. Used to decide whether a pre-havoc
    /// snapshot of the argument renderings is needed for the call-site
    /// `requires` substitution.
    fn call_havocs_mut_ref_args(&self, call: &syn::ExprCall) -> bool {
        let resolved = self.resolved_call_arg_mut_flags(call);
        call.args.iter().enumerate().any(|(index, arg)| {
            self.call_arg_may_be_written_through(resolved.as_deref(), index, arg)
                && !mut_ref_arg_is_shared_ref_temporary(arg)
                && field_index_projection_root(arg)
                    .is_some_and(|root| self.has_scoped_name(&root) || self.vc.has_variable(&root))
        })
    }

    /// The callee-signature `&mut` flags for `call`, or `None` when this file
    /// cannot resolve the callee at all.
    ///
    /// `None` is a genuine UNKNOWN and is reported as one — it is NOT the empty
    /// vector. `collect_referenced_sibling_mut_ref_call_args` records an
    /// all-`false` vector for a resolved pure reader precisely so the two can be
    /// told apart here; conflating them is what let `use m::bump2; bump2(t)`
    /// read as "no mutable arguments".
    fn resolved_call_arg_mut_flags(&self, call: &syn::ExprCall) -> Option<Vec<bool>> {
        let symbol = super::call_function_symbol(call)
            .or_else(|| super::qualified_ufcs_call_symbol(call))?;
        self.mut_ref_call_args.get(&symbol).cloned()
    }

    /// Whether the callee may WRITE THROUGH argument `index` of a call.
    ///
    /// SOUNDNESS-CRITICAL, and THE place the two independent sources of the
    /// answer are reconciled:
    ///
    /// 1. `resolved` — the callee SIGNATURE, when this file resolves the callee.
    ///    This is the precise answer and the only one allowed to say NO: a
    ///    `&`-shared parameter is spelled IDENTICALLY at the call site
    ///    (`read(t)` vs `bump(t)`), so nothing but the signature separates them
    ///    and this is what keeps the framing free of over-rejection.
    /// 2. The ARGUMENT's own declared type, when the callee is UNKNOWN. A
    ///    binding of type `&mut T` passed bare is REBORROWED into the call, so
    ///    whoever the callee is may write through it. This needs no resolution,
    ///    which is exactly why it is the right fallback: the previous model
    ///    answered "no mutable arguments" for every spelling it could not
    ///    resolve — a file-level `use m::bump2;`, an inherent associated fn
    ///    `H::zap(t)`, a method argument `h.hit(t)`, an item from another crate
    ///    — and each of those was a live cardinal false verify.
    ///
    /// Restricted to a BARE path argument in the fallback: `o.c` passed by value
    /// is a copy, and `&mut o.c` is a borrow the general borrow-escape havoc
    /// (`havoc_mut_borrow_escaped_binding`) already owns.
    fn call_arg_may_be_written_through(
        &self,
        resolved: Option<&[bool]>,
        index: usize,
        arg: &Expr,
    ) -> bool {
        if let Some(flags) = resolved {
            return flags.get(index).copied().unwrap_or(false);
        }
        expr_path_ident(arg).is_some_and(|name| self.mut_ref_reborrowable_bindings.contains(&name))
    }

    fn havoc_mut_ref_call_arg_referents(&mut self, call: &syn::ExprCall) {
        let resolved = self.resolved_call_arg_mut_flags(call);
        self.havoc_written_through_call_args(&call.args, resolved.as_deref());
    }

    /// The METHOD-call twin of [`Self::havoc_mut_ref_call_arg_referents`].
    ///
    /// SOUNDNESS-CRITICAL: `havoc_mut_ref_call_arg_referents` is reached only
    /// from `visit_expr_call`, so a `&mut` NON-self parameter of an inherent or
    /// trait method — `impl H { fn hit(&self, c: &mut C) }` called `h.hit(t)`,
    /// and `impl B for H { fn bump(&self, c: &mut C) }` called `h.bump(t)` — was
    /// framed by nothing at all. Both were live cardinal false verifies in the
    /// return lane AND the in-body `assert!` lane. The RECEIVER is not touched
    /// here: `visit_expr_method_call`'s own receiver-mutation machinery owns it.
    fn havoc_mut_ref_method_call_args(&mut self, call: &syn::ExprMethodCall) {
        let resolved = self
            .method_arg_mut_flags
            .get(&call.method.to_string())
            .cloned();
        self.havoc_written_through_call_args(&call.args, resolved.as_deref());
    }

    fn havoc_written_through_call_args(
        &mut self,
        args: &syn::punctuated::Punctuated<Expr, syn::Token![,]>,
        resolved: Option<&[bool]>,
    ) {
        for (index, arg) in args.iter().enumerate() {
            if !self.call_arg_may_be_written_through(resolved, index, arg) {
                continue;
            }
            // `&mut &x` passes a mutable reference TO A TEMPORARY shared
            // reference: the callee can only rebind that temporary, never write
            // through the inner `&` — `x` itself is untouchable. Havocing `x`
            // here was over-conservative AND lossy: when the fresh-rebind
            // failed, `invalidate_scoped(x)` dropped the binding entirely and a
            // later `assert!(x == ..)` fail-closed with `unresolved variable`
            // (refs `mutref_arg_ref_unsupported` case, masked behind the
            // `test_mut_ref_forward` failure since d568e2e). This fires ONLY
            // for the literal `&mut &expr` shape — `&mut r` where `r` is a
            // local holding a reference still havocs `r` (the callee CAN
            // rebind `r`'s value through the mutable reference).
            if mut_ref_arg_is_shared_ref_temporary(arg) {
                continue;
            }
            let Some(root) = field_index_projection_root(arg) else {
                continue;
            };
            // Only havoc a tracked binding (a parameter / declared local). A
            // shadowing scoped-only local with no entry-pinned symbol is left to
            // the existing fail-closed model.
            if !self.has_scoped_name(&root) && !self.vc.has_variable(&root) {
                continue;
            }
            // Slice D: a scoped-only `let` local with a KNOWN scalar type is
            // rebound to a fresh unconstrained symbol instead of being dropped
            // (`invalidate_scoped` left a later read unresolved — fail-closed
            // but blocking the classic caller chain `let mut v = 5; f(&mut v);
            // assert!(v == ..)`). The fresh symbol carries NO constraints, so a
            // contract-less callee's mutation is modeled as arbitrary state (a
            // post-call `assert!(v == pre)` is a genuine Counterexample, never
            // Verified); a contracted callee's `ensures` re-threads over it.
            // SLICE-D REMEDIATION (p7b/p20 region-rollback resurface): this
            // havoc runs inside whatever rollback/conditional region encloses
            // the call (nested block, match arm, if branch, closure body) —
            // the region's snapshot-restore REVERTS it, and call-arg havoc
            // roots were never recorded into the region set, so
            // `exit_deref_write_region_and_havoc` did not re-havoc and a
            // post-region read saw the pre-call value again (for a
            // `requires`-pinned declared param a false `Verified`:
            // `{ nocontract(&mut p); } assert!(p == 5)`). Record the root
            // exactly like a deref write (`assign_mut_ref_target`), so the
            // region exit re-havocs it. No-op in the straight-line body.
            // Loop bodies are excluded: the loop modified-var machinery
            // (`ExternalAssignmentCollector` + invariant/`loop_modified_vars`
            // encoding or the no-invariant join havoc) owns loop framing, and
            // an exit re-havoc would clobber the bare invariant-constrained
            // symbol a post-loop read must see (over-rejection of sound
            // invariant loops that pass `&mut` args in the body).
            if self.loop_body_depth == 0 {
                self.record_deref_written_root(&root);
            }
            if self.havoc_declared_binding_to_fresh(&root)
                || self.havoc_scoped_scalar_local_to_fresh(&root)
            {
                // The fresh symbol IS the post-call model of this argument's
                // mutable borrow (which ends at the call — no alias survives).
                // Mark the literal `&mut root` argument node so
                // `visit_expr_reference`'s general mutable-borrow-escape
                // havoc/invalidation does not run for THIS node and rebind
                // right after we minted the fresh symbol (the call `ensures`
                // constrains THIS symbol; a second rebind would orphan it).
                if let Expr::Reference(reference) = strip_place_wrappers(arg) {
                    if reference.mutability.is_some() && expr_path_ident(&reference.expr).is_some()
                    {
                        self.mut_ref_call_arg_reference_havocs
                            .insert(reference as *const syn::ExprReference as usize);
                    }
                }
            } else {
                self.invalidate_scoped(&root);
            }
        }
    }

    /// Rebinds a scoped-only `let` local with a known modeled scalar type to a
    /// fresh, unconstrained, SMT-declared symbol (the `&mut`-call-arg havoc for
    /// locals that are not in the VC variable table). Returns `false` when the
    /// name is a declared variable (the declared-binding havoc owns it), is not
    /// scoped, or has no recorded scalar type — the caller then keeps the
    /// fail-closed `invalidate_scoped` model.
    fn havoc_scoped_scalar_local_to_fresh(&mut self, name: &str) -> bool {
        if self.vc.get_variable_type(name).is_some() || !self.has_scoped_name(name) {
            return false;
        }
        let Some(ty) = self.modified_var_scalar_type(name) else {
            return false;
        };
        let mut fresh = format!("{name}__havoc_{}", self.next_struct_havoc_index);
        self.next_struct_havoc_index += 1;
        while self.vc.get_variable_type(&fresh).is_some() {
            fresh = format!("{name}__havoc_{}", self.next_struct_havoc_index);
            self.next_struct_havoc_index += 1;
        }
        self.vc.declare_var_typed(&fresh, ty);
        // Forget every auxiliary scoped fact about `name` exactly as the
        // declared-binding havoc does, then rebind the scoped value to the
        // fresh symbol so later reads resolve to arbitrary state.
        self.invalidate_scoped(name);
        self.assign_scoped(name, fresh);
        self.set_concrete_scoped_nearest(name, false);
        true
    }

    /// SOUNDNESS-CRITICAL (slice-D remediation, base-era declared-var
    /// borrow-escape holes p1/p2/p4/p19/p23/p44): the general model for a
    /// mutable borrow `&mut name` ESCAPING through any shape the precise
    /// call-arg machinery does not own — a reborrow `&mut *(&mut p)`, a
    /// `&mut &mut p` inner node, a method-call argument `s.mwr(&mut p)`, a
    /// UFCS associated-fn argument `SPair::wr(&mut p)`, a fn-pointer call
    /// `g(&mut p)`, an alias-creating `let r = &mut p;` — after which the
    /// borrower may write through the reference at any time.
    ///
    /// The previous model was `invalidate_scoped` alone, which only drops a
    /// scoped rewrite: a DECLARED variable (a by-value `mut p: u64` param, or
    /// any VC-declared binding) then resolved back to its ENTRY symbol — still
    /// pinned by `requires`/`assume` — so a post-escape read proved STALE
    /// pre-escape facts (`assert!(p == 5)` after the callee wrote 99: a real
    /// false `Verified`, probed firsthand on base for all six shapes above).
    /// A declared binding is therefore HAVOCKED to a fresh unconstrained
    /// symbol (over-havoc is sound: a fresh symbol can only lose provability;
    /// a borrow that is never written through merely over-rejects, fail-closed).
    /// An UNDECLARED scoped-only local keeps the `invalidate_scoped` model —
    /// its post-escape read is an unresolved name (fail-closed `Error`), and
    /// switching it to a havoc would silently change the pinned fail-closed
    /// verdicts of the alias-forwarding battery cases.
    ///
    /// The root is also recorded into the active deref-write region (when one
    /// is open) so a region snapshot-restore cannot resurface the pre-escape
    /// value at the join (the p7b/p20 rollback class; no-op straight-line;
    /// loop bodies excluded — the loop modified-var machinery owns loop
    /// framing, see `havoc_mut_ref_call_arg_referents`).
    fn havoc_mut_borrow_escaped_binding(&mut self, name: &str) {
        if self.loop_body_depth == 0 {
            self.record_deref_written_root(name);
        }
        if !self.havoc_declared_binding_to_fresh(name) {
            self.invalidate_scoped(name);
        }
    }

    /// SOUNDNESS-CRITICAL (UFCS associated-fn mutation framing): a UFCS call
    /// `Type::method(recv, ..)`, `<Type>::method(recv, ..)`,
    /// `<Type as Trait>::method(recv, ..)`, or `Trait::method(recv, ..)` is the
    /// exact desugaring of the method call `recv.method(..)`. The method-call
    /// path (`visit_expr_method_call`) havocs a `&mut self` struct receiver and a
    /// non-pure collection receiver; the call path previously dropped that effect
    /// for every UFCS spelling — an inherent/trait associated fn is a
    /// `syn::ExprCall`, not a `MethodCall`, and `S::bump`/`Vec::push` are absent
    /// from `mut_ref_call_args` (which only carries declared FREE-fn signatures),
    /// while the `<S as T>::` qself form was additionally gated out of the
    /// free-call `&mut`-arg havoc. The receiver therefore kept its
    /// `requires`-pinned ENTRY value and a post-call `assert!`/read of it
    /// false-`Verified` (round-8 findings 6–10).
    ///
    /// We re-apply the SAME framing by resolving the receiver from the FIRST
    /// argument (the desugared `self`):
    ///  - a user struct/enum receiver whose `(resolved_type, method)` is a
    ///    `&mut self` method (`struct_self_receiver_kind`) is havoced
    ///    (`havoc_struct_receiver`). The receiver's resolved `Datatype` type is
    ///    the precise key (the Rust type system guarantees `args[0]` has the
    ///    method's `Self` type), so a `&self`/by-value method, or an associated
    ///    fn with NO `self` receiver (`S::new(x)`, `Wrapper::wrap(s)` — absent
    ///    from the receiver-kind registry, which only records methods whose first
    ///    input is a `Receiver`), resolves to `Ref`/`Value`/`None` and is left
    ///    untouched (NO over-rejection — a pure UFCS read still verifies);
    ///  - a std-collection-type UFCS mutator (`Vec::push(v, ..)`, `Vec::clear(v)`,
    ///    …) on a collection-like receiver that is not a pure read is havoced via
    ///    `havoc_declared_binding_to_fresh`, mirroring the auto-deref `v.push(..)`
    ///    / `v.clear()` collection-receiver havoc. The std-collection-type-name
    ///    gate keeps a pure UFCS read (and a user fn that merely takes a
    ///    collection by `&`) untouched.
    ///
    /// Runs for BOTH plain and qualified (`qself`) UFCS spellings, and is a no-op
    /// for a bare single-segment free-fn call (handled by
    /// `havoc_mut_ref_call_arg_referents`).
    fn havoc_ufcs_receiver_mutation(&mut self, call: &syn::ExprCall) {
        let Some((type_segment, method)) = ufcs_call_assoc_fn(call) else {
            return;
        };
        let Some(receiver) = call.args.first() else {
            return;
        };
        let Some(root) = field_index_projection_root(receiver) else {
            return;
        };
        // Only frame a tracked binding (a parameter / declared local). A
        // shadowing scoped-only local with no entry-pinned symbol is left to the
        // existing fail-closed model.
        if !self.has_scoped_name(&root) && !self.vc.has_variable(&root) {
            return;
        }
        // (1) user struct/enum receiver — resolve the receiver's actual struct
        // type and consult the impl-method receiver-kind registry. A `&mut self`
        // method mutates the caller's binding; a `&self`/by-value method or a
        // non-method associated fn (registry miss → `None`) does NOT.
        if let Some(struct_type) = self.receiver_struct_type_name(&root) {
            match self.vc.struct_self_receiver_kind(&struct_type, &method) {
                Some(SelfReceiverKind::RefMut) => {
                    // Mirror the method-call receiver-mutation path
                    // (`visit_expr_method_call`): drop any scoped field-rewrite /
                    // concrete record on the receiver BEFORE havocing, then rebind
                    // it to a fresh unconstrained symbol. Without the invalidate an
                    // OWNED struct param's `requires(s.x == 5)` leaves a scoped
                    // `s.x` field-rewrite that the post-call `assert!(s.x == 5)`
                    // would still read (a stale-field false `Verified`).
                    self.invalidate_scoped(&root);
                    self.havoc_struct_receiver(&root);
                }
                // `Ref`/`Value` (pure / by-value) or `None` (not a self-receiver
                // method): leave the receiver intact — NO over-rejection.
                _ => {}
            }
            return;
        }
        // (1b) GENERIC receiver: the UFCS spelling of the `TypeParam`-receiver
        // `&mut self` trait call (`Tr::bump(t)` for `t: &mut T`). Same framing as
        // the method-call path — without it the UFCS spelling reopens exactly the
        // hole `type_param_method_mutates_caller` closes.
        if self.type_param_method_mutates_caller(&root, &method) {
            self.havoc_declared_binding_to_fresh(&root);
            return;
        }
        // (2) std-collection mutator UFCS (`Vec::push(v, ..)`). The receiver is
        // modeled as a ghost `Seq`/`Set`/`Map` (so it has no `Datatype` type and
        // the struct branch above did not fire). Gate on the path's type segment
        // being a recognized std collection type so a user fn taking a collection
        // by `&` is never havoced, and require a non-pure (mutating) method.
        if type_segment
            .as_deref()
            .is_some_and(is_std_collection_type_name)
            && self.receiver_is_collection_like(&root)
            && !is_pure_collection_read_method(&method)
        {
            self.havoc_declared_binding_to_fresh(&root);
        }
    }

    /// Mint a fresh, unconstrained, declared symbol for the captured free
    /// variables of a closure whose injected hypothesis must be scoped to the
    /// closure, rebinding within the caller's (already-isolated) scope. See the
    /// `#74` soundness note in `visit_expr_closure`. A captured var is a
    /// single-ident reference in the body that is neither a closure parameter nor
    /// lexically bound before that use. Both declared variables and scoped-only
    /// locals are freshened: a scoped local can alias a declared, fact-bearing
    /// symbol (`let n = p`) even though the local itself has no VC declaration.
    ///
    /// WHICH captures are freshened is governed by `freshen_all` / `targets`:
    /// * `freshen_all` (an `assume!`-bearing closure): EVERY captured var — the
    ///   `assume!` macro tokens are opaque to a syn `Visit`, so we cannot pin
    ///   which capture the assumed relation constrains; freshening all of them is
    ///   the sound over-approximation of the original #74 fix.
    /// * otherwise (a contracted-helper-call closure): ONLY the captures that
    ///   actually appear in a contracted in-closure call's ARGUMENT list
    ///   (`targets`). A `__call_ensures_*` hypothesis can only constrain a capture
    ///   that was PASSED to the call, so a contracted call on a literal
    ///   (`checked(3u64)`) constrains no capture and freshens nothing — leaving an
    ///   unrelated outer fact about a capture intact (NO over-rejection).
    fn freshen_closure_captured_free_vars(
        &mut self,
        expr_closure: &syn::ExprClosure,
        freshen_all: bool,
        targets: &BTreeSet<String>,
    ) {
        // Collect lexical FREE-identifier candidates, including identifiers in
        // opaque macro token streams. Binding order matters: in
        // `{ assume!(n == 7); let n = 0; }`, the first `n` is the outer capture;
        // subtracting every binding that appears anywhere in the body would miss
        // it and leak the assumption. The collector tracks block scope in source
        // order and stops at nested closures, which isolate their own captures.
        let referenced = closure_free_ident_candidates(expr_closure);
        for name in referenced {
            if !freshen_all && !targets.contains(&name) {
                continue;
            }
            if self.vc.get_variable_type(&name).is_some() {
                // Reuses the loop-frame fresh-symbol mint: declares a fresh typed
                // symbol and rebinds `name`'s scoped value to it. Inside the
                // isolated closure scope, this rebinding is reverted on scope
                // restore, so the OUTER reading of `name` is unaffected.
                self.havoc_declared_binding_to_fresh(&name);
            } else if self.has_scoped_name(&name) {
                // CAPTURED SCOPED-LOCAL (round-10 be-2 findings 12-16): a
                // `let n = p;` alias local is NOT a declared `vc` variable, so the
                // branch above skips it — but it resolves THROUGH the scoped
                // substitution map to a fact-bearing symbol (the aliased parameter
                // `p`, a `let m = q` chain, …). An in-closure `assume!(n == 7)` is
                // then emitted over that underlying symbol and, because the
                // isolated-scope visit rolls back SCOPES but NOT emitted
                // obligations, leaks as a flat global hypothesis discharging a
                // sibling closure's / the enclosing body's `assert!` or a
                // postcondition / a div-by-zero check — even when the closure is
                // never called. Re-point the local's scoped value to a fresh,
                // unconstrained symbol for this isolated visit so the hypothesis
                // is scoped to the closure (the `let`-local sibling of the #74
                // captured-PARAM freshening). Reverted on scope restore, so an
                // outer TRUE fact about the local (`n == p`) still holds (NO
                // over-rejection).
                self.freshen_scoped_local_capture(&name);
            }
        }
    }

    /// Re-point a CAPTURED scoped-only local (`let n = p`) to a fresh,
    /// unconstrained symbol within the (already-isolated) closure scope, so an
    /// in-closure `assume!`/relation about it cannot leak through the alias to the
    /// underlying parameter symbol. See the call site in
    /// `freshen_closure_captured_free_vars`.
    ///
    /// When the local's scalar type is known, a fresh typed symbol is declared
    /// and bound (the precise model). Otherwise the scoped alias is dropped so the
    /// local resolves to its own bare (undeclared, unconstrained) symbol — still
    /// disjoint from the aliased value, so no hypothesis about it leaks.
    fn freshen_scoped_local_capture(&mut self, name: &str) {
        if let Some(ty) = self.modified_var_scalar_type(name) {
            let mut fresh = format!("{name}__closurecap_{}", self.next_struct_havoc_index);
            self.next_struct_havoc_index += 1;
            while self.vc.get_variable_type(&fresh).is_some() || self.has_scoped_name(&fresh) {
                fresh = format!("{name}__closurecap_{}", self.next_struct_havoc_index);
                self.next_struct_havoc_index += 1;
            }
            self.vc.declare_var_typed(&fresh, ty);
            self.assign_scoped(name, fresh);
            self.set_concrete_scoped_nearest(name, false);
        } else {
            self.invalidate_scoped(name);
        }
    }

    /// The set of captured-var idents that a DEFERRED closure body would inject a
    /// hypothesis about via a contracted free-helper call, so those captures must
    /// be freshened to keep the hypothesis scoped to the closure (#74). A call
    /// `h(args)` to a free helper `h` carrying a non-empty `ensures` is lowered by
    /// `record_helper_contract_call` to a `__call_ensures_*` ASSUME that survives
    /// the closure's isolated-scope visit (the visit rolls back SCOPES but NOT
    /// emitted obligations); that hypothesis can only constrain a captured var if
    /// the var was PASSED to the call, so this returns exactly the idents appearing
    /// in such calls' ARGUMENT lists. A literal-only contracted call
    /// (`checked(3u64)`) and a contract-LESS call (`pure_helper(n)` — empty
    /// `ensures`) both contribute nothing, so neither triggers freshening of an
    /// unrelated capture (NO over-rejection). Mirrors `record_helper_contract_call`'s
    /// lookup (same `helper_contracts` table, same `call_function_symbol`
    /// resolution, same `!ensures.is_empty()` gate) so the freshening trigger
    /// matches EXACTLY which calls inject a hypothesis.
    fn closure_contracted_call_arg_idents(&self, body: &Expr) -> BTreeSet<String> {
        let Some(helper_contracts) = self.helper_contracts else {
            return BTreeSet::new();
        };
        struct ContractedCallArgIdentFinder<'a> {
            helper_contracts: &'a BTreeMap<String, HelperCallContract>,
            idents: BTreeSet<String>,
        }
        impl<'ast> Visit<'ast> for ContractedCallArgIdentFinder<'_> {
            fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
                if let Some(name) = super::call_function_symbol(call) {
                    if self
                        .helper_contracts
                        .get(&name)
                        .is_some_and(|contract| !contract.ensures.is_empty())
                    {
                        for arg in &call.args {
                            collect_token_stream_idents(arg.to_token_stream(), &mut self.idents);
                        }
                    }
                }
                visit::visit_expr_call(self, call);
            }
        }
        let mut finder = ContractedCallArgIdentFinder {
            helper_contracts,
            idents: BTreeSet::new(),
        };
        finder.visit_expr(body);
        finder.idents
    }

    /// Post-loop frame model: for each loop-modified name, either freshen it
    /// (no invariant — break the entry/`requires`/`assume` pin) or invalidate
    /// its scoped value (an invariant is present — the encoder owns the havoc
    /// and the post-loop read must see the invariant-constrained bare symbol).
    fn frame_loop_modified_vars(&mut self, names: BTreeSet<String>, has_invariant: bool) {
        for name in names {
            if has_invariant {
                self.invalidate_scoped(&name);
            } else {
                self.havoc_modified_var_at_loop_join(&name);
            }
        }
    }

    /// Exec panic-safety obligations for the RHS of a write through a
    /// dereference (`*P = <rhs>`, including the desugared `*P op= <rhs>`),
    /// mirroring the scalar-target assign path byte-for-byte: the top-level
    /// checked-arith/shift reflexive pin
    /// ([`Self::maybe_emit_exec_arith_overflow_check`]) plus, when the RHS is
    /// not itself a top-level checked expression, the nested index-bound and
    /// arithmetic-site pins. SOUNDNESS: previously the deref-write branches
    /// emitted NOTHING — `*x = *x + 1` at `u64::MAX` (or `*x = *x / d` with
    /// `d` unbounded) silently `Verified` while the SAME RHS assigned to a
    /// local carried the overflow / divide-by-zero obligation. Emitted only on
    /// the obligation walk (`emit_overflow_check`), BEFORE the rebind so the
    /// operands resolve to the pre-write state (matching the scalar path).
    fn emit_deref_write_rhs_safety_checks(&mut self, rhs: &Expr, emit_overflow_check: bool) {
        if !emit_overflow_check {
            return;
        }
        let value = self.expr_to_scoped_string(rhs);
        self.maybe_emit_exec_arith_overflow_check(rhs, &value);
        if !rhs_is_checked_scalar_arithmetic(rhs) && !rhs_is_checked_bit_shift(rhs) {
            self.emit_exec_index_bounds_checks_in_expr(rhs);
            self.emit_exec_arith_safety_checks_in_expr(rhs);
        }
    }

    /// Compound assignment through a dereference (`*P op= rhs` /
    /// `*alias op= rhs`) on a supported scalar (`Local`-target) mut-ref place:
    /// desugars AT THE AST LEVEL to the already-modeled single-write funnel
    /// `*P = (*P) op (rhs)` — read the CURRENT scoped value (the entry symbol
    /// when untouched), apply the operator, rebind — so SSA-chain ordering,
    /// `old()` entry semantics, `clean_finals` capture and the deref-write RHS
    /// safety obligations are all inherited from the plain-write path by
    /// construction (both operands are `Paren`-wrapped, so the string render
    /// keeps precedence when the current value is a compound term). Everything
    /// else keeps the pre-existing fail-closed rejection VERBATIM:
    /// - a non-`Local` target (field/index-projected alias): the projected
    ///   compound read-modify-write is not modeled;
    /// - a deref place that is not a bare alias (`*s.f`, `**p`, `*(&mut x)`);
    /// - an RHS containing any assignment: real compound assignment evaluates
    ///   the RHS BEFORE reading the place, while the desugar reads the place
    ///   first — an embedded write through the same place would read stale
    ///   state, so it stays rejected rather than silently reordered.
    fn assign_deref_compound_expr(
        &mut self,
        binary: &syn::ExprBinary,
        emit_overflow_check: bool,
    ) -> bool {
        let supported_op = value_binop_for_assignment(&binary.op).filter(|_| {
            // Slice-C remediation: the compound desugar reads the CURRENT
            // scoped value — inside a loop body that is the previous VISIT's
            // value, not the previous ITERATION's, so the chain would prove
            // first-iteration facts for every iteration. Keep the verbatim
            // pre-existing rejection in loop context.
            self.loop_body_depth == 0
                && !expr_contains_assignment(&binary.right)
                && deref_assignment_target_alias(binary.left.as_ref())
                    .and_then(|alias| self.erased_mut_ref_target_name(&alias))
                    .is_some_and(|target| matches!(target, ErasedMutRefTarget::Local(_)))
        });
        let Some(op) = supported_op else {
            self.parse_error = Some(unsupported_deref_assignment_error(binary.left.as_ref()));
            return false;
        };
        let paren = |expr: &Expr| {
            Expr::Paren(syn::ExprParen {
                attrs: Vec::new(),
                paren_token: Default::default(),
                expr: Box::new(expr.clone()),
            })
        };
        let desugared = syn::ExprAssign {
            attrs: binary.attrs.clone(),
            left: binary.left.clone(),
            eq_token: Default::default(),
            right: Box::new(Expr::Binary(syn::ExprBinary {
                attrs: Vec::new(),
                left: Box::new(paren(binary.left.as_ref())),
                op,
                right: Box::new(paren(binary.right.as_ref())),
            })),
        };
        let direct_deref_target =
            self.direct_deref_mut_reference_assignment_target(desugared.left.as_ref());
        self.assign_expr(&desugared, direct_deref_target, None, emit_overflow_check)
    }

    fn assign_mut_ref_target(
        &mut self,
        target: &ErasedMutRefTarget,
        rhs: &Expr,
        alias: Option<&str>,
    ) -> bool {
        // Slice-C remediation: inside a rollback/conditional region this
        // write will be reverted at the region snapshot-restore — record the
        // root so the region exit havocs it (post-region reads must never see
        // the stale pre-region value). No-op in the straight-line body, where
        // a write RE-ESTABLISHES exact tracking (clears the havoced-final
        // mark so the ensures resolver sees the clean final again).
        self.record_deref_written_root(target.root_name());
        if self.deref_written_region_roots.is_empty() {
            self.deref_region_havoced_roots.remove(target.root_name());
        }
        match target {
            ErasedMutRefTarget::Local(name) => {
                let concrete_value = self.expr_is_concrete(rhs);
                let value = self.expr_to_scoped_string(rhs);
                let struct_type = self.expr_struct_type_name(rhs);
                self.assign_scoped(name, value.clone());
                self.set_concrete_scoped_nearest(name, concrete_value);
                // SEQUENTIAL deref writes (slice C): `assign_scoped` may have
                // INSERTED the value binding into an INNER scope frame while the
                // seeded/let-time alias→target mapping lives in an OUTER frame —
                // and `erased_mut_ref_target_name` treats a nearer value binding
                // as a shadow, so a SECOND `*P = ..` in the same straight line
                // no longer resolved the target and failed closed (the once-only
                // guard the slice-B battery pinned). Re-pin the mapping and the
                // alias mark AT the binding's frame so each subsequent write
                // rebinds in order (SSA chain). The shadow discipline is
                // preserved: a plain rebind of the name (`P = ..`) clears the
                // mapping at that same frame (`unmark_erased_mut_ref_alias_nearest`),
                // a `let` shadow binds in a NEARER frame (mapping stays
                // shadowed), and a frame pop drops binding and mapping together.
                // SLICE-C REMEDIATION: the repin stays OFF inside loop bodies —
                // there the emergent once-only shadow IS the sound guard (a
                // second write's SSA read would be the previous VISIT's value,
                // not the previous ITERATION's).
                if self.loop_body_depth == 0 {
                    self.set_erased_mut_ref_target_nearest(name, target.clone());
                    self.mark_erased_mut_ref_alias_nearest(name);
                }
                if let Some(struct_type) = struct_type.clone() {
                    self.set_struct_type_nearest(name, struct_type);
                } else {
                    self.clear_struct_type_nearest(name);
                }
                for alias_name in self.erased_mut_ref_aliases_targeting(target) {
                    // SOUNDNESS-CRITICAL (slice-C remediation: alias shadow
                    // retarget, adversarial p8). `erased_mut_ref_aliases_targeting`
                    // collects alias NAMES across ALL frames, but `assign_scoped` /
                    // `set_*_nearest` act on the name's NEAREST value-binding frame
                    // — so when an OUTER binding of `r` targets this root while an
                    // INNER SHADOW `r` points at a DIFFERENT root (`let r = &mut *x;
                    // { let r = &mut *y; .. }`), the unfiltered update clobbered the
                    // shadow's value AND (via the repin) RETARGETED it to this root:
                    // a subsequent `*r = 9` then wrote `x` in the model while the
                    // compiled program writes `y` (rustc-panicking program
                    // `Verified`). Only touch names whose NEAREST resolution
                    // actually targets the written root; a shadowed name keeps its
                    // own meaning (its outer binding is unreachable by name until
                    // its shadow's frame pops, which also pops this write's frame
                    // or fails closed at the rollback gate).
                    if !self.erased_mut_ref_targets_aliases(&alias_name, target) {
                        continue;
                    }
                    self.assign_scoped(&alias_name, value.clone());
                    self.set_concrete_scoped_nearest(&alias_name, concrete_value);
                    // Repin off in loop bodies (see the `name` repin above).
                    if self.loop_body_depth == 0 {
                        self.set_erased_mut_ref_target_nearest(&alias_name, target.clone());
                        self.mark_erased_mut_ref_alias_nearest(&alias_name);
                    }
                    if let Some(struct_type) = struct_type.clone() {
                        self.set_struct_type_nearest(&alias_name, struct_type);
                    } else {
                        self.clear_struct_type_nearest(&alias_name);
                    }
                }
                if let Some(alias) = alias {
                    // The write came through `alias`, whose nearest resolution WAS
                    // `target` at the funnel — so it is normally covered by the
                    // filtered loop above. Re-bind it here ONLY when its resolution
                    // was lost entirely (`None`: a value insert created a nearer
                    // binding with no target entry — the sequential-write case).
                    // NEVER when it meanwhile resolves to a DIFFERENT root: that is
                    // a shadow of another target, and assigning/repinning it would
                    // be exactly the p8 retarget bug (base assigned the value here
                    // unconditionally; narrowing to `None` only removes clobbers of
                    // bindings that provably mean another variable).
                    if self.erased_mut_ref_target_name(alias).is_none() {
                        self.assign_scoped(alias, value);
                        self.set_concrete_scoped_nearest(alias, concrete_value);
                        // Repin off in loop bodies (see the `name` repin above).
                        if self.loop_body_depth == 0 {
                            self.set_erased_mut_ref_target_nearest(alias, target.clone());
                            self.mark_erased_mut_ref_alias_nearest(alias);
                        }
                        if let Some(struct_type) = struct_type {
                            self.set_struct_type_nearest(alias, struct_type);
                        } else {
                            self.clear_struct_type_nearest(alias);
                        }
                    }
                }
                true
            }
            ErasedMutRefTarget::Field { owner, member } => {
                if !self.assign_scoped_struct_field(owner, member, rhs) {
                    return false;
                }
                if let Some(alias) = alias {
                    let concrete_value = self.expr_is_concrete(rhs);
                    let value = self.expr_to_scoped_string(rhs);
                    self.assign_scoped(alias, value);
                    self.set_concrete_scoped_nearest(alias, concrete_value);
                    if let Some(struct_type) = self.expr_struct_type_name(rhs) {
                        self.set_struct_type_nearest(alias, struct_type);
                    } else {
                        self.clear_struct_type_nearest(alias);
                    }
                }
                true
            }
            ErasedMutRefTarget::Index { owner, index } => {
                let value = self.expr_to_scoped_string(rhs);
                self.assign_mut_ref_index_target(owner, index, &value);
                if let Some(alias) = alias {
                    self.assign_scoped(alias, value.clone());
                    self.set_concrete_scoped_nearest(alias, self.expr_is_concrete(rhs));
                }
                for alias_name in self.erased_mut_ref_aliases_targeting(target) {
                    // Same NEAREST-resolution filter as the `Local` arm: never
                    // clobber a shadowed name that means a different root.
                    if !self.erased_mut_ref_targets_aliases(&alias_name, target) {
                        continue;
                    }
                    self.assign_scoped(&alias_name, value.clone());
                    self.set_concrete_scoped_nearest(&alias_name, self.expr_is_concrete(rhs));
                }
                true
            }
        }
    }

    fn erased_mut_ref_aliases_targeting(&self, target: &ErasedMutRefTarget) -> BTreeSet<String> {
        self.erased_mut_ref_targets
            .iter()
            .flat_map(|targets| {
                targets
                    .iter()
                    .filter_map(|(alias, alias_target)| {
                        (alias_target == target).then_some(alias.clone())
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    fn erased_mut_ref_targets_aliases(&self, alias: &str, target: &ErasedMutRefTarget) -> bool {
        self.erased_mut_ref_target_name(alias)
            .as_ref()
            .is_some_and(|alias_target| alias_target == target)
    }

    fn lookup_mut_ref_alias_index_receiver(&self, alias: &str) -> Option<String> {
        let ErasedMutRefTarget::Local(root) = self.erased_mut_ref_target_name(alias)? else {
            return None;
        };
        Some(if self.has_scoped_name(&root) {
            self.lookup_scoped(&root)
        } else {
            self.lookup_scoped(alias)
        })
    }

    fn assign_mut_ref_alias_index(&mut self, alias: &str, index: &str, value: &str) -> bool {
        let Some(ErasedMutRefTarget::Local(root)) = self.erased_mut_ref_target_name(alias) else {
            return false;
        };
        // Slice-C remediation: same region-root recording as
        // `assign_mut_ref_target` (this alias-index write mutates `root`).
        self.record_deref_written_root(&root);
        let target = ErasedMutRefTarget::Local(root.clone());
        let receiver = if self.has_scoped_name(&root) {
            self.lookup_scoped(&root)
        } else {
            self.lookup_scoped(alias)
        };
        let updated = format!("{receiver}.update({index}, {value})");
        self.assign_scoped(&root, updated.clone());
        for alias_name in self.erased_mut_ref_aliases_targeting(&target) {
            // Same NEAREST-resolution filter as the `Local` arm: never clobber
            // a shadowed name that means a different root.
            if !self.erased_mut_ref_targets_aliases(&alias_name, &target) {
                continue;
            }
            self.assign_scoped(&alias_name, updated.clone());
        }
        true
    }

    fn assign_mut_ref_index_target(&mut self, owner: &str, index: &str, value: &str) {
        let receiver = self.lookup_scoped(owner);
        self.assign_scoped(owner, format!("{receiver}.update({index}, {value})"));
    }

    fn assign_scoped_struct_field(&mut self, owner: &str, member: &str, rhs: &Expr) -> bool {
        let Some(struct_type) = self.scoped_struct_type_name(owner) else {
            return false;
        };

        let receiver_concrete = self.is_concrete_scoped_name(owner);
        let concrete_value = receiver_concrete && self.expr_is_concrete(rhs);
        let receiver = self.lookup_scoped(owner);
        let value = self.expr_to_scoped_string(rhs);
        let updated = format!("{struct_type} {{ {member}: {value}, ..{receiver} }}");

        self.assign_scoped(owner, updated);
        self.set_concrete_scoped_nearest(owner, concrete_value);
        self.set_struct_type_nearest(owner, struct_type);
        true
    }

    fn assign_indexed_tuple_field_expr(&mut self, assign: &syn::ExprAssign) -> Option<bool> {
        let (name, index_expr, field_index) =
            indexed_tuple_field_assignment_target(assign.left.as_ref())?;
        if self.is_erased_shared_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            self.parse_error = Some(unsupported_reference_index_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        }
        if matches!(
            self.erased_mut_ref_target_name(&name),
            Some(ErasedMutRefTarget::Field { .. } | ErasedMutRefTarget::Index { .. })
        ) {
            self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        }

        let Some(field_names) = self.indexed_tuple_element_field_names(&name) else {
            self.parse_error = Some(unsupported_index_assignment_error(assign.left.as_ref()));
            return Some(false);
        };
        if field_index >= field_names.len() {
            self.parse_error = Some(unsupported_index_assignment_error(assign.left.as_ref()));
            return Some(false);
        }

        let mut assignments = self.externally_assigned_in_expr(index_expr);
        assignments.extend(self.externally_assigned_in_expr(&assign.right));
        if !assignments.is_empty() {
            self.parse_error = Some(unsupported_index_assignment_error(assign.left.as_ref()));
            return Some(false);
        }

        let receiver = self
            .lookup_mut_ref_alias_index_receiver(&name)
            .unwrap_or_else(|| self.lookup_scoped(&name));
        let index = self.expr_to_scoped_string(index_expr);
        let value = self.expr_to_scoped_string(&assign.right);
        let element_receiver = format!("({receiver})[{index}]");
        let mut fields = Vec::with_capacity(field_names.len());
        for (candidate_index, field_name) in field_names.iter().enumerate() {
            if candidate_index == field_index {
                fields.push(value.clone());
            } else {
                fields.push(format!("({element_receiver}).{field_name}"));
            }
        }
        let trailing_comma = if fields.len() == 1 { "," } else { "" };
        let updated_element = format!("({}{trailing_comma})", fields.join(", "));
        if self.assign_mut_ref_alias_index(&name, &index, &updated_element) {
            return Some(true);
        }
        self.assign_scoped(
            &name,
            format!("{receiver}.update({index}, {updated_element})"),
        );
        Some(true)
    }

    fn indexed_tuple_element_field_names(&self, name: &str) -> Option<Vec<String>> {
        let type_owner = match self.erased_mut_ref_target_name(name) {
            Some(ErasedMutRefTarget::Local(root)) => root,
            Some(ErasedMutRefTarget::Field { .. } | ErasedMutRefTarget::Index { .. }) => {
                return None;
            }
            None => name.to_string(),
        };
        let element_ty = match self.vc.get_variable_type(&type_owner)? {
            TrustVcType::Array(element_ty, _) | TrustVcType::Seq(element_ty) => element_ty,
            _ => return None,
        };
        let TrustVcType::Datatype { variants, .. } = element_ty.as_ref() else {
            return None;
        };
        let [DatatypeVariant { name, fields }] = variants.as_slice() else {
            return None;
        };
        if name != TUPLE_VARIANT_NAME {
            return None;
        }
        let field_names = fields
            .iter()
            .enumerate()
            .map(|(index, (name, _))| (name == &index.to_string()).then_some(name.clone()))
            .collect::<Option<Vec<_>>>()?;
        (!field_names.is_empty()).then_some(field_names)
    }

    fn assign_mut_ref_field_expr(&mut self, assign: &syn::ExprAssign) -> Option<bool> {
        let Expr::Field(field) = strip_place_wrappers(assign.left.as_ref()) else {
            return None;
        };
        let alias = expr_path_ident(&field.base)?;
        if !self.is_erased_mut_ref_name(&alias) {
            return None;
        }
        let syn::Member::Named(member) = &field.member else {
            self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        };
        let Some(target) = self.erased_mut_ref_target_name(&alias) else {
            self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        };
        let ErasedMutRefTarget::Local(target) = target else {
            self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        };
        let Some(struct_type) = self
            .scoped_struct_type_name(&target)
            .or_else(|| self.scoped_struct_type_name(&alias))
        else {
            self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                assign.left.as_ref(),
            ));
            return Some(false);
        };

        let receiver_concrete =
            self.is_concrete_scoped_name(&target) || self.is_concrete_scoped_name(&alias);
        let concrete_value = receiver_concrete && self.expr_is_concrete(&assign.right);
        // The owning local and every alias targeting it hold the same logical
        // referent value, so the named alias's current scoped value is a sound
        // base for the functional-update record.
        let receiver = self.lookup_scoped(&alias);
        let value = self.expr_to_scoped_string(&assign.right);
        let updated = format!("{struct_type} {{ {member}: {value}, ..{receiver} }}");

        self.assign_scoped(&target, updated.clone());
        self.set_concrete_scoped_nearest(&target, concrete_value);
        self.set_struct_type_nearest(&target, struct_type.clone());
        // All erased mut-ref aliases that target this local — including any
        // intermediate reborrow aliases — share the same referent and must
        // observe the write. Updating only the directly-named alias would leave
        // an intermediate reborrow alias (e.g. `b` in
        // `let b = &mut a; let c = b; c.x = ...`) pointing at the stale
        // pre-write struct, which would unsoundly verify stale reads of `b`.
        let target_term = ErasedMutRefTarget::Local(target);
        for alias_name in self.erased_mut_ref_aliases_targeting(&target_term) {
            self.assign_scoped(&alias_name, updated.clone());
            self.set_concrete_scoped_nearest(&alias_name, concrete_value);
            self.set_struct_type_nearest(&alias_name, struct_type.clone());
        }
        Some(true)
    }

    /// SOUNDNESS-CRITICAL (P0-A dropped field write): model a DIRECT field
    /// assignment `s.f = value` (named `s.x`, tuple `p.0`, or nested `s.inner.x`)
    /// to an OWNED local or a (struct/enum) parameter as a functional struct
    /// update of the root's scoped value, so a later read of `s.f` sees the new
    /// value (a false post-state claim counterexamples, a true one verifies)
    /// instead of the silently-frozen entry value. The erased-mut-ref-alias field
    /// write (`assign_mut_ref_field_expr`) and the indexed/tuple-element write
    /// (`assign_indexed_tuple_field_expr` / index path) are handled earlier; this
    /// closes the remaining direct field-write surface. Returns `None` when the
    /// LHS is not a field place rooted at a resolvable owned/parameter struct (so
    /// the caller's other handlers / fail-closed net still apply); fails CLOSED
    /// (parse_error) for an unmodelable shape rather than dropping the write.
    fn assign_direct_field_expr(&mut self, assign: &syn::ExprAssign) -> Option<bool> {
        let Expr::Field(_) = strip_place_wrappers(assign.left.as_ref()) else {
            return None;
        };
        let (root, members) = field_assignment_path(assign.left.as_ref())?;
        // Erased mut-ref / shared-ref aliases are owned by their dedicated paths
        // (an alias field write is `assign_mut_ref_field_expr`; a shared-ref write
        // is rejected). Leave them to those handlers / the fail-closed net.
        if self.is_erased_mut_ref_name(&root)
            || self.is_erased_shared_ref_name(&root)
            || self.is_unsupported_index_receiver(&root)
        {
            return None;
        }
        let Some(root_ty) = self.owner_struct_datatype(&root) else {
            // Not a resolvable struct/enum local or parameter; let the caller's
            // remaining handlers run (and the fail-closed net catch it).
            return None;
        };
        // A side-effecting RHS would be re-rendered into the functional-update
        // record; refuse rather than duplicate the effect.
        if !self.externally_assigned_in_expr(&assign.right).is_empty() {
            self.parse_error = Some(unsupported_field_assignment_error(assign.left.as_ref()));
            return Some(false);
        }
        let receiver = self.lookup_scoped(&root);
        let concrete_value =
            self.is_concrete_scoped_name(&root) && self.expr_is_concrete(&assign.right);
        let value = self.expr_to_scoped_string(&assign.right);
        let member_refs: Vec<&str> = members.iter().map(String::as_str).collect();
        let Some(updated) =
            self.build_nested_field_update(&root_ty, &receiver, &member_refs, &value)
        else {
            self.parse_error = Some(unsupported_field_assignment_error(assign.left.as_ref()));
            return Some(false);
        };
        let TrustVcType::Datatype {
            name: struct_type, ..
        } = &root_ty
        else {
            return None;
        };
        let struct_type = struct_type.clone();
        self.invalidate_mut_ref_aliases_targeting(&root);
        self.assign_scoped(&root, updated.clone());
        self.set_concrete_scoped_nearest(&root, concrete_value);
        self.set_struct_type_nearest(&root, struct_type.clone());
        // Mut-ref aliases targeting this local share the referent and must observe
        // the write (mirrors `assign_mut_ref_field_expr`).
        for alias_name in
            self.erased_mut_ref_aliases_targeting(&ErasedMutRefTarget::Local(root.clone()))
        {
            self.assign_scoped(&alias_name, updated.clone());
            self.set_concrete_scoped_nearest(&alias_name, concrete_value);
            self.set_struct_type_nearest(&alias_name, struct_type.clone());
        }
        Some(true)
    }

    /// The base struct/enum `Datatype` backing an OWNED local or parameter `root`:
    /// an inferred scoped struct type (a let-local bound from a `S { .. }` literal
    /// or a `Pair(..)` constructor) first, else the declared parameter/variable
    /// `Datatype` type. Used by [`Self::assign_direct_field_expr`].
    fn owner_struct_datatype(&self, root: &str) -> Option<TrustVcType> {
        if let Some(type_name) = self.scoped_struct_type_name(root) {
            if let Some(ty) = self.datatype_for_scoped_type_name(&type_name) {
                return Some(ty);
            }
        }
        match self.vc.get_variable_type(root) {
            Some(ty @ TrustVcType::Datatype { .. }) => Some(ty.clone()),
            _ => None,
        }
    }

    /// Builds the functional struct-update string for assigning `value` at the
    /// field path `members` (root->leaf) of a struct value `current` of type
    /// `struct_ty`. A single member yields `Type { field: value, ..current }`; a
    /// nested path recurses into the inner field's struct type, projecting the
    /// inner value as `(current).field`. Returns `None` when a non-leaf field is
    /// not itself a struct/enum (so the path is unmodelable) — the caller then
    /// fails closed.
    fn build_nested_field_update(
        &self,
        struct_ty: &TrustVcType,
        current: &str,
        members: &[&str],
        value: &str,
    ) -> Option<String> {
        let TrustVcType::Datatype { name, variants } = struct_ty else {
            return None;
        };
        // A struct (or single-variant datatype) used for field-update has exactly
        // one variant whose fields are the struct's fields.
        let [variant] = variants.as_slice() else {
            return None;
        };
        let (member, rest) = members.split_first()?;
        if rest.is_empty() {
            return Some(format!("{name} {{ {member}: {value}, ..{current} }}"));
        }
        let (_, field_ty) = datatype_field(variant, member)?;
        let sub_current = format!("({current}).{member}");
        let sub_updated = self.build_nested_field_update(field_ty, &sub_current, rest, value)?;
        Some(format!("{name} {{ {member}: {sub_updated}, ..{current} }}"))
    }

    fn assign_compound_expr(
        &mut self,
        binary: &syn::ExprBinary,
        emit_overflow_check: bool,
    ) -> bool {
        if is_deref_assignment_target(binary.left.as_ref()) {
            // Slice C: `*P op= rhs` on a supported scalar mut-ref place desugars
            // to the single-write funnel; every other deref shape keeps the
            // pre-existing fail-closed rejection inside the helper.
            return self.assign_deref_compound_expr(binary, emit_overflow_check);
        }
        let Expr::Index(index_target) = strip_place_wrappers(binary.left.as_ref()) else {
            if assignment_target_uses_erased_mut_ref_alias(binary.left.as_ref(), self) {
                self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                    binary.left.as_ref(),
                ));
            }
            return false;
        };
        let Some(op) = compound_assignment_value_op(&binary.op) else {
            return false;
        };
        if let Some((name, outer_index_expr, inner_index_expr)) =
            nested_index_assignment_target(index_target)
        {
            if self.is_unsupported_index_receiver(&name) {
                self.parse_error = Some(unsupported_reference_index_assignment_error(
                    binary.left.as_ref(),
                ));
                return false;
            }

            let mut assignments = self.externally_assigned_in_expr(outer_index_expr);
            assignments.extend(self.externally_assigned_in_expr(inner_index_expr));
            assignments.extend(self.externally_assigned_in_expr(&binary.right));
            if !assignments.is_empty() {
                self.parse_error = Some(unsupported_index_compound_assignment_error(&binary.op));
                return false;
            }

            let receiver = self.lookup_scoped(&name);
            let outer_index = self.expr_to_scoped_string(outer_index_expr);
            let inner_index = self.expr_to_scoped_string(inner_index_expr);
            let rhs = format!("({})", self.expr_to_scoped_string(&binary.right));
            let old_value = format!("({receiver})[{outer_index}][{inner_index}]");
            let value = format!("({old_value} {op} {rhs})");
            // External-assignment side effects are already rejected above; gate the
            // 2D element-safety on a modelable receiver (mirroring the 1D path).
            self.maybe_emit_exec_compound_element_safety(
                &value,
                emit_overflow_check && self.index_receiver_is_modelable(&name),
            );
            let inner_receiver = format!("({receiver})[{outer_index}]");
            let updated_inner = format!("{inner_receiver}.update({inner_index}, {value})");
            self.assign_scoped(
                &name,
                format!("{receiver}.update({outer_index}, {updated_inner})"),
            );
            return true;
        }
        let Some(name) = expr_path_ident(&index_target.expr) else {
            return false;
        };

        let index_assignments = self.externally_assigned_in_expr(&index_target.index);
        let rhs_assignments = self.externally_assigned_in_expr(&binary.right);
        if index_assignments.contains(&name) || rhs_assignments.contains(&name) {
            self.invalidate_scoped(&name);
            return true;
        }

        // SOUNDNESS-CRITICAL (#83, exec array/slice OOB panic-freedom). A compound
        // write whose INDEX or RHS has a side effect — e.g. `ar[{ j = i; j }] += 1`,
        // or the realistic `ar[m.next()] += 1` where `next()` is `&mut self` and may
        // return an out-of-bounds index — must STILL carry the write-index bound +
        // element-overflow check. Previously the obligation was SKIPPED for ANY
        // side-effecting index/RHS (to avoid re-executing the effect across the
        // `update(idx, a[idx] OP rhs)` rewrite, which mentions `idx` twice), so an
        // unbounded resulting index silently `Verified` despite a runtime OOB panic.
        //
        // The index and RHS are evaluated EXACTLY ONCE here. A block-embedded PLAIN
        // (local-variable) assignment is FOLDED into a pure value by
        // `eval_block_expr` (the effect is applied to the evaluation's own throwaway
        // scope, never re-rendered into the result string), so the resolved index is
        // a side-effect-free VALUE that can be reused in the element read, in the
        // reflexive `(value) == (value)` obligation, AND in the `update` chain
        // without re-executing anything — the effect is modeled once. Such a
        // side-effecting index/RHS that does NOT fold to a pure value (e.g. a bare
        // `ar[(j = i)] += 1`, whose raw `j = i` would be textually re-embedded by
        // every use) is refused outright below, failing closed rather than silently
        // `Verified`.
        //
        // EXCEPTION — a side effect that writes THROUGH A DEREFERENCE (`*r = …`, the
        // mut-ref aliasing-evaluation-order case like `x[{ *r = 1; 0 }] += { *r = 2;
        // 2 }`) is NOT modeled: the throwaway scoped evaluation reverts the aliased
        // write, so trust-vc cannot soundly reason about the post-write alias and the
        // function fails closed on its own when that alias is later observed (the
        // binding is unresolved). For that subset the original skip is preserved
        // verbatim — no obligation is pinned (so it neither shifts the
        // independently-failing obligation program points nor pretends to model the
        // alias) and the purity guard is bypassed. Closing the residual OOB for an
        // UNOBSERVED deref-aliased index requires a faithful mut-ref aliasing model
        // and is tracked separately, out of #83's plain-side-effect scope.
        let has_deref_write_side_effect = expr_contains_deref_assignment(&index_target.index)
            || expr_contains_deref_assignment(&binary.right);
        let index = self.expr_to_scoped_string(&index_target.index);
        let rhs = format!("({})", self.expr_to_scoped_string(&binary.right));
        if !has_deref_write_side_effect
            && ((expr_contains_assignment(&index_target.index)
                && !resolved_value_is_side_effect_free(&index))
                || (expr_contains_assignment(&binary.right)
                    && !resolved_value_is_side_effect_free(&rhs)))
        {
            self.parse_error = Some(unsupported_index_compound_assignment_error(&binary.op));
            return false;
        }
        // Emit the element-safety obligation for any faithfully modeled write (a
        // modelable receiver) whose side effects fold to re-usable pure values. A
        // PLAIN side-effecting index is no longer exempt — its write-index bound and
        // element-overflow check fire exactly like a side-effect-free one; only the
        // un-modelable deref-aliasing case keeps the conservative skip.
        let emit_element_safety = emit_overflow_check
            && self.index_receiver_is_modelable(&name)
            && !has_deref_write_side_effect;
        if let Some(receiver) = self.lookup_mut_ref_alias_index_receiver(&name) {
            let old_value = format!("({receiver})[{index}]");
            let value = format!("({old_value} {op} {rhs})");
            self.maybe_emit_exec_compound_element_safety(&value, emit_element_safety);
            return self.assign_mut_ref_alias_index(&name, &index, &value);
        }
        if self.is_unsupported_index_receiver(&name) {
            self.parse_error = Some(unsupported_reference_index_assignment_error(
                binary.left.as_ref(),
            ));
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        let old_value = format!("({receiver})[{index}]");
        let value = format!("({old_value} {op} {rhs})");
        self.maybe_emit_exec_compound_element_safety(&value, emit_element_safety);
        self.assign_scoped(&name, format!("{receiver}.update({index}, {value})"));
        true
    }

    fn expr_to_scoped_string(&mut self, expr: &Expr) -> String {
        if let Some(rendered) = self.expr_to_scoped_string_inner(expr) {
            return rendered;
        }
        // FAIL CLOSED before handing back the raw token fallback. See
        // `raw_fallback_dropped_mutations`: the fallback re-emits the
        // expression VERBATIM, which is correct for a pure expression the
        // encoder can re-parse and CATASTROPHIC for one whose nested blocks
        // carry statement-position mutations — the encoder has no statement
        // semantics, so it reads each block's tail against the ENTRY state.
        if self.parse_error.is_none() {
            let dropped = self.raw_fallback_dropped_mutations(expr);
            if !dropped.is_empty() {
                self.parse_error = Some(raw_fallback_dropped_mutation_error(expr, &dropped));
            }
        }
        super::extract_expr_string(expr)
    }

    /// The bindings whose mutation a RAW token rendering of `expr` would
    /// silently drop.
    ///
    /// SOUNDNESS-CRITICAL. `expr_to_scoped_string`'s fallback re-emits the
    /// expression verbatim when no arm models it. For an expression containing a
    /// STATEMENT-position side effect the encoder loses it entirely and reads the
    /// container's tail against the ENTRY state. Three live cardinal false
    /// verifies, differing from the already-pinned straight-line form ONLY in
    /// which syntactic container the returned expression sat in:
    ///
    ///     pub fn a1(f: bool, t: &mut C) -> u64 { if f { bump(t); t.n } else { bump(t); t.n } }
    ///     pub fn a5(t: &mut C) -> u64        { let x = { bump(t); t.n }; x }
    ///     pub fn p1(k: bool, t: &mut C) -> u64 { match k { true => { bump(t); t.n } false => { bump(t); t.n } } }
    ///
    /// each proving `result == 0` while every execution returns 1. The root
    /// itself WAS havoced — `assert!(t.n == 0)` after the same `let` is correctly
    /// refuted — so the defect is precisely "the value carried out of the
    /// container was rendered against a state the container had already left",
    /// not a missing havoc.
    ///
    /// NARROW ON PURPOSE, and this is what a blunter "decline every unmodelled
    /// container" implementation fails: only the statements a raw rendering
    /// DROPS are examined (a trailing tail expression is kept, so it is not
    /// dropped), and only a MUTATION counts. `if c { let y = t.n; y } else { 0 }`
    /// and every statement-free container keep the existing rendering untouched.
    /// Closure bodies are excluded — they are not evaluated at this site and the
    /// Phase-C closure lane models them itself.
    fn raw_fallback_dropped_mutations(&self, expr: &Expr) -> BTreeSet<String> {
        #[derive(Default)]
        struct NestedBlocks<'ast> {
            blocks: Vec<&'ast syn::Block>,
        }
        impl<'ast> Visit<'ast> for NestedBlocks<'ast> {
            fn visit_block(&mut self, block: &'ast syn::Block) {
                self.blocks.push(block);
                visit::visit_block(self, block);
            }
            fn visit_expr_closure(&mut self, _closure: &'ast syn::ExprClosure) {}
        }
        let mut nested = NestedBlocks::default();
        nested.visit_expr(expr);
        let mut dropped = BTreeSet::new();
        for block in nested.blocks {
            // The trailing tail expression IS carried by the raw rendering; only
            // the statements in front of it are lost.
            let non_tail = match block.stmts.last() {
                Some(Stmt::Expr(_, None)) => &block.stmts[..block.stmts.len() - 1],
                _ => &block.stmts[..],
            };
            // MIRROR `eval_scoped_stmts` EXACTLY, and this is load-bearing: it
            // models `Stmt::Expr(Expr::Assign, Some(_))` and the compound-assign
            // form itself (`assign_expr` / `assign_compound_expr` rewrite the
            // scoped value) and declines ONLY on a discarded-value expression
            // statement that externally assigns. Counting an assignment
            // statement here rejected `let _ = (ar[{ j = i; j }], 0usize);` —
            // a side-effecting index whose write IS applied, by the dedicated
            // once-only index machinery, and whose rejection was pure
            // over-rejection (`exec_index_bounds_faithful`
            // `nested_side_effecting_index_{bounded_read_verifies,
            // unbounded_read_is_rejected}` both went red). The two functions
            // must agree on what "unmodelable" means or this gate rejects
            // programs the renderer handles.
            let unmodelable: Vec<Stmt> = non_tail
                .iter()
                .filter(|stmt| {
                    matches!(stmt, Stmt::Expr(expr, Some(_))
                        if !matches!(expr, Expr::Assign(_))
                            && !matches!(expr, Expr::Binary(binary) if is_assignment_binop(&binary.op)))
                })
                .cloned()
                .collect();
            if unmodelable.is_empty() {
                continue;
            }
            dropped.extend(self.externally_assigned_in_stmts(&unmodelable));
        }
        dropped
    }

    fn externally_assigned_in_stmts(&self, stmts: &[Stmt]) -> BTreeSet<String> {
        let mut collector = ExternalAssignmentCollector::with_macro_scopes(&self.local_macros);
        collector.collection_receivers = self.collection_typed_receiver_names();
        collector.struct_receivers = self.struct_typed_receiver_names();
        collector.struct_self_receiver_kinds = self.vc.struct_self_receiver_kinds_clone();
        collector.type_param_mut_methods = self.type_param_mut_methods_by_receiver();
        collector.mut_ref_call_args = self.mut_ref_call_args.clone();
        collector.method_arg_mut_flags = self.method_arg_mut_flags.clone();
        collector.mut_ref_reborrowable_bindings = self.mut_ref_reborrowable_bindings.clone();
        for stmt in stmts {
            collector.visit_stmt(stmt);
        }
        collector.external_assignments
    }

    /// Slice B of the mut-ref two-state keystone: `old(P)` / `old(*P)` /
    /// `*old(P)` / `*old(*P)` inside an exec-fn BODY (assert!/assume!/
    /// invariant!/assignment RHS — every scoped rendering funnels through
    /// `expr_to_scoped_string_inner`) denotes the ENTRY (pre-state) value of a
    /// supported scalar `&mut` parameter. In the string-substitution body model
    /// that is exactly the DECLARED parameter symbol: assignments rebind the
    /// SCOPED value (`lookup_scoped`), aliases route through
    /// `erased_mut_ref_targets` to the same scoped rebind, and havocs bind
    /// FRESH symbols — but the bare declared symbol itself is never re-bound or
    /// re-constrained after the `requires` assumptions pin it at entry.
    ///
    /// SOUNDNESS-CRITICAL (the time-travel landmine): this deliberately does
    /// NOT call `lookup_scoped(name)`. The scoped value is the CURRENT
    /// (post-assignment) state, so rendering it would make `old()` silently
    /// read the post state whenever the assert follows a write through the
    /// param (`*x = 7; assert!(*old(x) == 7)` would wrongly verify) or through
    /// an alias — the catastrophic direction. The same never-read-current
    /// discipline as the slice-A contract rewriter (`FinalValueSubstituter`).
    ///
    /// Returns `Some(entry_symbol)` for a supported bare/deref param shape;
    /// sets the fail-closed error for an `old()` over a non-supported param or
    /// a non-bare argument (`old(field)`, `old(expr)`, `old()`, …) — the
    /// PRE-EXISTING `unsupported_old_state_call_error` message VERBATIM, so
    /// every unsupported body shape keeps the exact error the manifest/port
    /// fail-closed pins expect (only genuinely-supported shapes change
    /// behavior); `None` (no error) when the expression is not an `old(..)`
    /// form at all.
    fn old_state_body_entry_symbol(&mut self, expr: &Expr) -> Option<String> {
        match super::classify_old_call(expr) {
            super::OldCallShape::Param(name)
                if self.supported_mut_ref_param_targets.contains(&name) =>
            {
                Some(name)
            }
            super::OldCallShape::Param(_) | super::OldCallShape::BadArg => {
                // The classified expression is `old(..)` or `*old(..)`; recover
                // the inner call node for the (unchanged) error rendering.
                let call = match expr {
                    Expr::Call(call) => Some(call),
                    Expr::Unary(unary) => match unary.expr.as_ref() {
                        Expr::Call(call) => Some(call),
                        _ => None,
                    },
                    _ => None,
                };
                self.parse_error = Some(match call {
                    Some(call) => unsupported_old_state_call_error(call),
                    // Unreachable given the classifier's shape, but stay
                    // fail-closed rather than panic if it ever drifts.
                    None => TrustVcError::Encoding {
                        context: "extract body assertions",
                        detail: format!(
                            "Unsupported old-state expression `old(...)` in \
                             vc_extraction: `{}`",
                            expr.to_token_stream()
                        ),
                    },
                });
                None
            }
            super::OldCallShape::NotOld => None,
        }
    }

    fn expr_to_scoped_string_inner(&mut self, expr: &Expr) -> Option<String> {
        // Two-state `old(..)` body forms FIRST (mirrors the slice-A contract
        // rewriter's arm ordering): an `old(..)` call — with or without the
        // outer deref — must be intercepted before the generic `Unary`/`Call`
        // arms below would render `*` + a call, or route the call to
        // `format_call_expr` (whose `old` arm stays as the fail-closed
        // backstop for any other funnel). On a classified-but-unsupported
        // shape `old_state_body_entry_symbol` has set `parse_error`; returning
        // `None` falls back to the raw rendering, which the pending hard error
        // then rejects (fail-closed, never a silent current-state read).
        if matches!(expr, Expr::Call(_) | Expr::Unary(_)) {
            if !matches!(super::classify_old_call(expr), super::OldCallShape::NotOld) {
                return self.old_state_body_entry_symbol(expr);
            }
        }
        match expr {
            Expr::Path(_) => expr_path_ident(expr).map(|name| self.lookup_scoped(&name)),
            Expr::Lit(_) => Some(super::extract_expr_string(expr)),
            Expr::Paren(paren) => Some(format!("({})", self.expr_to_scoped_string(&paren.expr))),
            Expr::Group(group) => self.expr_to_scoped_string_inner(&group.expr),
            Expr::Unary(unary)
                if matches!(unary.op, syn::UnOp::Deref(_))
                    && (self.is_erased_shared_ref_expr(&unary.expr)
                        || self.is_erased_mut_ref_expr(&unary.expr)
                        || expr_path_ident(&unary.expr).as_deref().is_some_and(|name| {
                            self.supported_mut_ref_param_targets.contains(name)
                        })) =>
            {
                Some(self.expr_to_scoped_string(&unary.expr))
            }
            Expr::Unary(unary) => Some(format!(
                "{}{}",
                unary.op.to_token_stream(),
                self.expr_to_scoped_string(&unary.expr)
            )),
            Expr::Reference(reference) if reference.mutability.is_none() => {
                Some(self.expr_to_scoped_string(&reference.expr))
            }
            Expr::Field(field) => {
                let base = self.expr_to_scoped_string(&field.base);
                Some(format!("({base}).{}", field_member_name(&field.member)))
            }
            Expr::Index(index) => {
                let base = self.expr_to_scoped_string(&index.expr);
                let index = self.expr_to_scoped_string(&index.index);
                Some(format!("{base}[{index}]"))
            }
            Expr::Binary(binary) => {
                if is_assignment_binop(&binary.op) {
                    None
                } else {
                    Some(self.with_temporary_scopes(|collector| {
                        let left = collector.expr_to_scoped_string(&binary.left);
                        collector.invalidate_expr_side_effects(&binary.left);
                        let right = collector.expr_to_scoped_string(&binary.right);
                        format!("{} {} {}", left, binary.op.to_token_stream(), right)
                    }))
                }
            }
            Expr::Cast(cast) => Some(format!(
                "{} as {}",
                self.expr_to_scoped_string(&cast.expr),
                cast.ty.to_token_stream()
            )),
            Expr::Struct(strukt) => Some(self.format_struct_expr(strukt)),
            Expr::Call(call) => {
                self.with_temporary_scopes(|collector| collector.format_call_expr(call))
            }
            Expr::MethodCall(method_call) => {
                Some(self.with_temporary_scopes(|collector| {
                    collector.format_method_call_expr(method_call)
                }))
            }
            Expr::Macro(mac) => {
                self.with_temporary_scopes(|collector| collector.format_supported_macro_expr(mac))
            }
            Expr::Block(block) => self.eval_block_expr(&block.block),
            // Scope-substitute a `match` expression in return/value position so
            // let-bound locals referenced in the scrutinee or arm bodies resolve
            // to their models. This is what lets the REAL `eval_constraint` body
            // `match constraint.rel { PbRel::Ge => lhs >= rhs, PbRel::Eq => lhs
            // == rhs }` lower as the function's return value: without this arm
            // the match falls through to the raw `extract_expr_string` fallback
            // and the let-bound `lhs`/`rhs` are emitted verbatim, so the encoder
            // rejects the `return_value` obligation with "unresolved variable
            // `lhs`". Each arm's own pattern bindings are SHADOWED so a binding
            // that shares a name with an outer local is not rewritten. Guarded
            // arms are not modeled here (fall back), keeping this sound.
            Expr::Match(expr_match) => {
                let scrutinee = self.expr_to_scoped_string(&expr_match.expr);
                let arm_count = expr_match.arms.len();
                let has_wildcard = expr_match
                    .arms
                    .iter()
                    .any(|arm| matches!(&arm.pat, Pat::Wild(_)));
                // The last-arm-as-`_` rewrite below is sound ONLY for an
                // EXHAUSTIVE match. A non-exhaustive one (rustc-invalid but the
                // syn path does not check) would pin its uncovered cases to the
                // last arm — a false-verify. Gate on a real exhaustiveness check.
                let exhaustive = self.match_is_exhaustive(expr_match);
                let mut arms = Vec::with_capacity(arm_count);
                for (index, arm) in expr_match.arms.iter().enumerate() {
                    if arm.guard.is_some() {
                        return None;
                    }
                    let body = self.with_temporary_scopes(|collector| {
                        collector.shadow_pat_bindings(&arm.pat);
                        collector.expr_to_scoped_string(&arm.body)
                    });
                    // The encoder's `match` requires a catch-all else branch, so
                    // an EXHAUSTIVE match with no `_` arm (bool `true`/`false`, an
                    // all-variants enum, …) is otherwise rejected ("Every
                    // non-wildcard arm must have an else branch"). Render the LAST
                    // arm as `_`: since the input is valid Rust the match is
                    // exhaustive, so by top-to-bottom arm order the residual after
                    // the earlier arms is exactly the last arm's cases — `_`
                    // denotes the same set. Guarded to when the last pattern binds
                    // no identifier its body reads, so the `_` never drops a used
                    // binding (`Some(x) => x` is left intact → fail-closed if the
                    // encoder can't take it). Sound: over-approximating to `_`
                    // cannot admit a case the original arm excluded.
                    let is_catch_all_last = index + 1 == arm_count
                        && exhaustive
                        && !has_wildcard
                        && !matches!(&arm.pat, Pat::Wild(_))
                        && pat_bound_idents(&arm.pat)
                            .is_disjoint(&closure_body_referenced_path_idents(&arm.body));
                    if is_catch_all_last {
                        arms.push(format!("_ => {body}"));
                    } else {
                        let pat = arm.pat.to_token_stream();
                        arms.push(format!("{pat} => {body}"));
                    }
                }
                Some(format!("match {scrutinee} {{ {} }}", arms.join(", ")))
            }
            // Scope-substitute an `if`/`else` expression in return/value position
            // so let-bound locals referenced in the guard or either branch resolve
            // to their models. This is what lets the REAL `eval_lit` body
            // `let value = ..; if lit.negated { !value } else { value }` lower as
            // the function's return value: without this arm the `if` falls through
            // to the raw `extract_expr_string` fallback and the let-bound `value`
            // is emitted verbatim, so the encoder rejects the `return_value`
            // obligation with "unresolved variable `value`". Both branch blocks
            // and the guard are rendered with the current scope (each branch in a
            // temporary scope so a branch-local binding does not leak); the result
            // is the faithful `if g { t } else { e }` term — a pure value
            // substitution, sound exactly like the `Expr::Match` arm above. An
            // `if let` guard or a value-position `if` without an `else` is not
            // modeled here (returns None -> raw fallback), keeping it sound.
            Expr::If(expr_if) => {
                if matches!(&*expr_if.cond, Expr::Let(_)) {
                    return None;
                }
                let (_, else_expr) = expr_if.else_branch.as_ref()?;
                let condition = self.with_temporary_scopes(|collector| {
                    collector.expr_to_scoped_string(&expr_if.cond)
                });
                let then_value = self.with_temporary_scopes(|collector| {
                    collector.eval_block_expr(&expr_if.then_branch)
                })?;
                let else_value = self
                    .with_temporary_scopes(|collector| collector.expr_to_scoped_string(else_expr));
                Some(format!(
                    "if {condition} {{ {then_value} }} else {{ {else_value} }}"
                ))
            }
            // GAP1: scope-substitute a closure body so a let-bound local that is
            // referenced inside the closure (e.g. the `nonneg` in `forall(|i:
            // int| nonneg.contains(i))`) resolves to its scoped model. Without
            // this arm a closure falls through to the raw `extract_expr_string`
            // fallback and the local is emitted verbatim/unresolved — the SMT
            // encoder then rejects the condition with "unresolved variable".
            Expr::Closure(closure) => Some(self.scoped_closure_string(closure)),
            _ => None,
        }
    }

    /// Resolves the outer let-bound locals that a (spec/quantifier) closure body
    /// CAPTURES, substituting each with its scoped model, while SHADOWING the
    /// closure parameters (a parameter that shares a name with an outer binding
    /// is freshly bound, so it must NOT be rewritten).
    ///
    /// The rewrite is performed at the AST level over a clone of the whole
    /// closure and only replaces free single-ident value references, so the
    /// closure's structure — parameter patterns, return type, block/`return`
    /// bodies, and inner `#![trigger ..]` annotations — is preserved verbatim.
    /// When the body captures nothing that needs resolving, the EXACT raw
    /// rendering is returned unchanged (no spacing/structure drift).
    fn scoped_closure_string(&mut self, closure: &syn::ExprClosure) -> String {
        // Parameter names are freshly bound by the closure; never substitute
        // them. `ContractExprSubstituter` is a flat (non-scoped) rewriter, so we
        // also exclude EVERY identifier bound anywhere inside the body (nested
        // closure params, `let`s, `match`/`for` patterns). A name re-bound in an
        // inner scope must not be replaced with an outer value; excluding it
        // conservatively leaves it intact (fail-closed) rather than risk an
        // unsound substitution under nested shadowing.
        // Normalize `==>`/`<==>` marker macros in the body to same-named CALL
        // forms so the syn visitors below (which do NOT descend into a macro's
        // opaque tokens) can see and rewrite a let-local inside an implies/iff
        // (e.g. `forall|k| s.contains(k) ==> ..`). Denormalized back before
        // rendering. Analysis + rewrite run on this normalized copy; the empty-
        // substitutions early return still renders the ORIGINAL closure verbatim.
        let mut norm_closure = closure.clone();
        normalize_spec_markers(&mut norm_closure.body);
        let mut shadowed = BTreeSet::new();
        for input in &norm_closure.inputs {
            shadowed.extend(bound_idents_from_pat(input));
        }
        shadowed.extend(closure_body_bound_idents(&norm_closure.body));
        // Map each captured free ident that resolves to a *distinct* scoped value
        // (a let-bound local, or a re-bound parameter) to that value's AST.
        let mut substitutions = BTreeMap::new();
        for name in closure_referenced_idents(&norm_closure.body) {
            if shadowed.contains(&name) || !self.has_scoped_name(&name) {
                continue;
            }
            let value = self.lookup_scoped(&name);
            if value == name {
                continue;
            }
            match syn::parse_str::<Expr>(&value) {
                Ok(expr) => {
                    // Capture-avoidance (SOUNDNESS): the value is spliced *under*
                    // the closure's binders. If it references any identifier the
                    // closure binds (a param or inner binder), splicing it would
                    // CAPTURE that free variable — e.g. substituting the model of
                    // `c = Set::new(|x| x >= p)` into a body that rebinds `p` via
                    // `forall |p| ..` collapses membership to the tautology
                    // `p >= p` and makes a FALSE property verify. `shadowed` is
                    // exactly the closure's bound-ident set, so when the value's
                    // referenced idents intersect it, skip the substitution and
                    // leave the reference unresolved (fail-closed) rather than
                    // perform a capturing (unsound) substitution. The hygienic
                    // alternative would alpha-rename the colliding binder; the
                    // skip is the conservative, obviously-sound choice.
                    // Only the value's FREE identifiers can be captured: an
                    // identifier bound *inside* the value (e.g. the `i` in
                    // `Set::new(SpecFn::new(|i| i >= 0))`) is already scoped
                    // within the value and is alpha-renamable, so it cannot be
                    // captured by an outer binder of the same name. Subtract the
                    // value's own bound idents before testing the collision, or
                    // we would over-skip legitimate substitutions whose inner
                    // closure params merely happen to match the outer binder.
                    // Normalize markers in the VALUE too, so a free ident hidden
                    // inside an implies/iff in the substituted value is counted by
                    // the capture check (never under-count a potential capture).
                    let mut norm_value = expr.clone();
                    normalize_spec_markers(&mut norm_value);
                    let mut value_free = closure_referenced_idents(&norm_value);
                    for bound in closure_body_bound_idents(&norm_value) {
                        value_free.remove(&bound);
                    }
                    if value_free.iter().any(|ident| shadowed.contains(ident)) {
                        continue;
                    }
                    substitutions.insert(name, expr);
                }
                // If a scoped model does not re-parse as an expression we cannot
                // safely splice it; leave the reference for the existing
                // fail-closed handling rather than emit malformed syntax.
                Err(_) => continue,
            }
        }
        if substitutions.is_empty() {
            return closure.to_token_stream().to_string();
        }
        let mut rewritten = Expr::Closure(norm_closure);
        let erased_shared_ref_params = BTreeSet::new();
        let old_substitutions = BTreeMap::new();
        let erased_mut_ref_value_params = BTreeSet::new();
        ContractExprSubstituter {
            substitutions: &substitutions,
            erased_shared_ref_params: &erased_shared_ref_params,
            old_substitutions: &old_substitutions,
            erased_mut_ref_value_params: &erased_mut_ref_value_params,
            binder_scopes: Vec::new(),
            unscopable_binder: false,
        }
        .visit_expr_mut(&mut rewritten);
        denormalize_spec_markers(&mut rewritten);
        rewritten.to_token_stream().to_string()
    }

    fn format_call_expr(&mut self, call: &syn::ExprCall) -> Option<String> {
        self.record_helper_contract_call(call);
        if let Some(inlined) = self.try_inline_capture_free_exec_closure_call(call) {
            return Some(inlined);
        }
        let Expr::Path(func_path) = &*call.func else {
            return None;
        };
        if super::path_last_segment(&func_path.path).as_deref() == Some("old") {
            self.parse_error = Some(unsupported_old_state_call_error(call));
            return None;
        }
        // A NO-SELF UFCS associated call `<S as Trait>::assoc()` (a qualified path
        // with an empty argument list) is rendered with the CONCRETE self type
        // named by `qself.ty` (`S::assoc`) rather than the trait-qualified
        // `Trait::assoc` — the trait name loses which impl is meant, so it cannot
        // distinguish two impls, and the concrete `S::assoc` symbol is the one the
        // inherent-style associated registration keys into. A WITH-self UFCS call
        // (args present, e.g. `<S as Trait>::m(&s)`) keeps its existing rendering,
        // which already resolves via the concrete-receiver metadata.
        let func = match &func_path.qself {
            Some(qself) if call.args.is_empty() => {
                match super::path_last_segment(&func_path.path) {
                    Some(method) => {
                        format!(
                            "{}::{}",
                            crate::local_vars::extract_type_string(&qself.ty),
                            method
                        )
                    }
                    None => func_path.path.to_token_stream().to_string(),
                }
            }
            _ => func_path.path.to_token_stream().to_string(),
        };
        let args = self.scoped_call_args_left_to_right(&call.args).join(", ");
        Some(format!("{func}({args})"))
    }

    /// If `call` applies a BARE let-bound exec closure `f` (from
    /// `exec_closure_defs`) whose body is a PURE function of its parameters — no
    /// captured outer locals and no free callees (every referenced single-segment
    /// ident is a parameter or bound inside the body) — return the inlined body
    /// rendered as a scoped string with each parameter substituted by its call
    /// argument. This lets `let f = |y| y + 1; f(x)` model as `x + 1` so
    /// `ensures(result == x + 1)` VERIFIES, instead of failing closed at lowering
    /// ("unknown return type for function 'f'"). Bare `let`-bound closures are
    /// otherwise unmodeled (only `closure!` literals and `Fn`-bound params get a
    /// `SpecFn` type / call-site obligations).
    ///
    /// SOUNDNESS: restricting to CAPTURE-FREE bodies makes the inline an exact
    /// value substitution independent of move/non-move capture semantics — the
    /// closure IS its body applied to the arguments. A captured outer variable
    /// (the mutation-capture false-verify class the `closure!` def-side check
    /// also fails closed on) or a free callee leaves the referenced-ident set
    /// non-empty, so we return `None` and the call stays fail-closed (sound
    /// OVER-rejection). The simple-ident-param / arity / no-param-reshadowed
    /// guards mirror `maybe_emit_invoked_exec_closure_arith_safety`, keeping the
    /// substitution exact. Panic-freedom of the inlined body is unaffected: the
    /// arith-safety path (same substitution) still pins the body's overflow /
    /// divide-by-zero / index obligations independently.
    fn try_inline_capture_free_exec_closure_call(
        &mut self,
        call: &syn::ExprCall,
    ) -> Option<String> {
        let Expr::Path(func_path) = &*call.func else {
            return None;
        };
        if func_path.qself.is_some() || func_path.path.segments.len() != 1 {
            return None;
        }
        let name = func_path.path.segments[0].ident.to_string();
        let closure = self.exec_closure_defs.get(&name)?.clone();
        // A macro invocation in the body (`assert!`, `assume!`, `seq!`, …) is
        // OPAQUE to the syn visitors — `closure_body_referenced_path_idents`
        // cannot see idents inside its token stream, so a captured local or free
        // callee hidden in a macro would be missed and the body wrongly judged
        // capture-free. Bail so such a body stays fail-closed (the value-carrying
        // capability bodies — `y + 1`, `y`, `7` — carry no macro).
        if closure_body_contains_macro(&closure.body) {
            return None;
        }
        let mut param_names = Vec::with_capacity(closure.inputs.len());
        for input in &closure.inputs {
            param_names.push(closure_param_simple_ident(input)?);
        }
        if param_names.len() != call.args.len() {
            return None;
        }
        let body_bound = closure_body_bound_idents(&closure.body);
        // Shadowing-safety: a param re-bound in the body must not be flat-substituted.
        if param_names.iter().any(|n| body_bound.contains(n)) {
            return None;
        }
        // Capture-freedom: every referenced single-segment ident must be a
        // parameter or bound inside the body. Anything else is a captured outer
        // local or a free callee -> bail (fail closed, sound over-rejection).
        let param_set: BTreeSet<String> = param_names.iter().cloned().collect();
        let referenced = closure_body_referenced_path_idents(&closure.body);
        if referenced
            .iter()
            .any(|id| !param_set.contains(id) && !body_bound.contains(id))
        {
            return None;
        }
        let subst: HashMap<String, Expr> = param_names
            .into_iter()
            .zip(call.args.iter().cloned())
            .collect();
        let mut body = (*closure.body).clone();
        substitute_param_idents(&mut body, &subst);
        Some(self.expr_to_scoped_string(&body))
    }

    fn scoped_call_args_left_to_right(
        &mut self,
        args: &Punctuated<Expr, Token![,]>,
    ) -> Vec<String> {
        args.iter()
            .map(|arg| {
                let rendered = self.expr_to_scoped_string(arg);
                self.invalidate_expr_side_effects(arg);
                rendered
            })
            .collect()
    }

    /// Argument renderings for a CONTRACTED helper call's requires/ensures
    /// substitution (slice D). Identical to `scoped_call_args_left_to_right`
    /// except at a `&mut`-SCALAR callee position whose argument is the literal
    /// `&mut v` of a tracked scalar binding: there the REFERENT VALUE rendering
    /// is used (`v`'s scoped value — the pre-call value before the havoc, the
    /// fresh symbol after), because the callee's contract constrains the
    /// referent's value, never the reference. Every other shape keeps the
    /// literal default rendering, which fails CLOSED downstream (`&mut` is not
    /// a supported specification expression).
    fn scoped_contract_call_args_left_to_right(
        &mut self,
        args: &Punctuated<Expr, Token![,]>,
        mut_scalar_flags: &[bool],
    ) -> Vec<String> {
        args.iter()
            .enumerate()
            .map(|(index, arg)| {
                let rendered = if mut_scalar_flags.get(index).copied().unwrap_or(false) {
                    self.mut_ref_scalar_call_arg_value_rendering(arg)
                        .unwrap_or_else(|| self.expr_to_scoped_string(arg))
                } else {
                    self.expr_to_scoped_string(arg)
                };
                self.invalidate_expr_side_effects(arg);
                rendered
            })
            .collect()
    }

    /// The referent-VALUE rendering of a literal `&mut v` argument at a
    /// `&mut`-scalar callee position, or `None` for every out-of-scope shape
    /// (which then keeps the fail-closed literal rendering):
    /// - `&mut &x` mutable-ref-to-shared-temporary (the callee cannot write
    ///   through it; the referent-erase would wrongly bind `x`),
    /// - non-bare places (`&mut v.field`, `&mut v[i]`, `&mut *p` reborrows),
    /// - an untracked binding, or one with no known SCALAR type (bool/integer)
    ///   — exactly the bindings `havoc_mut_ref_call_arg_referents` cannot
    ///   rebind to a fresh typed symbol, so a post-call "rendering" would not
    ///   actually be post-havoc.
    /// Bare-name forwarding (`f(x)` with `x` a scalar `&mut` param) is NOT
    /// routed here: its default rendering already IS the referent value via
    /// the erased-mut-ref model.
    fn mut_ref_scalar_call_arg_value_rendering(&mut self, arg: &Expr) -> Option<String> {
        if mut_ref_arg_is_shared_ref_temporary(arg) {
            return None;
        }
        // `mut_ref_path_ident` matches exactly `&mut <bare ident>` through
        // paren/group wrappers: fields, indexes, and `&mut *p` reborrows all
        // resolve to `None` (out of slice-D scope, keep the literal rendering).
        let referent = mut_ref_path_ident(arg)?;
        if !self.has_scoped_name(&referent) && !self.vc.has_variable(&referent) {
            return None;
        }
        let scalar = match self.vc.get_variable_type(&referent) {
            Some(ty) => matches!(ty, TrustVcType::Bool) || ty.is_integer(),
            None => self.modified_var_scalar_type(&referent).is_some(),
        };
        if !scalar {
            return None;
        }
        let path: Expr = syn::parse_str(&referent).ok()?;
        Some(self.expr_to_scoped_string(&path))
    }

    fn record_helper_contract_call(&mut self, call: &syn::ExprCall) {
        if self.parse_error.is_some() {
            return;
        }
        // INCREMENT 2b re-entrancy guard: while rendering a pass-site linkage
        // ground fact, a substituted result term `g(c, 5)` is rendered through
        // `format_call_expr` (which lands here). That is a REFERENCE to the
        // already-processed call, not a new occurrence — recording it again would
        // recurse without bound (the substituted node escapes the pointer dedup)
        // and double-emit obligations. Skip it.
        if self.suppress_helper_contract_recording {
            return;
        }
        let Some(helper_contracts) = self.helper_contracts else {
            return;
        };
        let key = call as *const syn::ExprCall as usize;
        if !self.recorded_helper_contract_call_sites.insert(key) {
            return;
        }

        let Some(helper_name) = super::call_function_symbol(call) else {
            return;
        };
        let Some(contract) = helper_contracts.get(&helper_name).cloned() else {
            return;
        };
        if contract.requires.is_empty() && contract.ensures.is_empty() {
            return;
        }
        if call.args.len() != contract.params.len() {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract sibling helper call contracts",
                detail: format!(
                    "Call to sibling helper `{helper_name}` has {} argument(s), but its contract has {} parameter(s)",
                    call.args.len(),
                    contract.params.len()
                ),
            });
            return;
        }

        let mut_scalar_flags = contract.mut_ref_scalar_params.clone();
        let call_args = self.with_temporary_scopes(|collector| {
            collector.scoped_contract_call_args_left_to_right(&call.args, &mut_scalar_flags)
        });
        let call_expr = format!("{helper_name}({})", call_args.join(", "));

        // Pre-havoc argument renderings snapshotted by `visit_expr_call` (only
        // present when this call havocs a `&mut`-passed root). The `requires`
        // substitution must see the PRE-call state; `ensures` keeps `call_args`
        // (the post-havoc rendering constraining the fresh post-call value).
        let pre_havoc_args = self
            .pre_havoc_call_args
            .remove(&key)
            .filter(|pre| pre.len() == call_args.len());

        // SOUNDNESS-CRITICAL (slice D, expression-position recording): when the
        // call HAVOCS a `&mut`-passed root but no pre-havoc snapshot exists,
        // this record was reached through an expression rendering (`let r =
        // f(&mut v)` / a nested call argument) BEFORE `visit_expr_call` ran the
        // havoc — so `call_args` above is a PRE-havoc rendering and binding the
        // `ensures` over it would pin the callee's postcondition onto the
        // pre-call value (with a caller `requires` pinning the same symbol this
        // manufactures a contradiction — vacuous-truth territory — and a
        // post-call `old(P)`-entry read could false-`Verified`). Emit the
        // `requires` obligations (the renderings ARE pre-call, exactly what
        // `requires` needs) but DROP the `ensures` assumption — havoc-only,
        // fail-closed-incomplete.
        let ensures_binding_sound =
            pre_havoc_args.is_some() || !self.call_havocs_mut_ref_args(call);

        if let Err(err) = self.add_helper_contract_obligations(
            &helper_name,
            &contract,
            &call_args,
            pre_havoc_args.as_deref(),
            &call_expr,
            ensures_binding_sound,
        ) {
            self.parse_error = Some(err);
        }
    }

    /// Phase C part 2 seam: for a DIRECT APPLICATION `f(arg)` of a KNOWN LOCAL
    /// `trust_vc::closure!` literal (registered in `closure_reflection_contracts`
    /// by `emit_closure_reflection_axioms`, with a co-emitted, independently
    /// def-side-CHECKED obligation), emit the call-site contract obligations by
    /// adapting the stored [`ClosureReflectionContract`] into a
    /// [`HelperCallContract`] and reusing the sound
    /// [`Self::add_helper_contract_obligations`] emitter: PROVE `f.requires(arg)`
    /// (an obligation, at the shared call-site program point) and ASSUME
    /// `f.ensures(arg, f(arg))` binding the REAL returned `spec_fn_apply` term
    /// (the identical UF the caller read `let t = f(arg)` lowers to — the term is
    /// pinned ONLY here). The reuse inherits the loop-body / unguardable-match-arm
    /// / short-circuit-RHS DROP discipline and forward-only ordering, so an
    /// in-loop `f(arg)` ensures never leaks past a zero-trip loop.
    ///
    /// UNARY only — a non-unary / arity-mismatched application returns with NO
    /// obligation, staying a fail-closed deferred lowering error (matching the
    /// unary-only guard in `dispatch/calls.rs`). A callee that is not a registered
    /// closure literal returns immediately, so helper / free calls are unaffected.
    ///
    /// CARDINAL INVARIANT: the assumed ensures is ONLY ever the def-side-CHECKED
    /// written clause. A closure is registered here iff
    /// `emit_closure_reflection_axioms` ran, which is co-located with the def-side
    /// obligation whose failure independently poisons the parent
    /// (`record_closure_def_side_failure` → `closure_def_side_failure`), so a lying
    /// closure sinks the whole function regardless of what this seam assumes.
    ///
    /// Two entry points feed the shared core
    /// [`Self::emit_closure_application_call_obligations`]: this one for calls the
    /// straight-line `visit_expr_call` walk reaches (a `let`-RHS / statement /
    /// call-argument occurrence, deduped by call-site pointer), and
    /// [`Self::emit_closure_application_obligations_in_expr`] for an occurrence
    /// inside an `assert!` / `assume!` macro's tokens (which the walk never
    /// reaches — mirroring the reflection ground-fact surface).
    fn record_closure_application_obligations(&mut self, call: &syn::ExprCall) {
        if self.parse_error.is_some() {
            return;
        }
        let key = call as *const syn::ExprCall as usize;
        if !self.recorded_closure_application_call_sites.insert(key) {
            return;
        }
        self.emit_closure_application_call_obligations(call);
        // INCREMENT 2a: a direct application `f(a)` of an Fn-bound `SpecFn`
        // PARAMETER (never a `closure!` literal — handled above) also emits its
        // call-site conditional assume over the opaque reflection UFs. A callee
        // that is neither returns with NO obligation, so helper/free calls and the
        // literal path are unaffected.
        self.emit_fn_bound_param_application_obligations(call);
    }

    /// The shared core: emit the prove-requires obligation + assume-ensures for a
    /// SINGLE direct-application call `f(arg)` of a registered UNARY closure!
    /// literal. Non-registered / non-unary callees return with NO obligation. The
    /// caller is responsible for single emission per source occurrence (the
    /// `visit_expr_call` path dedups on pointer; the assert/assume-condition path
    /// re-parses fresh tokens so each occurrence is visited exactly once).
    fn emit_closure_application_call_obligations(&mut self, call: &syn::ExprCall) {
        if self.parse_error.is_some() {
            return;
        }
        let Some(callee) = super::call_function_symbol(call) else {
            return;
        };
        let Some(contract) = self.closure_reflection_contracts.get(&callee).cloned() else {
            return;
        };
        // UNARY only; every other arity stays deferred (fail closed in lowering).
        if contract.params.len() != 1 || call.args.len() != 1 {
            return;
        }

        let call_args = self.with_temporary_scopes(|collector| {
            collector.scoped_contract_call_args_left_to_right(&call.args, &[])
        });
        let call_expr = format!("{callee}({})", call_args.join(", "));

        // Adapt the reflection contract into the helper-call shape. Closures here
        // are pure value params (the `closure_modelable_type` + capture guards), so
        // every `&mut` / erased-shared-ref flag is false, there is no pre-havoc
        // snapshot, and `ensures_binding_sound` is true — the simplest already
        // covered `add_helper_contract_obligations` path.
        let return_binding = contract
            .ensures
            .as_ref()
            .map(|(result_name, _)| result_name.clone())
            .unwrap_or_default();
        let requires = contract
            .requires
            .as_ref()
            .map(|condition| {
                vec![HelperContractClause {
                    condition: condition.clone(),
                    solver_mode: None,
                    proof_note: None,
                }]
            })
            .unwrap_or_default();
        let ensures = contract
            .ensures
            .as_ref()
            .map(|(_, condition)| {
                vec![HelperContractClause {
                    condition: condition.clone(),
                    solver_mode: None,
                    proof_note: None,
                }]
            })
            .unwrap_or_default();
        let helper = HelperCallContract {
            params: contract.params.clone(),
            erased_shared_ref_params: vec![false; contract.params.len()],
            mut_ref_scalar_params: vec![false; contract.params.len()],
            return_binding,
            requires,
            ensures,
            allow_in_spec: false,
        };
        if let Err(err) = self
            .add_helper_contract_obligations(&callee, &helper, &call_args, None, &call_expr, true)
        {
            self.parse_error = Some(err);
        }
    }

    /// INCREMENT 2a (Fn-bound closure dispatch, callee-side obligation model):
    /// for a DIRECT APPLICATION `f(arg)` where `f` is an `F: Fn(A) -> B`-bounded
    /// value PARAMETER (typed `SpecFn` by Increment 1, tracked in
    /// `fn_bound_spec_fn_params`), emit — over the OPAQUE, DISJOINT reflection UFs
    /// `call_requires%` / `call_ensures%` (`ir_builder`) — the SOUND call-site
    /// conditional assumption
    ///
    ///     call_requires%(f, arg)  ==>  call_ensures%(f, arg, f(arg))
    ///
    /// binding the REAL returned `spec_fn_apply(f, arg)` term (the identical UF the
    /// caller read `let r = f(arg)` lowers to). This is the closure's OWN written
    /// contract, unconditionally valid for ANY closure satisfying `F: Fn`.
    ///
    /// SOUNDNESS — the prove-requires GATES the assume-ensures. `call_ensures%` is
    /// NEVER assumed unconditionally: it becomes derivable ONLY once
    /// `call_requires%(f, arg)` is independently established — from the callee's own
    /// `requires f.requires((arg,))` (which lowers to an ASSUMED `call_requires%` —
    /// standard precondition assumption) or an explicit `assume!`. A callee that
    /// USES `f.ensures` WITHOUT establishing the (opaque, non-trivial) `f.requires`
    /// cannot derive the postcondition and fails closed (never a false Verified).
    /// `call_ensures%` stays OPAQUE, so the callee never invents a CONCRETE result
    /// value — a concrete pin (`assert!(f(a) == 5)`) still counterexamples. The
    /// callee proves a VALID CONDITIONAL "IF f.requires THEN f.ensures", sound for
    /// every `F: Fn`; the def-side-less parameter never enters an assumed lane with
    /// a concrete value, so the direct-application cardinal invariant (no def-side
    /// is invented for the parameter) is NOT weakened.
    ///
    /// WHY A CONDITIONAL ASSUME AND NOT A SEPARATE PROVE-`requires` OBLIGATION: the
    /// closure literal path (`emit_closure_application_call_obligations`) emits a
    /// standalone prove-`requires` because a literal's `requires` is a CONCRETE,
    /// def-side-checked clause that is normally dischargeable (e.g. `2 == 2`). A
    /// Fn-bound parameter's `requires` is the OPAQUE `call_requires%`, never
    /// dischargeable except by an assumed precondition; a standalone prove would
    /// therefore reject the sound Increment-1 determinism capability (`let a =
    /// f(3); let b = f(3); assert!(a == b)`, which uses only the congruent term and
    /// declares no `requires`). Folding the requires into the antecedent of the
    /// assume keeps determinism verifying while making the ensures underivable
    /// without the requires — the SAME modular obligation propagation as a
    /// standalone prove for every callee that actually uses the ensures, and strictly
    /// sound (the conditional is valid for any `F: Fn`). Realized by passing an
    /// EMPTY `requires` (so `add_helper_contract_obligations` emits no standalone
    /// obligation and no guard) and baking `!f.requires((arg,)) || f.ensures((arg,),
    /// result)` into a SINGLE `ensures` clause — which inherits that emitter's
    /// loop-body / unguardable-match-arm / short-circuit-RHS DROP discipline and
    /// forward-only ordering verbatim.
    ///
    /// Fires ONLY for a known Fn-bound `SpecFn` PARAMETER (never a `closure!`
    /// literal, a bare-closure local, or a ghost `SpecFn<A,B>` param), UNARY only;
    /// every other callee returns with NO obligation.
    fn emit_fn_bound_param_application_obligations(&mut self, call: &syn::ExprCall) {
        if self.parse_error.is_some() {
            return;
        }
        let Some(callee) = super::call_function_symbol(call) else {
            return;
        };
        // Fn-bound PARAMETER only. A `closure!` literal (in
        // `closure_reflection_contracts`) is handled by the sibling
        // `emit_closure_application_call_obligations`; a bare-closure / ghost-SpecFn
        // local is out of scope for this seam.
        if !self.fn_bound_spec_fn_params.contains(&callee)
            || self.closure_reflection_contracts.contains_key(&callee)
        {
            return;
        }
        // The parameter must be an ARITY-N `SpecFn` value whose arity matches the
        // call; a mismatch is a fail-closed deferred lowering error (matching
        // dispatch/calls.rs). The `SpecFn` typing is read from the VC variable table
        // — a Fn-bound parameter is a declared variable, so this is present exactly
        // when `f` is such a parameter.
        let Some(TrustVcType::SpecFn(arg_tys, _ret_ty)) =
            self.vc.get_variable_type(&callee).cloned()
        else {
            return;
        };
        if arg_tys.len() != call.args.len() {
            return;
        }

        // Synthetic binder / result names for the helper-contract substitution — one
        // arg binder per closure parameter (`__trust_vc_fnbound_arg{i}`). They are
        // ordinary (never-source-colliding) identifiers so the parsed clause `Expr`
        // and `ContractExprSubstituter` handle them like any param; the receiver `f`
        // (= `callee`) is NOT in the substitution map, so it stays as the in-scope
        // `SpecFn` parameter and its `.requires`/`.ensures` reflection lowers to the
        // opaque UFs (`dispatch/methods.rs`).
        const RESULT_BINDER: &str = "__trust_vc_fnbound_result";
        let arg_binders: Vec<String> = (0..arg_tys.len())
            .map(|i| format!("__trust_vc_fnbound_arg{i}"))
            .collect();

        // The N-tuple of arg binders, e.g. `(a0, a1,)` — a TRAILING COMMA so the
        // unary case renders a 1-tuple `(a0,)` (Rust/Verus tuple syntax), and `()`
        // for the nullary case (a comma-less empty tuple).
        let arg_tuple_src = if arg_binders.is_empty() {
            "()".to_string()
        } else {
            format!("({},)", arg_binders.join(", "))
        };

        // The SINGLE conditional-assume clause `!f.requires((a0, a1, ..)) ||
        // f.ensures((a0, a1, ..), result)` over the n-tuple.
        // `add_helper_contract_obligations` substitutes each `arg_binder{i} :=
        // arg{i}` and `RESULT_BINDER := f(a0, a1, ..)` and ASSUMES it (guard = None
        // because `requires` is empty), so nothing is asserted that a requires-free
        // call could fail.
        let ensures_src = format!(
            "!({callee}.requires({arg_tuple_src})) || {callee}.ensures({arg_tuple_src}, {RESULT_BINDER})"
        );
        let ensures_condition = match parse_helper_contract_expr(&ensures_src, &callee, "ensures") {
            Ok(expr) => expr,
            Err(err) => {
                self.parse_error = Some(err);
                return;
            }
        };

        let call_args = self.with_temporary_scopes(|collector| {
            collector.scoped_contract_call_args_left_to_right(&call.args, &[])
        });
        let call_expr = format!("{callee}({})", call_args.join(", "));

        let arg_count = arg_binders.len();
        let helper = HelperCallContract {
            params: arg_binders,
            erased_shared_ref_params: vec![false; arg_count],
            mut_ref_scalar_params: vec![false; arg_count],
            return_binding: RESULT_BINDER.to_string(),
            // EMPTY `requires`: the prove-requires is folded into the conditional
            // assume (see the doc-comment) rather than emitted standalone.
            requires: Vec::new(),
            ensures: vec![HelperContractClause {
                condition: ensures_condition,
                solver_mode: None,
                proof_note: None,
            }],
            allow_in_spec: false,
        };
        if let Err(err) = self
            .add_helper_contract_obligations(&callee, &helper, &call_args, None, &call_expr, true)
        {
            self.parse_error = Some(err);
        }
    }

    /// Phase C part 2, assert/assume surface: emit the call-site obligations for
    /// every DIRECT APPLICATION `f(arg)` of a registered closure literal appearing
    /// inside an `assert!` / `assume!` condition `expr`. Sibling of
    /// [`Self::emit_reflection_ground_facts_in_expr`] (which handles the
    /// `f.requires(..)` / `f.ensures(..)` reflection surface): a call in a macro's
    /// tokens is never reached by the straight-line `visit_expr_call` walk, so the
    /// prove-requires obligation and assume-ensures must be emitted here. Called
    /// BEFORE the enclosing assert/assume obligation is pushed, so the
    /// assume-ensures forward-dominates it (the assert then reads the identical
    /// `spec_fn_apply` term the assume pins). The shared core inherits the
    /// loop-body / unguardable-match-arm / short-circuit DROP discipline, so an
    /// in-loop assert's assume-ensures is still dropped.
    fn emit_closure_application_obligations_in_expr(&mut self, expr: &Expr) {
        if self.parse_error.is_some()
            || (self.closure_reflection_contracts.is_empty()
                && self.fn_bound_spec_fn_params.is_empty())
        {
            return;
        }
        let calls = {
            let mut collector = ClosureApplicationUseCollector {
                contracts: &self.closure_reflection_contracts,
                // INCREMENT 2a: also collect direct applications of an Fn-bound
                // `SpecFn` parameter embedded in an assert/assume, so its
                // conditional assume forward-dominates the enclosing obligation
                // exactly as the closure-literal path does.
                fn_bound_params: &self.fn_bound_spec_fn_params,
                uses: Vec::new(),
            };
            syn::visit::Visit::visit_expr(&mut collector, expr);
            collector.uses
        };
        for call in calls {
            // Each emitter is a no-op for a callee it does not own (literal vs.
            // Fn-bound parameter), so routing to both is safe and keeps a single
            // collection pass.
            self.emit_closure_application_call_obligations(&call);
            self.emit_fn_bound_param_application_obligations(&call);
        }
    }

    fn helper_call_returns_erased_shared_ref(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Call(call) => {
                let Some(helper_contracts) = self.helper_contracts else {
                    return false;
                };
                let Some(helper_name) = super::call_function_symbol(call) else {
                    return false;
                };
                let Some(contract) = helper_contracts.get(&helper_name) else {
                    return false;
                };
                call.args.len() == contract.params.len()
                    && helper_return_aliases_erased_shared_ref_param(contract)
            }
            Expr::Paren(paren) => self.helper_call_returns_erased_shared_ref(&paren.expr),
            Expr::Group(group) => self.helper_call_returns_erased_shared_ref(&group.expr),
            _ => false,
        }
    }

    fn add_helper_contract_obligations(
        &mut self,
        helper_name: &str,
        contract: &HelperCallContract,
        call_args: &[String],
        pre_havoc_args: Option<&[String]>,
        call_expr: &str,
        ensures_binding_sound: bool,
    ) -> TrustVcResult<()> {
        let call_index = self.next_helper_call_contract_index;
        self.next_helper_call_contract_index += 1;

        // SOUNDNESS-CRITICAL (call-site `requires` backward-leak, round-8
        // findings 11/12): reserve ONE straight-line program point for this call
        // site, SHARED by the call-site `requires` obligation (checked AT the
        // call point) and the call's `ensures` assumption (established AT the
        // call point). Stamping both with the same `pp{N}` makes
        // `forward_visible_assumptions` (a) hide a strictly-LATER body `assume!`
        // / call-`ensures` from this `requires` obligation — closing the
        // backward-leak where a later fact discharged an earlier precondition
        // (`need(x); assume!(x == 7)` / `need(x); mk(x)` with `mk` ensuring
        // `x == 7`) — while still (b) keeping the call's OWN `ensures` invisible
        // to its own `requires` (a same-point assume is dropped) and to any
        // EARLIER body assert. An EARLIER `assume!`/call-`ensures` (point `< N`)
        // is retained, so a precondition legitimately established before the call
        // still discharges (NO over-rejection). The slot is consumed from the
        // shared `next_assertion_index` counter so the call orders exactly like a
        // body `assume!`/`assert!` placed at the call site. Reserved once per
        // call site (the caller only reaches here with at least one
        // requires/ensures clause).
        //
        // INCREMENT 2b (pass-site linkage) ORDERING: the reservation itself is
        // deferred to just BEFORE the prove-`requires` loop below, so the pass-site
        // linkage ground facts (emitted from the substitution maps, which are built
        // next) take strictly-EARLIER program points and FORWARD-DOMINATE this
        // call's prove-`requires` obligation. `forward_visible_assumptions` hides a
        // same-or-later assume from an assert, so a linkage fact stamped at this
        // shared point (or after) would be invisible to the very obligation it must
        // discharge. When no linkage fact is emitted (the common path), the reserved
        // value is byte-identical to reserving here.

        let mut substitutions = BTreeMap::new();
        let mut erased_shared_ref_params = BTreeSet::new();
        // `&mut` SCALAR params (slice D): their argument renderings are referent
        // VALUES, so a contract `*P` erases the deref and substitutes the value
        // directly, and `old(P)` forms bind the PRE-call value map below.
        let mut erased_mut_ref_value_params = BTreeSet::new();
        let mut_scalar_flags: &[bool] =
            if contract.mut_ref_scalar_params.len() == contract.params.len() {
                &contract.mut_ref_scalar_params
            } else {
                &[]
            };
        for (index, ((param, arg), erased_shared_ref)) in contract
            .params
            .iter()
            .zip(call_args)
            .zip(contract.erased_shared_ref_params.iter().copied())
            .enumerate()
        {
            let mut arg_expr = parse_helper_contract_expr(arg, helper_name, "call argument")?;
            if erased_shared_ref {
                arg_expr = erase_shared_reference_argument(arg_expr);
                erased_shared_ref_params.insert(param.clone());
            }
            if mut_scalar_flags.get(index).copied().unwrap_or(false) {
                erased_mut_ref_value_params.insert(param.clone());
            }
            substitutions.insert(param.clone(), arg_expr);
        }
        substitutions.insert(
            contract.return_binding.clone(),
            parse_helper_contract_expr(call_expr, helper_name, "call result")?,
        );

        // The `old(P)` two-state map: ALWAYS the PRE-call renderings of the
        // `&mut`-scalar params (`old(P)` in a callee contract denotes the value
        // AT CALL TIME from the caller's perspective — in `requires` it
        // coincides with bare `P`; in `ensures` it is the pre-state side of the
        // relation, while bare `P` reads the post-havoc fresh symbol).
        let old_source: &[String] = pre_havoc_args.unwrap_or(call_args);
        let mut old_substitutions = BTreeMap::new();
        for (index, (param, arg)) in contract.params.iter().zip(old_source).enumerate() {
            if !mut_scalar_flags.get(index).copied().unwrap_or(false) {
                continue;
            }
            old_substitutions.insert(
                param.clone(),
                parse_helper_contract_expr(arg, helper_name, "call argument")?,
            );
        }

        // The call-site `requires` is checked against the PRE-call state: when
        // this call havocs a `&mut`-passed root, substitute the pre-havoc
        // argument renderings (snapshotted in `visit_expr_call`) instead of the
        // post-havoc ones. Post-havoc substitution rendered a satisfied
        // precondition over the fresh unconstrained `_havoc_` symbol —
        // unprovable, so a correct caller was wrongly counterexampled (refs
        // `test_mut_ref_forward`). The `ensures` assumption below keeps the
        // post-havoc `substitutions` map: it constrains the fresh post-call
        // value, which is exactly d568e2e's re-threading intent.
        let requires_substitutions = match pre_havoc_args {
            Some(pre_args) => {
                let mut pre_substitutions = BTreeMap::new();
                for ((param, arg), erased_shared_ref) in contract
                    .params
                    .iter()
                    .zip(pre_args)
                    .zip(contract.erased_shared_ref_params.iter().copied())
                {
                    let mut arg_expr =
                        parse_helper_contract_expr(arg, helper_name, "call argument")?;
                    if erased_shared_ref {
                        arg_expr = erase_shared_reference_argument(arg_expr);
                    }
                    pre_substitutions.insert(param.clone(), arg_expr);
                }
                pre_substitutions.insert(
                    contract.return_binding.clone(),
                    parse_helper_contract_expr(call_expr, helper_name, "call result")?,
                );
                pre_substitutions
            }
            None => substitutions.clone(),
        };

        let requires = contract
            .requires
            .iter()
            .map(|clause| {
                // In `requires`, `old(P)` denotes the value AT CALL TIME — the
                // same PRE-call map bare `P` substitutes from.
                substitute_helper_contract_clause(
                    clause,
                    &requires_substitutions,
                    &erased_shared_ref_params,
                    &old_substitutions,
                    &erased_mut_ref_value_params,
                )
            })
            .collect::<TrustVcResult<Vec<_>>>()?;

        // INCREMENT 2b (Fn-bound closure dispatch, cross-boundary PASS-SITE
        // linkage): when a call argument is a bare-ident `closure!` literal
        // registered in `closure_reflection_contracts` and the callee reflects
        // it via `.requires`/`.ensures` (e.g. `g(c, 5)` with `g`'s contract
        // `requires f.requires((a,)); ensures f.ensures((a,), result)`), the
        // callee's `f.requires((a,))` / `f.ensures((a,), result)` clauses
        // substitute to `c.requires((5,))` / `c.ensures((5,), g(c, 5))`, which
        // lower to the OPAQUE reflection UFs `call_requires%` / `call_ensures%`.
        // Emit the DEFINITIONAL ground facts tying those UF applications to `c`'s
        // OWN concrete, arg-substituted requires/ensures, so the caller can
        // discharge `g`'s prove-`requires` and USE `g`'s assumed `ensures`. These
        // are emitted BEFORE reserving the shared call-site program point below,
        // so they forward-dominate the prove-`requires` obligation. Emits ONLY for
        // a registered closure literal (a re-passed Fn-bound param is not in the
        // map ⇒ no fact ⇒ fails closed); the fact is CONSERVATIVE (it fixes the
        // opaque UF's value, never a raw hypothesis) and the closure's def-side
        // was independently checked at its `let c = …`.
        self.emit_closure_pass_site_linkage_facts(
            contract,
            &substitutions,
            &requires_substitutions,
            &erased_shared_ref_params,
            &old_substitutions,
            &erased_mut_ref_value_params,
        );

        // Reserve the shared call-site program point now (see the deferral note at
        // the top of this function): any pass-site linkage facts above have already
        // taken strictly-earlier points, so this point still orders the call's
        // prove-`requires` obligation and assume-`ensures` exactly at the call site.
        let call_site_program_point = self.next_assertion_index;
        self.next_assertion_index += 1;

        for (index, (clause, condition)) in contract.requires.iter().zip(&requires).enumerate() {
            let name = format!(
                "__call_requires_pp{call_site_program_point}_{helper_name}_{call_index}_{index}"
            );
            // SOUNDNESS / no-over-rejection: branch-guard the call-site
            // precondition with the enclosing path conditions, exactly as
            // `add_assertion` does. A call under guard `G` must establish its
            // precondition `R` only when the branch is taken, lowered to
            // `G ==> R` (rendered `!(G) || (R)`). Without this a branch-local
            // call whose `R` is implied by `G` (e.g. `if c > 100 { need(c) }`
            // with `need` requiring `c > 10`) was wrongly counterexampled, and a
            // statically-dead `if false { need(..) }` wrongly checked.
            let guarded_requires = self.guard_with_path_conditions(condition);
            let obligation = ProofObligation::assert(name, guarded_requires)
                // Thread the callee clause's proof-note label onto the
                // caller-side discharge obligation (Verus: a precondition
                // failure carries the callee clause's span label).
                .with_proof_note(clause.proof_note.clone());
            self.vc
                .push_obligation(self.with_contract_solver_mode(obligation, clause));
        }

        let guard = if requires.is_empty() {
            None
        } else {
            Some(
                requires
                    .iter()
                    .map(|condition| format!("({condition})"))
                    .collect::<Vec<_>>()
                    .join(" && "),
            )
        };
        // SOUNDNESS-CRITICAL (loop-body call-ensures leak): a call inside ANY loop
        // body (`while` / `for` / bare `loop` / `while let`) must NOT contribute
        // its `ensures` as an assumption to the surrounding straight-line context.
        // The body may execute zero times, so the call may never run; trust-vc's
        // loop encoding does not route a body assumption through the loop's
        // zero-trip / havoc model, so a body call-ensures assume would survive as a
        // flat, unconditional hypothesis PAST the (possibly skipped) loop — a
        // catastrophic false `Verified` (e.g. a post-loop `assert!(a == 7)` proven
        // by a loop-body `mk(a)` whose `ensures(x == 7)` never ran). Fail closed by
        // DROPPING ONLY the `ensures` ASSUMPTION here, exactly mirroring the
        // arithmetic-safety loop-body deferral (`maybe_emit_exec_arith_overflow_check`)
        // and the `.set` index-model deferral (`assign_local_set_method_call`).
        //
        // What is deliberately NOT changed: the call-site `requires` obligations
        // emitted ABOVE are an obligation we PROVE (not an assumption) and stay
        // intact, so a loop-body call with an unmet precondition is STILL a
        // counterexample; in-loop `assert!`/`assume!` are untouched (NOT made
        // vacuous — no guard is threaded onto `path_conditions`). The accepted,
        // sound incompleteness: code that RELIES on a loop-body call's `ensures`
        // (within or after the loop) will not discharge. `loop_body_depth` covers
        // every loop form uniformly; `loop_contexts` is OR'd for the boolean-guard
        // `while` form for defense in depth.
        if !self.loop_contexts.is_empty() || self.loop_body_depth > 0 {
            return Ok(());
        }
        // SOUNDNESS-CRITICAL (match-arm call-ensures leak): drop the call's
        // `ensures` ASSUMPTION when the enclosing `match` arm's selection path
        // condition could not be soundly rendered (mirrors the body `assume!`
        // drop). The call-site `requires` obligations emitted above are PROVEN, not
        // assumed, so they remain intact (a branch-local call with an unmet
        // precondition is still a counterexample). Sibling of the loop-body drop.
        if self.match_arm_unguardable_depth > 0 {
            return Ok(());
        }
        // SOUNDNESS-CRITICAL (short-circuit condition-position call-ensures
        // leak, slice-D remediation p8/p8b): a call in the RHS of `&&` / `||`
        // is CONDITIONALLY EVALUATED, and that conditionality is not on the
        // path-condition stack — `if c && add1b(&mut v) {}` guarded the
        // ensures with NOTHING, so the state-transition postcondition (over
        // the havoc'd fresh symbol) was assumed even on the real `c == false`
        // execution where the call never ran (`assert!(v == 6)` false
        // `Verified`). Drop ONLY the `ensures` ASSUMPTION: the `requires`
        // obligations above are PROVEN (over-rejection is fail-closed) and the
        // `&mut`-arg havoc in `visit_expr_call` stays (over-havoc is sound).
        // Sibling of the loop-body / unguardable-match-arm drops above.
        if self.short_circuit_rhs_depth > 0 {
            return Ok(());
        }
        // SOUNDNESS-CRITICAL (slice D): recorded through an expression rendering
        // BEFORE the `&mut`-arg havoc ran — `substitutions` is a PRE-havoc
        // rendering, so assuming the `ensures` over it would pin the callee's
        // postcondition onto the PRE-call value. Drop the assumption
        // (havoc-only, fail-closed-incomplete); the `requires` obligations
        // above are correct (they need exactly the pre-call renderings).
        if !ensures_binding_sound {
            return Ok(());
        }
        // SOUNDNESS-CRITICAL (forward-only ordering, mirrors the #67 body
        // `assume!` fix): stamp every ensures assume with the SAME call-site
        // program point reserved above (shared with the `requires` obligation),
        // through the `__call_ensures_pp{N}_…` name. `body_program_point` parses
        // that `N`, so `forward_visible_assumptions` hides the call's `ensures`
        // from any body `assert!` (and from this call's OWN `requires`) at an
        // earlier-or-equal point — an `assert!(P)` textually BEFORE the call is
        // NOT retroactively satisfied by the call's `ensures`.
        let ensures_program_point = call_site_program_point;
        for (index, clause) in contract.ensures.iter().enumerate() {
            // THE DIRECTIONALITY SPLIT (slice D): bare `P` substitutes the
            // POST-havoc map (`substitutions` — the fresh post-call symbol for
            // a `&mut`-scalar arg); `old(P)` forms substitute the PRE-call map
            // (`old_substitutions`), in one simultaneous, never-recursing pass.
            let ensures = substitute_helper_contract_clause(
                clause,
                &substitutions,
                &erased_shared_ref_params,
                &old_substitutions,
                &erased_mut_ref_value_params,
            )?;
            let condition = match &guard {
                Some(guard) => format!("!({guard}) || ({ensures})"),
                None => ensures,
            };
            // SOUNDNESS-CRITICAL: branch-guard the call's ensures with the
            // enclosing path conditions before assuming it. A conditionally
            // executed call's postcondition holds only when the branch is taken;
            // lowering it to `G ==> (R ==> E)` (rendered `!(G) || (…)`) prevents
            // a branch-local call's `ensures` from leaking past the branch (into
            // sibling `else`, post-branch code, a dead `if false`, or the
            // function postcondition). Sibling of the #67 `assume!` leak.
            let guarded = self.guard_with_path_conditions(&condition);
            let name = format!(
                "__call_ensures_pp{ensures_program_point}_{helper_name}_{call_index}_{index}"
            );
            let obligation = ProofObligation::assume(name, guarded);
            self.vc
                .push_obligation(self.with_contract_solver_mode(obligation, clause));
        }

        Ok(())
    }

    /// Records caller-side `requires` obligations for a generic trait-bounded
    /// method call `z.f(args)` where `z: TypeParam(P)` and `P: T`.
    ///
    /// Every out-of-scope shape falls through with NO obligation
    /// (fail-closed/unchanged): a non-bare-ident receiver, a receiver whose
    /// resolved type is not a `TypeParam`, an absent `(type_param, method)` map
    /// entry, a concrete receiver, etc.
    ///
    /// CAREFUL — "a missed obligation is conservative" is TRUE FOR AN ASSUMPTION
    /// AND FALSE FOR A `requires`, and this map is the only producer of
    /// call-site precondition asserts. Dropping one does not weaken what the
    /// caller may conclude — the trait postcondition axiom is itself
    /// `requires ==> ensures`, so an unestablished precondition yields no
    /// `ensures` either — but it does mean a precondition-VIOLATING call is
    /// never flagged. That is a missed bug report, not a false proof; the two
    /// are not interchangeable and the older phrasing of this comment invited
    /// treating them as such.
    ///
    /// An unresolvable receiver — `self.inner.f(x)`, `v[0].f(x)`, `make().f(x)`,
    /// or a bare ident whose type never resolved — therefore FAILS CLOSED rather
    /// than falling through, but only when a same-named method with a non-empty
    /// `requires` is actually in scope. Without that guard the rejection would
    /// fire on every unresolvable receiver in the language; with it, a program is
    /// only rejected when there is a real precondition that could have been
    /// missed. See `tests/receiver_shape_precondition_drop_witness.rs`.
    ///
    /// Still open, same shape: the sibling ambiguity drop in `trait_contracts.rs`
    /// removes the key for BOTH traits when two declare a same-named
    /// requires-bearing method for one concrete type, and wants the disjunction
    /// of candidate `requires`.
    fn record_trait_method_contract_call(&mut self, mc: &syn::ExprMethodCall) {
        if self.parse_error.is_some() {
            return;
        }
        // Nothing to do unless at least one of the generic (unit 1) or concrete
        // (unit 2) trait-method maps is present.
        if self.trait_method_contracts.is_none() && self.concrete_method_contracts.is_none() {
            return;
        }
        let key = mc as *const syn::ExprMethodCall as usize;
        if !self.recorded_trait_method_contract_call_sites.insert(key) {
            return;
        }
        // A separate dedup set for the concrete-map path keeps unit-2 emission
        // independent of unit-1; both maps share the bare-ident/known-type
        // guards below but key into different contract tables.
        self.recorded_concrete_method_contract_call_sites
            .insert(key);

        let method = mc.method.to_string();

        // Receiver must be a bare identifier with a known type. Anything else —
        // `o.inner.f(x)`, `v[0].f(x)`, `make().f(x)`, or a bare ident whose type
        // never resolved — cannot be routed to a contract.
        //
        // SOUNDNESS: this arm used to `return` silently, which let a call that
        // VIOLATES the callee's `requires` pass unflagged purely because of the
        // receiver's syntactic shape (see
        // `tests/receiver_shape_precondition_drop_witness.rs`). Silence is only
        // safe when no requires-bearing method of this name is in scope; when one
        // IS, the call must fail closed instead. That keeps the over-rejection as
        // narrow as the evidence allows: a same-named contract with a non-empty
        // `requires` has to exist before anything is rejected.
        if let Some((receiver_name, receiver_ty)) = expr_path_ident(&mc.receiver).and_then(|name| {
            self.vc
                .get_variable_type(&name)
                .cloned()
                .map(|ty| (name, ty))
        }) {
            return self.dispatch_resolved_trait_method_call(mc, receiver_name, receiver_ty);
        }

        if self.method_name_has_requires_bearing_contract(&method) {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract trait-bounded method call contracts",
                detail: format!(
                    "Cannot resolve the receiver of the call to `{method}`, and a trait method \
                     named `{method}` declares a `requires` clause. Refusing to verify rather \
                     than skip the call-site precondition check: bind the receiver to a local \
                     first (`let r = <receiver>; r.{method}(..)`) so its type resolves."
                ),
            });
        }
    }

    /// True when either contract map holds an entry for `method` whose `requires`
    /// list is non-empty — i.e. dropping this call site could hide a real
    /// precondition violation. A contract with no `requires` produces no call-site
    /// obligation anyway, so dropping it is genuinely harmless and must NOT
    /// trigger the fail-closed path.
    fn method_name_has_requires_bearing_contract(&self, method: &str) -> bool {
        let has = |map: Option<&BTreeMap<(String, String), TraitMethodCallContract>>| {
            map.is_some_and(|m| {
                m.iter()
                    .any(|((_, name), contract)| name == method && !contract.requires.is_empty())
            })
        };
        has(self.trait_method_contracts) || has(self.concrete_method_contracts)
    }

    /// The resolved-receiver path, split out of `record_trait_method_contract_call`
    /// so the unresolved path above reads as the single fail-closed decision.
    fn dispatch_resolved_trait_method_call(
        &mut self,
        mc: &syn::ExprMethodCall,
        receiver_name: String,
        receiver_ty: TrustVcType,
    ) {
        let method = mc.method.to_string();

        // Resolve the applicable contract: a `TypeParam` receiver routes to the
        // generic map (unit 1) keyed by the type-param name; any other receiver
        // type routes to the concrete map (unit 2) keyed by its
        // `to_type_string()`. Either path may have no entry (fail-closed).
        let contract = match &receiver_ty {
            TrustVcType::TypeParam(type_param) => self
                .trait_method_contracts
                .and_then(|map| map.get(&(type_param.clone(), method.clone())))
                .cloned(),
            other => self
                .concrete_method_contracts
                .and_then(|map| map.get(&(other.to_type_string(), method.clone())))
                .cloned(),
        };
        let Some(contract) = contract else {
            return;
        };

        if let Err(err) = self.discharge_trait_method_requires(mc, &receiver_name, &contract) {
            self.parse_error = Some(err);
        }
    }

    /// Arity-checks the call against the resolved contract and, on success,
    /// emits the `requires` obligations. Shared by the generic (unit 1) and
    /// concrete (unit 2) dispatch arms of `record_trait_method_contract_call`.
    fn discharge_trait_method_requires(
        &mut self,
        mc: &syn::ExprMethodCall,
        receiver_name: &str,
        contract: &TraitMethodCallContract,
    ) -> TrustVcResult<()> {
        // Arity check mirrors the path-form helper-call site: the number of
        // call arguments must match the trait method's declared (non-`self`)
        // parameters, else fail closed with an encoding error.
        if mc.args.len() != contract.param_names.len() {
            return Err(TrustVcError::Encoding {
                context: "extract trait-bounded method call contracts",
                detail: format!(
                    "Call to trait method `{}` has {} argument(s), but its declaration has {} parameter(s)",
                    contract.uf_prefix,
                    mc.args.len(),
                    contract.param_names.len()
                ),
            });
        }

        let receiver_string = self.lookup_scoped(receiver_name);
        let arg_strings = self
            .with_temporary_scopes(|collector| collector.scoped_call_args_left_to_right(&mc.args));

        self.add_trait_method_requires_obligations(contract, &receiver_string, &arg_strings)
    }

    /// Emits one `__call_requires_{uf_prefix}_{call_index}_{i}` ground
    /// `assert` per `requires` clause, with `self := receiver` and
    /// `param_i := arg_i`. Requires-only: the matching `ensures` is supplied
    /// globally by the trait postcondition axiom, so NO `__call_ensures_*` is
    /// emitted here.
    ///
    /// Reuses `parse_helper_contract_expr` + `substitute_helper_contract_clause`
    /// verbatim — the same audited substitution path the green path-form
    /// helper-call site uses.
    fn add_trait_method_requires_obligations(
        &mut self,
        contract: &TraitMethodCallContract,
        receiver_string: &str,
        arg_strings: &[String],
    ) -> TrustVcResult<()> {
        let call_index = self.next_helper_call_contract_index;
        self.next_helper_call_contract_index += 1;

        // SOUNDNESS-CRITICAL (call-site `requires` backward-leak, round-8
        // findings 11/12, trait-method sibling): reserve a straight-line program
        // point for this call site and stamp the requires obligation with it, so
        // `forward_visible_assumptions` hides a strictly-LATER body `assume!`
        // from the precondition check. The trait method's `ensures` is supplied
        // by a GLOBAL postcondition axiom (no program point), so stamping the
        // requires here only drops later body `assume!`s — an earlier fact still
        // discharges (NO over-rejection).
        let call_site_program_point = self.next_assertion_index;
        self.next_assertion_index += 1;

        let mut substitutions = BTreeMap::new();
        substitutions.insert(
            contract.receiver_binding.clone(),
            parse_helper_contract_expr(receiver_string, &contract.uf_prefix, "call receiver")?,
        );
        for (param, arg) in contract.param_names.iter().zip(arg_strings) {
            substitutions.insert(
                param.clone(),
                parse_helper_contract_expr(arg, &contract.uf_prefix, "call argument")?,
            );
        }

        // No erased shared-ref params, no two-state `&mut`-scalar params for
        // trait-bounded calls in unit 1 (slice-D old()/value-erasure is
        // free-fn-only; an old() form here stays verbatim → encoder-fail-closed).
        let erased_shared_ref_params = BTreeSet::new();
        let old_substitutions = BTreeMap::new();
        let erased_mut_ref_value_params = BTreeSet::new();
        for (index, req_str) in contract.requires.iter().enumerate() {
            let condition = syn::parse_str::<Expr>(req_str).map_err(|err| TrustVcError::Encoding {
                context: "extract trait-bounded method call contracts",
                detail: format!(
                    "Failed to parse `requires` clause for trait method `{}`: {err}; clause: {req_str}",
                    contract.uf_prefix
                ),
            })?;
            let clause = HelperContractClause {
                condition,
                solver_mode: None,
                proof_note: None,
            };
            let condition = substitute_helper_contract_clause(
                &clause,
                &substitutions,
                &erased_shared_ref_params,
                &old_substitutions,
                &erased_mut_ref_value_params,
            )?;
            let name = format!(
                "__call_requires_pp{call_site_program_point}_{}_{call_index}_{index}",
                contract.uf_prefix
            );
            let obligation = ProofObligation::assert(name, condition);
            self.vc
                .push_obligation(self.with_contract_solver_mode(obligation, &clause));
        }

        Ok(())
    }

    /// Records caller-side `requires` obligations for a QUALIFIED-UFCS
    /// trait-function call `<S as T>::f(s, args)` (unit 4).
    ///
    /// `<S as T>::f(...)` is an `Expr::Call` whose `func` is an `Expr::Path`
    /// with `qself.is_some()`. The concrete receiver type `S` is named
    /// EXPLICITLY by `qself.ty` (no `get_variable_type`, no generic
    /// substitution); the method is the path's last segment. The applicable
    /// contract is the SAME `(type_name, method)` entry the concrete-receiver
    /// (unit 2) form keys into, so this reuses `concrete_method_contracts`
    /// verbatim. The explicit receiver/self argument is `args[0]` and the
    /// declared (non-`self`) parameters are positionally `args[1..]`, so the
    /// arity check is `call.args.len() == param_names.len() + 1`.
    ///
    /// Fall-through with NO obligation (fail-closed/unchanged): a non-qualified
    /// path (`qself.is_none()` — handled by the existing helper path), an
    /// absent concrete map, a `(type_name, method)` with no entry (e.g. a
    /// generic `<P as T>::f` whose `qself.ty` is a type-param → intentionally
    /// fail-closed), a missing last segment, or a previously-recorded site.
    /// Arity mismatch is the one hard `Encoding` error.
    fn record_qualified_trait_fn_contract_call(&mut self, call: &syn::ExprCall) {
        if self.parse_error.is_some() {
            return;
        }
        // Nothing to do unless the concrete (unit 2) map is present — it carries
        // the `(type_name, method)` entries this form keys into.
        let Some(concrete_method_contracts) = self.concrete_method_contracts else {
            return;
        };
        // Only qualified-UFCS calls `<S as T>::f(...)` apply: the `func` must be
        // a path with a `qself`. Everything else falls through unchanged.
        let Expr::Path(func_path) = &*call.func else {
            return;
        };
        let Some(qself) = func_path.qself.as_ref() else {
            return;
        };
        let key = call as *const syn::ExprCall as usize;
        if !self.recorded_qualified_trait_fn_call_sites.insert(key) {
            return;
        }

        // The concrete type `S` is named explicitly by `qself.ty`; key the
        // concrete map by its `to_type_string()` (the same normalization the
        // concrete builder uses, so they match; a mismatch fails closed).
        let type_name =
            TrustVcType::parse_or_opaque(&crate::local_vars::extract_type_string(&qself.ty))
                .to_type_string();
        // The method is the qualified path's last segment.
        let Some(method) = super::path_last_segment(&func_path.path) else {
            return;
        };
        let Some(contract) = concrete_method_contracts.get(&(type_name, method)).cloned() else {
            return;
        };

        // The explicit receiver/self argument is `args[0]`; the declared
        // (non-`self`) parameters are positionally `args[1..]`.
        if call.args.len() != contract.param_names.len() + 1 {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract qualified-UFCS trait-function call contracts",
                detail: format!(
                    "Qualified-UFCS call to trait method `{}` has {} argument(s), but its declaration has {} parameter(s) plus the explicit receiver",
                    contract.uf_prefix,
                    call.args.len(),
                    contract.param_names.len()
                ),
            });
            return;
        }

        // Render every argument left-to-right via the scoped-arg path; this also
        // resolves the `&s` receiver — an `Expr::Reference` with no `mut` lowers
        // to its scoped referent (`s`), so the substituted `self.req()` becomes
        // the receiver's `req()` with no bare `self` and no stray `&`.
        let mut arg_strings = self.with_temporary_scopes(|collector| {
            collector.scoped_call_args_left_to_right(&call.args)
        });
        // `args[0]` is the explicit receiver/self; the remainder map positionally
        // onto the declared parameters.
        let receiver_string = arg_strings.remove(0);

        if let Err(err) =
            self.add_trait_method_requires_obligations(&contract, &receiver_string, &arg_strings)
        {
            self.parse_error = Some(err);
        }
    }

    fn with_contract_solver_mode(
        &self,
        obligation: ProofObligation,
        clause: &HelperContractClause,
    ) -> ProofObligation {
        match clause.solver_mode.or(self.ambient_solver_mode) {
            Some(mode) => obligation.with_solver_mode(mode),
            None => obligation,
        }
    }

    fn format_method_call_expr(&mut self, method_call: &syn::ExprMethodCall) -> String {
        // CONCRETE GROUND FILTER: `seq![intlit, ..].filter(SpecFn::new(|x| PRED))`
        // where every element is an integer literal and PRED folds to a definite
        // bool per element — render the concrete kept `seq![..]` so downstream
        // `.contains`/`.len`/index hit the WORKING fixed-array path
        // (encode_fixed_array_contains) instead of the Skolemized filter-result
        // quantifier, which non-terminates on positive membership
        // (reference-seq-filter-membership-quantifier-incomplete). Sound by
        // construction: a literal-vs-literal comparison folds EXACTLY to the spec
        // (mathematical) truth, and ANYTHING not exactly foldable — a non-ground
        // receiver, a non-literal element, arithmetic, or an unhandled predicate
        // shape — declines to `None` and falls through to the opaque filter
        // (→ NotProved, fail-closed). Never guesses.
        if method_call.method == "filter" && method_call.args.len() == 1 {
            if let Some(result) = try_concrete_ground_filter(method_call) {
                return result;
            }
        }
        let receiver = self.expr_to_scoped_string(&method_call.receiver);
        self.invalidate_expr_side_effects(&method_call.receiver);
        let method = method_call.method.to_string();
        // `v.as_slice()` on a Vec/array-modeled receiver is an IMMUTABLE VIEW with
        // the SAME elements — it shares the receiver's `Seq` model, so render it as
        // the receiver itself (identity). Without this it lowers to an `as_slice`
        // call on a `Seq`, which the encoder rejects ("unsupported method
        // `as_slice()` on type `Seq<..>`"). Sound: every read through the slice
        // (`len`/index/`contains`) equals the same read on the receiver. Guarded on
        // a collection-model receiver so a user `as_slice` on an unrelated type is
        // not mis-modeled. (`as_mut_slice` is deliberately NOT identity-folded here
        // — a write through it mutates the receiver and must reach the deref-write
        // path.)
        if method == "as_slice"
            && method_call.args.is_empty()
            && (is_scoped_vec_receiver_model(&receiver)
                || expr_path_ident(&method_call.receiver)
                    .is_some_and(|name| self.receiver_is_collection_like(&name)))
        {
            return format!("({receiver})");
        }
        let turbofish = method_call
            .turbofish
            .as_ref()
            .map(|args| args.to_token_stream().to_string())
            .unwrap_or_default();
        let args = method_call
            .args
            .iter()
            .map(|arg| {
                let rendered = self.expr_to_scoped_string(arg);
                self.invalidate_expr_side_effects(arg);
                rendered
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("({receiver}).{method}{turbofish}({args})")
    }

    fn assign_local_push_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "push" || method_call.args.len() != 1 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        let receiver = self.lookup_scoped(&name);
        let Some(arg) = method_call.args.first() else {
            return false;
        };
        let value = self.expr_to_scoped_string(arg);
        self.invalidate_expr_side_effects(arg);
        self.assign_scoped(&name, format!("({receiver}).push({value})"));
        true
    }

    /// Lowers a discarded `recv.set(idx, val)` statement on a mutable
    /// slice/`Vec`/array place to the same scoped re-binding that
    /// `recv[idx] = val` already uses: `recv = recv.update(idx, val)`.
    ///
    /// This is the faithful surface used by upstream Verus `slices.rs`
    /// `test_set`/`test_set3` (vstd `<[T]>::set`). The bounds obligation
    /// `idx < recv.len()` is emitted downstream by `native_seq_update`
    /// (via `native_seq_bounds_check`), matching vstd `set`'s
    /// `requires idx < self@.len()`, so this is at least as conservative
    /// as Verus.
    ///
    /// Returns `true` only when the receiver is a directly-bound local or
    /// parameter place whose modeled state is sequence-like (a `Seq`/slice,
    /// `Vec`, or fixed-size array). Any other `.set(_, _)` receiver returns
    /// `false` and falls through to the existing receiver-invalidation path,
    /// so a user-defined `set` method on an unrelated type is never
    /// mis-modeled as a sequence update (fail-closed: later reads of an
    /// invalidated receiver become non-provable rather than wrongly proven).
    fn assign_local_set_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "set" || method_call.args.len() != 2 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        // Inside a loop body, the index-assignment model is re-bound but the
        // bounds obligation it carries would be solved in the function-entry
        // context (trust-vc does not yet route the loop guard/invariant into
        // body-site obligations), yielding a spurious counterexample. Decline
        // to lower `.set` here so the receiver is conservatively forgotten by
        // the existing invalidation path (fail-closed), exactly as
        // `maybe_emit_exec_arith_overflow_check` defers loop-body arithmetic.
        if !self.loop_contexts.is_empty() {
            return false;
        }
        // Borrowed/aliased and otherwise-unmodelable index receivers are
        // exactly those the simple `recv[idx] = val` path refuses; mirror that
        // refusal here so aliased state is never treated as an independent
        // array. Erased mutable-reference aliases are handled below.
        if self.is_erased_shared_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        if !self.set_receiver_models_sequence_place(&name) {
            return false;
        }

        let Some(index_expr) = method_call.args.first() else {
            return false;
        };
        let Some(value_expr) = method_call.args.get(1) else {
            return false;
        };

        let index = self.expr_to_scoped_string(index_expr);
        let value = self.expr_to_scoped_string(value_expr);

        // An erased mutable-reference alias re-binds the underlying root and all
        // of its aliases through `update()`, identical to `recv[idx] = val`.
        if self.assign_mut_ref_alias_index(&name, &index, &value) {
            self.emit_seq_set_bounds_obligation(&name);
            return true;
        }

        // A side-effecting index expression (e.g. an assignment in the index)
        // makes the post-state model unsound to track precisely; conservatively
        // forget the receiver, exactly as the index-assignment path does.
        if !self.externally_assigned_in_expr(index_expr).is_empty()
            || !self.externally_assigned_in_expr(value_expr).is_empty()
        {
            self.invalidate_scoped(&name);
            return true;
        }

        let receiver = self.lookup_scoped(&name);
        if let (Some(len), Some(index_value)) = (
            scoped_vec_literal_len(&receiver),
            literal_usize_index_expr(index_expr),
        ) {
            if index_value >= len {
                self.parse_error = Some(out_of_bounds_vec_literal_index_assignment_error(
                    &method_call.receiver,
                    index_value,
                    len,
                ));
                return false;
            }
        }
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(&name, format!("{receiver}.update({index}, {value})"));
        self.emit_seq_set_bounds_obligation(&name);
        true
    }

    /// Pin the post-`set` model of `name` into a reflexive `(v) == (v)`
    /// obligation so the `idx < len` bounds precondition that
    /// `native_seq_update` carries fires at the `.set` statement site, even
    /// when `recv` is never read again. vstd `<[T]>::set` carries
    /// `requires idx < self@.len()`, which Verus checks at every call site
    /// regardless of whether the result is used; without this pin a discarded
    /// `recv.set(idx, val)` (upstream `test_set3`) would carry no obligation
    /// and the bounds check would be skipped — less conservative than Verus.
    /// The equality itself is trivially Verified; only the embedded bounds
    /// overflow-check can fail. Gated on `check_overflow()` (exec functions)
    /// to mirror the discarded-result exec arithmetic-safety path.
    fn emit_seq_set_bounds_obligation(&mut self, name: &str) {
        if !self.vc.check_overflow() {
            return;
        }
        let model = self.lookup_scoped(name);
        let condition = format!("({model}) == ({model})");
        let obligation_name = format!("overflow_check_{}", self.next_assertion_index);
        self.next_assertion_index += 1;
        self.vc.push_obligation(
            self.with_ambient_solver_mode(ProofObligation::assert(&obligation_name, &condition)),
        );
    }

    /// True when `name` denotes a directly-bound place whose modeled state is
    /// sequence-like (slice/`Seq`, `Vec`, or fixed-size array), so a
    /// `.set(idx, val)` re-binding through `update()` is sound.
    fn set_receiver_models_sequence_place(&self, name: &str) -> bool {
        // Declared parameter/place type is the most reliable signal and is
        // stable across `update()` re-bindings (the place keeps its type).
        if let Some(ty) = self.vc.get_variable_type(name) {
            if matches!(ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _)) {
                return true;
            }
        }
        // Locals without a registered declared type: accept recognized
        // sequence-shaped scoped models (vec literals, `Vec::*` constructions,
        // array literals, or values already derived through sequence ops).
        if self.has_scoped_name(name) {
            let receiver = self.lookup_scoped(name);
            return scoped_vec_literal_len(&receiver).is_some()
                || is_scoped_vec_receiver_model(&receiver)
                || is_scoped_sequence_shaped_model(&receiver);
        }
        false
    }

    fn assign_local_vec_insert_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "insert" || method_call.args.len() != 2 {
            return false;
        }
        // A ghost-collection `.insert(k, v)` (immutable `Map`) is a functional
        // VALUE, not a `Vec` in-place insert — decline (WITHOUT a parse error) so
        // it renders through the normal ghost path. `Vec::insert` and `Map::insert`
        // share arity 2, so without this a `let m = Map::empty().insert(k, v)` (or
        // `m.insert(k, v)` on a ghost-marked local) would hit the Vec-receiver
        // rejection below and fail closed. Seq's `push` handler already declines
        // for a ghost receiver the same way; this restores the Seq/Set/Map
        // symmetry. A real `Vec` local is never ghost-marked (its `Vec::new` root
        // is not a ghost constructor), so Vec::insert is unaffected.
        if self.expr_models_ghost_collection(&method_call.receiver) {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            self.parse_error = Some(unsupported_vec_insert_receiver_error(&method_call.receiver));
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            self.parse_error = Some(unsupported_vec_insert_receiver_error(&method_call.receiver));
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            self.parse_error = Some(unsupported_vec_insert_receiver_error(&method_call.receiver));
            return false;
        }

        let mut args = method_call.args.iter();
        let Some(index_expr) = args.next() else {
            return false;
        };
        let Some(value_expr) = args.next() else {
            return false;
        };
        if !is_stable_vec_insert_index_expr(index_expr) {
            self.parse_error = Some(unsupported_vec_insert_index_error(index_expr));
            return false;
        }
        if !self.externally_assigned_in_expr(index_expr).is_empty()
            || !self.externally_assigned_in_expr(value_expr).is_empty()
        {
            self.parse_error = Some(unsupported_vec_insert_side_effect_error(method_call));
            return false;
        }

        let index = self.expr_to_scoped_string(index_expr);
        let value = self.expr_to_scoped_string(value_expr);
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(
            &name,
            format!(
                "({receiver}).subrange(0usize, {index}).push({value}).add(({receiver}).subrange({index}, ({receiver}).len()))"
            ),
        );
        true
    }

    fn assign_local_vec_remove_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "remove" || method_call.args.len() != 1 {
            return false;
        }
        // A ghost-collection `.remove(k)` (immutable `Map`/`Set`/`Multiset`) is a
        // functional VALUE, not a `Vec` in-place remove — decline (WITHOUT a parse
        // error) so it renders through the normal ghost path. `Vec::remove(index)`
        // and `Map`/`Set`/`Multiset::remove(elem)` share arity 1, so without this a
        // `Map::empty().insert(..).remove(k)` would hit the Vec-receiver rejection
        // below and fail closed (the same arity-collision the `insert` guard fixes).
        // A real `Vec` local is never ghost-marked, so `Vec::remove` is unaffected.
        if self.expr_models_ghost_collection(&method_call.receiver) {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "remove",
                &method_call.receiver,
            ));
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "remove",
                &method_call.receiver,
            ));
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "remove",
                &method_call.receiver,
            ));
            return false;
        }

        let Some(index_expr) = method_call.args.first() else {
            return false;
        };
        if !is_stable_vec_insert_index_expr(index_expr) {
            self.parse_error = Some(unsupported_vec_insert_index_error(index_expr));
            return false;
        }
        if !self.externally_assigned_in_expr(index_expr).is_empty() {
            self.parse_error = Some(unsupported_vec_mutation_side_effect_error(
                "remove",
                method_call,
            ));
            return false;
        }

        let index = self.expr_to_scoped_string(index_expr);
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(
            &name,
            format!(
                "({receiver}).subrange(0usize, {index}).add(({receiver}).subrange({index} + 1usize, ({receiver}).len()))"
            ),
        );
        true
    }

    /// Lowers a discarded `v.pop()` to the EXACT post-state re-binding, instead of
    /// the conservative receiver havoc the fall-through mutation path uses. `pop`
    /// removes (and returns, discarded here) the LAST element; on an EMPTY receiver
    /// it is a no-op. Model:
    ///     v = (v.len() == 0 ? v : v.subrange(0, v.len() - 1))
    /// The conditional is load-bearing for SOUNDNESS: it avoids evaluating
    /// `v.len() - 1` at length 0 (a usize underflow / negative index), and it makes
    /// the empty case an exact no-op. For a non-empty receiver `subrange(0, len-1)`
    /// is the first `len-1` elements — the receiver minus its last — a total,
    /// side-effect-free function of the pre-state (same discipline as
    /// `remove`/`insert`). Returns `true` only for a bare local/param receiver whose
    /// scoped state is sequence-like; every other `.pop()` receiver returns `false`
    /// and falls through to the existing havoc (fail-closed). The RESULT `Option` is
    /// not modeled — a `let x = v.pop()` that USES `x` stays fail-closed on `x`.
    fn assign_local_vec_pop_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "pop" || !method_call.args.is_empty() {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            return false;
        }
        self.invalidate_mut_ref_aliases_targeting(&name);
        // `v.subrange(0, len - 1)` — the first `len-1` elements, i.e. the receiver
        // minus its last. INT arithmetic (`0int`, `- 1int`), never `usize`: a
        // `len - 1usize` carries a usize underflow check that the overflow pass
        // cannot encode; the ghost `int` `len - 1` is exact and check-free.
        //
        // The EMPTY case is handled by `subrange`'s own `start <= end` precondition,
        // NOT a conditional: at `len == 0` this is `subrange(0, -1)` whose
        // `0 <= -1` obligation is FALSE, so any later use of the receiver is
        // NotProved (fail-closed) — sound. A plain (non-conditional) `subrange`
        // also avoids the encoder's `if`-in-overflow-check limitation. A caller
        // that has established `v.len() > 0` (the usual `while !v.is_empty()` /
        // length-precondition shape) discharges the precondition and gets the exact
        // post-pop model.
        self.assign_scoped(
            &name,
            format!("({receiver}).subrange(0int, ({receiver}).len() - 1int)"),
        );
        true
    }

    /// Lowers a `v.clear()` to the exact post-state re-binding `v = v.subrange(0, 0)`
    /// (the empty prefix), instead of the conservative havoc. `subrange(0, 0)` is
    /// total — its `0 <= 0` and `0 <= len` obligations always hold — so this is
    /// exact AND complete (no over-rejection): a later `v.len()` is provably `0`.
    /// Returns `true` only for a bare local/param receiver whose scoped state is
    /// sequence-like; every other `.clear()` receiver keeps the existing havoc.
    fn assign_local_vec_clear_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "clear" || !method_call.args.is_empty() {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            return false;
        }
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(&name, format!("({receiver}).subrange(0usize, 0usize)"));
        true
    }

    /// Lowers a `v.truncate(n)` to the exact post-state re-binding
    /// `v = v.subrange(0, n)` (the first `n` elements), instead of the havoc. Exact
    /// when `n <= v.len()`. For `n > len` (`truncate` is a no-op) the `n <= len`
    /// half of `subrange`'s precondition is FALSE, so a later use of the receiver is
    /// NotProved (fail-closed) — a sound OVER-rejection of the shrink-nothing case,
    /// never a false-verify. No arithmetic on `n`, so no overflow-check hazard.
    /// Returns `true` only for a bare local/param sequence-like receiver with a
    /// side-effect-free length argument.
    fn assign_local_vec_truncate_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "truncate" || method_call.args.len() != 1 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            return false;
        }
        let Some(len_expr) = method_call.args.first() else {
            return false;
        };
        if !self.externally_assigned_in_expr(len_expr).is_empty() {
            return false;
        }
        let n = self.expr_to_scoped_string(len_expr);
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(&name, format!("({receiver}).subrange(0usize, {n})"));
        true
    }

    /// Lowers `v.resize(n, val)` to the exact SHRINK post-state `v = v.subrange(0, n)`
    /// (the first `n` elements — identical to `truncate(n)`; `val` is unused when
    /// `n <= len`). The GROW case (`n > len`, which appends `n - len` copies of
    /// `val`) is handled by `subrange`'s own `n <= len` precondition: it is FALSE
    /// there, so a later use of the receiver is NotProved (fail-closed) — a sound
    /// OVER-rejection of the grow direction (modeling it needs a repeated-`val`
    /// fill sequence), never a false-verify. No arithmetic on `n`, so no
    /// overflow-check hazard. Bare local/param sequence-like receiver +
    /// side-effect-free length argument.
    fn assign_local_vec_resize_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "resize" || method_call.args.len() != 2 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            return false;
        }
        let Some(len_expr) = method_call.args.first() else {
            return false;
        };
        if !self.externally_assigned_in_expr(len_expr).is_empty() {
            return false;
        }
        let n = self.expr_to_scoped_string(len_expr);
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(&name, format!("({receiver}).subrange(0usize, {n})"));
        true
    }

    fn assign_local_vec_swap_remove_method_call(
        &mut self,
        method_call: &syn::ExprMethodCall,
    ) -> bool {
        if method_call.method != "swap_remove" || method_call.args.len() != 1 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "swap_remove",
                &method_call.receiver,
            ));
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "swap_remove",
                &method_call.receiver,
            ));
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "swap_remove",
                &method_call.receiver,
            ));
            return false;
        }

        let Some(index_expr) = method_call.args.first() else {
            return false;
        };
        if !is_stable_vec_insert_index_expr(index_expr) {
            self.parse_error = Some(unsupported_vec_insert_index_error(index_expr));
            return false;
        }
        if !self.externally_assigned_in_expr(index_expr).is_empty() {
            self.parse_error = Some(unsupported_vec_mutation_side_effect_error(
                "swap_remove",
                method_call,
            ));
            return false;
        }

        let index = self.expr_to_scoped_string(index_expr);
        let last_index = format!("({receiver}).len() - 1usize");
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(
            &name,
            format!(
                "({receiver}).update({index}, ({receiver}).index({last_index})).subrange(0usize, {last_index})"
            ),
        );
        true
    }

    fn assign_local_vec_append_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "append" || method_call.args.len() != 1 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "append",
                &method_call.receiver,
            ));
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "append",
                &method_call.receiver,
            ));
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            self.parse_error = Some(unsupported_vec_mutation_receiver_error(
                "append",
                &method_call.receiver,
            ));
            return false;
        }

        let Some(arg_expr) = method_call.args.first() else {
            return false;
        };
        let Some(other_name) = mut_ref_path_ident(arg_expr) else {
            self.parse_error = Some(unsupported_vec_append_arg_error(arg_expr));
            return false;
        };
        if self.is_erased_mut_ref_name(&other_name)
            || self.is_unsupported_index_receiver(&other_name)
        {
            self.parse_error = Some(unsupported_vec_append_arg_error(arg_expr));
            return false;
        }
        let other = self.lookup_scoped(&other_name);
        if !is_scoped_vec_receiver_model(&other) {
            self.parse_error = Some(unsupported_vec_append_arg_error(arg_expr));
            return false;
        }
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.invalidate_mut_ref_aliases_targeting(&other_name);
        self.assign_scoped(&name, format!("({receiver}).add({other})"));
        self.assign_scoped(
            &other_name,
            format!("({other}).subrange(({other}).len(), ({other}).len())"),
        );
        true
    }

    /// Lowers `v.split_off(at)` to the exact post-state `v = v.subrange(0, at)` (v
    /// KEEPS `[0, at)`; the returned tail `[at, len)` is NOT modeled, so a `let tail
    /// = v.split_off(at)` that USES `tail` stays fail-closed on `tail`). Same
    /// prefix-`subrange` shape as `truncate`: `subrange`'s own `at <= len`
    /// precondition fail-closes an out-of-range split (NotProved), never a
    /// false-verify. No arithmetic on `at`, so no overflow-check hazard. Bare
    /// local/param sequence-like receiver + side-effect-free arg only.
    fn assign_local_vec_split_off_method_call(
        &mut self,
        method_call: &syn::ExprMethodCall,
    ) -> bool {
        if method_call.method != "split_off" || method_call.args.len() != 1 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            return false;
        }
        let Some(at_expr) = method_call.args.first() else {
            return false;
        };
        if !self.externally_assigned_in_expr(at_expr).is_empty() {
            return false;
        }
        let at = self.expr_to_scoped_string(at_expr);
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(&name, format!("({receiver}).subrange(0usize, {at})"));
        true
    }

    /// Lowers a discarded `v.drain(range)` to the exact post-state = the elements
    /// OUTSIDE `range`, for the SINGLE-CONTIGUOUS-remainder half-open shapes:
    ///   `..`    -> `subrange(0, 0)`      (empty — identical to clear)
    ///   `a..`   -> `subrange(0, a)`      (keep the prefix — like truncate)
    ///   `..b`   -> `subrange(b, len)`    (keep the suffix)
    /// The MIDDLE range `a..b` (remainder `[0,a) ++ [b,len)` — a two-piece `add`)
    /// is DECLINED: its `subrange(..).add(subrange(..))` with a later index read is
    /// the same quantifier-heavy path as the insert-index slow case, so it stays
    /// fail-closed (havoc) rather than emit a costly obligation. Inclusive `..=b`
    /// is declined (the `end+1` arithmetic is out of scope). Each `subrange` bound
    /// carries its own `start <= end <= len` precondition, so an out-of-range drain
    /// is NotProved (fail-closed), never a false-verify. The drained-elements
    /// iterator is not modeled. Bare local/param sequence-like receiver +
    /// side-effect-free bounds only.
    fn assign_local_vec_drain_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "drain" || method_call.args.len() != 1 {
            return false;
        }
        let Some(Expr::Range(range)) = method_call.args.first() else {
            return false;
        };
        if matches!(range.limits, syn::RangeLimits::Closed(_)) {
            return false;
        }
        // Decline the middle range `a..b` (two-piece remainder — see doc).
        if range.start.is_some() && range.end.is_some() {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            return false;
        }
        if range
            .start
            .as_ref()
            .is_some_and(|s| !self.externally_assigned_in_expr(s).is_empty())
            || range
                .end
                .as_ref()
                .is_some_and(|e| !self.externally_assigned_in_expr(e).is_empty())
        {
            return false;
        }
        let start = range.start.as_ref().map(|s| self.expr_to_scoped_string(s));
        let end = range.end.as_ref().map(|e| self.expr_to_scoped_string(e));
        self.invalidate_mut_ref_aliases_targeting(&name);
        let value = match (start, end) {
            (Some(a), None) => format!("({receiver}).subrange(0usize, {a})"),
            (None, Some(b)) => format!("({receiver}).subrange({b}, ({receiver}).len())"),
            _ => format!("({receiver}).subrange(0usize, 0usize)"),
        };
        self.assign_scoped(&name, value);
        true
    }

    /// Lowers `v.extend(other)` where `other` is a BY-VALUE Vec local to the exact
    /// concat post-state `v = v.add(other)`, mirroring `append` (the difference is
    /// `append` takes `&mut other` and empties it, while `extend` MOVES `other`, so
    /// `other` is simply invalidated — it cannot be read again in valid Rust). Fires
    /// ONLY when the argument is a bare Vec-local path whose scoped state is
    /// sequence-like; every other `extend` argument (`&other`, `other.iter()`, a
    /// range `0..n`, an array literal, any iterator adaptor) is NOT a bare vec-model
    /// path, so this returns `false` and the call keeps the existing havoc
    /// (fail-closed). Sound-by-construction: `extend` appends the argument's
    /// elements, and for a whole Vec that is exactly `v ++ other == v.add(other)`.
    fn assign_local_vec_extend_method_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        if method_call.method != "extend" || method_call.args.len() != 1 {
            return false;
        }
        let Some(name) = expr_path_ident(&method_call.receiver) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&name) || self.is_unsupported_index_receiver(&name) {
            return false;
        }
        let receiver = self.lookup_scoped(&name);
        if !is_scoped_vec_receiver_model(&receiver) {
            return false;
        }
        let Some(arg_expr) = method_call.args.first() else {
            return false;
        };
        let Some(other_name) = expr_path_ident(arg_expr) else {
            return false;
        };
        if self.is_erased_mut_ref_name(&other_name)
            || self.is_unsupported_index_receiver(&other_name)
        {
            return false;
        }
        let other = self.lookup_scoped(&other_name);
        if !is_scoped_vec_receiver_model(&other) {
            return false;
        }
        self.invalidate_mut_ref_aliases_targeting(&name);
        self.assign_scoped(&name, format!("({receiver}).add({other})"));
        // `other` is MOVED by `extend`; it cannot be read again in valid Rust, so
        // drop its scoped model (a later spurious read then fails closed).
        self.invalidate_scoped(&other_name);
        true
    }

    fn format_supported_macro_expr(&mut self, mac: &syn::ExprMacro) -> Option<String> {
        let trailing_name = mac.mac.path.segments.last()?.ident.to_string();
        if self.lookup_local_macro(&trailing_name).is_some() {
            self.parse_error = Some(unsupported_local_macro_expression_error(&trailing_name));
            return None;
        }
        match trailing_name.as_str() {
            "vec" => self.format_vec_macro_expr(&mac.mac),
            "ext_eq" | "ext_ne" | "strict_eq" | "equal" => self.format_two_expr_macro(&mac.mac),
            // `==>` / `<==>` lower to these binary MARKER macros; render each
            // operand scope-substituted (so a let-local like `p` in `p ==> Q`
            // resolves to its model) and re-emit the marker. Without this the
            // Macro arm falls to the verbatim `extract_expr_string` and the
            // let-local is unresolved ("unresolved variable `p`"). The two-expr
            // renderer already scopes each side; a TOP-LEVEL marker binds nothing,
            // so there is no capture (the inside-a-quantifier case is handled with
            // capture-avoidance by `scoped_closure_string`).
            name if name == crate::chained_comparisons::IMPLIES_MARKER_MACRO
                || name == crate::chained_comparisons::IFF_MARKER_MACRO =>
            {
                self.format_two_expr_macro(&mac.mac)
            }
            _ => None,
        }
    }

    fn format_vec_macro_expr(&mut self, mac: &Macro) -> Option<String> {
        let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
        let args = parser.parse2(mac.tokens.clone()).ok()?;
        let rendered = args
            .iter()
            .map(|arg| {
                let value = self.expr_to_scoped_string(arg);
                self.invalidate_expr_side_effects(arg);
                value
            })
            .collect::<Vec<_>>()
            .join(", ");
        Some(format!("vec![{rendered}]"))
    }

    fn format_two_expr_macro(&mut self, mac: &Macro) -> Option<String> {
        let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
        let args = parser.parse2(mac.tokens.clone()).ok()?;
        let [lhs_expr, rhs_expr] = args.into_iter().collect::<Vec<_>>().try_into().ok()?;
        let lhs = self.expr_to_scoped_string(&lhs_expr);
        self.invalidate_expr_side_effects(&lhs_expr);
        let rhs = self.expr_to_scoped_string(&rhs_expr);
        self.invalidate_expr_side_effects(&rhs_expr);
        let path = mac.path.to_token_stream();
        Some(format!("{path}!({lhs}, {rhs})"))
    }

    fn record_option_closure_contract_call(&mut self, method_call: &syn::ExprMethodCall) -> bool {
        let method = method_call.method.to_string();
        if !matches!(
            method.as_str(),
            "ok_or_else" | "unwrap_or_else" | "and_then"
        ) {
            return false;
        }
        let Some(arg) = method_call.args.first() else {
            return false;
        };
        let Expr::Macro(expr_macro) = arg else {
            return false;
        };
        if !is_trust_vc_closure_expr_macro(expr_macro) {
            return false;
        }

        let contract: BodyOptionClosureContract = match syn::parse2(expr_macro.mac.tokens.clone()) {
            Ok(contract) => contract,
            Err(err) => {
                self.parse_error = Some(TrustVcError::Encoding {
                    context: "extract Option closure contracts",
                    detail: format!(
                        "Option::{method} trust_vc::closure! argument is malformed: {err}"
                    ),
                });
                return true;
            }
        };

        if !contract.has_contract_clause() {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract Option closure contracts",
                detail:
                    "trust_vc::closure! requires at least a requires(...) or ensures(...) clause"
                        .to_string(),
            });
            return true;
        }
        if !self.validate_option_closure_contract_arity(&method, &contract) {
            return true;
        }

        let receiver = self.expr_to_scoped_string(&method_call.receiver);
        if let Some(requires) = contract.requires.as_ref() {
            let condition = option_closure_branch_condition(
                &method,
                &receiver,
                &contract,
                &requires.to_token_stream().to_string(),
            );
            self.add_option_closure_requires(&method, condition);
        }
        if let Some(ensures) = contract.ensures_condition() {
            let condition = option_closure_branch_condition(
                &method,
                &receiver,
                &contract,
                &ensures.to_token_stream().to_string(),
            );
            self.add_option_closure_ensures(&method, condition);
        }
        true
    }

    fn validate_option_closure_contract_arity(
        &mut self,
        method: &str,
        contract: &BodyOptionClosureContract,
    ) -> bool {
        let expected = match method {
            "ok_or_else" | "unwrap_or_else" => 0,
            "and_then" => 1,
            _ => return false,
        };
        if contract.params.len() == expected {
            return true;
        }
        self.parse_error = Some(TrustVcError::Encoding {
            context: "extract Option closure contracts",
            detail: format!(
                "Option::{method} trust_vc::closure! expects {expected} parameters, got {}",
                contract.params.len()
            ),
        });
        false
    }

    fn format_struct_expr(&mut self, strukt: &syn::ExprStruct) -> String {
        let path = strukt.path.to_token_stream().to_string();
        let fields = strukt
            .fields
            .iter()
            .map(|field| {
                let name = field_member_name(&field.member);
                let value = self.expr_to_scoped_string(&field.expr);
                self.invalidate_expr_side_effects(&field.expr);
                format!("{name}: {value}")
            })
            .collect::<Vec<_>>()
            .join(", ");
        match &strukt.rest {
            Some(rest) => format!(
                "{path} {{ {fields}, ..{} }}",
                self.expr_to_scoped_string(rest)
            ),
            None => format!("{path} {{ {fields} }}"),
        }
    }

    fn eval_block_expr(&mut self, block: &syn::Block) -> Option<String> {
        let saved_scopes = self.scope_snapshot();
        self.push_scope();
        // Slice-C remediation: this value-path evaluation ALWAYS restores the
        // pre-block snapshot, so a deref write in here is reverted — region-
        // track its root and havoc after the restore (mirrors the
        // obligation-walk `visit_expr_block` region), so no post-block read
        // can see the reverted state.
        self.enter_deref_write_region();
        let mut result = None;
        let ok = self.eval_scoped_stmts(&block.stmts, &mut result);
        self.restore_scope_snapshot(saved_scopes);
        self.exit_deref_write_region_and_havoc();
        if !ok {
            return None;
        }
        result
    }

    fn eval_scoped_stmts(&mut self, stmts: &[Stmt], result: &mut Option<String>) -> bool {
        for stmt in stmts {
            match stmt {
                Stmt::Local(local) => self.bind_local(local),
                Stmt::Expr(Expr::Assign(assign), Some(_)) => {
                    let direct_deref_target =
                        self.direct_deref_mut_reference_assignment_target(assign.left.as_ref());
                    let right_mut_ref_target = self.direct_mut_reference_target(&assign.right);
                    // Value-computation path (scoped-string evaluation of a
                    // block expression): must not emit obligations.
                    if !self.assign_expr(assign, direct_deref_target, right_mut_ref_target, false) {
                        if self.parse_error.is_none() {
                            if assignment_target_uses_erased_mut_ref_alias(
                                assign.left.as_ref(),
                                self,
                            ) {
                                self.parse_error =
                                    Some(unsupported_mut_ref_projection_assignment_error(
                                        assign.left.as_ref(),
                                    ));
                            } else if matches!(
                                strip_place_wrappers(assign.left.as_ref()),
                                Expr::Index(_)
                            ) {
                                self.parse_error =
                                    Some(unsupported_index_assignment_error(assign.left.as_ref()));
                            }
                        }
                        return false;
                    }
                }
                Stmt::Expr(Expr::Binary(binary), Some(_)) if is_assignment_binop(&binary.op) => {
                    // Value-computation path: must not emit obligations.
                    if !self.assign_compound_expr(binary, false) {
                        return false;
                    }
                }
                Stmt::Expr(expr, None) => *result = Some(self.expr_to_scoped_string(expr)),
                Stmt::Expr(expr, Some(_)) => {
                    if let Expr::MethodCall(method_call) = expr {
                        if self.assign_local_push_method_call(method_call)
                            || self.assign_local_set_method_call(method_call)
                            || self.assign_local_vec_insert_method_call(method_call)
                            || self.assign_local_vec_remove_method_call(method_call)
                            || self.assign_local_vec_swap_remove_method_call(method_call)
                            || self.assign_local_vec_append_method_call(method_call)
                        {
                            continue;
                        }
                        if self.parse_error.is_some() {
                            return false;
                        }
                    }
                    if !self.externally_assigned_in_expr(expr).is_empty() {
                        return false;
                    }
                }
                Stmt::Macro(stmt_macro) => {
                    match self.expand_local_macro_for_eval(&stmt_macro.mac) {
                        Ok(true) => {}
                        Ok(false) => {
                            if !is_supported_body_macro(&stmt_macro.mac) {
                                self.parse_error = Some(unsupported_macro_error(&stmt_macro.mac));
                                return false;
                            }
                        }
                        Err(err) => {
                            self.parse_error = Some(err);
                            return false;
                        }
                    }
                }
                Stmt::Item(item) => {
                    // Value-computation context (scoped-string evaluation of a
                    // block expression): bind the item but never emit
                    // obligations — those belong to the obligation-emitting
                    // visitor pass, not value substitution.
                    if let Err(err) = self.handle_nested_item(item, false) {
                        self.parse_error = Some(err);
                        return false;
                    }
                }
            }
        }
        true
    }

    fn current_scope_mut(&mut self) -> &mut BTreeMap<String, String> {
        if self.scopes.is_empty() {
            self.scopes.push(BTreeMap::new());
        }
        let index = self.scopes.len() - 1;
        &mut self.scopes[index]
    }

    fn current_macro_scope_mut(&mut self) -> &mut BTreeMap<String, LocalMacroDefinition> {
        if self.local_macros.is_empty() {
            self.local_macros.push(BTreeMap::new());
        }
        let index = self.local_macros.len() - 1;
        &mut self.local_macros[index]
    }

    fn push_scope(&mut self) {
        self.scopes.push(BTreeMap::new());
        self.concrete_scoped_values.push(BTreeSet::new());
        self.ghost_collection_scopes.push(BTreeSet::new());
        self.scoped_struct_types.push(BTreeMap::new());
        self.erased_shared_ref_aliases.push(BTreeSet::new());
        self.erased_mut_ref_aliases.push(BTreeSet::new());
        self.erased_mut_ref_targets.push(BTreeMap::new());
        self.local_macros.push(BTreeMap::new());
        self.unsupported_index_receivers.push(BTreeSet::new());
        self.scoped_local_types.push(HashMap::new());
        self.closure_reflection_contract_changes
            .push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        if let Some(changes) = self.closure_reflection_contract_changes.pop() {
            for (name, previous) in changes {
                match previous {
                    Some(contract) => {
                        self.closure_reflection_contracts.insert(name, contract);
                    }
                    None => {
                        self.closure_reflection_contracts.remove(&name);
                    }
                }
            }
        }
        self.scopes.pop();
        self.concrete_scoped_values.pop();
        self.ghost_collection_scopes.pop();
        self.scoped_struct_types.pop();
        self.erased_shared_ref_aliases.pop();
        self.erased_mut_ref_aliases.pop();
        self.erased_mut_ref_targets.pop();
        self.local_macros.pop();
        self.unsupported_index_receivers.pop();
        self.scoped_local_types.pop();
    }

    fn scope_snapshot(&self) -> ScopeSnapshot {
        ScopeSnapshot {
            scopes: self.scopes.clone(),
            concrete_scoped_values: self.concrete_scoped_values.clone(),
            ghost_collection_scopes: self.ghost_collection_scopes.clone(),
            scoped_struct_types: self.scoped_struct_types.clone(),
            erased_shared_ref_aliases: self.erased_shared_ref_aliases.clone(),
            erased_mut_ref_aliases: self.erased_mut_ref_aliases.clone(),
            erased_mut_ref_targets: self.erased_mut_ref_targets.clone(),
            unsupported_index_receivers: self.unsupported_index_receivers.clone(),
            local_macros: self.local_macros.clone(),
            exec_closure_defs: self.exec_closure_defs.clone(),
            closure_reflection_contracts: self.closure_reflection_contracts.clone(),
            closure_reflection_contract_changes: self.closure_reflection_contract_changes.clone(),
            scoped_local_types: self.scoped_local_types.clone(),
        }
    }

    fn restore_scope_snapshot(&mut self, snapshot: ScopeSnapshot) {
        self.scopes = snapshot.scopes;
        self.concrete_scoped_values = snapshot.concrete_scoped_values;
        self.ghost_collection_scopes = snapshot.ghost_collection_scopes;
        self.scoped_struct_types = snapshot.scoped_struct_types;
        self.erased_shared_ref_aliases = snapshot.erased_shared_ref_aliases;
        self.erased_mut_ref_aliases = snapshot.erased_mut_ref_aliases;
        self.erased_mut_ref_targets = snapshot.erased_mut_ref_targets;
        self.unsupported_index_receivers = snapshot.unsupported_index_receivers;
        self.local_macros = snapshot.local_macros;
        self.exec_closure_defs = snapshot.exec_closure_defs;
        self.closure_reflection_contracts = snapshot.closure_reflection_contracts;
        self.closure_reflection_contract_changes = snapshot.closure_reflection_contract_changes;
        self.scoped_local_types = snapshot.scoped_local_types;
    }

    fn lookup_local_macro(&self, name: &str) -> Option<LocalMacroDefinition> {
        self.local_macros
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .cloned()
    }

    fn handle_nested_item(&mut self, item: &Item, emit_overflow: bool) -> TrustVcResult<()> {
        match item {
            Item::Use(_) => Ok(()),
            Item::Macro(item_macro) => {
                if super::path_last_segment(&item_macro.mac.path).as_deref() != Some("macro_rules")
                {
                    return Err(unsupported_nested_item_error(item));
                }
                let (name, definition) = parse_local_macro_rules_item(item_macro)?;
                self.current_macro_scope_mut().insert(name, definition);
                Ok(())
            }
            Item::Const(item_const) => {
                self.bind_nested_const_static(&item_const.ident, &item_const.expr, emit_overflow)
            }
            Item::Static(item_static) => {
                self.bind_nested_const_static(&item_static.ident, &item_static.expr, emit_overflow)
            }
            _ => Err(unsupported_nested_item_error(item)),
        }
    }

    /// Binds a function-local `const`/`static` item's initializer into the
    /// current scope and, in obligation-emitting contexts, runs the
    /// initializer through the exec-mode arithmetic-overflow obligation path.
    ///
    /// Faithful to Verus, an exec `const`/`static` whose initializer overflows
    /// its declared type is a verification error. We reuse the same
    /// `maybe_emit_exec_arith_overflow_check` machinery the `let`-binding path
    /// uses (no second overflow definition), so a `255u8 + 1u8` initializer
    /// fails closed while a safe one verifies. The bound scoped value lets
    /// later references to the item substitute its initializer. Part of #2778.
    fn bind_nested_const_static(
        &mut self,
        ident: &syn::Ident,
        init: &Expr,
        emit_overflow: bool,
    ) -> TrustVcResult<()> {
        let name = ident.to_string();
        let value = self.expr_to_scoped_string(init);
        if let Some(err) = self.parse_error.take() {
            return Err(err);
        }
        if emit_overflow {
            self.maybe_emit_exec_arith_overflow_check(init, &value);
            if let Some(err) = self.parse_error.take() {
                return Err(err);
            }
            // SOUNDNESS-CRITICAL (exec scalar arithmetic): mirror the `let`-init
            // nested-site pin for an arithmetic site nested in a non-arith
            // const/static initializer.
            if !rhs_is_checked_scalar_arithmetic(init) && !rhs_is_checked_bit_shift(init) {
                self.emit_exec_arith_safety_checks_in_expr(init);
                if let Some(err) = self.parse_error.take() {
                    return Err(err);
                }
            }
        }
        let concrete = self.expr_is_concrete(init);
        let struct_type = self.expr_struct_type_name(init);
        self.current_scope_mut().insert(name.clone(), value);
        self.set_concrete_scoped_current(&name, concrete);
        if let Some(struct_type) = struct_type {
            self.set_struct_type_current(&name, struct_type);
        } else {
            self.clear_struct_type_current(&name);
        }
        Ok(())
    }

    fn expand_local_macro_stmt(&mut self, mac: &Macro) -> TrustVcResult<bool> {
        let Some(name) = super::path_last_segment(&mac.path) else {
            return Ok(false);
        };
        let Some(definition) = self.lookup_local_macro(&name) else {
            return Ok(false);
        };
        ensure_zero_arg_local_macro_invocation(mac, &name)?;
        let block = parse_local_macro_expansion_block(&name, &definition)?;
        self.expand_local_macro_block(&name, &block)?;
        Ok(true)
    }

    fn expand_local_macro_for_eval(&mut self, mac: &Macro) -> TrustVcResult<bool> {
        let Some(name) = super::path_last_segment(&mac.path) else {
            return Ok(false);
        };
        let Some(definition) = self.lookup_local_macro(&name) else {
            return Ok(false);
        };
        ensure_zero_arg_local_macro_invocation(mac, &name)?;
        let block = parse_local_macro_expansion_block(&name, &definition)?;
        self.enter_local_macro_expansion(&name)?;
        let mut result = None;
        let ok = self.eval_scoped_stmts(&block.stmts, &mut result);
        let nested_error = self.parse_error.take();
        self.macro_expansion_depth -= 1;
        if let Some(err) = nested_error {
            return Err(err);
        }
        if !ok {
            return Err(local_macro_expansion_error(
                &name,
                "expansion contains unsupported statements for scoped expression evaluation",
            ));
        }
        Ok(true)
    }

    fn expand_local_macro_block(&mut self, name: &str, block: &syn::Block) -> TrustVcResult<()> {
        self.enter_local_macro_expansion(name)?;
        let mut nested_error = None;
        for stmt in &block.stmts {
            self.visit_stmt(stmt);
            if self.parse_error.is_some() {
                nested_error = self.parse_error.take();
                break;
            }
        }
        self.macro_expansion_depth -= 1;
        if let Some(err) = nested_error {
            return Err(err);
        }
        Ok(())
    }

    fn enter_local_macro_expansion(&mut self, name: &str) -> TrustVcResult<()> {
        if self.macro_expansion_depth >= LOCAL_MACRO_EXPANSION_LIMIT {
            return Err(local_macro_expansion_error(
                name,
                "expansion depth limit exceeded",
            ));
        }
        self.macro_expansion_depth += 1;
        Ok(())
    }

    fn externally_assigned_in_expr(&self, expr: &Expr) -> BTreeSet<String> {
        let mut collector = ExternalAssignmentCollector::with_macro_scopes(&self.local_macros);
        collector.collection_receivers = self.collection_typed_receiver_names();
        collector.struct_receivers = self.struct_typed_receiver_names();
        collector.struct_self_receiver_kinds = self.vc.struct_self_receiver_kinds_clone();
        collector.type_param_mut_methods = self.type_param_mut_methods_by_receiver();
        collector.mut_ref_call_args = self.mut_ref_call_args.clone();
        collector.method_arg_mut_flags = self.method_arg_mut_flags.clone();
        collector.mut_ref_reborrowable_bindings = self.mut_ref_reborrowable_bindings.clone();
        collector.visit_expr(expr);
        collector.external_assignments
    }

    fn externally_assigned_in_block(&self, block: &syn::Block) -> BTreeSet<String> {
        let mut collector = ExternalAssignmentCollector::with_macro_scopes(&self.local_macros);
        collector.collection_receivers = self.collection_typed_receiver_names();
        collector.struct_receivers = self.struct_typed_receiver_names();
        collector.struct_self_receiver_kinds = self.vc.struct_self_receiver_kinds_clone();
        collector.type_param_mut_methods = self.type_param_mut_methods_by_receiver();
        collector.mut_ref_call_args = self.mut_ref_call_args.clone();
        collector.method_arg_mut_flags = self.method_arg_mut_flags.clone();
        collector.mut_ref_reborrowable_bindings = self.mut_ref_reborrowable_bindings.clone();
        collector.visit_block(block);
        collector.external_assignments
    }

    /// `externally_assigned_in_block` for a JOIN consumer (the `then` branch of
    /// an `if`): deref roots EXCLUDED — see `externally_assigned_in_join_expr`.
    fn externally_assigned_in_join_block(&self, block: &syn::Block) -> BTreeSet<String> {
        let mut collector = ExternalAssignmentCollector::with_macro_scopes(&self.local_macros);
        collector.collection_receivers = self.collection_typed_receiver_names();
        collector.struct_receivers = self.struct_typed_receiver_names();
        collector.struct_self_receiver_kinds = self.vc.struct_self_receiver_kinds_clone();
        collector.type_param_mut_methods = self.type_param_mut_methods_by_receiver();
        collector.mut_ref_call_args = self.mut_ref_call_args.clone();
        collector.method_arg_mut_flags = self.method_arg_mut_flags.clone();
        collector.mut_ref_reborrowable_bindings = self.mut_ref_reborrowable_bindings.clone();
        collector.include_deref_roots = false;
        collector.visit_block(block);
        collector.external_assignments
    }

    /// `externally_assigned_in_expr` for a JOIN consumer (an `else` branch
    /// expression, a `match` arm body): deref roots EXCLUDED, exactly like
    /// `externally_assigned_in_block` for the `then` branch — see
    /// `externally_assigned_in_loop_body` for why joins must not see them.
    /// The plain `externally_assigned_in_expr` keeps them because its other
    /// callers are the side-effecting index/RHS evaluation checks, where a
    /// deref write must fail closed (exec_index_bounds_faithful
    /// `bounded_deref_aliasing_side_effecting_index_compound_write_fails_closed`).
    fn externally_assigned_in_join_expr(&self, expr: &Expr) -> BTreeSet<String> {
        let mut collector = ExternalAssignmentCollector::with_macro_scopes(&self.local_macros);
        collector.collection_receivers = self.collection_typed_receiver_names();
        collector.struct_receivers = self.struct_typed_receiver_names();
        collector.struct_self_receiver_kinds = self.vc.struct_self_receiver_kinds_clone();
        collector.type_param_mut_methods = self.type_param_mut_methods_by_receiver();
        collector.mut_ref_call_args = self.mut_ref_call_args.clone();
        collector.method_arg_mut_flags = self.method_arg_mut_flags.clone();
        collector.mut_ref_reborrowable_bindings = self.mut_ref_reborrowable_bindings.clone();
        collector.include_deref_roots = false;
        collector.visit_expr(expr);
        collector.external_assignments
    }

    /// `externally_assigned_in_block` for a LOOP body: KEEPS the root of every
    /// bare external deref write (`*p = v` / `*p op= v`) in the set so the
    /// loop frame (`frame_loop_modified_vars`, invariant preservation) havocs
    /// it — the 1c0cfb56 soundness intent. Block JOINS (`if`/`else` branches,
    /// plain `{ .. }` / `unsafe` blocks via `externally_assigned_in_block`)
    /// must NOT get the roots: there the #83 skip holds and the slice-C region
    /// machinery (`deref_written_region_roots`: exact in-region SSA +
    /// region-exit havoc) already covers them. Feeding a deref root into a
    /// join's modified set invalidates the alias's scoped target at the join,
    /// after which the next `*x = ..` resolves to no erased target and fails
    /// closed — the 1c0cfb56 regression (bisected: good d255c1c3, bad
    /// 1c0cfb56) that turned the mut_ref_control_flow_gate /
    /// mut_ref_old_body_asserts branch ports into `assignment through a
    /// dereferenced reference is unsupported` Errors on BOTH the Verified and
    /// the Counterexample direction.
    fn externally_assigned_in_loop_body(&self, block: &syn::Block) -> BTreeSet<String> {
        let mut collector = ExternalAssignmentCollector::with_macro_scopes(&self.local_macros);
        collector.collection_receivers = self.collection_typed_receiver_names();
        collector.struct_receivers = self.struct_typed_receiver_names();
        collector.struct_self_receiver_kinds = self.vc.struct_self_receiver_kinds_clone();
        collector.type_param_mut_methods = self.type_param_mut_methods_by_receiver();
        collector.mut_ref_call_args = self.mut_ref_call_args.clone();
        collector.method_arg_mut_flags = self.method_arg_mut_flags.clone();
        collector.mut_ref_reborrowable_bindings = self.mut_ref_reborrowable_bindings.clone();
        collector.include_deref_roots = true;
        collector.visit_block(block);
        collector.external_assignments
    }

    /// The declared variables whose modeled type is a user struct/enum
    /// (`Datatype`), mapped to the base type name. These are the receivers on
    /// which a possibly-mutating method call must be conservatively recorded as a
    /// loop modification (the user-struct analog of `collection_typed_variable_names`).
    fn struct_typed_variable_names(&self) -> BTreeMap<String, String> {
        self.vc
            .variables()
            .iter()
            .filter_map(|decl| match &decl.ty {
                TrustVcType::Datatype { name, .. } => Some((decl.name.clone(), name.clone())),
                _ => None,
            })
            .collect()
    }

    /// The set of declared variable names whose modeled type is a collection
    /// (`Set`/`Seq`/`Map`/`Multiset`). These are exactly the receivers on which
    /// an unrecognized method call must be conservatively treated as a possible
    /// in-place mutation (the catastrophic loop collection-mutation gap). See
    /// `ExternalAssignmentCollector::collection_receivers`.
    fn collection_typed_variable_names(&self) -> BTreeSet<String> {
        self.vc
            .variables()
            .iter()
            .filter(|decl| {
                matches!(
                    decl.ty,
                    TrustVcType::Set(_)
                        | TrustVcType::Seq(_)
                        | TrustVcType::Map(_, _)
                        | TrustVcType::Multiset(_)
                )
            })
            .map(|decl| decl.name.clone())
            .collect()
    }

    /// The struct/enum-typed receivers the loop modified-set collector must
    /// consult: the declared `vc` variables (`struct_typed_variable_names`) PLUS
    /// the in-scope `let`-bound LOCAL struct/enum bindings.
    ///
    /// SOUNDNESS (round-10 be-2 findings 6-7): the loop-frame modified-set
    /// collector classifies a method-call receiver as a possibly-mutated struct
    /// ONLY when it appears in `struct_receivers`. Seeding it solely from
    /// `vc.variables()` (params / declared vars) left a `let mut c = Counter{..}`
    /// local mutated by a `&mut self` method (`c.bump()`) inside a loop OUT of the
    /// modified set, so the frame pinned `c == c_pre` and a post-loop `assert!`
    /// over the frozen entry value falsely `Verified`. The let-local's scoped
    /// struct type is recorded in `scoped_struct_types`; surfacing it here lets
    /// the collector record the receiver exactly as it does for a `&mut S`
    /// parameter. A pure `&self`/by-value reader is still NOT recorded by the
    /// collector (`struct_method_mutates_caller`), so an only-read let-local
    /// struct stays framed (NO over-rejection).
    fn struct_typed_receiver_names(&self) -> BTreeMap<String, String> {
        let mut receivers = self.struct_typed_variable_names();
        for name in self.scoped_binding_names() {
            if let Some(struct_type) = self.scoped_struct_type_name(&name) {
                receivers.insert(name, scoped_struct_type_base_name(&struct_type));
            } else {
                // A nearer non-struct `let` may shadow a same-named declared
                // struct parameter. The source binding, not the stale VC-table
                // entry, controls receiver classification in this scope.
                receivers.remove(&name);
            }
        }
        receivers
    }

    /// The collection-typed receivers the loop modified-set collector must
    /// consult: the declared `vc` collection variables
    /// (`collection_typed_variable_names`) PLUS the in-scope `let`-bound LOCAL
    /// bindings that model a collection (a ghost `Set`/`Seq`/`Map` local, or any
    /// scoped local the extractor recognizes as collection-like).
    ///
    /// SOUNDNESS (round-10 be-2 findings 8-11): the conservative loop-frame
    /// collection-mutation default fires only for a receiver in
    /// `collection_receivers`. Seeding it solely from `vc.variables()` left a
    /// `let`-local collection mutated by an unrecognized non-pure method OUT of
    /// the modified set. Surfacing the let-local collection makes the existing
    /// typed conservative default record an UNlisted non-pure method without
    /// relying on a method-name guess. A pure `&self` read
    /// (`len`/`index`/`contains`/…) is excluded by the collector
    /// (`is_pure_collection_read_method`), so an only-read let-local collection
    /// stays framed (NO over-rejection).
    fn collection_typed_receiver_names(&self) -> BTreeSet<String> {
        let mut receivers = self.collection_typed_variable_names();
        for name in self.scoped_binding_names() {
            if self.receiver_is_collection_like(&name) {
                receivers.insert(name);
            } else {
                // A nearer non-collection `let` may shadow a same-named
                // collection parameter. Do not let the stale VC-table type
                // classify a user struct's method by a collection method name.
                receivers.remove(&name);
            }
        }
        receivers
    }

    /// Every name currently bound in some scoped value-numbering frame — the
    /// candidate set of in-scope `let`-locals (plus reassigned params) for the
    /// let-local receiver-seeding above.
    fn scoped_binding_names(&self) -> BTreeSet<String> {
        self.scopes
            .iter()
            .flat_map(|scope| scope.keys().cloned())
            .collect()
    }

    fn lookup_scoped(&self, name: &str) -> String {
        // SOUNDNESS-CRITICAL (loop-body exec arithmetic safety): while rendering a
        // loop-body arithmetic-safety obligation, a loop-MODIFIED scalar resolves
        // to its fresh, unconstrained havoc symbol — its arbitrary value at
        // loop-body entry — NOT its function-entry / pre-loop scoped value. This
        // is the ONLY resolution path that consults the havoc map, and it is
        // gated on `render_loop_body_havoc`, which is set transiently solely
        // around arithmetic/index obligation rendering. Every other read (the
        // loop invariant, the M4 single-iteration transition, post-loop reads,
        // ordinary assertions) sees the unperturbed scoped value.
        if self.render_loop_body_havoc {
            if let Some(fresh) = self
                .loop_body_havoc
                .iter()
                .rev()
                .find_map(|map| map.get(name))
            {
                return format!("({fresh})");
            }
        }
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .map(|value| format!("({value})"))
            .unwrap_or_else(|| name.to_string())
    }

    fn assign_scoped(&mut self, name: &str, value: String) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(name) {
                scope.insert(name.to_string(), value);
                return;
            }
        }
        self.current_scope_mut().insert(name.to_string(), value);
    }

    fn set_concrete_scoped_current(&mut self, name: &str, concrete: bool) {
        if self.concrete_scoped_values.is_empty() {
            self.concrete_scoped_values.push(BTreeSet::new());
        }
        let index = self.concrete_scoped_values.len() - 1;
        let concrete_values = &mut self.concrete_scoped_values[index];
        if concrete {
            concrete_values.insert(name.to_string());
        } else {
            concrete_values.remove(name);
        }
    }

    fn set_concrete_scoped_nearest(&mut self, name: &str, concrete: bool) {
        for (scope, concrete_values) in self
            .scopes
            .iter()
            .zip(self.concrete_scoped_values.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                if concrete {
                    concrete_values.insert(name.to_string());
                } else {
                    concrete_values.remove(name);
                }
                return;
            }
        }
        self.set_concrete_scoped_current(name, concrete);
    }

    fn is_concrete_scoped_name(&self, name: &str) -> bool {
        for (scope, concrete_values) in self.scopes.iter().zip(&self.concrete_scoped_values).rev() {
            if scope.contains_key(name) {
                return concrete_values.contains(name);
            }
        }
        false
    }

    /// Records (or clears) whether the current-scope binding of `name` models an
    /// immutable ghost collection (GAP2). See `ghost_collection_scopes`.
    fn set_ghost_collection_current(&mut self, name: &str, is_ghost_collection: bool) {
        if self.ghost_collection_scopes.is_empty() {
            self.ghost_collection_scopes.push(BTreeSet::new());
        }
        let index = self.ghost_collection_scopes.len() - 1;
        let ghost_collections = &mut self.ghost_collection_scopes[index];
        if is_ghost_collection {
            ghost_collections.insert(name.to_string());
        } else {
            ghost_collections.remove(name);
        }
    }

    /// True when the nearest binding of `name` is a marked immutable ghost
    /// collection.
    fn is_ghost_collection_name(&self, name: &str) -> bool {
        for (scope, ghost_collections) in
            self.scopes.iter().zip(&self.ghost_collection_scopes).rev()
        {
            if scope.contains_key(name) {
                return ghost_collections.contains(name);
            }
        }
        false
    }

    /// True when `name` denotes a collection-shaped receiver: either a let-local
    /// inferred to model an immutable ghost collection, or a declared variable
    /// whose modeled type is a collection (`Set`/`Seq`/`Map`/`Multiset`).
    ///
    /// NOTE: the IR collapses several *mutable* exec containers onto the same
    /// modeled type as their immutable ghost views (`Vec`/`[T]`/`[T; N]` =>
    /// `Seq`, `HashSet`/`BTreeSet` => `Set`, `HashMap`/`BTreeMap` => `Map`), so
    /// "collection-like" does NOT imply "immutable". This predicate only TARGETS
    /// the preservation relaxation; soundness is enforced separately by the
    /// pure-combinator gate in `method_call_preserves_receiver`.
    fn receiver_is_collection_like(&self, name: &str) -> bool {
        if self.is_ghost_collection_name(name) {
            return true;
        }
        // `let`-bound exec collections are scoped value-numbering bindings, not
        // VC declarations. Recognize the sequence models the extractor itself
        // creates (`Vec::new`, array literals, and update/push/subrange chains),
        // so the loop modified-set collector can apply its conservative
        // non-pure-method rule to a local receiver. This is deliberately based on
        // known collection-producing models, never on a method name alone.
        let scoped_model = self.scopes.iter().rev().find_map(|scope| scope.get(name));
        if scoped_model.is_some_and(|value| {
            is_scoped_vec_receiver_model(value) || is_scoped_sequence_shaped_model(value)
        }) {
            return true;
        }
        // A scoped non-collection binding shadows any same-named parameter in
        // the flat VC declaration table. Do not fall through to that stale type.
        if scoped_model.is_some() {
            return false;
        }
        matches!(
            self.vc.get_variable_type(name),
            Some(
                TrustVcType::Set(_)
                    | TrustVcType::Seq(_)
                    | TrustVcType::Map(_, _)
                    | TrustVcType::Multiset(_)
            )
        )
    }

    /// True when `recv.method(..)` provably leaves the scoped model of `recv`
    /// unchanged, so the receiver binding may survive the call instead of being
    /// conservatively invalidated (GAP2).
    ///
    /// SOUNDNESS: this must NEVER preserve a receiver across a call that could
    /// mutate it. Because the modeled type does not distinguish an immutable
    /// ghost `Seq`/`Set`/`Map` from a *mutable* `Vec`/`HashSet`/`HashMap`
    /// (they share a `TrustVcType`), we do NOT key the decision on the type and
    /// we do NOT key it on the complement of `is_known_mutating_method` (that
    /// list omits in-place mutators such as `Vec::sort`/`dedup`/`retain`, so its
    /// complement would wrongly preserve a mutated `Vec`). Instead we require the
    /// method to be a `pure_ghost_collection_combinator` — a name that returns a
    /// NEW value (or reads through `&self`) and has NO same-named in-place
    /// mutator on any std container — which guarantees the receiver value is
    /// unchanged regardless of whether it is a ghost or an exec collection. The
    /// `receiver_is_collection_like` gate additionally excludes user types that
    /// might define a `&mut self` method sharing a combinator name.
    fn method_call_preserves_receiver(&self, name: &str, method: &str) -> bool {
        pure_ghost_collection_combinator(method) && self.receiver_is_collection_like(name)
    }

    /// Bind-time inference: does `expr` evaluate to an immutable ghost
    /// collection? Used to mark let-locals (which carry no declared type) so a
    /// reused `let s = Set::new(..)` survives a later `s.filter(..)`/`s.map(..)`.
    /// True when `name` denotes an IMMUTABLE ghost collection value: a let-local
    /// inferred to model one (`ghost_collection_scopes`), or — absent any scoped
    /// model — a declared variable of collection type. This is the ghost-decline
    /// predicate the exec `Vec` method models (`assign_local_vec_insert_method_call`
    /// & co.) consult through `expr_models_ghost_collection`; it must NOT be
    /// `receiver_is_collection_like`, which since 998c65c7 ALSO recognizes the
    /// extractor's own exec `Vec` models (`Vec::new`/push/update chains) so the
    /// loop modified-set collector can frame a let-local `Vec`. Routing the
    /// ghost-decline through that widened predicate classified every let-local
    /// exec `Vec` as ghost, so `v.insert(..)` / `v.remove(..)` declined their
    /// exact models, fell through to the conservative receiver invalidation, and
    /// the next `v.len()` lowered to an unresolved `v`
    /// (map_letlocal_value_capability `vec_insert_still_models` /
    /// `vec_remove_still_models`; bisected good 7711d988, bad 998c65c7).
    fn receiver_models_ghost_collection(&self, name: &str) -> bool {
        if self.is_ghost_collection_name(name) {
            return true;
        }
        if self.scopes.iter().any(|scope| scope.contains_key(name)) {
            return false;
        }
        matches!(
            self.vc.get_variable_type(name),
            Some(
                TrustVcType::Set(_)
                    | TrustVcType::Seq(_)
                    | TrustVcType::Map(_, _)
                    | TrustVcType::Multiset(_)
            )
        )
    }

    fn expr_models_ghost_collection(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Paren(paren) => self.expr_models_ghost_collection(&paren.expr),
            Expr::Group(group) => self.expr_models_ghost_collection(&group.expr),
            Expr::Reference(reference) if reference.mutability.is_none() => {
                self.expr_models_ghost_collection(&reference.expr)
            }
            Expr::Path(_) => expr_path_ident(expr)
                .is_some_and(|name| self.receiver_models_ghost_collection(&name)),
            // A ghost-collection constructor such as `Set::new(..)`/`Seq::empty()`.
            Expr::Call(call) => ghost_collection_constructor_path(&call.func),
            // A pure combinator (`s.filter(..)`) OR a value-producing builder
            // (`s.push(..)`/`s.insert(..)`) applied to something that already
            // models a ghost collection produces another ghost collection. The
            // builder set is separate from the pure-combinator set (see
            // `ghost_collection_value_producing_method`) because those names also
            // denote exec in-place mutators; the recursion only reaches them when
            // the chain is rooted at a ghost constructor, so exec chains are never
            // marked.
            Expr::MethodCall(method_call) => {
                let method = method_call.method.to_string();
                (pure_ghost_collection_combinator(&method)
                    || ghost_collection_value_producing_method(&method))
                    && self.expr_models_ghost_collection(&method_call.receiver)
            }
            _ => false,
        }
    }

    fn set_struct_type_current(&mut self, name: &str, struct_type: String) {
        if self.scoped_struct_types.is_empty() {
            self.scoped_struct_types.push(BTreeMap::new());
        }
        let index = self.scoped_struct_types.len() - 1;
        self.scoped_struct_types[index].insert(name.to_string(), struct_type);
    }

    fn set_struct_type_nearest(&mut self, name: &str, struct_type: String) {
        for (scope, struct_types) in self
            .scopes
            .iter()
            .zip(self.scoped_struct_types.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                struct_types.insert(name.to_string(), struct_type);
                return;
            }
        }
        self.set_struct_type_current(name, struct_type);
    }

    fn clear_struct_type_current(&mut self, name: &str) {
        if let Some(scope) = self.scoped_struct_types.last_mut() {
            scope.remove(name);
        }
    }

    fn clear_struct_type_nearest(&mut self, name: &str) {
        for (scope, struct_types) in self
            .scopes
            .iter()
            .zip(self.scoped_struct_types.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                struct_types.remove(name);
                return;
            }
        }
    }

    fn scoped_struct_type_name(&self, name: &str) -> Option<String> {
        for (scope, struct_types) in self.scopes.iter().zip(&self.scoped_struct_types).rev() {
            if let Some(struct_type) = struct_types.get(name) {
                return Some(struct_type.clone());
            }
            if scope.contains_key(name) {
                return None;
            }
        }
        None
    }

    fn has_scoped_name(&self, name: &str) -> bool {
        self.scopes
            .iter()
            .rev()
            .any(|scope| scope.contains_key(name))
    }

    fn invalidate_scoped(&mut self, name: &str) {
        for scope in &mut self.scopes {
            scope.remove(name);
        }
        for concrete_values in &mut self.concrete_scoped_values {
            concrete_values.remove(name);
        }
        for ghost_collections in &mut self.ghost_collection_scopes {
            ghost_collections.remove(name);
        }
        for struct_types in &mut self.scoped_struct_types {
            struct_types.remove(name);
        }
        for scope in &mut self.erased_shared_ref_aliases {
            scope.remove(name);
        }
        for scope in &mut self.erased_mut_ref_aliases {
            scope.remove(name);
        }
        for targets in &mut self.erased_mut_ref_targets {
            targets.remove(name);
        }
        self.invalidate_mut_ref_aliases_targeting(name);
        for scope in &mut self.unsupported_index_receivers {
            scope.remove(name);
        }
        // A reassigned / invalidated name can no longer be relied on to denote the
        // closure it was last bound to, so drop any tracked exec-closure body
        // (avoids instrumenting a `g(args)` whose `g` is now something else — no
        // over-rejection). Part of #2778 invoked-exec-closure body arith.
        self.exec_closure_defs.remove(name);
    }

    fn invalidate_scoped_names(&mut self, names: BTreeSet<String>) {
        for name in names {
            self.invalidate_scoped(&name);
        }
    }

    fn scoped_snapshot_value(snapshot: &ScopeSnapshot, name: &str) -> Option<String> {
        snapshot
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn merge_common_assigned_branch_values(
        assigned_names: &BTreeSet<String>,
        then_snapshot: &ScopeSnapshot,
        else_snapshot: Option<&ScopeSnapshot>,
    ) -> BTreeMap<String, String> {
        let Some(else_snapshot) = else_snapshot else {
            return BTreeMap::new();
        };

        assigned_names
            .iter()
            .filter_map(|name| {
                let then_value = Self::scoped_snapshot_value(then_snapshot, name)?;
                let else_value = Self::scoped_snapshot_value(else_snapshot, name)?;
                (then_value == else_value).then(|| (name.clone(), then_value))
            })
            .collect()
    }

    fn assign_scoped_at_snapshot_depth(
        &mut self,
        name: &str,
        value: String,
        snapshot: &ScopeSnapshot,
    ) {
        if let Some(index) = snapshot
            .scopes
            .iter()
            .rposition(|scope| scope.contains_key(name))
        {
            if let Some(scope) = self.scopes.get_mut(index) {
                scope.insert(name.to_string(), value);
                return;
            }
        }
        self.assign_scoped(name, value);
    }

    fn invalidate_expr_side_effects(&mut self, expr: &Expr) {
        self.invalidate_scoped_names(self.externally_assigned_in_expr(expr));
    }

    /// Picks a fresh solver symbol for every `assert forall` binder whose name
    /// collides with an ALREADY-DECLARED program variable (a parameter or an
    /// earlier local). Binders that collide with nothing are left alone, so the
    /// overwhelmingly common case keeps its source name in models and cached
    /// obligation text.
    fn fresh_assert_forall_binder_renames(
        &self,
        source_names: &[String],
    ) -> BTreeMap<String, String> {
        let mut renames = BTreeMap::new();
        for name in source_names {
            if self.vc.get_variable_type(name).is_none() {
                continue;
            }
            let mut index = 0usize;
            let mut fresh = format!("{name}__afb{index}");
            while self.vc.get_variable_type(&fresh).is_some()
                || source_names.iter().any(|other| other == &fresh)
                || renames.values().any(|taken: &String| taken == &fresh)
            {
                index += 1;
                fresh = format!("{name}__afb{index}");
            }
            renames.insert(name.clone(), fresh);
        }
        renames
    }

    /// Binds `name` in the current scope to the solver symbol `target`.
    /// `shadow_name(n)` is the identity case (`target == n`).
    fn shadow_name_as(&mut self, name: &str, target: &str) {
        self.shadow_name(name);
        self.current_scope_mut()
            .insert(name.to_string(), target.to_string());
    }

    fn shadow_name(&mut self, name: &str) {
        self.current_scope_mut()
            .insert(name.to_string(), name.to_string());
        self.set_concrete_scoped_current(name, false);
        self.set_ghost_collection_current(name, false);
        self.clear_struct_type_current(name);
        self.unmark_erased_shared_ref_alias_current(name);
        self.unmark_erased_mut_ref_alias_current(name);
        self.clear_erased_mut_ref_target_current(name);
        self.exec_closure_defs.remove(name);
        self.clear_closure_reflection_contract(name);
    }

    /// Record the pre-scope value for `name` once, before mutating the active
    /// closure-contract registry. Multiple Rust shadowings in one lexical scope
    /// intentionally share one undo entry: leaving that scope restores the value
    /// visible when the scope was entered, not an intermediate shadow.
    fn journal_closure_reflection_contract(&mut self, name: &str) {
        let previous = self.closure_reflection_contracts.get(name).cloned();
        if self.closure_reflection_contract_changes.is_empty() {
            self.closure_reflection_contract_changes
                .push(HashMap::new());
        }
        self.closure_reflection_contract_changes
            .last_mut()
            // quality-audit: allow-expect — pushed-when-empty above; a missing journal must abort, not silently skip the undo record
            .expect("closure-reflection scope journal must exist")
            .entry(name.to_string())
            .or_insert(previous);
    }

    fn replace_closure_reflection_contract(
        &mut self,
        name: String,
        contract: ClosureReflectionContract,
    ) {
        self.journal_closure_reflection_contract(&name);
        self.closure_reflection_contracts.insert(name, contract);
    }

    fn clear_closure_reflection_contract(&mut self, name: &str) {
        if self.closure_reflection_contracts.contains_key(name) {
            self.journal_closure_reflection_contract(name);
            self.closure_reflection_contracts.remove(name);
        }
    }

    fn mark_erased_shared_ref_alias(&mut self, name: &str) {
        if self.erased_shared_ref_aliases.is_empty() {
            self.erased_shared_ref_aliases.push(BTreeSet::new());
        }
        let index = self.erased_shared_ref_aliases.len() - 1;
        self.erased_shared_ref_aliases[index].insert(name.to_string());
    }

    fn mark_erased_shared_ref_alias_nearest(&mut self, name: &str) {
        for (scope, aliases) in self
            .scopes
            .iter()
            .zip(self.erased_shared_ref_aliases.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                aliases.insert(name.to_string());
                return;
            }
        }
        self.mark_erased_shared_ref_alias(name);
    }

    fn unmark_erased_shared_ref_alias_current(&mut self, name: &str) {
        if let Some(scope) = self.erased_shared_ref_aliases.last_mut() {
            scope.remove(name);
        }
    }

    fn unmark_erased_shared_ref_alias_nearest(&mut self, name: &str) {
        for (scope, aliases) in self
            .scopes
            .iter()
            .zip(self.erased_shared_ref_aliases.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                aliases.remove(name);
                return;
            }
        }
    }

    fn is_erased_shared_ref_name(&self, name: &str) -> bool {
        for (scope, aliases) in self
            .scopes
            .iter()
            .zip(&self.erased_shared_ref_aliases)
            .rev()
        {
            if aliases.contains(name) {
                return true;
            }
            if scope.contains_key(name) {
                return false;
            }
        }
        self.vc.is_erased_shared_ref_var(name)
    }

    fn is_erased_shared_ref_expr(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Path(_) => expr_path_ident(expr)
                .as_deref()
                .is_some_and(|name| self.is_erased_shared_ref_name(name)),
            Expr::Paren(paren) => self.is_erased_shared_ref_expr(&paren.expr),
            Expr::Group(group) => self.is_erased_shared_ref_expr(&group.expr),
            Expr::Reference(reference) => reference.mutability.is_none(),
            _ => false,
        }
    }

    fn mark_erased_mut_ref_alias(&mut self, name: &str) {
        if self.erased_mut_ref_aliases.is_empty() {
            self.erased_mut_ref_aliases.push(BTreeSet::new());
        }
        let index = self.erased_mut_ref_aliases.len() - 1;
        self.erased_mut_ref_aliases[index].insert(name.to_string());
    }

    fn mark_erased_mut_ref_alias_nearest(&mut self, name: &str) {
        for (scope, aliases) in self
            .scopes
            .iter()
            .zip(self.erased_mut_ref_aliases.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                aliases.insert(name.to_string());
                return;
            }
        }
        self.mark_erased_mut_ref_alias(name);
    }

    fn unmark_erased_mut_ref_alias_current(&mut self, name: &str) {
        if let Some(scope) = self.erased_mut_ref_aliases.last_mut() {
            scope.remove(name);
        }
        self.clear_erased_mut_ref_target_current(name);
    }

    fn unmark_erased_mut_ref_alias_nearest(&mut self, name: &str) {
        for ((scope, aliases), targets) in self
            .scopes
            .iter()
            .zip(self.erased_mut_ref_aliases.iter_mut())
            .zip(self.erased_mut_ref_targets.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                aliases.remove(name);
                targets.remove(name);
                return;
            }
        }
    }

    fn set_erased_mut_ref_target_current(&mut self, name: &str, target: ErasedMutRefTarget) {
        if self.erased_mut_ref_targets.is_empty() {
            self.erased_mut_ref_targets.push(BTreeMap::new());
        }
        let index = self.erased_mut_ref_targets.len() - 1;
        self.erased_mut_ref_targets[index].insert(name.to_string(), target);
    }

    fn set_erased_mut_ref_target_nearest(&mut self, name: &str, target: ErasedMutRefTarget) {
        for (scope, targets) in self
            .scopes
            .iter()
            .zip(self.erased_mut_ref_targets.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                targets.insert(name.to_string(), target);
                return;
            }
        }
        self.set_erased_mut_ref_target_current(name, target);
    }

    fn clear_erased_mut_ref_target_current(&mut self, name: &str) {
        if let Some(scope) = self.erased_mut_ref_targets.last_mut() {
            scope.remove(name);
        }
    }

    fn clear_erased_mut_ref_target_nearest(&mut self, name: &str) {
        for (scope, targets) in self
            .scopes
            .iter()
            .zip(self.erased_mut_ref_targets.iter_mut())
            .rev()
        {
            if scope.contains_key(name) {
                targets.remove(name);
                return;
            }
        }
    }

    fn erased_mut_ref_target_name(&self, name: &str) -> Option<ErasedMutRefTarget> {
        for (scope, targets) in self.scopes.iter().zip(&self.erased_mut_ref_targets).rev() {
            if let Some(target) = targets.get(name) {
                return Some(target.clone());
            }
            if scope.contains_key(name) {
                return None;
            }
        }
        None
    }

    fn invalidate_mut_ref_aliases_targeting(&mut self, target: &str) {
        let aliases = self
            .erased_mut_ref_targets
            .iter()
            .flat_map(|targets| {
                targets
                    .iter()
                    .filter(|(_, alias_target)| alias_target.root_name() == target)
                    .map(|(alias, _)| alias.clone())
            })
            .collect::<BTreeSet<_>>();

        for alias in aliases {
            for scope in &mut self.scopes {
                scope.remove(&alias);
            }
            for concrete_values in &mut self.concrete_scoped_values {
                concrete_values.remove(&alias);
            }
            for ghost_collections in &mut self.ghost_collection_scopes {
                ghost_collections.remove(&alias);
            }
            for struct_types in &mut self.scoped_struct_types {
                struct_types.remove(&alias);
            }
            for aliases in &mut self.erased_mut_ref_aliases {
                aliases.remove(&alias);
            }
            for targets in &mut self.erased_mut_ref_targets {
                targets.remove(&alias);
            }
            for unsupported in &mut self.unsupported_index_receivers {
                unsupported.remove(&alias);
            }
        }
    }

    fn is_erased_mut_ref_name(&self, name: &str) -> bool {
        for (scope, aliases) in self.scopes.iter().zip(&self.erased_mut_ref_aliases).rev() {
            if aliases.contains(name) {
                return true;
            }
            if scope.contains_key(name) {
                return false;
            }
        }
        false
    }

    fn is_erased_mut_ref_expr(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Path(_) => expr_path_ident(expr)
                .as_deref()
                .is_some_and(|name| self.is_erased_mut_ref_name(name)),
            Expr::Paren(paren) => self.is_erased_mut_ref_expr(&paren.expr),
            Expr::Group(group) => self.is_erased_mut_ref_expr(&group.expr),
            _ => false,
        }
    }

    fn mutable_reference_referent_scoped_string(&mut self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Reference(reference) if reference.mutability.is_some() => {
                Some(self.expr_to_scoped_string(&reference.expr))
            }
            Expr::Paren(paren) => self.mutable_reference_referent_scoped_string(&paren.expr),
            Expr::Group(group) => self.mutable_reference_referent_scoped_string(&group.expr),
            _ => None,
        }
    }

    fn expr_is_concrete(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Lit(_) => true,
            Expr::Path(_) => expr_path_ident(expr)
                .as_deref()
                .is_some_and(|name| self.is_concrete_scoped_name(name)),
            Expr::Paren(paren) => self.expr_is_concrete(&paren.expr),
            Expr::Group(group) => self.expr_is_concrete(&group.expr),
            Expr::Unary(unary) => self.expr_is_concrete(&unary.expr),
            Expr::Reference(reference) => self.expr_is_concrete(&reference.expr),
            Expr::Field(field) => self.expr_is_concrete(&field.base),
            Expr::Index(index) => {
                self.expr_is_concrete(&index.expr) && self.expr_is_concrete(&index.index)
            }
            Expr::Binary(binary) if !is_assignment_binop(&binary.op) => {
                self.expr_is_concrete(&binary.left) && self.expr_is_concrete(&binary.right)
            }
            Expr::Cast(cast) => self.expr_is_concrete(&cast.expr),
            Expr::Struct(strukt) => {
                strukt
                    .fields
                    .iter()
                    .all(|field| self.expr_is_concrete(&field.expr))
                    && strukt
                        .rest
                        .as_ref()
                        .is_none_or(|rest| self.expr_is_concrete(rest))
            }
            Expr::Tuple(tuple) => tuple.elems.iter().all(|elem| self.expr_is_concrete(elem)),
            _ => false,
        }
    }

    fn local_init_erases_mut_reference_alias(&self, local: &syn::Local) -> bool {
        let Some(init) = local.init.as_ref() else {
            return false;
        };
        expr_is_mut_reference(&init.expr)
            || self.is_erased_mut_ref_expr(&init.expr)
            || (local_pat_is_mut_reference(&local.pat) && expr_path_ident(&init.expr).is_some())
    }

    fn local_init_is_concrete(&self, local: &syn::Local) -> bool {
        local
            .init
            .as_ref()
            .is_some_and(|init| self.expr_is_concrete(&init.expr))
    }

    fn local_init_struct_type_name(&self, local: &syn::Local) -> Option<String> {
        local
            .init
            .as_ref()
            .and_then(|init| self.expr_struct_type_name(&init.expr))
    }

    fn local_scoped_struct_type_name(
        &self,
        local: &syn::Local,
        erased_mut_ref_target: Option<&ErasedMutRefTarget>,
    ) -> Option<String> {
        self.local_init_struct_type_name(local).or_else(|| {
            erased_mut_ref_target.and_then(|target| match target {
                ErasedMutRefTarget::Local(name) => self.scoped_struct_type_name(name),
                ErasedMutRefTarget::Field { .. } => None,
                ErasedMutRefTarget::Index { .. } => None,
            })
        })
    }

    fn expr_struct_type_name(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Struct(strukt) => Some(strukt.path.to_token_stream().to_string()),
            Expr::Path(_) => expr_path_ident(expr)
                .as_deref()
                .and_then(|name| self.scoped_struct_type_name(name)),
            // #102: a tuple-struct constructor `TupleThing(..)` /
            // `TupleThing::<..>(..)` is a call whose callee path names a struct.
            // A named struct cannot be constructed with call syntax in Rust, so
            // a single-segment callee path resolving to a registered struct is a
            // tuple-struct constructor; record its type so the bound local can be
            // destructured.
            Expr::Call(call) => expr_path_ident(&call.func)
                .filter(|func_name| {
                    self.vc
                        .struct_types
                        .iter()
                        .any(|def| def.name == *func_name)
                })
                // An enum tuple-variant constructor `Enum::Variant(..)` /
                // `Enum::<..>::Variant(..)` is a MULTI-segment callee path, so
                // `expr_path_ident` (single-segment only) returns `None`.
                // Recover the ENUM type from the second-to-last path segment so a
                // local bound to an enum-variant constructor can be destructured
                // with a matching `let Enum::Variant(..) = local` pattern —
                // mirroring the tuple-struct case above. Soundness: Rust permits
                // an irrefutable enum-variant `let` pattern ONLY for a
                // single-variant enum, so the field projections the destructure
                // emits are total; a multi-variant enum `let` is an E0005
                // refutable-pattern compile error and never reaches the verifier.
                .or_else(|| self.enum_type_name_of_variant_call(&call.func)),
            Expr::Paren(paren) => self.expr_struct_type_name(&paren.expr),
            Expr::Group(group) => self.expr_struct_type_name(&group.expr),
            _ => None,
        }
    }

    /// The enum type named by an enum tuple-variant constructor callee path
    /// `Enum::Variant` (or a module-qualified `a::b::Enum::Variant`): the enum
    /// is the second-to-last segment and the variant is the last. Returns the
    /// enum name ONLY when the second-to-last segment resolves to a registered
    /// datatype AND the last segment is a real variant of it. The variant check
    /// is what keeps an associated-function call on a datatype
    /// (`Enum::assoc_fn(..)`, whose result is NOT the enum) from being
    /// mis-inferred as an enum-variant constructor — which would otherwise let a
    /// later field access project the wrong type.
    fn enum_type_name_of_variant_call(&self, func: &Expr) -> Option<String> {
        let Expr::Path(expr_path) = func else {
            return None;
        };
        let segments = &expr_path.path.segments;
        if segments.len() < 2 {
            return None;
        }
        let enum_name = segments[segments.len() - 2].ident.to_string();
        let variant_name = segments[segments.len() - 1].ident.to_string();
        let ty = self.datatype_for_scoped_type_name(&enum_name)?;
        datatype_variant(&ty, &variant_name).map(|_| enum_name)
    }

    /// Datatype of a GROUND struct-constructor match scrutinee: a plain struct
    /// literal `S { .. }` (single-segment path only, so an enum struct-variant
    /// literal `E::V { .. }` can never mis-resolve to an unrelated struct that
    /// shares the variant's name) or a tuple-struct constructor call `S(..)`.
    /// Used by `visit_expr_match` when `local_pattern_base` cannot resolve a
    /// declared variable (the scrutinee is a constructor expression, not a
    /// path), so a flat arm pattern can still project its bindings from the
    /// scrutinee's scoped value — the exact machinery the local-scrutinee path
    /// already uses.
    fn ground_struct_scrutinee_datatype(&self, expr: &Expr) -> Option<TrustVcType> {
        match expr {
            Expr::Paren(paren) => self.ground_struct_scrutinee_datatype(&paren.expr),
            Expr::Group(group) => self.ground_struct_scrutinee_datatype(&group.expr),
            Expr::Struct(strukt) if strukt.path.segments.len() == 1 => {
                let name = strukt.path.segments[0].ident.to_string();
                self.vc
                    .struct_types
                    .iter()
                    .find(|def| def.name == name)
                    .map(|def| def.to_datatype_type())
            }
            Expr::Call(call) => {
                let name = expr_path_ident(&call.func)?;
                self.vc
                    .struct_types
                    .iter()
                    .find(|def| def.name == name)
                    .map(|def| def.to_datatype_type())
            }
            _ => None,
        }
    }

    /// Datatype of a GROUND enum tuple-variant constructor match scrutinee
    /// (`Enum::Variant(..)`), the enum sibling of
    /// [`Self::ground_struct_scrutinee_datatype`]. `visit_expr_match` consumes
    /// this ONLY for or-pattern arms: an ordinary variant arm over a ground
    /// enum constructor stays fail-closed (a pinned corpus boundary —
    /// `match_enum_tuple_variant_statement_payload_error`), while an or-pattern
    /// arm's MERGED binder carries its own per-disjunct guards, so resolving it
    /// here closes the or-pattern payload regression without widening that
    /// boundary.
    fn ground_enum_scrutinee_datatype(&self, expr: &Expr) -> Option<TrustVcType> {
        match expr {
            Expr::Paren(paren) => self.ground_enum_scrutinee_datatype(&paren.expr),
            Expr::Group(group) => self.ground_enum_scrutinee_datatype(&group.expr),
            Expr::Call(call) => {
                let enum_name = self.enum_type_name_of_variant_call(&call.func)?;
                self.datatype_for_scoped_type_name(&enum_name)
            }
            _ => None,
        }
    }

    /// Whether a wildcard-less `match` is genuinely EXHAUSTIVE, so the
    /// last-arm-as-`_` rewrite in `expr_to_scoped_string` is sound. A wildcard-less
    /// exhaustive match is necessarily an ALL-VARIANTS enum match or a BOTH-VALUES
    /// bool match; anything else — a NON-exhaustive enum match (rustc-invalid, but
    /// the syn file-path never exhaustiveness-checks) or an int/other match — is
    /// treated as non-exhaustive so the rewrite is skipped and the encoder
    /// fail-closes. Prevents the false-verify where `match x { A(_)=>10, B(_)=>20 }`
    /// with `x` an uncovered `C` pinned `C` to the last arm (20) and verified a
    /// false postcondition. Conservative: any pattern shape it cannot classify
    /// (an unqualified unit-variant `Pat::Ident`, a `use`-imported bare variant)
    /// makes the match non-exhaustive here — sound (fail-closed), never a
    /// false-verify.
    fn match_is_exhaustive(&self, expr_match: &syn::ExprMatch) -> bool {
        use std::collections::BTreeSet;
        if expr_match.arms.is_empty() {
            return false;
        }
        // Bool: both `true` and `false` covered.
        if expr_match
            .arms
            .iter()
            .all(|arm| pat_bool_literal(&arm.pat).is_some())
        {
            let bools: BTreeSet<bool> = expr_match
                .arms
                .iter()
                .filter_map(|arm| pat_bool_literal(&arm.pat))
                .collect();
            return bools.len() == 2;
        }
        // Enum: every arm a variant pattern of ONE enum, covering ALL its variants.
        let mut enum_name: Option<String> = None;
        let mut covered: BTreeSet<String> = BTreeSet::new();
        for arm in &expr_match.arms {
            let Some((en, vn)) = pat_enum_variant(&arm.pat) else {
                return false;
            };
            match &enum_name {
                None => enum_name = Some(en),
                Some(existing) if *existing != en => return false,
                _ => {}
            }
            covered.insert(vn);
        }
        let Some(en) = enum_name else {
            return false;
        };
        let Some(TrustVcType::Datatype { variants, .. }) = self.datatype_for_scoped_type_name(&en)
        else {
            return false;
        };
        let all: BTreeSet<String> = variants.iter().map(|v| v.name.clone()).collect();
        !all.is_empty() && all.iter().all(|v| covered.contains(v))
    }

    fn direct_mut_reference_target(&self, expr: &Expr) -> Option<ErasedMutRefTarget> {
        match strip_place_wrappers(expr) {
            Expr::Reference(reference) if reference.mutability.is_some() => {
                self.mutable_reference_place_target(&reference.expr)
            }
            _ => None,
        }
    }

    fn mutable_reference_place_target(&self, expr: &Expr) -> Option<ErasedMutRefTarget> {
        match strip_place_wrappers(expr) {
            Expr::Path(_) => {
                let name = expr_path_ident(expr)?;
                self.has_scoped_name(&name)
                    .then_some(ErasedMutRefTarget::Local(name))
            }
            Expr::Field(field) => {
                let syn::Member::Named(member) = &field.member else {
                    return None;
                };
                let owner = expr_path_ident(&field.base)?;
                if !self.has_scoped_name(&owner) || self.scoped_struct_type_name(&owner).is_none() {
                    return None;
                }
                Some(ErasedMutRefTarget::Field {
                    owner,
                    member: member.to_string(),
                })
            }
            Expr::Index(index) => {
                let owner = expr_path_ident(&index.expr)?;
                (self.has_scoped_name(&owner) || self.vc.has_variable(&owner)).then_some(
                    ErasedMutRefTarget::Index {
                        owner,
                        index: index.index.to_token_stream().to_string(),
                    },
                )
            }
            Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                let alias = expr_path_ident(&unary.expr)?;
                self.erased_mut_ref_target_name(&alias)
            }
            _ => None,
        }
    }

    fn direct_deref_mut_reference_assignment_target(
        &self,
        expr: &Expr,
    ) -> Option<ErasedMutRefTarget> {
        let Expr::Unary(unary) = strip_place_wrappers(expr) else {
            return None;
        };
        if !matches!(unary.op, syn::UnOp::Deref(_)) {
            return None;
        }
        self.direct_mut_reference_target(&unary.expr)
    }

    fn local_mut_reference_target(&self, local: &syn::Local) -> Option<ErasedMutRefTarget> {
        let init = local.init.as_ref()?;
        self.direct_mut_reference_target(&init.expr)
            .or_else(|| self.param_mut_reference_alias_target(local, &init.expr))
            .or_else(|| self.reborrow_mut_reference_alias_target(local, &init.expr))
    }

    fn param_mut_reference_alias_target(
        &self,
        local: &syn::Local,
        init: &Expr,
    ) -> Option<ErasedMutRefTarget> {
        if !local_pat_is_mut_reference(&local.pat) {
            return None;
        }
        let name = expr_path_ident(init)?;
        self.supported_mut_ref_param_targets
            .contains(&name)
            .then_some(ErasedMutRefTarget::Local(name))
    }

    fn reborrow_mut_reference_alias_target(
        &self,
        local: &syn::Local,
        init: &Expr,
    ) -> Option<ErasedMutRefTarget> {
        if !local_pat_is_mut_reference(&local.pat) {
            return None;
        }
        let alias = expr_path_ident(init)?;
        self.erased_mut_ref_target_name(&alias)
    }

    fn mark_unsupported_index_receiver(&mut self, name: &str) {
        if self.unsupported_index_receivers.is_empty() {
            self.unsupported_index_receivers.push(BTreeSet::new());
        }
        let index = self.unsupported_index_receivers.len() - 1;
        self.unsupported_index_receivers[index].insert(name.to_string());
    }

    fn is_unsupported_index_receiver(&self, name: &str) -> bool {
        for (scope, unsupported) in self
            .scopes
            .iter()
            .zip(&self.unsupported_index_receivers)
            .rev()
        {
            if unsupported.contains(name) {
                return true;
            }
            if scope.contains_key(name) {
                return false;
            }
        }
        false
    }

    fn shadow_names(&mut self, names: &BTreeSet<String>) {
        for name in names {
            self.shadow_name(name);
        }
    }

    fn shadow_pat_bindings(&mut self, pat: &Pat) {
        let names = bound_idents_from_pat(pat);
        self.shadow_names(&names);
    }

    fn with_isolated_scopes(&mut self, f: impl FnOnce(&mut Self)) {
        let saved_scopes = self.scope_snapshot();
        f(self);
        self.restore_scope_snapshot(saved_scopes);
    }

    fn with_temporary_scopes<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved_scopes = self.scope_snapshot();
        let result = f(self);
        self.restore_scope_snapshot(saved_scopes);
        result
    }

    /// Renders a `match` arm guard expression with the arm pattern's bindings
    /// substituted to their scrutinee projections, so the guard becomes a
    /// condition over the scrutinee (e.g. `x if x == 0` => `scrutinee == 0`).
    /// Returns `None` when the pattern binds names that cannot be projected onto
    /// the scrutinee (so the guard cannot be soundly rendered over it).
    fn render_arm_guard(
        &mut self,
        guard: &Expr,
        pat: &Pat,
        scrutinee: &str,
        scrutinee_ty: Option<&TrustVcType>,
    ) -> Option<String> {
        // A guard over a MULTI-disjunct or-pattern cannot be rendered from one
        // merged binding: Rust retries LATER disjuncts when the guard fails for
        // an earlier matching one (`(true, a) | (a, false) if a` re-binds `a`
        // and re-checks), so a single first-match substitution would model the
        // wrong selection. Fail closed — the arm becomes unguardable, which
        // drops its assume-side hypotheses rather than mis-scoping them.
        if matches!(pat, Pat::Or(or_pat) if or_pat.cases.len() > 1) {
            return None;
        }
        let bindings = bound_idents_from_pat(pat);
        if !bindings.is_empty() {
            // The guard may reference the pattern bindings; we must be able to
            // express each as a scrutinee projection or we cannot render soundly.
            let ty = scrutinee_ty?;
            let projected = pattern_bindings_for_scoped_value(pat, scrutinee, ty)?;
            let projected_names: BTreeSet<String> =
                projected.iter().map(|(name, _)| name.clone()).collect();
            if !bindings.is_subset(&projected_names) {
                return None;
            }
            Some(self.with_temporary_scopes(|collector| {
                for (name, value) in &projected {
                    collector
                        .current_scope_mut()
                        .insert(name.clone(), value.clone());
                }
                collector.expr_to_scoped_string(guard)
            }))
        } else {
            Some(self.expr_to_scoped_string(guard))
        }
    }

    fn parse_calc_macro(&mut self, mac: &Macro, name: &str) -> TrustVcResult<Vec<String>> {
        let block = parse_calc(mac.tokens.clone()).map_err(|source| TrustVcError::Encoding {
            context: "extract body assertions",
            detail: format!(
                "Failed to parse {}!() block — this would silently drop calc proof obligations: {}",
                name, source
            ),
        })?;

        let mut step_conditions = Vec::with_capacity(block.operators.len());
        let calc_index = self.next_assertion_index;
        self.next_assertion_index += 1;
        let n_steps = block.operators.len();

        for (index, op) in block.operators.iter().copied().enumerate() {
            let lhs = block.expressions.get(index).ok_or_else(|| {
                calc_encoding_error("parsed calc block is missing a step lhs expression")
            })?;
            let rhs = block.expressions.get(index + 1).ok_or_else(|| {
                calc_encoding_error("parsed calc block is missing a step rhs expression")
            })?;
            let condition = self.format_calc_condition(lhs, op, rhs);
            let scoped = self.extract_calc_proof_block(&block.proof_blocks[index])?;
            let name = format!("calc_{calc_index}_step_{}", index + 1);
            self.vc.add_assert_by(&name, &condition, scoped);
            if let Some(last) = self.vc.obligations.last_mut() {
                last.step_meta = Some(ProofStepMeta::new(
                    name,
                    format!("calc step {} of {n_steps}", index + 1),
                ));
            }
            step_conditions.push(condition);
        }

        if n_steps > 1 {
            let overall_op = block
                .overall_op_hint
                .or_else(|| transitive_op(&block.operators))
                .ok_or_else(|| {
                    calc_encoding_error(
                        "calc! operators are incompatible: cannot derive a transitive conclusion",
                    )
                })?;
            let first = block.expressions.first().ok_or_else(|| {
                calc_encoding_error("parsed calc block is missing its initial expression")
            })?;
            let last = block.expressions.last().ok_or_else(|| {
                calc_encoding_error("parsed calc block is missing its final expression")
            })?;
            let condition = self.format_calc_condition(first, overall_op, last);
            let scoped = step_conditions
                .iter()
                .enumerate()
                .map(|(index, condition)| {
                    ProofObligation::assume(
                        format!("calc_{calc_index}_conclusion_step_{}", index + 1),
                        condition.clone(),
                    )
                })
                .collect::<Vec<_>>();
            let name = format!("calc_{calc_index}_conclusion");
            self.vc.add_assert_by(&name, &condition, scoped);
            if let Some(last) = self.vc.obligations.last_mut() {
                last.step_meta = Some(ProofStepMeta::new(name, "calc conclusion"));
            }
        }

        Ok(Vec::new())
    }

    fn extract_calc_proof_block(
        &mut self,
        proof: &proc_macro2::TokenStream,
    ) -> TrustVcResult<Vec<ProofObligation>> {
        if proof.is_empty() {
            return Ok(Vec::new());
        }
        if let Some(err) = self.parse_error.take() {
            return Err(err);
        }
        let block = syn::parse2::<syn::Block>(quote::quote!({ #proof })).map_err(|source| {
            TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse calc! proof block — this would silently drop scoped calc proof obligations: {source}"
                ),
            }
        })?;

        let saved_scopes = self.scope_snapshot();
        let start_len = self.vc.obligations.len();
        // Slice-C remediation: proof context must not mutate exec state, and
        // this visit is snapshot-discarded — a deref write in here fails
        // closed at the funnel.
        self.deref_write_rollback_depth += 1;
        self.visit_block(&block);
        self.deref_write_rollback_depth -= 1;
        let scoped = self.vc.obligations.split_off(start_len);
        self.restore_scope_snapshot(saved_scopes);
        if let Some(err) = self.parse_error.take() {
            return Err(err);
        }
        Ok(scoped)
    }

    fn extract_assert_by_contradiction_proof_block(
        &mut self,
        proof: &proc_macro2::TokenStream,
    ) -> TrustVcResult<Vec<ProofObligation>> {
        self.extract_scoped_proof_block(proof, "assert_by_contradiction")
    }

    /// Extract the obligations produced by a `{ .. }` proof block into a SCOPED
    /// obligation list (the `assert_by_scopes` entry) rather than the top-level
    /// stream.
    ///
    /// The surrounding scope snapshot is saved and restored around the visit, so
    /// block-local `let` bindings do not escape the block — the same
    /// let-shadowing boundary the session path gets from restoring
    /// `local_let_bindings` at scope close.
    fn extract_scoped_proof_block(
        &mut self,
        proof: &proc_macro2::TokenStream,
        macro_name: &str,
    ) -> TrustVcResult<Vec<ProofObligation>> {
        let block = syn::parse2::<syn::Block>(proof.clone()).map_err(|source| {
            TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse {macro_name}! proof block — this would silently drop scoped proof obligations: {source}"
                ),
            }
        })?;
        if block.stmts.is_empty() {
            return Ok(Vec::new());
        }
        if let Some(err) = self.parse_error.take() {
            return Err(err);
        }

        let saved_scopes = self.scope_snapshot();
        let start_len = self.vc.obligations.len();
        // Slice-C remediation: proof context must not mutate exec state, and
        // this visit is snapshot-discarded — a deref write in here fails
        // closed at the funnel.
        self.deref_write_rollback_depth += 1;
        self.visit_block(&block);
        self.deref_write_rollback_depth -= 1;
        let scoped = self.vc.obligations.split_off(start_len);
        self.restore_scope_snapshot(saved_scopes);
        if let Some(err) = self.parse_error.take() {
            return Err(err);
        }
        Ok(scoped)
    }

    /// `source_names` are the binder names as WRITTEN; `renames` maps any binder
    /// that was alpha-renamed (because it collided with a program variable) to
    /// its fresh solver symbol. The proof block must see the same mapping as the
    /// quantified condition, or an `assert!(f(i))` inside the block would refer
    /// to the outer program `i` instead of the binder.
    fn extract_assert_forall_by_proof_block(
        &mut self,
        proof: &syn::Block,
        source_names: &[String],
        renames: &BTreeMap<String, String>,
    ) -> TrustVcResult<Vec<ProofObligation>> {
        if proof.stmts.is_empty() {
            return Ok(Vec::new());
        }
        if let Some(err) = self.parse_error.take() {
            return Err(err);
        }

        let saved_scopes = self.scope_snapshot();
        let start_len = self.vc.obligations.len();
        self.push_scope();
        for name in source_names {
            let target = renames.get(name).map_or(name.as_str(), String::as_str);
            self.shadow_name_as(name, target);
        }
        // Slice-C remediation: proof context must not mutate exec state, and
        // this visit is snapshot-discarded — a deref write in here fails
        // closed at the funnel.
        self.deref_write_rollback_depth += 1;
        self.visit_block(proof);
        self.deref_write_rollback_depth -= 1;
        let scoped = self.vc.obligations.split_off(start_len);
        self.restore_scope_snapshot(saved_scopes);
        if let Some(err) = self.parse_error.take() {
            return Err(err);
        }
        Ok(scoped)
    }

    fn format_calc_condition(&mut self, lhs: &Expr, op: CalcOp, rhs: &Expr) -> String {
        format!(
            "{} {} {}",
            self.expr_to_scoped_string(lhs),
            op.to_tokens(),
            self.expr_to_scoped_string(rhs)
        )
    }
}

impl<'ast> Visit<'ast> for AssertionCollector<'_> {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.push_scope();
        for stmt in &block.stmts {
            self.visit_stmt(stmt);
        }
        self.pop_scope();
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        if self.parse_error.is_some() {
            return;
        }
        match stmt {
            Stmt::Local(local) => {
                // Phase C closure reflection: intercept `let f = trust_vc::closure!(..)`
                // at the BINDING site so the bound name `f` is threaded into the
                // co-located def-side + reflection emission. Anonymous forms
                // (`let _ = closure!(..)`, statement-position closures) keep the
                // binding-less def-side path via `visit_expr_macro`. A closure value
                // has no scalar model to bind, so the generic let processing is
                // skipped for this init.
                if let Some(init) = local.init.as_ref() {
                    if let Expr::Macro(expr_macro) = strip_paren_group_expr(&init.expr) {
                        if is_trust_vc_closure_expr_macro(expr_macro) {
                            let binding = local_ident(&local.pat);
                            self.emit_closure_def_side_obligation(
                                &expr_macro.mac,
                                binding.as_deref(),
                            );
                            return;
                        }
                    }
                }
                let value = self.local_init_scoped_value(local);
                let erased_mut_ref_target = self.local_mut_reference_target(local);
                let scoped_struct_type =
                    self.local_scoped_struct_type_name(local, erased_mut_ref_target.as_ref());
                let concrete_value = self.local_init_is_concrete(local);
                if let Some(init) = local.init.as_ref() {
                    self.visit_expr(&init.expr);
                    if let Some((_, diverge)) = &init.diverge {
                        self.visit_expr(diverge);
                    }
                }
                if let Some(condition) = self.local_let_else_match_condition(local) {
                    let diverge_returns = local
                        .init
                        .as_ref()
                        .and_then(|init| init.diverge.as_ref())
                        .is_some_and(|(_, diverge)| contains_return_expr(diverge));
                    if condition != "true" && !diverge_returns {
                        self.add_assumption(condition);
                    }
                }
                if let (Some(init), Some(scoped)) = (local.init.as_ref(), value.as_ref()) {
                    self.maybe_emit_exec_arith_overflow_check(&init.expr, scoped);
                }
                // SOUNDNESS (#81): an exec `let _ = a[i];` / `let x = a[i];`
                // discards an array/slice access whose bound never reaches an
                // assertion. When the initializer is not itself a top-level
                // checked-arith/shift expression (those already pin a reflexive
                // that fires the bound on the whole RHS), pin the bound on each
                // value-position index access in it.
                if let Some(init) = local.init.as_ref() {
                    if !rhs_is_checked_scalar_arithmetic(&init.expr)
                        && !rhs_is_checked_bit_shift(&init.expr)
                    {
                        self.emit_exec_index_bounds_checks_in_expr(&init.expr);
                        // SOUNDNESS-CRITICAL (exec scalar arithmetic): the top-level
                        // `maybe_emit_exec_arith_overflow_check` above only pinned a
                        // checked-arith/shift RHS at the OUTERMOST position (its pin
                        // already fires every arithmetic precheck nested in an
                        // arithmetic spine). When the initializer is NOT itself a
                        // top-level arithmetic/shift expression, an arithmetic site
                        // nested in a tuple / array / struct literal or a call
                        // argument (`let _ = (a / b, 0);`) carried no obligation —
                        // pin the safety check on each such nested site.
                        self.emit_exec_arith_safety_checks_in_expr(&init.expr);
                    }
                }
                self.bind_local_with_value(
                    local,
                    value,
                    erased_mut_ref_target,
                    concrete_value,
                    scoped_struct_type,
                );
            }
            Stmt::Expr(expr, _) => {
                self.visit_expr(expr);
                // SOUNDNESS (#81): a bare `a[i];` (or a tail `a[i]`) discards an
                // array/slice access whose bound never reaches an assertion. Pin
                // the bound on each value-position index access. Assignment /
                // compound-assignment statements (`a[i] = v;` / `a[i] += v;`) are
                // routed by `visit_expr` to the write SITES, which emit their own
                // bound + element safety; the collector skips assignment binops
                // and `Expr::Assign`, so this never double-instruments them.
                self.emit_exec_index_bounds_checks_in_expr(expr);
                // SOUNDNESS-CRITICAL (exec scalar arithmetic): a bare `a / b;` /
                // `a % b;` (or a tail arithmetic expression) discards an arithmetic
                // site whose overflow / divide-by-zero panic never reaches an
                // assertion. Unlike the `let`/assign paths there is no top-level
                // `maybe_emit_exec_arith_overflow_check` here, so pin the safety
                // obligation on every value-position arithmetic site in the
                // statement (top-level and nested).
                self.emit_exec_arith_safety_checks_in_expr(expr);
            }
            Stmt::Macro(stmt_macro) => match self.expand_local_macro_stmt(&stmt_macro.mac) {
                Ok(true) => {}
                // Thread the STATEMENT-level attrs so a
                // `#[verifier::proof_note("…")] assert!(…);` label is pooled
                // with any expression-level label inside the macro tokens.
                Ok(false) => {
                    self.visit_assertion_macro_with_attrs(&stmt_macro.mac, &stmt_macro.attrs)
                }
                Err(err) => self.parse_error = Some(err),
            },
            Stmt::Item(item) => self.visit_item(item),
        }
    }

    fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
        if self.parse_error.is_some() {
            return;
        }
        // Keep the invoked-exec-closure binding in sync with a reassignment of a
        // simple local (`g = |..| ..;` re-records the new body; `g = other;` clears
        // the stale body so a later `g(args)` is not instrumented with the wrong
        // closure). Part of #2778 invoked-exec-closure body arith.
        if let Some(name) = expr_path_ident(assign.left.as_ref()) {
            self.record_or_clear_exec_closure_def(&name, Some(assign.right.as_ref()));
        }
        let direct_deref_target =
            self.direct_deref_mut_reference_assignment_target(assign.left.as_ref());
        let right_mut_ref_target = self.direct_mut_reference_target(&assign.right);
        match strip_place_wrappers(assign.left.as_ref()) {
            Expr::Index(index) => {
                self.visit_expr(&index.expr);
                self.visit_expr(&index.index);
            }
            other => self.visit_expr(other),
        }
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&assign.right);
        if self.parse_error.is_some() {
            return;
        }
        // SOUNDNESS (#81): for an index-write `a[i] = v`, emit the write-index
        // bound (resolving the old element `a[i]` fires `add_seq_index_bounds_check`
        // for the same `i < len` precondition the discarded `update` would carry)
        // and the read bound for any index access in the RHS value — BEFORE
        // `assign_expr` rewrites the scope. This dispatch runs only on the
        // obligation path (the value-computation path uses `eval_scoped_stmts`),
        // and covers every index-write sub-path (simple / mut-ref-alias /
        // struct-field / nested) uniformly. Scalar-target assigns (`x = a[i]`)
        // get their RHS read bound inside `assign_expr`.
        if matches!(strip_place_wrappers(assign.left.as_ref()), Expr::Index(_)) {
            let lhs = strip_place_wrappers(assign.left.as_ref());
            self.emit_exec_index_bounds_checks_in_expr(lhs);
            self.emit_exec_index_bounds_checks_in_expr(&assign.right);
        }
        if !self.assign_expr(assign, direct_deref_target, right_mut_ref_target, true)
            && self.parse_error.is_none()
        {
            if assignment_target_uses_erased_mut_ref_alias(assign.left.as_ref(), self) {
                self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                    assign.left.as_ref(),
                ));
            } else if matches!(strip_place_wrappers(assign.left.as_ref()), Expr::Index(_)) {
                self.parse_error = Some(unsupported_index_assignment_error(assign.left.as_ref()));
            }
        }
    }

    fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
        if self.parse_error.is_some() {
            return;
        }
        if is_assignment_binop(&binary.op) {
            if let Expr::Index(index) = strip_place_wrappers(binary.left.as_ref()) {
                self.visit_expr(&index.expr);
                self.visit_expr(&index.index);
            } else {
                self.visit_expr(&binary.left);
            }
            if self.parse_error.is_some() {
                return;
            }
            self.visit_expr(&binary.right);
            if self.parse_error.is_some() {
                return;
            }
            if matches!(strip_place_wrappers(binary.left.as_ref()), Expr::Index(_)) {
                // Obligation path: emit the compound element-safety obligation
                // (write-index bound + element overflow) inside `assign_compound_expr`.
                if !self.assign_compound_expr(binary, true) && self.parse_error.is_none() {
                    self.parse_error =
                        Some(unsupported_index_compound_assignment_error(&binary.op));
                }
            } else if is_deref_assignment_target(binary.left.as_ref()) {
                // Slice C: obligation walk for `*P op= rhs` — desugars to the
                // single-write funnel (which emits the deref-write RHS safety
                // obligations); unsupported deref shapes keep the pre-existing
                // fail-closed rejection inside the helper.
                self.assign_deref_compound_expr(binary, true);
            } else if let Some(name) = expr_path_ident(&binary.left) {
                // SOUNDNESS-CRITICAL (exec scalar compound `a OP= b`): the implicit
                // `a OP b` carries the same overflow / divide-by-zero / shift-bounds
                // panic obligation Verus checks at the site, yet the scalar-compound
                // path previously only `invalidate_scoped`d the target and emitted
                // NOTHING — so `total /= count;` / `acc += x;` (operands unbounded)
                // silently `Verified` a guaranteed runtime panic. Synthesize the
                // updated value `(old_a) OP (b)` and pin it reflexively (mirroring
                // the array-element compound `maybe_emit_exec_compound_element_safety`),
                // firing the arithmetic precheck. The value is built from the SINGLE
                // resolved `old_a` / `b` renderings (the reflexive obligation itself
                // updates no binding, and the straight-line rebind below reuses the
                // SAME renderings, so neither side effect is duplicated). The
                // arithmetic RHS is also walked for any nested
                // arithmetic site (covering bitwise compounds like `a ^= x / y`,
                // whose `OP` needs no check but whose `x / y` does). Done BEFORE
                // `invalidate_scoped` so `old_a` still resolves.
                if let Some(op) = compound_assignment_value_op(&binary.op) {
                    if matches!(op, "+" | "-" | "*" | "/" | "%" | "<<" | ">>") {
                        // Render `old_a` / `b` over the fresh loop-body havoc
                        // symbols inside a loop body, so `x += 100` is checked
                        // against `x`'s arbitrary loop-body-entry value (the closed
                        // hole) rather than its function-entry value. Outside a loop
                        // body this is the ordinary scoped rendering.
                        let value = self.render_with_loop_body_havoc(|c| {
                            let old_value = c.lookup_scoped(&name);
                            let rhs = c.expr_to_scoped_string(&binary.right);
                            format!("({old_value}) {op} ({rhs})")
                        });
                        self.maybe_emit_exec_scalar_compound_safety(&value);
                    }
                }
                self.emit_exec_arith_safety_checks_in_expr(&binary.right);
                // Straight-line local scalar read-modify-write: desugar `x op=
                // rhs` to `x = (x) op (rhs)` so LATER reads of `x` resolve.
                // Previously the binding was unconditionally invalidated, so any
                // subsequent read failed closed as `unresolved variable` (sound
                // but incomplete — blocks upstream basic.rs test_compound_assign
                // `x += 2; assert(x == 3)`). Mirrors the slice-C deref desugar
                // (`assign_deref_compound_expr`) and REUSES the same `old_a` /
                // `rhs` renderings the safety obligation above range-checked, so
                // the persisted value cannot disagree with what was checked. Kept
                // fail-closed (invalidate) exactly where the read-then-rebind
                // would be unsound: inside a loop body (the scoped read is the
                // previous VISIT's value, not the previous ITERATION's — the same
                // guard the deref desugar carries); when the RHS embeds an
                // assignment (real compound evaluates the RHS BEFORE reading the
                // place, the desugar reads first); a non-value op; or an
                // unbound/shadowed-away target.
                let can_rebind_local_compound = self.loop_body_depth == 0
                    && !expr_contains_assignment(&binary.right)
                    && self
                        .scopes
                        .iter()
                        .any(|scope| scope.contains_key(name.as_str()));
                match compound_assignment_value_op(&binary.op).filter(|_| can_rebind_local_compound)
                {
                    Some(op) => {
                        let old_value = self.lookup_scoped(&name);
                        let rhs = self.expr_to_scoped_string(&binary.right);
                        self.assign_scoped(&name, format!("(({old_value}) {op} ({rhs}))"));
                    }
                    None => self.invalidate_scoped(&name),
                }
            } else if assignment_target_uses_erased_mut_ref_alias(binary.left.as_ref(), self) {
                self.parse_error = Some(unsupported_mut_ref_projection_assignment_error(
                    binary.left.as_ref(),
                ));
            }
        } else if matches!(binary.op, syn::BinOp::And(_) | syn::BinOp::Or(_)) {
            // SOUNDNESS-CRITICAL (short-circuit RHS conditional evaluation,
            // slice-D remediation p8/p8b): the RIGHT operand of `&&` / `||`
            // runs only when the LEFT does not short-circuit, and that
            // conditionality is invisible to `path_conditions`. Raise
            // `short_circuit_rhs_depth` around the RHS visit so a
            // state-transition assume established inside it (a `&mut`-arg
            // call's `__call_ensures_*`, a bare `assume!`, a post-loop exit
            // fact) is DROPPED rather than leaked unconditionally into the
            // surrounding straight-line context. The LHS is ALWAYS evaluated
            // and is visited outside the raise; obligations we PROVE
            // (call-site `requires`, `assert!`, arith safety) and the
            // `&mut`-arg havoc are untouched (fail-closed / sound).
            self.visit_expr(&binary.left);
            self.short_circuit_rhs_depth += 1;
            self.visit_expr(&binary.right);
            self.short_circuit_rhs_depth -= 1;
        } else {
            visit::visit_expr_binary(self, binary);
        }
    }

    fn visit_expr_reference(&mut self, reference: &'ast syn::ExprReference) {
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&reference.expr);
        // Slice D: a literal `&mut v` CALL-ARGUMENT node whose referent the
        // `&mut`-call-arg havoc already rebound to a fresh post-call symbol —
        // the borrow is a call-scoped temporary (no alias survives the call)
        // and the fresh symbol IS its mutation model, so the general
        // borrow-escape invalidation below must not drop it. Consumed per node
        // visit; every other `&mut v` keeps the fail-closed invalidation.
        if self
            .mut_ref_call_arg_reference_havocs
            .remove(&(reference as *const syn::ExprReference as usize))
        {
            return;
        }
        if reference.mutability.is_some() {
            if let Some(name) = expr_path_ident(&reference.expr) {
                // SLICE-D REMEDIATION (p1/p2/p4/p19/p23/p44): a mutable borrow
                // of a bare binding escaping through ANY unowned shape must
                // never leave a DECLARED variable resolving to its
                // entry-pinned symbol — havoc it to a fresh unconstrained
                // symbol (undeclared locals keep the fail-closed invalidate).
                // The literal `&mut v` argument of an owned contracted/tracked
                // free call never reaches here (the
                // `mut_ref_call_arg_reference_havocs` skip above).
                self.havoc_mut_borrow_escaped_binding(&name);
            } else if matches!(
                strip_place_wrappers(&reference.expr),
                Expr::Field(_) | Expr::Index(_)
            ) {
                // REBORROW of a STRUCT SUB-PLACE (`&mut o.inner`): the alias grants
                // mutable access to a sub-field of a struct binding, and the body
                // model does NOT track a `&mut self` method mutation flowing through
                // it (`let a = &mut o.inner; a.bump();`). The only sound model is to
                // forget the root struct's value now (a later read of `o.inner.x`
                // then sees arbitrary state), closing the reborrow-alias laundered
                // mutation false `Verified`.
                //
                // SCOPE: restricted to STRUCT roots. Scalar (`&mut *b`) and array
                // (`&mut a[i]`) sub-place reborrows are PRECISELY tracked by the
                // erased-mut-ref deref-assignment machinery (`*b = v` updates the
                // owner + aliases), so havocing there would over-reject a sound
                // alias assignment. Collection sub-place reborrows in a loop are
                // covered by the loop modified-var collector; the straight-line
                // collection form already fails closed via the place-mutation
                // postcondition reject.
                if let Some(root) = field_index_projection_root(&reference.expr) {
                    if self.receiver_struct_type_name(&root).is_some() {
                        self.havoc_struct_receiver(&root);
                    }
                }
            }
        }
    }

    fn visit_expr_index(&mut self, index: &'ast syn::ExprIndex) {
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&index.expr);
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&index.index);
        if self.parse_error.is_some() {
            return;
        }
        let Some(name) = expr_path_ident(&index.expr) else {
            return;
        };
        let receiver = self.lookup_scoped(&name);
        if let (Some(len), Some(index_value)) = (
            scoped_vec_literal_len(&receiver),
            literal_usize_index_expr(&index.index),
        ) {
            if index_value >= len {
                self.parse_error = Some(out_of_bounds_vec_literal_index_error(
                    &Expr::Index(index.clone()),
                    index_value,
                    len,
                ));
            }
        }
    }

    fn visit_expr_method_call(&mut self, method_call: &'ast syn::ExprMethodCall) {
        if self.parse_error.is_some() {
            return;
        }
        if self.assign_local_push_method_call(method_call)
            || self.assign_local_set_method_call(method_call)
            || self.assign_local_vec_insert_method_call(method_call)
            || self.assign_local_vec_remove_method_call(method_call)
            || self.assign_local_vec_pop_method_call(method_call)
            || self.assign_local_vec_clear_method_call(method_call)
            || self.assign_local_vec_truncate_method_call(method_call)
            || self.assign_local_vec_swap_remove_method_call(method_call)
            || self.assign_local_vec_append_method_call(method_call)
            || self.assign_local_vec_extend_method_call(method_call)
            || self.assign_local_vec_split_off_method_call(method_call)
            || self.assign_local_vec_drain_method_call(method_call)
            || self.assign_local_vec_resize_method_call(method_call)
        {
            return;
        }
        if self.parse_error.is_some() {
            return;
        }
        let handled_option_closure = self.record_option_closure_contract_call(method_call);
        if self.parse_error.is_some() {
            return;
        }
        // This is the TRUE chokepoint for both `a.f();` (Stmt::Expr) and
        // `let _g = a.f();` (Stmt::Local init); rendering-only paths such as
        // `format_method_call_expr` are NOT reached for a discarded statement.
        self.record_trait_method_contract_call(method_call);
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&method_call.receiver);
        if !handled_option_closure {
            for arg in &method_call.args {
                self.visit_expr(arg);
            }
        }
        // SOUNDNESS-CRITICAL: a `&mut` NON-self ARGUMENT of a method call
        // (`h.hit(t)`, `h.bump(t)`) is framed by nothing else — the free-call
        // havoc keys on `ExprCall`. Runs after the argument sub-visits so their
        // own renderings still see the pre-call state, and BEFORE the receiver
        // mutation block below, which owns the receiver and only the receiver.
        self.havoc_mut_ref_method_call_args(method_call);
        if let Some(name) = expr_path_ident(&method_call.receiver) {
            // GAP2: a pure ghost-collection combinator (e.g. `s.filter(..)`,
            // `s.map(..)`) does not mutate its receiver, so the binding must
            // survive — otherwise a reused `let s = Set::new(..)` is lost after
            // the first use ("unresolved variable s"). Every other method on a
            // path-ident receiver is still conservatively forgotten (fail-closed)
            // so a genuinely-mutated receiver (e.g. `v.clear()`/`v.pop()`/
            // `hs.insert(..)`) never carries stale pre-mutation state forward.
            let method = method_call.method.to_string();
            if !self.method_call_preserves_receiver(&name, &method) {
                // USER-STRUCT mutation (straight-line sibling of the catastrophic
                // collection-mutation gap): `invalidate_scoped` only drops a scoped
                // rewrite — for a parameter/binding with no rewrite, `name` still
                // resolves to its constrained ENTRY symbol, so a later read of a
                // struct receiver mutated by `s.bump()` (&mut self) would see the
                // stale pre-call value (a false `Verified`). When the resolved
                // method may mutate the caller's binding, havoc the receiver to a
                // fresh unconstrained symbol. A pure `&self`/by-value reader is NOT
                // havocked (NO over-rejection). Resolve the struct type BEFORE
                // `invalidate_scoped`, which clears the scoped struct-type record.
                let mutated_struct = self
                    .receiver_struct_type_name(&name)
                    .filter(|struct_type| self.struct_method_mutates_caller(struct_type, &method));
                // COLLECTION-RECEIVER mutation (the straight-line sibling of the
                // catastrophic loop / postcondition collection-mutation gaps): a
                // `&mut Vec`/`&mut HashSet`/`&mut HashMap` parameter is modeled as a
                // ghost `Seq`/`Set`/`Map`, so `receiver_struct_type_name` is `None`
                // and the struct havoc above never fires. The already-MODELED
                // re-bind mutators (`push`/`set`/`insert`/`remove`/`swap_remove`/
                // `append`) returned earlier (or fail-closed), so any method that
                // reaches here on a collection receiver and is NOT a recognized pure
                // `&self` read (`len`/`index`/`contains`/`get`/`iter`/the pure ghost
                // combinators) is an unmodeled in-place mutation (`clear`/`pop`/
                // `truncate`/`drain`/`retain`/`extend`/`sort`/`dedup`/…). Without a
                // havoc the bare parameter still resolves to its precondition-pinned
                // ENTRY symbol, so a later `v.len()`/`v[i]`/`s.contains(..)` in an
                // in-body `assert!` reads stale pre-mutation state — a false
                // `Verified`. Havoc the receiver to a fresh, unconstrained
                // collection symbol (computed BEFORE `invalidate_scoped`, which
                // clears the ghost-collection / scoped records). A pure read keeps
                // the binding (NO over-rejection); a true post-mutation claim is
                // Unknown (sound) rather than wrongly discharged.
                let mutated_collection = mutated_struct.is_none()
                    && self.receiver_is_collection_like(&name)
                    && !is_pure_collection_read_method(&method);
                // GENERIC-RECEIVER mutation (`fn g<T: Tr>(t: &mut T)`, and its
                // `&mut impl Tr` sugar): the receiver is a bare `TypeParam`, so
                // neither the struct nor the collection branch above can see it,
                // and an `&mut self` trait call was a NO-OP on the caller's
                // binding — the bound-method UF `Tr__a(t)` is a function OF the
                // receiver term, so two reads bracketing `t.bump()` collapsed to
                // one term and a false claim about their difference verified.
                // `havoc_declared_binding_to_fresh` mints a fresh symbol of the
                // receiver's own declared type, which is exactly what makes the
                // post-call `Tr__a(t')` an independent, unconstrained term.
                let mutated_type_param = mutated_struct.is_none()
                    && !mutated_collection
                    && self.type_param_method_mutates_caller(&name, &method);
                self.invalidate_scoped(&name);
                if mutated_struct.is_some() {
                    self.havoc_struct_receiver(&name);
                } else if mutated_type_param {
                    self.havoc_declared_binding_to_fresh(&name);
                } else if mutated_collection {
                    // `havoc_declared_binding_to_fresh` mints a fresh symbol of the
                    // receiver's declared collection type and rebinds the scoped
                    // value to it. For a declared `&mut <collection>` parameter this
                    // is always available; an undeclared scoped-only ghost-collection
                    // local has no entry-pinned bare symbol, so the preceding
                    // `invalidate_scoped` already leaves it fail-closed (a later read
                    // is an unresolved variable, not a stale value).
                    self.havoc_declared_binding_to_fresh(&name);
                }
            }
        } else if let Some(root) = field_index_projection_root(&method_call.receiver) {
            // FIELD-PROJECTION receiver (`o.inner.bump()`): a method laundered
            // through a field/index projection of a struct binding. When the
            // projected SUB-FIELD's own struct type RESOLVES (the field's declared
            // `Datatype`, walked from the root binding's type), classify the call
            // by the SAME receiver-kind registry the root-receiver path uses: a
            // `&mut self` (or unresolved-non-pure) method havocs the ROOT struct
            // binding (a later read of `o.inner.x` then sees arbitrary state,
            // closing the laundered-mutation false `Verified`), while a pure
            // `&self` sub-field getter — REGARDLESS of name (`o.inner.peek()`,
            // `o.inner.value()`, ...) — is NOT havocked (NO over-rejection).
            // Only when the sub-field type is UNRESOLVABLE do we fall back to the
            // conservative universal pure-read allow-list (fail-closed).
            let method = method_call.method.to_string();
            if self.receiver_struct_type_name(&root).is_some() {
                let mutates = match self.projected_receiver_struct_type(&method_call.receiver) {
                    Some(sub_type) => self.struct_method_mutates_caller(&sub_type, &method),
                    None => !is_known_pure_struct_method(&method),
                };
                if mutates {
                    self.havoc_struct_receiver(&root);
                }
            } else if receiver_field_projection_path(&method_call.receiver)
                .is_some_and(|(_, path)| path.is_empty())
                && self.receiver_is_collection_like(&root)
                && !self.method_call_preserves_receiver(&root, &method)
                && !is_pure_collection_read_method(&method)
            {
                // EXPLICIT-DEREF receiver `(*v).clear()` on a bare COLLECTION place
                // (empty projection path): the deref sibling of the bare-ident
                // collection-mutation havoc above. `field_index_projection_root`
                // peels the deref so `(*v)` lands here with `root == "v"`; an
                // empty projection path distinguishes a bare deref of the
                // collection itself from a struct field projection (`o.inner...`,
                // handled by the struct branch above). A non-pure in-place mutator
                // on the deref'd collection must havoc it for the same reason as
                // the auto-deref `v.clear()` form — otherwise the stale entry
                // length/membership survives. A pure read is left untouched.
                self.havoc_declared_binding_to_fresh(&root);
            }
        }
    }

    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if self.parse_error.is_some() {
            return;
        }
        // SOUNDNESS-CRITICAL: havoc the referent of each `&mut`-passed argument
        // BEFORE recording the helper contract, so an opaque call's mutation is
        // reflected and a contracted helper's `ensures` is re-threaded over the
        // fresh post-call value. See `havoc_mut_ref_call_arg_referents`.
        //
        // The call-site `requires`, however, is a property of the PRE-call
        // state: snapshot the pre-havoc argument renderings first so
        // `add_helper_contract_obligations` substitutes the values the callee
        // actually receives into `requires` (post-havoc rendering made a
        // satisfied precondition unprovable — the fresh `p__havoc_0` is
        // unconstrained — wrongly counterexampling refs `test_mut_ref_forward`).
        if !call_func_is_qualified_path(call) {
            // Snapshot ONLY for calls whose contract will actually consume it
            // (a helper with a non-empty `requires` OR `ensures`): rendering
            // has scoped side effects that contract-less calls never incurred
            // here. Consumers: the `requires` substitution AND (slice D) the
            // `old(P)` bindings of the `ensures` assumption — an ensures-only
            // callee (`ensures(*a == *old(a) + 1)`) needs the pre-call
            // renderings just as much, or `old` would bind post-havoc.
            if self.call_has_helper_contract(call) && self.call_havocs_mut_ref_args(call) {
                let mut_scalar_flags = self.helper_contract_mut_ref_scalar_flags(call);
                let pre_args = self.with_temporary_scopes(|collector| {
                    collector.scoped_contract_call_args_left_to_right(&call.args, &mut_scalar_flags)
                });
                self.pre_havoc_call_args
                    .insert(call as *const syn::ExprCall as usize, pre_args);
            }
        }
        // SOUNDNESS-CRITICAL: the argument havoc runs for the QUALIFIED-UFCS
        // spelling too. It used to sit inside the `!call_func_is_qualified_path`
        // arm above, so `<H as B>::tb(&h, t)` — a trait method with a `&mut`
        // non-self parameter — was framed by nothing and proved `result == 0`
        // for a body that returns 1. Only the CONTRACT routing differs between
        // the two spellings; which arguments the callee may write through does
        // not. `resolved_call_arg_mut_flags` reads the qualified spelling's
        // `Type::method` key, so the framing stays signature-precise rather than
        // falling back to the argument type.
        self.havoc_mut_ref_call_arg_referents(call);
        // A qualified-UFCS call `<S as T>::f(s, args)` routes to the unit-4
        // discharge and must NOT consume the helper-call dedup set (its `func`
        // path has a `qself`, so `record_helper_contract_call` would bail with
        // no obligation anyway, but only after recording the site). Plain and
        // `S::f` calls continue down the unchanged helper path.
        if call_func_is_qualified_path(call) {
            self.record_qualified_trait_fn_contract_call(call);
        } else {
            self.record_helper_contract_call(call);
            // Phase C part 2: a DIRECT APPLICATION `f(arg)` of a registered
            // `closure!` literal emits its call-site prove-requires obligation and
            // assume-ensures here (unary only; every other callee returns with no
            // obligation, leaving helper / free calls unaffected).
            self.record_closure_application_obligations(call);
        }
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&call.func);
        for arg in &call.args {
            self.visit_expr(arg);
        }
        if self.parse_error.is_some() {
            return;
        }
        // SOUNDNESS-CRITICAL (UFCS associated-fn mutation framing): a UFCS call
        // `S::bump(s)` / `<S>::bump(s)` / `<S as T>::traise(s)` / `Tr::traise(s)`
        // / `Vec::push(v, ..)` is the desugaring of `recv.method(..)` and must
        // havoc a `&mut self` struct / non-pure collection receiver exactly as
        // the method-call path does. Runs for BOTH plain and `qself` spellings
        // (the qualified form is otherwise gated out of the free-call havoc
        // above). A pure UFCS read / associated constructor is left untouched.
        // Applied AFTER visiting the arguments: a `&mut s` reborrow argument
        // re-binds the owned receiver `s` to its entry symbol while being
        // visited, so havocing earlier would be undone — the post-arg position is
        // the genuine post-call program point for the receiver's fresh value.
        self.havoc_ufcs_receiver_mutation(call);
        // SOUNDNESS-CRITICAL (invoked-exec-closure body panic-freedom): pin the
        // arith-safety / index-bounds obligations for the body of a `let`-bound (or
        // immediately-invoked) exec closure called here. See the method doc for the
        // exec-vs-spec discrimination that keeps spec closures untouched.
        self.maybe_emit_invoked_exec_closure_arith_safety(call);
    }

    fn visit_expr_let(&mut self, expr_let: &'ast syn::ExprLet) {
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&expr_let.expr);
    }

    fn visit_expr_block(&mut self, block: &'ast syn::ExprBlock) {
        if self.parse_error.is_some() {
            return;
        }
        let assigned_outer = self.externally_assigned_in_block(&block.block);
        // SOUNDNESS-CRITICAL (cross-scope exec-closure rebind, round-8 finding
        // 13): a `let mut g = |..| ..;` REASSIGNED inside this block (`{ g = |..|
        // body2; }`) is visited in an isolated scope whose `restore_scope_snapshot`
        // reverts `exec_closure_defs` to the pre-block def, after which
        // `invalidate_scoped_names` DROPS it — so a post-block call `g(args)`
        // emitted NO invoked-exec-closure arith-safety / index-bounds obligation
        // (a div-by-zero `g(a, 0)` false-`Verified`). Capture the block's NET
        // closure rebind for every outer-assigned name BEFORE the restore and
        // RE-APPLY it after the invalidate, so the post-block call instruments the
        // REASSIGNED body (correct modeling — the block is unconditional, so its
        // last write is the post-block value). A name rebound to a NON-closure has
        // no captured def and stays dropped (no instrumentation — correct).
        let saved = self.scope_snapshot();
        // Slice-C remediation: this nested block's deref writes are rolled
        // back by the `restore_scope_snapshot` below and deref roots are
        // never in `assigned_outer` (#83 skip), so `{ *x += 1; }
        // assert!(*x == 10)` read the PRE-block value (false on every path).
        // In-block SSA semantics are exact; the region exit below havocs the
        // written roots so no post-block read can see the reverted state.
        self.enter_deref_write_region();
        self.visit_block(&block.block);
        let rebound: Vec<(String, syn::ExprClosure)> = assigned_outer
            .iter()
            .filter_map(|name| {
                self.exec_closure_defs
                    .get(name)
                    .map(|closure| (name.clone(), closure.clone()))
            })
            .collect();
        self.restore_scope_snapshot(saved);
        self.invalidate_scoped_names(assigned_outer);
        for (name, closure) in rebound {
            self.exec_closure_defs.insert(name, closure);
        }
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr_unsafe(&mut self, expr_unsafe: &'ast syn::ExprUnsafe) {
        // Slice-C remediation recheck (u1): `unsafe { ... }` executes INLINE
        // with identical scoping semantics to a plain block, but ExprUnsafe
        // had no override — syn's default recursion reached visit_block,
        // which push/pops a NAME scope with no value snapshot and NO deref
        // region, so a first deref write inside `unsafe {}` was silently
        // dropped at scope exit (`unsafe { *x = 7; } assert!(*x == 5)`
        // false-VERIFIED). Give it the exact ExprBlock treatment: snapshot +
        // region enter, visit, closure-rebind recovery, restore, region
        // exit + havoc of written roots.
        if self.parse_error.is_some() {
            return;
        }
        let assigned_outer = self.externally_assigned_in_block(&expr_unsafe.block);
        let saved = self.scope_snapshot();
        self.enter_deref_write_region();
        self.visit_block(&expr_unsafe.block);
        let rebound: Vec<(String, syn::ExprClosure)> = assigned_outer
            .iter()
            .filter_map(|name| {
                self.exec_closure_defs
                    .get(name)
                    .map(|closure| (name.clone(), closure.clone()))
            })
            .collect();
        self.restore_scope_snapshot(saved);
        self.invalidate_scoped_names(assigned_outer);
        for (name, closure) in rebound {
            self.exec_closure_defs.insert(name, closure);
        }
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr_async(&mut self, expr_async: &'ast syn::ExprAsync) {
        // An async block's body does NOT execute at creation — modeling its
        // deref writes as inline (even with exit havoc) would be wrong in
        // both directions. Fail closed if it touches a supported &mut param;
        // otherwise leave the default recursion behavior unchanged.
        if self.parse_error.is_some() {
            return;
        }
        if block_contains_deref_write(&expr_async.block) {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: "assignment through a dereferenced reference is \
                         unsupported in vc_extraction: deref write inside an async block (deferred execution) is not modeled"
                    .to_string(),
            });
            return;
        }
        syn::visit::visit_expr_async(self, expr_async);
    }

    fn visit_expr_try_block(&mut self, expr_try: &'ast syn::ExprTryBlock) {
        // Try blocks have early-exit-on-`?` semantics the scoped model does
        // not represent; fail closed on deref writes inside.
        if self.parse_error.is_some() {
            return;
        }
        if block_contains_deref_write(&expr_try.block) {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: "assignment through a dereferenced reference is \
                         unsupported in vc_extraction: deref write inside a try block is not modeled"
                    .to_string(),
            });
            return;
        }
        syn::visit::visit_expr_try_block(self, expr_try);
    }

    fn visit_expr_const(&mut self, expr_const: &'ast syn::ExprConst) {
        // Const blocks evaluate at compile time; a deref write to a runtime
        // &mut param inside one is not representable — fail closed.
        if self.parse_error.is_some() {
            return;
        }
        if block_contains_deref_write(&expr_const.block) {
            self.parse_error = Some(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: "assignment through a dereferenced reference is \
                         unsupported in vc_extraction: deref write inside a const block is not modeled"
                    .to_string(),
            });
            return;
        }
        syn::visit::visit_expr_const(self, expr_const);
    }

    fn visit_expr_if(&mut self, expr_if: &'ast syn::ExprIf) {
        if self.parse_error.is_some() {
            return;
        }
        // Path condition for branch-guarded asserts (#2779 Feature B). A plain
        // boolean `if` condition yields the condition string. An `if let P = e`
        // threads the discriminant's "pattern matches" condition (e.g.
        // `opt.is_some()`) so a branch-local `assume!`/call-`ensures` in the
        // then-branch is guarded and cannot leak past the `if let` into
        // straight-line code (P0-B). An `if let` whose match condition cannot be
        // rendered (`Unknown`) suppresses assume!/call-ensures in both branches
        // (sound — drops a hypothesis rather than leaking it unconditionally).
        let mut suppress_iflet_assumes = false;
        // Field projections for the `if let` pattern's variables, when the
        // discriminant is a resolvable datatype — computed here while `disc` /
        // `disc_ty` are in scope, applied to the then-branch scope below so a
        // then-branch obligation (`assert!`) resolves the binding instead of
        // seeing it shadowed-opaque ("unresolved variable"). Mirrors the
        // match-arm projection binding in `visit_expr_match`.
        let mut iflet_projections: Option<Vec<(String, String)>> = None;
        let path_condition = if let Expr::Let(expr_let) = &*expr_if.cond {
            self.visit_expr(&expr_let.expr);
            let (disc, disc_ty) = match self.local_pattern_base(&expr_let.expr) {
                Some((base, ty)) => (base, Some(ty)),
                None => (self.expr_to_scoped_string(&expr_let.expr), None),
            };
            iflet_projections = disc_ty
                .as_ref()
                .and_then(|ty| pattern_bindings_for_scoped_value(&expr_let.pat, &disc, ty));
            match arm_pattern_match_condition(&expr_let.pat, &disc, disc_ty.as_ref()) {
                ArmMatchCond::Refutable(c) => Some(c),
                ArmMatchCond::Always => None,
                ArmMatchCond::Unknown => {
                    suppress_iflet_assumes = true;
                    None
                }
            }
        } else {
            self.visit_expr(&expr_if.cond);
            // SOUNDNESS-CRITICAL (if-condition arithmetic / index panic-freedom):
            // an `if` boolean test is evaluated EXACTLY ONCE, UNCONDITIONALLY,
            // before either branch — exactly like a `match` scrutinee (see
            // `visit_expr_match`, which anchors both checks on `expr_match.expr`).
            // So an arithmetic (`if a / b > 0`) or index (`if arr[i] > 0`) site in
            // the condition carries a real exec panic obligation (div-by-zero,
            // overflow, signed MIN/-1, shift-bounds, OOB) that must fire at the
            // PRE-BRANCH program point. `visit_expr` above only did value-numbering
            // / path-condition rendering and never emitted these, so the obligation
            // silently dropped. We emit it here under the ENCLOSING path conditions
            // only (none for a top-level `if`; `!(c)` for an `else if` nested in the
            // else arm, so `if c {} else if a / b > 0 {}` checks `a / b` only on the
            // reachable `!(c)` path) — NOT gated by this `if`'s own then/else path
            // condition (not yet pushed). A SAFE condition (`if b > 0`, or
            // `if a / b > 0` under `requires(b != 0)`) still verifies. Short-circuit
            // `&&`/`||` right operands and `else if` chains are handled by the
            // collector's reachability guards and the recursive `visit_expr_if`.
            self.emit_exec_index_bounds_checks_in_expr(&expr_if.cond);
            self.emit_exec_arith_safety_checks_in_expr(&expr_if.cond);
            Some(self.expr_to_scoped_string(&expr_if.cond))
        };
        let then_bindings = if let Expr::Let(expr_let) = &*expr_if.cond {
            bound_idents_from_pat(&expr_let.pat)
        } else {
            BTreeSet::new()
        };

        let mut assigned_outer = self.externally_assigned_in_join_block(&expr_if.then_branch);
        let assigned_else = expr_if
            .else_branch
            .as_ref()
            .map(|(_, else_branch)| self.externally_assigned_in_join_expr(else_branch));
        if let Some(assigned_else) = &assigned_else {
            assigned_outer.extend(assigned_else.clone());
        }

        for name in &assigned_outer {
            if !self.has_scoped_name(name) {
                self.current_scope_mut()
                    .insert(name.to_string(), name.to_string());
            }
        }

        let after_condition = self.scope_snapshot();
        // Slice-C remediation: both branches are visited under
        // snapshot-restore and deref roots never reach `assigned_outer`
        // (#83 skip), so a branch deref write was silently dropped at the
        // join (`if c { *x += 1; } assert!(*x == 5)` false-`Verified` for
        // `c`; single first writes had the same hole on base). One region
        // spans BOTH branches: in-branch SSA semantics stay exact (each
        // branch starts from `after_condition`), and the exit at the join
        // havocs every deref-written root so no post-join read can see the
        // reverted state.
        self.enter_deref_write_region();

        self.shadow_names(&then_bindings);
        // Override the datatype-resolvable then-bindings with their discriminant
        // field projections. Sound: this then-branch scope is snapshot-restored
        // below (`restore_scope_snapshot(after_condition)`), so the binding is
        // then-branch-local (never leaks to the else / after), and the branch's
        // obligations are guarded by `path_condition` (pushed next) — so `x` is
        // only ever `<disc>.<variant>_i` under `is-<variant>(disc)`.
        if let Some(bindings) = &iflet_projections {
            for (name, value) in bindings {
                self.current_scope_mut().insert(name.clone(), value.clone());
                self.set_concrete_scoped_current(name, false);
                self.clear_struct_type_current(name);
            }
        }
        if let Some(path) = &path_condition {
            self.path_conditions.push(path.clone());
        }
        if suppress_iflet_assumes {
            self.match_arm_unguardable_depth += 1;
        }
        self.visit_block(&expr_if.then_branch);
        if suppress_iflet_assumes {
            self.match_arm_unguardable_depth -= 1;
        }
        if path_condition.is_some() {
            self.path_conditions.pop();
        }
        let then_snapshot = self.scope_snapshot();
        self.restore_scope_snapshot(after_condition.clone());

        let mut else_snapshot = None;
        if let Some((_, else_branch)) = &expr_if.else_branch {
            // The else arm is reached only when the guard is false.
            if let Some(path) = &path_condition {
                self.path_conditions.push(format!("!({path})"));
            }
            if suppress_iflet_assumes {
                self.match_arm_unguardable_depth += 1;
            }
            if let Expr::Block(block) = else_branch.as_ref() {
                self.visit_block(&block.block);
            } else {
                self.visit_expr(else_branch);
            }
            if suppress_iflet_assumes {
                self.match_arm_unguardable_depth -= 1;
            }
            if path_condition.is_some() {
                self.path_conditions.pop();
            }
            else_snapshot = Some(self.scope_snapshot());
            self.restore_scope_snapshot(after_condition.clone());
        }

        let merged_values = Self::merge_common_assigned_branch_values(
            &assigned_outer,
            &then_snapshot,
            else_snapshot.as_ref(),
        );
        let merged_names: BTreeSet<String> =
            merged_values.iter().map(|(name, _)| name.clone()).collect();
        self.invalidate_scoped_names(assigned_outer.clone());
        for (name, value) in merged_values {
            self.assign_scoped_at_snapshot_depth(&name, value, &after_condition);
        }
        // SOUNDNESS (round-2 audit P0-A + free-call `&mut`-arg branch frame): a
        // name assigned on only some branches (or to differing values) is NOT kept
        // by the common-value merge; `invalidate_scoped` alone would let a
        // `&mut`/owned param revert to its entry value, dropping the conditional
        // write. Havoc the un-merged assigned names so a post-join read sees
        // arbitrary state — covering struct/enum (functional-update model),
        // collection, and scalar bindings alike (a collection `&mut`-mutated only
        // on the `then` path, e.g. `if b { push_helper(v); }`, must not revert to
        // its entry length).
        for name in &assigned_outer {
            if !merged_names.contains(name) {
                self.havoc_unmerged_assigned_at_join(name);
            }
        }
        // SOUNDNESS-CRITICAL (cross-scope exec-closure rebind across a branch
        // join, round-8 finding 13b): `invalidate_scoped_names` above dropped the
        // `exec_closure_defs` entry of any `g` reassigned in a branch, so a
        // post-`if` call `g(args)` would emit NO invoked-exec-closure arith-safety
        // obligation. When BOTH reachable branches rebind `g` to the SAME closure
        // body, the post-join body is unambiguous — re-apply it so the call
        // instruments the rebound body (correct modeling; the witness rebinds to
        // the same `|x, y| x / y` on both arms, so `g(a, 0)` re-fails closed). A
        // partial or differing-body rebind is left dropped (the pre-existing
        // fail-closed-by-omission behavior — no new false-`Verified`, and no
        // over-rejection of a safe straight-line closure).
        self.reapply_common_branch_exec_closure_rebinds(
            &assigned_outer,
            &then_snapshot,
            else_snapshot.as_ref(),
        );
        // Slice-C remediation: havoc every deref-written root at the join
        // (post-join state, after the merge/havoc of `assigned_outer` names).
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr_match(&mut self, expr_match: &'ast syn::ExprMatch) {
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&expr_match.expr);
        if self.parse_error.is_some() {
            return;
        }
        // The scrutinee scoped value (+ its datatype type when resolvable) drives
        // each arm's "this arm matches" path condition.
        let (scrutinee, scrutinee_ty) = match self.local_pattern_base(&expr_match.expr) {
            Some((base, ty)) => (base, Some(ty)),
            None => (self.expr_to_scoped_string(&expr_match.expr), None),
        };
        // GROUND-constructor scrutinee fallback (`match S(..) { .. }`,
        // `match (S { .. }) { .. }`, `match Enum::Variant(..) { .. }`): the
        // scrutinee is a constructor expression, not a declared variable, so
        // `local_pattern_base` cannot type it — but its datatype is statically
        // known from the constructor itself, and arm-binding projections over
        // its scoped value are the SAME machinery the local-scrutinee path
        // uses. Supplied PER ARM below, gated on the arm pattern being flat
        // (exactly modelable — see `or_disjunct_is_flat`); the enum form is
        // additionally restricted to or-pattern arms so the pinned
        // fail-closed boundary for ordinary variant arms over a ground enum
        // constructor stays intact.
        let ground_struct_ty = if scrutinee_ty.is_none() {
            self.ground_struct_scrutinee_datatype(&expr_match.expr)
        } else {
            None
        };
        let ground_enum_ty = if scrutinee_ty.is_none() && ground_struct_ty.is_none() {
            self.ground_enum_scrutinee_datatype(&expr_match.expr)
        } else {
            None
        };
        // SOUNDNESS-CRITICAL (match-scrutinee arithmetic): the scrutinee is
        // evaluated EXACTLY ONCE, unconditionally, before any arm dispatch — so an
        // arithmetic / index site in it (`match a / b { .. }`) carries a real exec
        // panic obligation that must fire unconditionally (NOT under an arm guard).
        self.emit_exec_index_bounds_checks_in_expr(&expr_match.expr);
        self.emit_exec_arith_safety_checks_in_expr(&expr_match.expr);

        let mut assigned_outer = BTreeSet::new();
        // Cumulative negations of EARLIER arms whose selection condition we could
        // render: arm `i` is selected only when no earlier arm matched, so these
        // tighten arm `i`'s path condition to its exact reachable state set. Once
        // an earlier arm's selection cannot be rendered, no later arm can soundly
        // exclude it, so later arms become unguardable (assume!/call-ensures drop).
        let mut prior_negations: Vec<String> = Vec::new();
        let mut prior_unrenderable = false;
        // Slice-C remediation: ONE deref-write region spans the WHOLE arm
        // sweep (arm bodies are visited under `with_isolated_scopes`, so each
        // arm starts from the pre-match state — a per-arm exit havoc would
        // wrongly pollute later arms' in-arm reads). In-arm SSA semantics
        // stay exact; the exit after the sweep havocs every deref-written
        // root so no post-match read can see an arm's reverted write.
        self.enter_deref_write_region();
        for arm in &expr_match.arms {
            let arm_bindings = bound_idents_from_pat(&arm.pat);
            let assigned_arm = self.externally_assigned_in_join_expr(&arm.body);
            assigned_outer.extend(assigned_arm);
            if let Some((_, guard)) = &arm.guard {
                assigned_outer.extend(self.externally_assigned_in_expr(guard));
            }

            // The scrutinee type THIS arm may model against: the declared
            // variable's type when resolved, else the ground-constructor
            // fallback for a flat arm pattern (enum constructors: or-pattern
            // arms only — see the fallback derivation above).
            let arm_scrutinee_ty: Option<&TrustVcType> = scrutinee_ty.as_ref().or_else(|| {
                let flat = match &arm.pat {
                    Pat::Or(or_pat) => or_pat.cases.iter().all(or_disjunct_is_flat),
                    pat => or_disjunct_is_flat(pat),
                };
                if !flat {
                    return None;
                }
                ground_struct_ty.as_ref().or_else(|| {
                    matches!(arm.pat, Pat::Or(_))
                        .then(|| ground_enum_ty.as_ref())
                        .flatten()
                })
            });

            let match_cond = arm_pattern_match_condition(&arm.pat, &scrutinee, arm_scrutinee_ty);
            // Render the arm guard with its pattern bindings substituted to
            // scrutinee projections (so `x if x == 0` renders as `scrutinee == 0`).
            // `renderable_guard` distinguishes a guard we could fully render from
            // one we could not (a binding we cannot project) — the latter makes the
            // arm's selection unrenderable.
            let (rendered_guard, guard_renderable) = match &arm.guard {
                None => (None, true),
                Some((_, guard)) => {
                    match self.render_arm_guard(guard, &arm.pat, &scrutinee, arm_scrutinee_ty) {
                        Some(g) => (Some(g), true),
                        None => (None, false),
                    }
                }
            };

            // Positive conjuncts identifying THIS arm (its own match + guard).
            let mut positive: Vec<String> = Vec::new();
            let positive_renderable = match &match_cond {
                ArmMatchCond::Always => true,
                ArmMatchCond::Refutable(c) => {
                    positive.push(c.clone());
                    true
                }
                ArmMatchCond::Unknown => false,
            } && guard_renderable;
            if let Some(g) = &rendered_guard {
                positive.push(g.clone());
            }

            // Decide whether this arm is soundly guardable.
            let arm_guardable = positive_renderable && !prior_unrenderable;
            let mut conjuncts = positive.clone();
            if arm_guardable {
                conjuncts.extend(prior_negations.iter().cloned());
            }

            // Field projections for this arm's pattern variables, when the
            // scrutinee is a resolvable datatype. Computed here (free fn, no
            // `self` borrow) so it can be applied inside the isolated arm scope.
            let arm_projections = arm_scrutinee_ty
                .and_then(|ty| pattern_bindings_for_scoped_value(&arm.pat, &scrutinee, ty));
            // A bare whole-value binding `x` with no datatype projection (e.g. a
            // SCALAR scrutinee, `match n { x if x > 3 => { assert!(x > 3); } .. }`)
            // binds to the SCRUTINEE itself — the arm's `x` IS the scrutinee value.
            // When `arm_projections` is None and the pattern is a bare irrefutable
            // ident, `scrutinee_ty` is None (a bare ident over a resolvable datatype
            // already resolves via `collect_pattern_bindings`), so this only fires
            // for non-datatype scrutinees. Sound for the same reason as the
            // projection case: arm-isolated scope + the arm's path condition guard.
            let arm_whole_value_bind: Option<(String, String)> = if arm_projections.is_none() {
                match &arm.pat {
                    syn::Pat::Ident(id)
                        if id.by_ref.is_none()
                            && id.mutability.is_none()
                            && id.subpat.is_none() =>
                    {
                        Some((id.ident.to_string(), scrutinee.clone()))
                    }
                    _ => None,
                }
            } else {
                None
            };
            self.with_isolated_scopes(|collector| {
                // Bind the arm's pattern variables to FIELD PROJECTIONS of the
                // scrutinee so an obligation (`assert!`, …) inside the arm body
                // resolves them, instead of leaving them shadowed-opaque
                // (`x` → `"x"`, an "unresolved variable" at lower time). Sound:
                // the bindings are arm-ISOLATED (`with_isolated_scopes`) and
                // every arm-body obligation is guarded by the arm's path
                // condition (pushed below), so `x` is only ever
                // `<scrutinee>.<variant>_i` under `is-<variant>(scrutinee)`.
                // Shadow first (declares every bound ident), then override the
                // datatype-resolvable ones with their projection; falls back to
                // pure shadowing when the scrutinee type is not a datatype
                // (fail closed, prior behavior).
                collector.shadow_names(&arm_bindings);
                if let Some(bindings) = &arm_projections {
                    for (name, value) in bindings {
                        collector
                            .current_scope_mut()
                            .insert(name.clone(), value.clone());
                        collector.set_concrete_scoped_current(name, false);
                        collector.clear_struct_type_current(name);
                    }
                }
                if let Some((name, value)) = &arm_whole_value_bind {
                    collector
                        .current_scope_mut()
                        .insert(name.clone(), value.clone());
                    collector.set_concrete_scoped_current(name, false);
                    collector.clear_struct_type_current(name);
                }
                let pushed_path = if arm_guardable && !conjuncts.is_empty() {
                    collector.path_conditions.push(conjuncts.join(" && "));
                    true
                } else {
                    false
                };
                let suppressed = if !arm_guardable {
                    collector.match_arm_unguardable_depth += 1;
                    true
                } else {
                    false
                };
                if let Some((_, guard)) = &arm.guard {
                    collector.visit_expr(guard);
                    // A match-arm GUARD is evaluated (Rust: whenever the arm's
                    // pattern matches, before the body), so its arithmetic / index
                    // safety must be checked. `visit_expr` above only
                    // value-numbers and renders the path condition — it never
                    // emits these obligations (the exact analog of the `if`
                    // CONDITION, which needed its own explicit emit). Without this
                    // a panicking guard (`_ if a / b > 0` with b == 0) was a
                    // false-verify. Emitted under the arm's pattern path condition.
                    collector.emit_exec_index_bounds_checks_in_expr(guard);
                    collector.emit_exec_arith_safety_checks_in_expr(guard);
                }
                collector.visit_expr(&arm.body);
                // The arm body is a value position evaluated only when the arm is
                // selected: route its arithmetic / index safety obligations under
                // the arm path condition (so a SAFE arm does not over-reject while
                // a genuinely-panicking arm — `0 => a / b` under `requires(b==0)` —
                // is a counterexample).
                collector.emit_exec_index_bounds_checks_in_expr(&arm.body);
                collector.emit_exec_arith_safety_checks_in_expr(&arm.body);
                if pushed_path {
                    collector.path_conditions.pop();
                }
                if suppressed {
                    collector.match_arm_unguardable_depth -= 1;
                }
            });

            // Update the running negation set for subsequent arms.
            let selected_cond = match (&match_cond, &rendered_guard, guard_renderable) {
                (ArmMatchCond::Unknown, _, _) => None,
                (_, None, false) => None, // guard present but unrenderable
                (ArmMatchCond::Always, None, _) => Some("true".to_string()),
                (ArmMatchCond::Always, Some(g), _) => Some(g.clone()),
                (ArmMatchCond::Refutable(c), None, _) => Some(c.clone()),
                (ArmMatchCond::Refutable(c), Some(g), _) => Some(format!("({c}) && ({g})")),
            };
            match selected_cond {
                Some(cond) => prior_negations.push(format!("!({cond})")),
                None => prior_unrenderable = true,
            }
        }
        self.invalidate_scoped_names(assigned_outer.clone());
        // SOUNDNESS (round-2 audit P0-A + slice-D remediation p20): havoc EVERY
        // name assigned in any arm — struct/enum (functional-update model, the
        // original P0-A fix for `match s { _ => s.x = v }`) AND declared
        // scalar/collection bindings (`havoc_unmerged_assigned_at_join`
        // dispatches). The struct-only havoc left a DECLARED scalar param
        // mutated in an arm (`match c { true => { nocontract(&mut p); } .. }`,
        // or a plain arm assignment `p = 9`) reverting to its
        // `requires`-pinned ENTRY value after the `invalidate_scoped_names`
        // above — a post-match `assert!(p == 5)` false-`Verified` (the
        // match sibling of the `if`-join P0-A hole, which
        // `havoc_unmerged_assigned_at_join` already closes at the `if` join).
        // Undeclared scoped-only locals keep the fail-closed invalidate.
        for name in &assigned_outer {
            self.havoc_unmerged_assigned_at_join(name);
        }
        // Slice-C remediation: havoc every deref-written root at the join.
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr_loop(&mut self, expr_loop: &'ast syn::ExprLoop) {
        if self.parse_error.is_some() {
            return;
        }
        let assigned_body = self.externally_assigned_in_loop_body(&expr_loop.body);
        // Slice-C remediation: a PLAIN single deref write in the loop body
        // keeps the pre-existing (base) modeling — per-iteration
        // value-numbering, rolled back by the isolated visit — but its root
        // is region-recorded and havocked at the loop join, closing the base
        // hole where a post-loop read saw the stale pre-loop value. The
        // slice-C capabilities (compound desugar, sequential repins) stay
        // OFF inside loop bodies (`loop_body_depth` checks at their sites):
        // their SSA chain would read the previous VISIT's value, not the
        // previous ITERATION's.
        self.enter_deref_write_region();
        self.with_isolated_scopes(|collector| {
            collector.invalidate_scoped_names(assigned_body.clone());
            collector.loop_body_depth += 1;
            collector.visit_block(&expr_loop.body);
            collector.loop_body_depth -= 1;
        });
        // Slice-D recheck fix (bare-`loop{}` family): `invalidate_scoped_names`
        // only invalidates SCOPED locals — a requires-pinned DECLARED param
        // written in the loop body fell back to its ENTRY symbol after the
        // loop, false-verifying stale reads (three base-era holes plus one
        // landing-chain regression once contract lowering removed the Error
        // that had masked the fallback). Mirror visit_expr_for_loop: frame the
        // modified vars (declared vars havoc to fresh symbols unless a loop
        // invariant constrains them).
        let has_invariant = block_has_loop_invariant(&expr_loop.body);
        self.frame_loop_modified_vars(assigned_body, has_invariant);
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr_while(&mut self, expr_while: &'ast syn::ExprWhile) {
        if self.parse_error.is_some() {
            return;
        }
        let assigned_body = self.externally_assigned_in_loop_body(&expr_while.body);
        let has_invariant = block_has_loop_invariant(&expr_while.body);
        let mut loop_entry_bindings = if has_invariant {
            self.materialize_loop_snapshot_aliases(&assigned_body)
        } else {
            Vec::new()
        };
        // Loop-modified LET-LOCALS: declare each undeclared, typable one as a VC
        // var (exactly like a `mut i` param) BEFORE the guard is rendered. This
        // makes the invariant/guard conditions LOWER (the prepare-obligation
        // TypeEnv is `ctx.variables`) and activates the already-captured M4
        // single-iteration transition (the frame-condition step silently skips
        // vars absent from `ctx.variables`), routing let-local counters through
        // the same sound entry/preservation/post-loop machinery as params. A
        // shadowed param (`get_variable_type` Some) or an un-typable local is
        // skipped — those keep the fail-closed unresolved path unchanged, so no
        // new false-verify surface. Capture each declared local's pre-loop
        // (loop-HEAD, so a pre-loop reassignment is honored) scoped value as a
        // per-invariant ENTRY binding, THEN invalidate its scoped value so the
        // guard below renders the BARE declared symbol (`i < n`), not the stale
        // initializer (`0 < n` — the cardinal stale-exit-fact hazard).
        let mut declared_letlocals: BTreeSet<String> = BTreeSet::new();
        for name in &assigned_body {
            if self.vc.get_variable_type(name).is_some() {
                continue;
            }
            if let Some(ty) = self.modified_var_scalar_type(name) {
                let entry_value = self.lookup_scoped(name);
                if entry_value != *name {
                    loop_entry_bindings.push((name.clone(), entry_value));
                }
                self.vc.declare_var_typed(name, ty);
                declared_letlocals.insert(name.clone());
            }
        }
        self.invalidate_scoped_names(declared_letlocals);
        let boolean_guard = !matches!(&*expr_while.cond, Expr::Let(_));
        let guard = boolean_guard.then(|| self.expr_to_scoped_string(&expr_while.cond));
        let can_assume_normal_exit = boolean_guard
            && is_side_effect_free_guard(&expr_while.cond)
            && !contains_break(&expr_while.body);
        // Soundness gate for the loop-body transition (M4). The scoped
        // value-numbering yields an EXACT single-iteration transition for every
        // modified var only when the body is a flat, branch-free sequence of
        // total scalar assignments over pure arithmetic. Anything that can
        // re-invalidate a var mid-body (a conditional/`match`, a nested
        // block/loop, a `&mut`-passing call) followed by a dependent read would
        // pin a later var's transition to a stale loop-head value — masking a
        // true post-state (a false Verified). When the body is not flat we
        // capture nothing and fall back to pure havoc. Part of M4.
        //
        // A fresh immutable pure-arith `let` in the body is admitted (it defines
        // a NEW name and re-invalidates nothing). The shadow predicate below is
        // the narrowness pin that keeps that admission sound: a `let` may not
        // re-bind a loop-MODIFIED var (the transition capture would read the
        // shadow, which Rust reverts at block end — a WRONG transition), nor a
        // declared VC variable (a param / declared local, whose later reads and
        // whose `invariant!` occurrences would silently re-point), nor an outer
        // scoped let-local (`lookup_scoped` resolving to something other than the
        // bare name means the name already denotes a value here).
        let capture_transitions = loop_body_transition_is_exact(&expr_while.body, &|name| {
            assigned_body.contains(name)
                || self.vc.get_variable_type(name).is_some()
                || self.lookup_scoped(name) != name
        });
        let modified_vars = assigned_body.iter().cloned().collect::<Vec<_>>();
        // SOUNDNESS-CRITICAL (while-guard arithmetic / index panic-freedom): a
        // boolean `while` guard is evaluated UNCONDITIONALLY before the first
        // iteration (the guard always runs at least once), against the PRE-loop
        // state — exactly like a `match` scrutinee or an `if` condition. So an
        // arithmetic (`while a / b > 0`) or index (`while arr[i] > 0`) site in the
        // guard carries a real exec panic obligation that the loop encoding's
        // value-numbering visit (`collector.visit_expr(&expr_while.cond)` below)
        // never emitted, silently dropping div-by-zero / overflow / signed MIN÷-1 /
        // shift-bounds / OOB panics (masked further when a `break` body removes the
        // negated-guard post-loop side condition). Emit it HERE — before the loop
        // context / body havoc is pushed — so the obligation is checked against
        // pre-loop variable values under the enclosing path conditions only. A SAFE
        // guard (`requires(b != 0)`, or a non-arith guard `b > 0`) still verifies —
        // no over-rejection. The guard's re-evaluation over loop-MODIFIED state on
        // later iterations is owned by the loop-body machinery (accepted
        // incompleteness, mirroring the deferred body-site obligation posture). A
        // `while let` guard (`boolean_guard == false`) carries no scalar arithmetic
        // test and is skipped.
        if boolean_guard {
            self.emit_exec_index_bounds_checks_in_expr(&expr_while.cond);
            self.emit_exec_arith_safety_checks_in_expr(&expr_while.cond);
        }
        // Slice-C remediation: see `visit_expr_loop` — plain single deref
        // writes keep base modeling, roots are havocked at the loop join
        // (region opened here so cond + body writes both record); compound /
        // sequential deref writes stay off in loop context via
        // `loop_body_depth`.
        self.enter_deref_write_region();
        self.with_isolated_scopes(|collector| {
            collector.invalidate_scoped_names(assigned_body.clone());
            collector.visit_expr(&expr_while.cond);
            if let Some(guard) = guard.clone() {
                let modified_for_capture = assigned_body.iter().cloned().collect::<Vec<_>>();
                collector.loop_contexts.push(LoopExtractionContext {
                    modified_vars,
                    guard,
                    entry_bindings: loop_entry_bindings.clone(),
                    invariant_names: Vec::new(),
                    measure_decreases: Vec::new(),
                });
                // Inline the body block visit (rather than `visit_block`) so the
                // body-scoped value-numbering for modified vars can be read
                // before the block scope is popped — `visit_block` pushes then
                // pops a scope, which would discard the assignment values we
                // need to derive the single-iteration transition. Part of M4.
                collector.loop_body_depth += 1;
                collector.push_scope();
                // SOUNDNESS-CRITICAL (loop-body exec arithmetic safety): havoc the
                // loop-MODIFIED scalars to fresh, unconstrained symbols (their
                // arbitrary values at loop-body entry) and weaken every loop-body
                // arithmetic obligation by the loop GUARD + INVARIANTS over those
                // symbols. A body `x += 100` is then the Verus check "no overflow
                // GIVEN guard ∧ invariant hold at entry" against an arbitrary `x`
                // — catching the overflow that only manifests after iterations,
                // while a counter `i += 1` bounded by the guard `i < n`, and an
                // invariant-bounded var, still verify. The havoc is consulted ONLY
                // while rendering those obligations (`render_loop_body_havoc`), so
                // the invariant obligation, the M4 single-iteration transition
                // captured below, and post-loop reads are all unperturbed.
                collector.push_loop_body_havoc(&assigned_body);
                let pushed_arith_guards =
                    collector.push_loop_body_arith_guards(Some(&expr_while.cond), &expr_while.body);
                for stmt in &expr_while.body.stmts {
                    collector.visit_stmt(stmt);
                }
                collector.pop_loop_body_arith_guards(pushed_arith_guards);
                collector.pop_loop_body_havoc();
                let transitions: Vec<(String, String)> = if capture_transitions {
                    modified_for_capture
                        .iter()
                        .filter_map(|var| {
                            // `lookup_scoped` returns the bare name when no
                            // scoped value was recorded — i.e. the var was left
                            // havoc'd (conditional/aliased/nested-loop write or
                            // no total reassignment). Only a definite,
                            // unconditional straight-line assignment yields a
                            // value distinct from the bare name. Skipped vars
                            // stay arbitrary, which is sound (incomplete).
                            let value = collector.lookup_scoped(var);
                            (value != *var).then(|| (var.clone(), value))
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                collector.pop_scope();
                collector.loop_body_depth -= 1;
                if let Some(context) = collector.loop_contexts.pop() {
                    if !transitions.is_empty() {
                        for invariant_name in &context.invariant_names {
                            collector
                                .vc
                                .set_loop_body_transition(invariant_name, transitions.clone());
                        }
                    }
                    // Register each single-measure `loop_decreases!` obligation as
                    // a loop-scoped obligation — but ONLY when the body admitted
                    // an EXACT single-iteration transition (`capture_transitions`,
                    // i.e. a flat, branch-free body).
                    //
                    // SOUNDNESS (continue/break non-termination landmine): a
                    // non-flat body (`if{break}`, `continue`, nested loop, `for`)
                    // sets `capture_transitions == false`, so we register NO loop
                    // metadata for the measure. Its decrease + nonneg obligations
                    // then stay in the plain-assertion lane with a FREE entry
                    // variable, so `measure < entry_var` is falsifiable ⇒
                    // Counterexample — never a false-Verified. This reuses the
                    // SAME M4 flatness gate that protects invariant transitions;
                    // no bespoke straight-line capture for measures. Bare `loop{}`
                    // / `for` never push a context, so `context.measure_decreases`
                    // is empty there — a third, independent fail-closed layer.
                    if capture_transitions {
                        for binding in &context.measure_decreases {
                            // The entry variable must be in the measure's modified
                            // set or the entry-binding transition is skipped by the
                            // frame-condition step.
                            let mut measure_modified = context.modified_vars.clone();
                            measure_modified.push(binding.entry_var.clone());
                            // Extend the captured single-iteration transitions with
                            // the entry binding `entry_var == measure[pre]`, so the
                            // strict-descent step (WF2) proves `measure < entry_var`
                            // under `measure_current == measure(f(pre))`.
                            let mut measure_transitions = transitions.clone();
                            measure_transitions
                                .push((binding.entry_var.clone(), binding.measure_expr.clone()));
                            // Register the SAME loop metadata against BOTH the
                            // strict-descent AND the non-negativity obligation so
                            // NEITHER spills into the flat-assertion lane. The
                            // decrease is verified as a frame-condition inductive
                            // step (WF2); the nonneg is the direct-entailment floor
                            // (WF1), which consults `loop_modified_vars` (to havoc
                            // the loop vars) and `loop_guards` (to assume the guard)
                            // but not the body transition — a harmless extra.
                            for obligation_name in [
                                &binding.decrease_obligation_name,
                                &binding.nonneg_obligation_name,
                            ] {
                                collector.vc.set_loop_modified_vars(
                                    obligation_name,
                                    measure_modified.clone(),
                                );
                                collector.vc.add_loop_guard(obligation_name, &context.guard);
                                collector.vc.set_loop_body_transition(
                                    obligation_name,
                                    measure_transitions.clone(),
                                );
                            }
                        }
                    }
                }
            } else {
                // `while let` — no boolean guard / transition capture, but it is
                // still a loop body that may run zero times.
                collector.loop_body_depth += 1;
                collector.visit_block(&expr_while.body);
                collector.loop_body_depth -= 1;
            }
        });
        if has_invariant {
            // Invariant present: the encoder's `loop_modified_vars` machinery owns
            // the post-loop havoc and the post-loop read must see the bare,
            // invariant-constrained symbol — keep the legacy invalidate model.
            //
            // SOUNDNESS-CRITICAL (stale exit fact over an undeclared modified
            // counter): `guard` was rendered PRE-loop (above), so an UNDECLARED
            // modified local — a `let mut i = 0` counter with no VC var — resolved
            // to its concrete pre-loop VALUE there. Asserting `!(guard)` then pins
            // the negated guard about the ENTRY state: `while i < n` yields the
            // FALSE fact `!(0 < n) == n <= 0` whenever the loop iterates, so
            // `fn f(n){ let mut i=0; while i<n { invariant!(..); i+=1 } assert!(n==0) }`
            // false-Verified. Mirror the no-invariant branch below: DROP the exit
            // fact when the guard references any undeclared MODIFIED local (a
            // dropped hypothesis — sound; the counter is invalidated regardless, so
            // no post-loop read could consume the fact through it anyway). A guard
            // over declared vars (a `mut i` param) keeps the fact — its bare symbol
            // carries no stale value, so `!(i < n)` connects to the invariant-havoc
            // symbol as before (no over-rejection).
            let undeclared_modified: BTreeSet<String> = assigned_body
                .iter()
                .filter(|name| self.vc.get_variable_type(name).is_none())
                .cloned()
                .collect();
            self.invalidate_scoped_names(assigned_body);
            if can_assume_normal_exit {
                if let Some(guard) = &guard {
                    let guard_reads_undeclared_modified =
                        closure_referenced_idents(&expr_while.cond)
                            .iter()
                            .any(|ident| undeclared_modified.contains(ident));
                    if !guard_reads_undeclared_modified {
                        self.add_post_loop_assumption(format!("!({guard})"));
                    }
                }
            }
        } else {
            // No invariant (`invariant!(true)`): every modified DECLARED variable
            // (a param / declared local whose bare symbol carries entry facts) is
            // freshened so a post-loop read forgets its entry/`requires`/`assume`
            // value. UNDECLARED scoped-only locals (a `let mut i = ..` counter)
            // are left at their pre-loop scoped value WHILE the exit fact is
            // rendered (so the negated-guard stays lowerable, exactly as before),
            // then dropped.
            let mut undeclared = BTreeSet::new();
            for name in &assigned_body {
                if self.vc.get_variable_type(name).is_some() {
                    self.havoc_modified_var_at_loop_join(name);
                } else {
                    undeclared.insert(name.clone());
                }
            }
            // Render the negated-guard exit fact AFTER freshening the declared
            // modified vars, so it references their FRESH exit symbols (e.g.
            // `!(x__loop_havoc_0 < 10)`) — keeping it connected to the symbol a
            // post-loop read now resolves to (no over-rejection of a genuine
            // `assert!(x >= 10)`).
            //
            // SOUNDNESS-CRITICAL (undeclared modified counter in the guard): an
            // UNDECLARED scoped-only local (`let mut inner = i;`) that the body
            // MODIFIES has no exit symbol — its scoped value is its PRE-loop
            // initializer. Rendering the exit fact through it asserted the
            // negated guard about the ENTRY state (`!(i < 20)` for
            // `while inner < 20`), a FALSE fact whenever the loop actually
            // iterates: `fn f(i: u64) { let mut inner = i; while inner < 20
            // { inner += 1 } assert!(i >= 20) }` false-Verified, and in the
            // nested loops_no_spinoff case the same wrong fact contradicted
            // `requires(i < 10)` (vacuity Unknown). DROP the exit fact when the
            // guard references any undeclared MODIFIED local — sound (a dropped
            // hypothesis), and nearly lossless: the counter itself is
            // invalidated below, so no post-loop read could consume the fact
            // through it anyway. Guards over declared vars keep the fact.
            if can_assume_normal_exit && guard.is_some() {
                let guard_reads_undeclared_modified = closure_referenced_idents(&expr_while.cond)
                    .iter()
                    .any(|ident| undeclared.contains(ident));
                if !guard_reads_undeclared_modified {
                    let post_guard = self.expr_to_scoped_string(&expr_while.cond);
                    self.add_post_loop_assumption(format!("!({post_guard})"));
                }
            }
            self.invalidate_scoped_names(undeclared);
        }
        // Slice-C remediation: havoc the deref-written roots at the loop
        // join (after the modified-var framing above), closing the base
        // stale-post-loop-read hole.
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr_for_loop(&mut self, expr_for_loop: &'ast syn::ExprForLoop) {
        if self.parse_error.is_some() {
            return;
        }
        self.visit_expr(&expr_for_loop.expr);
        // SOUNDNESS-CRITICAL (for-loop range-bound arithmetic / index panic-freedom):
        // the iterator expression of a `for` loop is evaluated UNCONDITIONALLY,
        // exactly once, BEFORE the first iteration — just like a `while` guard, an
        // `if` condition, or a `match` scrutinee. In particular a `Range` /
        // `RangeInclusive` bound (`0..(a / b)`, `(a / b)..n`, `0..(a + b)`,
        // `0..=(a + b)`) constructs the range value by EAGERLY evaluating each
        // present bound, so a checked-arith / shift / negation site or an OOB index
        // in either bound carries a real exec panic obligation. The value-numbering
        // visit above never emitted it (the bare `a / b` binop falls through), so
        // div-by-zero / overflow / signed-MIN-÷-1 / shift-bounds / OOB in a range
        // bound silently `Verified`. Emit BOTH the index-bounds and arithmetic-safety
        // obligations on the iterator expression HERE — at the pre-loop program
        // point, before the loop context / body havoc is pushed — so they are checked
        // against pre-loop variable values under the enclosing path conditions only,
        // mirroring the `while`-guard block (see `visit_expr_while`). A SAFE range
        // (`0..n`, `(a / b)..n` under `requires(b != 0)`, `0..(a + b)` under
        // `requires(a < 100 && b < 100)`) still verifies — no over-rejection. The
        // collectors descend through `Expr::Range` into both bounds; the loop BODY's
        // own obligations are owned by the loop-body machinery and are unchanged.
        self.emit_exec_index_bounds_checks_in_expr(&expr_for_loop.expr);
        self.emit_exec_arith_safety_checks_in_expr(&expr_for_loop.expr);
        let assigned_body = self.externally_assigned_in_loop_body(&expr_for_loop.body);
        let loop_bindings = bound_idents_from_pat(&expr_for_loop.pat);
        // Slice-C remediation: see `visit_expr_loop` — plain single deref
        // writes keep base modeling, roots are havocked at the loop join;
        // compound / sequential deref writes stay off in loop context via
        // `loop_body_depth`.
        self.enter_deref_write_region();
        self.with_isolated_scopes(|collector| {
            collector.invalidate_scoped_names(assigned_body.clone());
            collector.shadow_names(&loop_bindings);
            collector.loop_body_depth += 1;
            collector.visit_block(&expr_for_loop.body);
            collector.loop_body_depth -= 1;
        });
        let has_invariant = block_has_loop_invariant(&expr_for_loop.body);
        self.frame_loop_modified_vars(assigned_body, has_invariant);
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr_closure(&mut self, expr_closure: &'ast syn::ExprClosure) {
        if self.parse_error.is_some() {
            return;
        }
        // SOUNDNESS-CRITICAL (P2 closure capture-mutation leak): a closure that
        // mutates a captured outer variable (`let mut inc = || { x = x + 1; }`)
        // has its assignment + call effects dropped by the isolated-scope visit
        // below, freezing the capture at its pre-closure value — so a stale-value
        // claim (`assert!(x == 0)` after two `inc()`) would falsely `Verified`.
        // The closure may run any number of times with an unmodeled effect, so the
        // only sound post-definition model for each mutated capture is ARBITRARY:
        // havoc it in the OUTER scope (a later read sees a fresh symbol, so the
        // frozen initializer is no longer provable). Closure parameters are local,
        // not captures, so they are excluded.
        let mut captured_mutated = self.externally_assigned_in_expr(&expr_closure.body);
        for input in &expr_closure.inputs {
            for name in bound_idents_from_pat(input) {
                captured_mutated.remove(&name);
            }
        }
        // NOTE: exec closure-BODY arith-safety (`|x, y| x / y` ⇒ divide-by-zero)
        // is NOT emitted on this definition-site visit — over arbitrary-valued
        // params it would falsely reject SPEC closures (`Seq::new(n, |i| ((i + 1)
        // as i32) * 10)`), whose parameter is a ghost index, not an exec value. The
        // invoked-exec-closure body panic-freedom obligation is instead emitted at
        // the CALL site (`maybe_invoked_exec_closure_arith_safety`), where the
        // closure is known to be exec (bound to a local + called) and the params
        // are bound to the actual call arguments — so a spec closure passed inline
        // to `Seq::new`/`map`/… is never instrumented.
        //
        // SOUNDNESS-CRITICAL (#74 cross-closure captured-var contamination): a
        // closure body containing an `assume!` (e.g. the expansion of a
        // `trust_vc::closure!` `requires`/body relation) constrains its captured
        // free variables; because the isolated-scope visit below does NOT roll back
        // emitted obligations, that hypothesis would otherwise survive as a flat,
        // unconditional global fact and discharge a SIBLING closure's `assert!`
        // over the SAME captured var (`n`) — a false `Verified`. We isolate each
        // such closure by minting a FRESH, unconstrained, declared symbol for every
        // captured free variable referenced in the body, scoped to this closure's
        // isolated visit. The fresh symbol keeps the closure's OWN `assume ⟹ assert`
        // reasoning intact (both sides resolve to the same fresh symbol) but is
        // disjoint from every sibling's symbol and from the outer binding, so no
        // cross-closure leak remains. Only assume-bearing closures are freshened,
        // so an `assume!`-free closure whose contract legitimately depends on an
        // outer fact about a capture is left untouched (no over-rejection). The
        // accepted incompleteness: an assume-bearing closure no longer sees outer
        // facts about its captures — sound, mirroring the capture-mutation havoc.
        //
        // A SECOND hypothesis source is a call to a CONTRACTED free helper
        // `h(args)` whose `ensures` is threaded as a `__call_ensures_*` ASSUME at
        // the call site: a closure body `let _ = mk(n);` (where `mk` ensures a
        // fact over its param) injects that fact about `n` even though the closure
        // is never invoked, and un-freshened it survives as an unconditional global
        // hypothesis that discharges a sibling/enclosing `assert!(n == 7)` — a
        // false `Verified`. That hypothesis can only constrain a capture PASSED to
        // the call, so — unlike the opaque `assume!` case — we freshen ONLY the
        // captures appearing in such calls' ARGUMENT lists
        // (`closure_contracted_call_arg_idents`). A literal-only contracted call
        // (`checked(3u64)`) constrains no capture and freshens nothing, so a
        // closure that merely happens to call a contracted helper while relying on
        // an UNRELATED outer fact about a capture keeps that fact (NO
        // over-rejection).
        let freshen_all = closure_body_contains_assume(&expr_closure.body);
        let contracted_arg_captures = if freshen_all {
            BTreeSet::new()
        } else {
            self.closure_contracted_call_arg_idents(&expr_closure.body)
        };
        let freshen_captures = freshen_all || !contracted_arg_captures.is_empty();
        // Slice-C remediation: a deref write in the closure body (`|| { *x =
        // 7; }`) is rolled back by the isolated visit AND excluded from
        // `captured_mutated` (the #83 `external_assignments` skip), so a
        // post-definition read saw the frozen pre-closure value even when the
        // closure was CALLED (probed firsthand: false-`Verified` on base).
        // Region-track the roots and havoc them right after the definition —
        // the deref-write sibling of the capture-mutation havoc above (the
        // closure may run any number of times, so ARBITRARY is the only sound
        // post-definition model; havoc never proves wrong facts).
        self.enter_deref_write_region();
        self.with_isolated_scopes(|collector| {
            for input in &expr_closure.inputs {
                collector.shadow_pat_bindings(input);
            }
            if freshen_captures {
                collector.freshen_closure_captured_free_vars(
                    expr_closure,
                    freshen_all,
                    &contracted_arg_captures,
                );
            }
            collector.visit_expr(&expr_closure.body);
        });
        self.invalidate_scoped_names(captured_mutated);
        self.exit_deref_write_region_and_havoc();
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        if self.parse_error.is_some() {
            return;
        }
        visit::visit_expr(self, expr);
    }

    fn visit_expr_macro(&mut self, expr_macro: &'ast syn::ExprMacro) {
        if self.parse_error.is_some() {
            return;
        }
        let name = super::path_last_segment(&expr_macro.mac.path);
        if let Some(name) = name.as_deref() {
            if self.lookup_local_macro(name).is_some() {
                self.parse_error = Some(unsupported_local_macro_expression_error(name));
                return;
            }
        }
        if name
            .as_deref()
            .is_some_and(is_supported_expression_macro_name)
        {
            return;
        }
        // A spec-carrying closure (`trust_vc::closure!(|p| requires(..) ensures(..) body)`)
        // is verified DEF-SIDE in an ISOLATED child context: assume its requires,
        // bind its result to its body, and prove its ensures — over fresh symbols,
        // whose assumption/assertion vectors are discarded, so NOTHING leaks into
        // this parent VC. The closure VALUE is never modeled, so any call site /
        // reflection / capture stays fail-closed (the assume-leak guard). Part of
        // the file-path closure! wiring.
        if is_trust_vc_closure_expr_macro(expr_macro) {
            // Anonymous / statement-position closure literal: def-side only, no
            // reflectable binding. A `let f = trust_vc::closure!(..)` binding is
            // intercepted earlier at the `Stmt::Local` site (which threads `f`).
            self.emit_closure_def_side_obligation(&expr_macro.mac, None);
            return;
        }
        self.visit_assertion_macro_with_attrs(&expr_macro.mac, &expr_macro.attrs);
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        self.visit_assertion_macro(mac);
    }

    fn visit_item(&mut self, item: &'ast Item) {
        if let Err(err) = self.handle_nested_item(item, true) {
            self.parse_error = Some(err);
        }
    }
}

fn is_supported_body_macro(mac: &Macro) -> bool {
    super::path_last_segment(&mac.path)
        .as_deref()
        .is_some_and(is_supported_body_macro_name)
}

/// The names this lane routes, derived from the ONE canonical list of macro
/// names trust-vc decides the meaning of from the name alone
/// (`crate::macro_scope::SPEC_MACRO_NAMES`).
///
/// It is derived rather than repeated so that the scope pass which resolves
/// those names and this dispatch cannot drift apart: a name dispatched below
/// but missing from the canonical list stops being routed here at all — a loud
/// failure — instead of quietly escaping the resolution check.
fn is_supported_body_macro_name(name: &str) -> bool {
    crate::macro_scope::is_body_lane_supported_macro_name(name)
}

fn reveal_target_name(path: &syn::Path) -> Option<String> {
    if path.leading_colon.is_some() || path.segments.len() != 1 {
        return None;
    }
    let segment = path.segments.first()?;
    match &segment.arguments {
        syn::PathArguments::None | syn::PathArguments::AngleBracketed(_) => {
            Some(segment.ident.to_string())
        }
        syn::PathArguments::Parenthesized(_) => None,
    }
}

fn is_supported_expression_macro_name(name: &str) -> bool {
    matches!(
        name,
        "choose" | "seq" | "map" | "set" | "vec" | "ext_eq" | "ext_ne" | "strict_eq" | "equal"
    )
}

/// Extract the assert expressions of a solver-mode assert proof block
/// (#2778): only plain `assert!(..)` / `trust_vc::assert!(..)` statements are
/// supported — anything else (lets, nested queries, control flow) is rejected
/// fail-closed so no proof obligation is silently dropped.
fn solver_mode_body_assert_exprs(block: &syn::Block, macro_name: &str) -> TrustVcResult<Vec<Expr>> {
    let mut asserts = Vec::new();
    for stmt in &block.stmts {
        let mac = match stmt {
            Stmt::Macro(stmt_macro) => &stmt_macro.mac,
            Stmt::Expr(Expr::Macro(expr_macro), _) => &expr_macro.mac,
            other => {
                return Err(TrustVcError::Encoding {
                    context: "extract body assertions",
                    detail: format!(
                        "Unsupported statement in {macro_name}!() proof block — only plain \
                         assert!() statements are supported (fail-closed so no proof \
                         obligation is silently dropped): `{}`",
                        other.to_token_stream()
                    ),
                });
            }
        };
        if super::path_last_segment(&mac.path).as_deref() != Some("assert") {
            return Err(TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Unsupported macro in {macro_name}!() proof block — only plain \
                     assert!() statements are supported (fail-closed so no proof \
                     obligation is silently dropped): `{}!()`",
                    mac.path.to_token_stream()
                ),
            });
        }
        let expr = crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
            .map_err(|source| TrustVcError::Encoding {
                context: "extract body assertions",
                detail: format!(
                    "Failed to parse assert!() inside {macro_name}!() proof block — this \
                     would silently drop the assertion: {source}"
                ),
            })?;
        asserts.push(expr);
    }
    Ok(asserts)
}

fn unsupported_macro_error(mac: &Macro) -> TrustVcError {
    let name = super::path_last_segment(&mac.path)
        .map(|name| format!("{name}!()"))
        .unwrap_or_else(|| format!("{}!()", mac.path.to_token_stream()));
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Unsupported {name} in vc_extraction — unsupported macros are rejected \
             to avoid silently dropping proof obligations"
        ),
    }
}

fn unsupported_old_state_call_error(call: &syn::ExprCall) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Unsupported old-state expression `old(...)` in vc_extraction: `{}`. \
             Source-level old-state for array/reference places is not modeled yet; \
             unsupported old-state expressions are rejected to avoid reasoning about \
             current state as pre-state.",
            call.to_token_stream()
        ),
    }
}

/// The fail-closed rejection for [`AssertionCollector::raw_fallback_dropped_mutations`].
fn raw_fallback_dropped_mutation_error(expr: &Expr, dropped: &BTreeSet<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "expression `{}` is not modeled by vc_extraction and its raw rendering would \
             DROP the statement-position mutation of `{}`; the value carried out of the \
             container would be read against the pre-mutation state, so TrustVc rejects it \
             instead of proving a claim about a state the program has already left.",
            expr.to_token_stream(),
            dropped.iter().cloned().collect::<Vec<_>>().join("`, `")
        ),
    }
}

fn unsupported_index_assignment_error(target: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "indexed assignment target is unsupported in vc_extraction: `{}`. \
             Only directly indexed local array/Seq variables can be modeled safely; \
             unsupported targets are rejected to avoid reasoning about stale array state.",
            target.to_token_stream()
        ),
    }
}

/// Verus rejects `forall(..)`, `exists(..)`, and `choose(..)` written with
/// PARENTHESES (the call form) — only the bare binder form `forall|x| ..` is
/// legal (upstream choose.rs `test1_choose_with_closure_illegal`). trust-vc's
/// legal binder-in-`let` forms are the `choose!(..)` / source-style macros, so a
/// `choose(|..| ..)` / `forall(|..| ..)` / `exists(|..| ..)` CALL in a `let`
/// initializer is always the illegal parenthesized form (the chained parser only
/// rewrites the bare form inside `assert!`/`assume!`/contract macros, never a
/// `let` init). Fail-closed: rejecting a program can never wrongly verify it. The
/// diagnostic contains the upstream message verbatim.
fn choose_binder_paren_error(local: &syn::Local) -> Option<TrustVcError> {
    let init = local.init.as_ref()?;
    let Expr::Call(call) = init.expr.as_ref() else {
        return None;
    };
    let Expr::Path(func) = call.func.as_ref() else {
        return None;
    };
    if func.qself.is_some() || func.path.segments.len() != 1 {
        return None;
    }
    if !matches!(
        func.path.segments[0].ident.to_string().as_str(),
        "forall" | "exists" | "choose"
    ) {
        return None;
    }
    if !matches!(call.args.first(), Some(Expr::Closure(_))) {
        return None;
    }
    Some(TrustVcError::Encoding {
        context: "extract body assertions",
        detail: "forall, choose, and exists do not allow parentheses".to_string(),
    })
}

/// Verus rejects a `choose_tuple(|i, j| ..)` whose binder tuple type does not
/// match the ascribed `let` pattern type (upstream choose.rs
/// `test1_choose_tuple_wrong_type`: `let (i, j): (int, nat) = choose_tuple(|i:
/// int, j: int| ..)` — the binders are `(int, int)` but the ascription is `(int,
/// nat)`). Fail-closed; the diagnostic contains the upstream message verbatim.
/// Only fires when every binder carries an explicit type ascription and the `let`
/// pattern is a typed tuple, so it cannot misfire on inferred forms.
fn choose_tuple_wrong_type_error(local: &syn::Local) -> Option<TrustVcError> {
    let init = local.init.as_ref()?;
    let Expr::Call(call) = init.expr.as_ref() else {
        return None;
    };
    let Expr::Path(func) = call.func.as_ref() else {
        return None;
    };
    if func.path.segments.last()?.ident != "choose_tuple" {
        return None;
    }
    let Some(Expr::Closure(closure)) = call.args.first() else {
        return None;
    };
    let syn::Pat::Type(pat_type) = &local.pat else {
        return None;
    };
    let syn::Type::Tuple(ascribed) = pat_type.ty.as_ref() else {
        return None;
    };
    let binder_types: Vec<String> = closure
        .inputs
        .iter()
        .map(|pat| match pat {
            syn::Pat::Type(pt) => pt.ty.to_token_stream().to_string(),
            // A binder without an explicit type: cannot compare — treat as a
            // fresh string so a genuine mismatch is not masked, but an all-typed
            // match still short-circuits to None below.
            _ => String::new(),
        })
        .collect();
    let ascribed_types: Vec<String> = ascribed
        .elems
        .iter()
        .map(|ty| ty.to_token_stream().to_string())
        .collect();
    if binder_types == ascribed_types {
        return None;
    }
    Some(TrustVcError::Encoding {
        context: "extract body assertions",
        detail: "expected choose_tuple to have type".to_string(),
    })
}

/// Verus rejects destructuring ASSIGNMENT outright — "The verifier does not
/// yet support the following Rust feature: destructuring assignment"
/// (upstream basic.rs `destructuring_assignment_unsupported`;
/// `rust_verify/src/rust_to_vir_expr.rs` tuple-LHS assign + `util.rs`
/// unsupported_err prefix). Fires on a tuple / array / struct pattern LHS of
/// an `=` expression anywhere, in any mode. `let (a, b) = ..` destructuring
/// BINDINGS are unaffected (they are `Stmt::Local`, never an `ExprAssign`),
/// and `_ = expr` is an `Expr::Infer` LHS, left on the existing path.
/// Fail-closed; the diagnostic contains the upstream message verbatim.
fn destructuring_assignment_error(target: &Expr) -> Option<TrustVcError> {
    match strip_place_wrappers(target) {
        Expr::Tuple(_) | Expr::Array(_) | Expr::Struct(_) => Some(TrustVcError::Encoding {
            context: "extract body assertions",
            detail:
                "The verifier does not yet support the following Rust feature: destructuring assignment"
                    .to_string(),
        }),
        _ => None,
    }
}

fn out_of_bounds_vec_literal_index_assignment_error(
    target: &Expr,
    index: usize,
    len: usize,
) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec literal indexed assignment is out of bounds in vc_extraction: `{}`. \
             The modeled Vec literal has length {len}, but the assignment index is {index}; \
             out-of-bounds mutation is rejected to avoid silently accepting unreachable Rust code.",
            target.to_token_stream()
        ),
    }
}

fn out_of_bounds_vec_literal_index_error(target: &Expr, index: usize, len: usize) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec literal index is out of bounds in vc_extraction: `{}`. \
             The modeled Vec literal has length {len}, but the access index is {index}; \
             out-of-bounds access is rejected to avoid solver Unknown or silently accepting unreachable Rust code.",
            target.to_token_stream()
        ),
    }
}

fn unsupported_reference_index_assignment_error(target: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "indexed assignment through a borrowed array/reference alias is unsupported in \
             vc_extraction: `{}`. Direct indexed mutation is modeled only for original local \
             or parameter array/Seq places; borrowed aliases are rejected to avoid treating \
             aliased state as an independent array.",
            target.to_token_stream()
        ),
    }
}

fn unsupported_vec_insert_receiver_error(receiver: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec::insert receiver is unsupported in vc_extraction: `{}`. \
             TrustVc only models direct local Vec receivers with unaliased scoped state; \
             borrowed aliases and projected receivers are rejected to avoid reasoning about stale Vec views.",
            receiver.to_token_stream()
        ),
    }
}

fn unsupported_vec_mutation_receiver_error(method: &str, receiver: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec::{method} receiver is unsupported in vc_extraction: `{}`. \
             TrustVc only models direct local Vec receivers with unaliased scoped state; \
             borrowed aliases and projected receivers are rejected to avoid reasoning about stale Vec views.",
            receiver.to_token_stream()
        ),
    }
}

fn unsupported_vec_insert_index_error(index: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec::insert index expression is unsupported in vc_extraction: `{}`. \
             TrustVc only models literal or local-variable insert indices so the source expression \
             is not duplicated while rewriting the Vec view update.",
            index.to_token_stream()
        ),
    }
}

fn unsupported_vec_append_arg_error(arg: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec::append argument is unsupported in vc_extraction: `{}`. \
             TrustVc only models append from a direct `&mut local_vec` argument with scoped Vec state.",
            arg.to_token_stream()
        ),
    }
}

fn unsupported_vec_insert_side_effect_error(method_call: &syn::ExprMethodCall) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec::insert with side-effecting arguments is unsupported in vc_extraction: `{}`. \
             TrustVc rejects these calls rather than duplicating or reordering argument effects in the scoped Vec view model.",
            method_call.to_token_stream()
        ),
    }
}

fn unsupported_vec_mutation_side_effect_error(
    method: &str,
    method_call: &syn::ExprMethodCall,
) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Vec::{method} with side-effecting arguments is unsupported in vc_extraction: `{}`. \
             TrustVc rejects these calls rather than duplicating or reordering argument effects in the scoped Vec view model.",
            method_call.to_token_stream()
        ),
    }
}

/// Conservative: does this block contain ANY write through a deref LHS
/// (`*place = ..` or `*place op= ..`)? Used to fail-close deref writes in
/// non-inline-execution blocks (async/try/const) where neither inline SSA nor
/// exit-havoc modeling is correct.
fn block_contains_deref_write(block: &syn::Block) -> bool {
    struct Finder {
        found: bool,
    }
    fn is_deref_lhs(e: &Expr) -> bool {
        let mut cur = e;
        loop {
            match cur {
                Expr::Paren(p) => cur = &p.expr,
                Expr::Group(g) => cur = &g.expr,
                Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => return true,
                _ => return false,
            }
        }
    }
    impl<'ast> Visit<'ast> for Finder {
        fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
            if is_deref_lhs(&assign.left) {
                self.found = true;
            }
            syn::visit::visit_expr_assign(self, assign);
        }
        fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
            if compound_assignment_value_op(&binary.op).is_some() && is_deref_lhs(&binary.left) {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, binary);
        }
    }
    let mut finder = Finder { found: false };
    finder.visit_block(block);
    finder.found
}

fn unsupported_deref_assignment_error(target: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "assignment through a dereferenced reference is unsupported in vc_extraction: `{}`. \
             TrustVc only models direct writes through aliases created by `&mut local` or by \
             direct scalar mutable-reference parameters when the referent has scoped state at \
             borrow time; non-scalar parameter-derived aliases, reborrows, tuple/index/nested \
             projections, and nested mutable-reference places are rejected to avoid \
             silently treating aliased mutable state as unchanged.",
            target.to_token_stream()
        ),
    }
}

fn unsupported_mut_ref_projection_assignment_error(target: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "assignment through a mutable-reference projection is unsupported in vc_extraction: `{}`. \
             TrustVc only models direct `*alias = value` writes and one-level named-field \
             `alias.field = value` writes for aliases created by `&mut local` when the local has \
             scoped struct state at borrow time; index, tuple-field, nested projections, \
             parameter-derived aliases, field-borrow projections, and reborrows are rejected to avoid \
             reasoning about partially stale aliased state.",
            target.to_token_stream()
        ),
    }
}

fn unsupported_field_assignment_error(target: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "direct field assignment to an owned/parameter struct is unsupported in this shape: `{}`. \
             TrustVc models a direct `s.field = value` (named, tuple, and nested) write as a \
             functional struct update, but this shape (an unresolved struct type, a side-effecting \
             right-hand side, or an unmodelable field path) is rejected (fail closed) rather than \
             risk dropping the write silently.",
            target.to_token_stream()
        ),
    }
}

fn unsupported_index_compound_assignment_error(op: &BinOp) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "indexed compound assignment to array element is unsupported in vc_extraction: `{}`. \
             Only directly indexed local array/Seq variables can be modeled safely; unsupported \
             targets are rejected to avoid reasoning about stale array state.",
            op.to_token_stream()
        ),
    }
}

/// The value operator of a compound-assignment operator (`+=` → `+`) as a syn
/// `BinOp`, for AST-level desugaring (`*P op= rhs` → `*P = (*P) op (rhs)`).
/// The `BinOp` twin of [`compound_assignment_value_op`] — kept exhaustive over
/// the same ten operators so the two can never drift silently.
fn value_binop_for_assignment(op: &BinOp) -> Option<BinOp> {
    Some(match op {
        BinOp::AddAssign(_) => BinOp::Add(Default::default()),
        BinOp::SubAssign(_) => BinOp::Sub(Default::default()),
        BinOp::MulAssign(_) => BinOp::Mul(Default::default()),
        BinOp::DivAssign(_) => BinOp::Div(Default::default()),
        BinOp::RemAssign(_) => BinOp::Rem(Default::default()),
        BinOp::BitXorAssign(_) => BinOp::BitXor(Default::default()),
        BinOp::BitAndAssign(_) => BinOp::BitAnd(Default::default()),
        BinOp::BitOrAssign(_) => BinOp::BitOr(Default::default()),
        BinOp::ShlAssign(_) => BinOp::Shl(Default::default()),
        BinOp::ShrAssign(_) => BinOp::Shr(Default::default()),
        _ => return None,
    })
}

fn compound_assignment_value_op(op: &BinOp) -> Option<&'static str> {
    match op {
        BinOp::AddAssign(_) => Some("+"),
        BinOp::SubAssign(_) => Some("-"),
        BinOp::MulAssign(_) => Some("*"),
        BinOp::DivAssign(_) => Some("/"),
        BinOp::RemAssign(_) => Some("%"),
        BinOp::BitXorAssign(_) => Some("^"),
        BinOp::BitAndAssign(_) => Some("&"),
        BinOp::BitOrAssign(_) => Some("|"),
        BinOp::ShlAssign(_) => Some("<<"),
        BinOp::ShrAssign(_) => Some(">>"),
        _ => None,
    }
}

fn is_verus_assert_forall_by(tokens: &TokenStream) -> bool {
    let mut iter = tokens.clone().into_iter();
    match iter.next() {
        Some(TokenTree::Ident(ident)) if ident == "forall" => {
            let starts_with_binder = matches!(
                iter.next(),
                Some(TokenTree::Punct(punct)) if punct.as_char() == '|'
            );
            starts_with_binder && has_top_level_by_block_after_binder(iter)
        }
        Some(TokenTree::Ident(ident)) if ident == "assert" => {
            matches!(
                iter.next(),
                Some(TokenTree::Ident(ident)) if ident == "forall"
            ) && matches!(
                iter.next(),
                Some(TokenTree::Punct(punct)) if punct.as_char() == '|'
            ) && has_top_level_by_block_after_binder(iter)
        }
        _ => false,
    }
}

fn has_top_level_by_block_after_binder(iter: impl IntoIterator<Item = TokenTree>) -> bool {
    let mut seen_closing_pipe = false;
    let mut iter = iter.into_iter().peekable();

    while let Some(tree) = iter.next() {
        if !seen_closing_pipe {
            if matches!(tree, TokenTree::Punct(punct) if punct.as_char() == '|') {
                seen_closing_pipe = true;
            }
            continue;
        }

        if matches!(&tree, TokenTree::Ident(ident) if ident == "by") {
            return matches!(
                iter.peek(),
                Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Brace
            );
        }
    }

    false
}

fn parse_local_macro_rules_item(
    item_macro: &ItemMacro,
) -> TrustVcResult<(String, LocalMacroDefinition)> {
    let name = item_macro
        .ident
        .as_ref()
        .map(ToString::to_string)
        .ok_or_else(|| unsupported_local_macro_definition_error(None, "missing macro name"))?;
    let body = parse_single_empty_macro_rules_body(&item_macro.mac.tokens, &name)?;
    Ok((name, LocalMacroDefinition { body }))
}

fn parse_single_empty_macro_rules_body(
    tokens: &TokenStream,
    name: &str,
) -> TrustVcResult<TokenStream> {
    let mut iter = tokens.clone().into_iter();
    let matcher = match iter.next() {
        Some(TokenTree::Group(group))
            if group.delimiter() == Delimiter::Parenthesis && group.stream().is_empty() =>
        {
            group
        }
        _ => {
            return Err(unsupported_local_macro_definition_error(
                Some(name),
                "only an empty `()` matcher is supported",
            ));
        }
    };
    drop(matcher);

    match (iter.next(), iter.next()) {
        (Some(TokenTree::Punct(eq)), Some(TokenTree::Punct(gt)))
            if eq.as_char() == '=' && gt.as_char() == '>' => {}
        _ => {
            return Err(unsupported_local_macro_definition_error(
                Some(name),
                "expected a single `() => ...` rule",
            ));
        }
    }

    let body = match iter.next() {
        Some(TokenTree::Group(group)) => group.stream(),
        _ => {
            return Err(unsupported_local_macro_definition_error(
                Some(name),
                "expected a delimited macro transcriber",
            ));
        }
    };

    let trailing = iter.collect::<Vec<_>>();
    if trailing.is_empty()
        || matches!(
            trailing.as_slice(),
            [TokenTree::Punct(punct)] if matches!(punct.as_char(), ';' | ',')
        )
    {
        Ok(body)
    } else {
        Err(unsupported_local_macro_definition_error(
            Some(name),
            "multiple macro arms are not supported",
        ))
    }
}

fn ensure_zero_arg_local_macro_invocation(mac: &Macro, name: &str) -> TrustVcResult<()> {
    if mac.tokens.is_empty() {
        Ok(())
    } else {
        Err(local_macro_expansion_error(
            name,
            "only zero-argument function-local macro invocations are supported",
        ))
    }
}

fn parse_local_macro_expansion_block(
    name: &str,
    definition: &LocalMacroDefinition,
) -> TrustVcResult<syn::Block> {
    let body = &definition.body;
    syn::parse2::<syn::Block>(quote::quote!({ #body })).map_err(|source| {
        local_macro_expansion_error(
            name,
            format!("failed to parse expanded macro body as Rust statements: {source}"),
        )
    })
}

fn unsupported_local_macro_definition_error(
    name: Option<&str>,
    detail: impl Into<String>,
) -> TrustVcError {
    let name = name.map(|name| format!(" `{name}`")).unwrap_or_default();
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Unsupported nested macro_rules! item{name} in function body — only single-arm \
             zero-argument function-local macro_rules! items can be expanded; nested macro \
             items are rejected to avoid silently dropping proof obligations: {}",
            detail.into()
        ),
    }
}

fn unsupported_local_macro_expression_error(name: &str) -> TrustVcError {
    local_macro_expansion_error(
        name,
        "function-local macro invocations in expression position are not supported",
    )
}

fn local_macro_expansion_error(name: &str, detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Unsupported function-local macro `{name}!()` in vc_extraction — local macros are \
             expanded only for the supported statement subset to avoid silently dropping proof \
             obligations: {}",
            detail.into()
        ),
    }
}

fn unsupported_nested_item_error(item: &Item) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "Unsupported nested {} item in function body — nested items are rejected \
             to avoid silently dropping proof obligations",
            nested_item_kind(item)
        ),
    }
}

fn nested_item_kind(item: &Item) -> &'static str {
    match item {
        Item::Const(_) => "const",
        Item::Enum(_) => "enum",
        Item::ExternCrate(_) => "extern crate",
        Item::Fn(_) => "fn",
        Item::ForeignMod(_) => "extern block",
        Item::Impl(_) => "impl",
        Item::Macro(_) => "macro",
        Item::Mod(_) => "mod",
        Item::Static(_) => "static",
        Item::Struct(_) => "struct",
        Item::Trait(_) => "trait",
        Item::TraitAlias(_) => "trait alias",
        Item::Type(_) => "type",
        Item::Union(_) => "union",
        Item::Use(_) => "use",
        Item::Verbatim(_) => "verbatim",
        _ => "unknown",
    }
}

/// Returns `true` iff `block` (a loop body) contains a `break` that exits *this*
/// loop, accounting for labels and loop nesting.
///
/// This gates whether the post-loop normal-exit fact `!(guard)` may be assumed:
/// it is sound only when the guard becoming false is the *only* way to leave the
/// loop. A `break` to a strictly-nested inner loop (or labeled block) does NOT
/// exit this loop and must not suppress the fact; a `break` to this loop (or an
/// enclosing one) does. Fail-closed: any break we can't prove targets a nested
/// construct is treated as exiting this loop. Part of #2777/loops (B2).
fn contains_break(block: &syn::Block) -> bool {
    #[derive(Clone)]
    enum NestedTarget {
        /// A nested loop (`while`/`loop`/`for`) with its optional label.
        Loop(Option<String>),
        /// A labeled block (`'b: { ... }`), reachable only by its label.
        LabeledBlock(String),
    }

    struct BreakVisitor {
        /// Stack of break-targets nested *inside* the loop body under analysis.
        nested: Vec<NestedTarget>,
        /// Set once a `break` is found that exits the loop under analysis.
        exits_this_loop: bool,
    }

    impl BreakVisitor {
        fn label_in_scope(&self, label: &str) -> bool {
            self.nested.iter().any(|target| match target {
                NestedTarget::Loop(Some(name)) => name == label,
                NestedTarget::LabeledBlock(name) => name == label,
                NestedTarget::Loop(None) => false,
            })
        }

        fn has_nested_loop(&self) -> bool {
            self.nested
                .iter()
                .any(|target| matches!(target, NestedTarget::Loop(_)))
        }

        fn with_nested<F>(&mut self, target: NestedTarget, descend: F)
        where
            F: FnOnce(&mut Self),
        {
            self.nested.push(target);
            descend(self);
            self.nested.pop();
        }
    }

    fn label_name(label: &Option<syn::Label>) -> Option<String> {
        label.as_ref().map(|label| label.name.ident.to_string())
    }

    impl<'ast> Visit<'ast> for BreakVisitor {
        fn visit_expr_break(&mut self, expr: &'ast syn::ExprBreak) {
            if self.exits_this_loop {
                return;
            }
            let exits = match &expr.label {
                // Labeled break: exits this loop unless it targets a strictly
                // nested loop or labeled block.
                Some(lifetime) => !self.label_in_scope(&lifetime.ident.to_string()),
                // Unlabeled break: targets the innermost nested loop if one
                // exists; otherwise it targets this loop.
                None => !self.has_nested_loop(),
            };
            if exits {
                self.exits_this_loop = true;
            }
            // A `break expr` operand may itself contain a loop-exiting break.
            if let Some(value) = &expr.expr {
                self.visit_expr(value);
            }
        }

        fn visit_expr_while(&mut self, expr: &'ast syn::ExprWhile) {
            // The guard is evaluated in this loop's scope (no new target).
            self.visit_expr(&expr.cond);
            self.with_nested(NestedTarget::Loop(label_name(&expr.label)), |visitor| {
                visitor.visit_block(&expr.body);
            });
        }

        fn visit_expr_loop(&mut self, expr: &'ast syn::ExprLoop) {
            self.with_nested(NestedTarget::Loop(label_name(&expr.label)), |visitor| {
                visitor.visit_block(&expr.body);
            });
        }

        fn visit_expr_for_loop(&mut self, expr: &'ast syn::ExprForLoop) {
            self.visit_expr(&expr.expr);
            self.with_nested(NestedTarget::Loop(label_name(&expr.label)), |visitor| {
                visitor.visit_block(&expr.body);
            });
        }

        fn visit_expr_block(&mut self, expr: &'ast syn::ExprBlock) {
            match label_name(&expr.label) {
                Some(label) => {
                    self.with_nested(NestedTarget::LabeledBlock(label), |visitor| {
                        visitor.visit_block(&expr.block);
                    });
                }
                None => self.visit_block(&expr.block),
            }
        }

        // A `break` cannot cross a closure boundary, so a break inside a nested
        // closure can never target an enclosing loop. Do not descend.
        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {}

        // Nested items introduce a fresh control-flow context. Do not descend.
        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = BreakVisitor {
        nested: Vec::new(),
        exits_this_loop: false,
    };
    visitor.visit_block(block);
    visitor.exits_this_loop
}

/// Returns `true` iff the while-loop body is a flat, branch-free sequence of
/// total scalar assignments over pure arithmetic — the ONLY body shape for
/// which the scoped value-numbering yields an EXACT single-iteration transition
/// for every modified variable (M4-minimal).
///
/// Why this exact shape: at body entry every modified var is invalidated, so a
/// bare read denotes the loop-head value. In a flat sequence of total
/// assignments, every read therefore sees the exact sequential value and every
/// modified var ends with a scoped value equal to its true post-body value as a
/// function of loop-head vars. Any construct that can re-invalidate a var
/// mid-body — a conditional (`if`/`match`, which invalidates a not-jointly-
/// assigned var to bare), a nested block/loop (whose assignment scope is
/// popped), or a call that mutates through `&mut` — followed by a dependent
/// read would silently pin a later var's transition to the loop-head value,
/// missing a real post-state and risking a FALSE Verified. Such bodies fail
/// this gate and fall back to pure havoc (sound, incomplete).
///
/// A FRESH immutable `let` binding over pure arithmetic is admitted too (see
/// `stmt_is_flat_scalar_assignment_or_spec`): it introduces a NEW name and
/// re-invalidates nothing, so every modified var still ends the body with an
/// exact scoped value. `binds_existing_name` is the load-bearing narrowness pin
/// — it must report `true` for any name that already denotes something in this
/// scope (a loop-modified var, a declared VC variable, or an outer scoped
/// let-local). Shadowing a loop-MODIFIED var is the cardinal hazard: the
/// end-of-body transition capture reads `lookup_scoped(var)` and would pick up
/// the shadow's value, while Rust reverts the real var at block end — a WRONG
/// transition, i.e. a false `Verified`.
fn loop_body_transition_is_exact(
    block: &syn::Block,
    binds_existing_name: &dyn Fn(&str) -> bool,
) -> bool {
    block
        .stmts
        .iter()
        .all(|stmt| stmt_is_flat_scalar_assignment_or_spec(stmt, binds_existing_name))
}

/// True for a single statement that is either a total scalar assignment over
/// pure arithmetic, a side-effect-free spec assertion macro, or a flat
/// collection `push` re-binding (`db.push(<pure-arith>)`) — the accumulate
/// shape of the cutting-planes `replay_derivation` loop, or a FRESH immutable
/// `let` binding over pure arithmetic. Anything else (items, nested control
/// flow, other bare expressions) disqualifies the body from exact transition
/// capture.
fn stmt_is_flat_scalar_assignment_or_spec(
    stmt: &Stmt,
    binds_existing_name: &dyn Fn(&str) -> bool,
) -> bool {
    match stmt {
        // A fresh immutable `let x = <pure-arith>;`. Sound under this gate's own
        // argument: the binding introduces a NEW name, so it re-invalidates no
        // existing var, and its RHS is the same total, side-effect-free function
        // of the already-exact scoped state that the assignment arm requires.
        // Every read after it therefore still sees the exact sequential value,
        // and every modified var still ends with an exact scoped value.
        //
        // NARROWNESS PINS, all load-bearing:
        //   * `binds_existing_name` — a shadow of a loop-MODIFIED var would make
        //     the end-of-body transition capture read the SHADOW instead of the
        //     real var (which Rust reverts at block end): a wrong transition and
        //     a false `Verified`. A shadow of any other in-scope name likewise
        //     re-points later reads (including a textually later `invariant!`),
        //     so those are rejected as well.
        //   * `mutability` — a `let mut` can be re-assigned later in the body;
        //     only an immutable binding is a one-shot definition.
        //   * `diverge` (`let ... else { ... }`) — a divergent arm is branching
        //     control flow, exactly what this gate excludes.
        //   * `by_ref` / `subpat` / non-ident patterns — not a flat scalar bind.
        Stmt::Local(local) => {
            let Some(name) = flat_scalar_local_binding_name(local) else {
                return false;
            };
            !binds_existing_name(&name)
        }
        // Spec assertion macros (`invariant!`, `assert!`, `assume!`, …) never
        // mutate exec scalars, so they do not perturb the value-numbering.
        Stmt::Macro(stmt_macro) => is_spec_assertion_macro_path(&stmt_macro.mac.path),
        Stmt::Expr(expr, _) => match expr {
            Expr::Assign(assign) => {
                expr_path_ident(&assign.left).is_some()
                    && (expr_is_pure_arith(&assign.right)
                        // `db = db.push(<pure-arith>)` — the functional (Seq)
                        // push re-binding, value-numbered to `(db).push(value)`
                        // exactly like the in-place `db.push(..)` statement
                        // below. Sound to capture for the same reason: the RHS
                        // is a total, side-effect-free function of the loop-head
                        // state.
                        || expr_is_flat_collection_push(&assign.right))
            }
            Expr::Binary(binary) if is_assignment_binop(&binary.op) => {
                expr_path_ident(&binary.left).is_some() && expr_is_pure_arith(&binary.right)
            }
            Expr::Macro(expr_macro) => is_spec_assertion_macro_path(&expr_macro.mac.path),
            // In-place `db.push(<pure-arith>)` accumulate step. The collection
            // mutation is value-numbered to the re-binding `db = (db).push(v)`
            // by `assign_local_push_method_call`, so the single-iteration
            // transition for `db` is the exact, side-effect-free function
            // `(db_pre).push(value_pre)` — preserving the inductive-step
            // soundness of the scalar-only capture (a non-flat body still falls
            // back to pure havoc). Part of the cutting-planes whole-loop lift.
            Expr::MethodCall(method_call) => expr_method_is_flat_collection_push(method_call),
            _ => false,
        },
        _ => false,
    }
}

/// The bound name of a `let` statement that is a FLAT SCALAR BINDING: a simple,
/// immutable, non-`ref`, sub-pattern-free ident initialized from a pure
/// arithmetic expression, with no `else` arm and no attributes. `None` for
/// every other `let`, which keeps the loop body out of exact transition capture.
///
/// A type annotation is optional: the binding never becomes a VC variable — it
/// is value-numbered and substituted into the reads that follow — so its width
/// is carried by the pure-arith RHS it was defined from.
fn flat_scalar_local_binding_name(local: &syn::Local) -> Option<String> {
    if !local.attrs.is_empty() {
        return None;
    }
    let init = local.init.as_ref()?;
    // `let ... else { ... }` is branching control flow.
    if init.diverge.is_some() {
        return None;
    }
    if !expr_is_pure_arith(&init.expr) {
        return None;
    }
    let pat_ident = match &local.pat {
        Pat::Ident(pat_ident) => pat_ident,
        Pat::Type(pat_type) => match &*pat_type.pat {
            Pat::Ident(pat_ident) => pat_ident,
            _ => return None,
        },
        _ => return None,
    };
    // `mut` could be re-assigned later in the body; `ref` binds a reference and
    // a sub-pattern (`x @ ..`) is not a flat scalar bind.
    if pat_ident.mutability.is_some() || pat_ident.by_ref.is_some() || pat_ident.subpat.is_some() {
        return None;
    }
    Some(pat_ident.ident.to_string())
}

/// True iff `expr` is a flat collection `push` of a pure-arithmetic value onto a
/// plain path-ident receiver: `recv.push(<pure-arith>)`. This is the only
/// collection-mutation form admitted into exact single-iteration transition
/// capture; the receiver must be a bare local/parameter (no deref/index/field)
/// so the value-numbering re-binding `recv = (recv).push(value)` is exact, and
/// the argument must be side-effect-free pure arithmetic so the transition is a
/// total function of the loop-head state (the same gate the scalar path uses).
fn expr_method_is_flat_collection_push(method_call: &syn::ExprMethodCall) -> bool {
    method_call.method == "push"
        && method_call.args.len() == 1
        && expr_path_ident(&method_call.receiver).is_some()
        && method_call
            .args
            .first()
            .is_some_and(|arg| expr_is_pure_arith(arg))
}

/// True iff `expr` is a flat collection `push` expression (used as the RHS of a
/// functional re-binding `db = db.push(value)`).
fn expr_is_flat_collection_push(expr: &Expr) -> bool {
    match expr {
        Expr::MethodCall(method_call) => expr_method_is_flat_collection_push(method_call),
        Expr::Paren(inner) => expr_is_flat_collection_push(&inner.expr),
        Expr::Group(inner) => expr_is_flat_collection_push(&inner.expr),
        _ => false,
    }
}

/// True iff the loop `body` carries a loop invariant (or `invariant_except_break`
/// / `loop_ensures`) at its top level. When present, the invariant + encoder
/// `loop_modified_vars` machinery performs the post-loop havoc, so the loop-frame
/// model must keep the bare (invariant-constrained) symbol; when ABSENT, the
/// loop is `invariant!(true)` and every modified declared variable must be
/// freshened at the join (see `havoc_modified_var_at_loop_join`). Verus requires
/// invariants directly in the loop body, so a top-level statement scan is exact.
fn block_has_loop_invariant(block: &syn::Block) -> bool {
    block.stmts.iter().any(|stmt| {
        let mac = match stmt {
            syn::Stmt::Macro(stmt_macro) => Some(&stmt_macro.mac),
            syn::Stmt::Expr(Expr::Macro(expr_macro), _) => Some(&expr_macro.mac),
            _ => None,
        };
        mac.and_then(|mac| super::path_last_segment(&mac.path))
            .is_some_and(|name| {
                matches!(
                    name.as_str(),
                    "invariant"
                        | "trust_vc_invariant"
                        | "invariant_except_break"
                        | "trust_vc_invariant_except_break"
                        | "loop_ensures"
                        | "trust_vc_loop_ensures"
                )
            })
    })
}

/// Parsed conditions of every top-level `invariant!` / `invariant_except_break!`
/// statement in `block`. A loop invariant is the inductive hypothesis available
/// in the loop body, so it is used to WEAKEN loop-body exec arithmetic-safety
/// obligations (the Verus check "the body arithmetic does not panic GIVEN the
/// invariant holds at body entry"). `loop_ensures!` is deliberately excluded —
/// it constrains the loop EXIT state, not the body-entry state, so it is not a
/// body hypothesis. A macro whose tokens fail to parse is skipped (the
/// obligation then stays unweakened — sound, possibly over-rejecting). The
/// rendering of each returned expr over the fresh havoc symbols (NOT the bare
/// invariant variables) is the caller's responsibility.
fn collect_loop_invariant_exprs(block: &syn::Block) -> Vec<Expr> {
    let mut exprs = Vec::new();
    for stmt in &block.stmts {
        let mac = match stmt {
            syn::Stmt::Macro(stmt_macro) => &stmt_macro.mac,
            syn::Stmt::Expr(Expr::Macro(expr_macro), _) => &expr_macro.mac,
            _ => continue,
        };
        let is_invariant = super::path_last_segment(&mac.path).is_some_and(|name| {
            matches!(
                name.as_str(),
                "invariant"
                    | "trust_vc_invariant"
                    | "invariant_except_break"
                    | "trust_vc_invariant_except_break"
            )
        });
        if !is_invariant {
            continue;
        }
        if let Ok(expr) =
            crate::chained_comparisons::parse_expr_tokens_with_chains(mac.tokens.clone())
        {
            exprs.push(expr);
        }
    }
    exprs
}

/// True iff `word` occurs in `haystack` as a WHOLE Rust identifier — bounded on
/// both sides by a non-identifier character (not an ASCII alphanumeric or `_`).
/// Used to detect a BARE havoc-variable reference in a rendered obligation while
/// never matching it as a substring of a longer identifier (e.g. searching for
/// `i` must NOT match inside `i__loopbody_0` or `idx`). `word` is always a real
/// identifier here, so an empty needle never arises.
fn string_contains_whole_word(haystack: &str, word: &str) -> bool {
    if word.is_empty() {
        return false;
    }
    let bytes = haystack.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut search_from = 0;
    while let Some(rel) = haystack[search_from..].find(word) {
        let start = search_from + rel;
        let end = start + word.len();
        let before_ok = start == 0 || !is_ident(bytes[start - 1]);
        let after_ok = end == bytes.len() || !is_ident(bytes[end]);
        if before_ok && after_ok {
            return true;
        }
        search_from = start + 1;
    }
    false
}

/// True iff `path`'s final segment names a side-effect-free spec assertion
/// macro. These never assign exec/scalar variables, so a body containing them
/// remains a faithful flat assignment sequence.
fn is_spec_assertion_macro_path(path: &syn::Path) -> bool {
    super::path_last_segment(path).is_some_and(|name| {
        name == "invariant"
            || name == "invariant_except_break"
            || name == "assume"
            || name == "assert"
            // `loop_decreases!` assigns no exec scalar, so — like `invariant!` —
            // it cannot perturb the body value-numbering. It MUST be admitted
            // here or `loop_body_transition_is_exact` goes `false` for the whole
            // loop, starving even the loop invariant's inductive transition
            // (silent-soundness trap). Part of the file-path `loop_decreases!`
            // wiring.
            || name == "loop_decreases"
            || name.starts_with("assert_")
    })
}

/// True iff `expr` is a pure arithmetic expression: only identifiers, literals,
/// parentheses/grouping, unary/binary arithmetic and comparison operators, and
/// numeric casts. Excludes calls, method calls, indexing, field access,
/// references, blocks, closures, and any control-flow expression — i.e. nothing
/// that could carry a side effect, non-determinism, or conditional value.
fn expr_is_pure_arith(expr: &Expr) -> bool {
    match expr {
        Expr::Path(_) | Expr::Lit(_) => true,
        Expr::Paren(inner) => expr_is_pure_arith(&inner.expr),
        Expr::Group(inner) => expr_is_pure_arith(&inner.expr),
        Expr::Unary(unary) => expr_is_pure_arith(&unary.expr),
        Expr::Cast(cast) => expr_is_pure_arith(&cast.expr),
        Expr::Binary(binary) if !is_assignment_binop(&binary.op) => {
            expr_is_pure_arith(&binary.left) && expr_is_pure_arith(&binary.right)
        }
        _ => false,
    }
}

/// True when the function body has a non-fall-through *normal* exit — a
/// `return` statement or a `?` (`Expr::Try`) — that is not nested inside a
/// closure or item boundary. Such an exit means the body's fall-through final
/// value for a `&mut` parameter need not hold on every path the postcondition
/// must cover, so the two-state postcondition rewriter fails closed rather than
/// risk a false `Verified`. (A diverging `panic!`/`unreachable!` is NOT an early
/// exit: it never returns, so no postcondition obligation applies on that path.)
fn body_has_early_exit(block: &syn::Block) -> bool {
    struct EarlyExitVisitor {
        found: bool,
    }

    impl<'ast> Visit<'ast> for EarlyExitVisitor {
        fn visit_expr_return(&mut self, _expr: &'ast syn::ExprReturn) {
            self.found = true;
        }

        fn visit_expr_try(&mut self, _expr: &'ast syn::ExprTry) {
            self.found = true;
        }

        // A `return`/`?` inside a nested closure or item belongs to that inner
        // control-flow scope, not this function body.
        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {}
        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = EarlyExitVisitor { found: false };
    visitor.visit_block(block);
    visitor.found
}

/// The subset of `params` that are the target of a deref-assignment (`*P = ..`
/// or `*P op= ..`) anywhere in the function body (ignoring nested item
/// boundaries). A `&mut` scalar parameter that is never deref-assigned and never
/// escapes is unchanged by the body, so a postcondition reading it can soundly
/// use its entry value (entry == final). A parameter that IS deref-assigned but
/// was not cleanly tracked to the exit has an uncertain final value (havoced by
/// a branch/loop join), so the rewriter fails closed.
fn mut_ref_params_mutated_in_body(
    block: &syn::Block,
    params: &BTreeSet<String>,
) -> BTreeSet<String> {
    struct MutationVisitor<'a> {
        params: &'a BTreeSet<String>,
        mutated: BTreeSet<String>,
    }

    fn deref_assignment_param(lhs: &Expr, params: &BTreeSet<String>) -> Option<String> {
        let lhs = strip_place_wrappers(lhs);
        if let Expr::Unary(unary) = lhs {
            if matches!(unary.op, syn::UnOp::Deref(_)) {
                if let Expr::Path(path) = unary.expr.as_ref() {
                    if path.qself.is_none() {
                        if let Some(ident) = path.path.get_ident() {
                            let name = ident.to_string();
                            if params.contains(&name) {
                                return Some(name);
                            }
                        }
                    }
                }
            }
        }
        None
    }

    impl<'ast> Visit<'ast> for MutationVisitor<'_> {
        fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
            if let Some(name) = deref_assignment_param(&assign.left, self.params) {
                self.mutated.insert(name);
            }
            syn::visit::visit_expr_assign(self, assign);
        }

        fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
            if is_assignment_binop(&binary.op) {
                if let Some(name) = deref_assignment_param(&binary.left, self.params) {
                    self.mutated.insert(name);
                }
            }
            syn::visit::visit_expr_binary(self, binary);
        }

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = MutationVisitor {
        params,
        mutated: BTreeSet::new(),
    };
    visitor.visit_block(block);
    visitor.mutated
}

/// The subset of `params` (each a `&mut <collection-or-array>` parameter, modeled
/// as `Seq`/`Set`/`Map`/`Multiset`/`Array`) that is mutated IN PLACE by a method call in
/// the body — i.e. a method call `P.m(..)` (or `(*P).m(..)`) where `m` is NOT a
/// recognized pure `&self` read (`len`/`get`/`index`/`contains`/`iter`/…).
///
/// SOUNDNESS (the straight-line `&mut`-collection postcondition gap, the
/// non-loop sibling of the catastrophic loop gap): the string body model
/// resolves a bare `&mut Vec`/`&mut HashMap`/… parameter in a postcondition to
/// its ENTRY-snapshot variable (collections are not `supported_mut_ref` scalars,
/// so the two-state final-value rewrite never runs for them). A method mutation
/// (`v.clear()`/`v.push(..)`/`v.retain(..)`/`v.extend(..)`/`v.sort()`/…) is not
/// threaded into that snapshot, so a postcondition reading the parameter is
/// checked against the PRE-call state — a false `Verified`. The caller uses this
/// set to FAIL CLOSED on such postconditions. Mirrors the conservative
/// collection-mutation default: any non-pure-read method counts as a mutation
/// (`is_known_mutating_method` omits `retain`/`drain`/`dedup`/`extend`/`sort`/
/// `reverse`/`rotate_*`/`fill`/`split_off`, so we key on the pure-read allow-list
/// complement, not that positive list). Let-move aliases (`let q = P`) and
/// sub-place receivers resolve back to the root parameter before classification.
pub(super) fn mut_ref_collection_params_method_mutated_in_body(
    block: &syn::Block,
    params: &BTreeSet<String>,
) -> BTreeSet<String> {
    struct MethodMutationVisitor<'a> {
        params: &'a BTreeSet<String>,
        mutated: BTreeSet<String>,
        /// Lexically-scoped local binding -> moved `&mut` parameter root. `None`
        /// records a non-alias shadow, including a local that shadows a parameter.
        aliases: BTreeMap<String, Option<String>>,
    }

    impl MethodMutationVisitor<'_> {
        fn resolve_root_param(&self, ident: &str) -> Option<String> {
            match self.aliases.get(ident) {
                Some(root) => root.clone(),
                None => self.params.contains(ident).then(|| ident.to_string()),
            }
        }

        fn method_receiver_param(&self, receiver: &Expr) -> Option<String> {
            // Direct auto/explicit-deref receiver (`P.m()` / `(*P).m()`), or a
            // projection (`P[i].m()`) whose in-place mutation changes the root
            // collection. Resolve the syntactic root through a let-move alias.
            let ident = method_call_receiver_ident(receiver)
                .or_else(|| field_index_projection_root(receiver))?;
            self.resolve_root_param(&ident)
        }
    }

    impl<'ast> Visit<'ast> for MethodMutationVisitor<'_> {
        fn visit_block(&mut self, block: &'ast syn::Block) {
            let saved = self.aliases.clone();
            syn::visit::visit_block(self, block);
            self.aliases = saved;
        }

        fn visit_local(&mut self, local: &'ast syn::Local) {
            let binding = local_binding_ident(&local.pat).map(|name| {
                let root = local.init.as_ref().and_then(|init| {
                    expr_path_ident(&init.expr).and_then(|ident| self.resolve_root_param(&ident))
                });
                (name, root)
            });
            // A `let` binding is not in scope in its own initializer (nor in a
            // diverging `let-else` arm), so visit the initializer under the old
            // alias environment before installing the new binding.
            syn::visit::visit_local(self, local);
            if let Some((name, root)) = binding {
                self.aliases.insert(name, root);
            }
        }

        fn visit_expr_method_call(&mut self, method_call: &'ast syn::ExprMethodCall) {
            if !is_pure_collection_read_method(&method_call.method.to_string()) {
                if let Some(name) = self.method_receiver_param(&method_call.receiver) {
                    self.mutated.insert(name);
                }
            }
            syn::visit::visit_expr_method_call(self, method_call);
        }

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = MethodMutationVisitor {
        params,
        mutated: BTreeSet::new(),
        aliases: BTreeMap::new(),
    };
    visitor.visit_block(block);
    visitor.mutated
}

/// SOUNDNESS-CRITICAL (P0-A `&mut` postcondition two-state gap, the direct-write
/// sibling of `mut_ref_collection_params_method_mutated_in_body`). The subset of
/// `params` (each a non-scalar `&mut` parameter — struct/enum/collection/array)
/// whose referent is mutated by a DIRECT PLACE WRITE rooted at the parameter
/// (`P.field = …`, `P[i] = …`, `*P = …`, and their compound `OP=` forms,
/// including nested `P.f.g = …` / `P.f[i] = …`) OR whose `&mut` reference is
/// reborrowed (`&mut *P`, `&mut P.f`, `&mut P[i]`), so a later mutation may flow
/// through the reborrow alias.
///
/// A bare non-scalar `&mut` parameter in a postcondition resolves to its ENTRY
/// snapshot (collections/structs/arrays are not `supported_mut_ref` scalars, so
/// the two-state final-value rewrite never runs for them). The body model DOES
/// thread a direct field/index write into the parameter's scoped value for
/// in-body reads, but the postcondition rewrite reads the entry snapshot — so a
/// postcondition over such a mutated parameter would be checked against the
/// PRE-write state, a false `Verified`. The caller FAILS CLOSED on such
/// postconditions (the direct-write analog of the method-mutation rejects).
pub(super) fn mut_ref_params_place_mutated_or_reborrowed_in_body(
    block: &syn::Block,
    params: &BTreeSet<String>,
) -> BTreeSet<String> {
    struct PlaceMutationVisitor<'a> {
        params: &'a BTreeSet<String>,
        flagged: BTreeSet<String>,
        // SOUNDNESS-CRITICAL (let-move alias of a non-scalar `&mut` param): a bare
        // `let q = p;` MOVES the `&mut S` / `&mut [T; N]` reference, so `q` denotes
        // the SAME referent as `p`. A place write through the alias (`q.f = ..`,
        // `q[i] = ..`, `*q = ..`), a reborrow of it (`&mut *q`, `&mut q.f`), or an
        // escape of it (`take(q)`) mutates `p`'s referent — but is rooted at `q`,
        // not `p`, so the param would otherwise never be flagged and a
        // postcondition reading `p` would resolve to its frozen ENTRY snapshot (a
        // false `Verified`; round-10 findings 16-17). Track each alias local -> the
        // root `&mut` param it aliases (chains flattened at insertion) and resolve a
        // place / escape root through it. The bare-move sibling of the scalar
        // `mut_ref_params_escaping_in_body` detector, which the non-scalar
        // place-mutation path previously lacked. A bare `let q = p;` with NO
        // through-alias mutation does NOT flag `p` (no over-rejection of a read-only
        // capture).
        aliases: BTreeMap<String, Option<String>>,
    }

    /// The anchoring identifier of a place expression (NO parameter filter),
    /// peeling field / index / deref / reference / paren / group wrappers — e.g.
    /// `q.inner.x` / `q.items[i]` / `*q` -> `q`. Resolution against the tracked
    /// params / let-move aliases is done by the visitor's `resolve_root_param`.
    fn place_root_ident(expr: &Expr) -> Option<String> {
        field_index_projection_root(expr)
    }

    impl PlaceMutationVisitor<'_> {
        /// Resolve a place-root identifier to the root non-scalar `&mut` param it
        /// denotes: the param itself, or the param a `let`-move alias chains to.
        fn resolve_root_param(&self, ident: &str) -> Option<String> {
            match self.aliases.get(ident) {
                Some(root) => root.clone(),
                None => self.params.contains(ident).then(|| ident.to_string()),
            }
        }

        /// The root param of an ASSIGNMENT LHS that is a genuine PROJECTION (a
        /// field / index / deref place) of a tracked param OR a let-move alias of
        /// one — not a bare rebinding of the reference variable (which is not a
        /// referent mutation).
        fn projection_root(&self, lhs: &Expr) -> Option<String> {
            match strip_place_wrappers(lhs) {
                Expr::Field(_) | Expr::Index(_) => place_root_ident(strip_place_wrappers(lhs))
                    .and_then(|id| self.resolve_root_param(&id)),
                Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                    place_root_ident(&unary.expr).and_then(|id| self.resolve_root_param(&id))
                }
                _ => None,
            }
        }

        /// The root param of a CALL/METHOD ARGUMENT passed in a referent-escaping
        /// way: a bare `P` / alias, a reborrow `&mut P` / `&mut *P` / `&mut P.f`, or
        /// an explicit `*P`. `core::mem::take(P)` / `replace(P, ..)` / `swap(P, Q)`
        /// / `clobber(P)` all pass the `&mut` referent out where a mutation is
        /// invisible to the body model. Mirrors the scalar
        /// `mut_ref_params_escaping_in_body`, resolving through let-move aliases.
        fn call_arg_escapes(&self, arg: &Expr) -> Option<String> {
            match strip_place_wrappers(arg) {
                Expr::Reference(reference) => self.call_arg_escapes(&reference.expr),
                Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                    self.call_arg_escapes(&unary.expr)
                }
                other => place_root_ident(other).and_then(|id| self.resolve_root_param(&id)),
            }
        }
    }

    impl<'ast> Visit<'ast> for PlaceMutationVisitor<'_> {
        fn visit_block(&mut self, block: &'ast syn::Block) {
            // Lexical scoping: a `let`-move alias is visible only within its block
            // (and nested blocks). Save/restore so an inner shadow does not leak
            // out and over-flag a same-named outer binding.
            let saved = self.aliases.clone();
            syn::visit::visit_block(self, block);
            self.aliases = saved;
        }

        fn visit_local(&mut self, local: &'ast syn::Local) {
            let binding = local_binding_ident(&local.pat).map(|name| {
                // `let q = p;` (or `let r = <existing alias>;`) — a bare path move
                // of a non-scalar `&mut` param (transitively) aliases its referent.
                // Any other RHS (or no initializer) re-binds the name to a
                // non-alias, shadowing away any prior alias for it in this scope.
                let aliased = local
                    .init
                    .as_ref()
                    .and_then(|init| expr_path_ident(&init.expr))
                    .and_then(|id| self.resolve_root_param(&id));
                (name, aliased)
            });
            syn::visit::visit_local(self, local);
            if let Some((name, aliased)) = binding {
                // Keep an explicit `None` for a non-alias binding so a local can
                // soundly shadow a parameter with the same name.
                self.aliases.insert(name, aliased);
            }
        }

        fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
            if let Some(root) = self.projection_root(&assign.left) {
                self.flagged.insert(root);
            }
            syn::visit::visit_expr_assign(self, assign);
        }

        fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
            if is_assignment_binop(&binary.op) {
                if let Some(root) = self.projection_root(&binary.left) {
                    self.flagged.insert(root);
                }
            }
            syn::visit::visit_expr_binary(self, binary);
        }

        fn visit_expr_reference(&mut self, reference: &'ast syn::ExprReference) {
            // A `&mut <place rooted at P or an alias of P>` reborrow lets a later
            // mutation flow through the alias, so the parameter's final value is
            // uncertain.
            if reference.mutability.is_some() {
                if let Some(root) =
                    place_root_ident(&reference.expr).and_then(|id| self.resolve_root_param(&id))
                {
                    self.flagged.insert(root);
                }
            }
            syn::visit::visit_expr_reference(self, reference);
        }

        fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
            // Free-function escape: `core::mem::take(P)` / `replace(P, ..)` /
            // `swap(P, Q)` / any `f(P)` (or `f(q)` for an alias `q` of `P`) passes
            // the `&mut` referent out where the body model cannot see the mutation
            // — fail closed on a postcondition reading `P`.
            for arg in &call.args {
                if let Some(root) = self.call_arg_escapes(arg) {
                    self.flagged.insert(root);
                }
            }
            syn::visit::visit_expr_call(self, call);
        }

        fn visit_expr_method_call(&mut self, method_call: &'ast syn::ExprMethodCall) {
            // A tracked param (or its alias) passed as a NON-receiver argument to a
            // method call (`other.absorb(P)`) escapes exactly like a free-function
            // argument. The RECEIVER position is classified by the method-mutation
            // detectors, not here.
            for arg in &method_call.args {
                if let Some(root) = self.call_arg_escapes(arg) {
                    self.flagged.insert(root);
                }
            }
            syn::visit::visit_expr_method_call(self, method_call);
        }

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = PlaceMutationVisitor {
        params,
        flagged: BTreeSet::new(),
        aliases: BTreeMap::new(),
    };
    visitor.visit_block(block);
    visitor.flagged
}

/// The subset of `params` whose *reference* is used bare anywhere in the body —
/// i.e. the parameter identifier appears as an expression NOT directly under a
/// `*` dereference. A scalar `&mut` parameter is read/written through `*P`, so a
/// bare `P` means the reference itself is being passed to a call/method, moved
/// into an alias binding, or otherwise escaping where the referent may be
/// mutated outside the caller's value-numbering. The post-body scoped value for
/// such a parameter can be stale, so a postcondition over it must fail closed.
fn mut_ref_params_escaping_in_body(
    block: &syn::Block,
    params: &BTreeSet<String>,
) -> BTreeSet<String> {
    struct EscapeVisitor<'a> {
        params: &'a BTreeSet<String>,
        escaped: BTreeSet<String>,
    }

    /// `P` or `*P` for a tracked parameter `P` (peeling paren/group wrappers).
    fn place_root_param(expr: &Expr, params: &BTreeSet<String>) -> Option<String> {
        match expr {
            Expr::Path(path) if path.qself.is_none() => path
                .path
                .get_ident()
                .map(ToString::to_string)
                .filter(|name| params.contains(name)),
            Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                place_root_param(&unary.expr, params)
            }
            Expr::Paren(paren) => place_root_param(&paren.expr, params),
            Expr::Group(group) => place_root_param(&group.expr, params),
            _ => None,
        }
    }

    fn deref_of_param(expr: &Expr, params: &BTreeSet<String>) -> bool {
        if let Expr::Unary(unary) = expr {
            if matches!(unary.op, syn::UnOp::Deref(_)) {
                if let Expr::Path(path) = unary.expr.as_ref() {
                    if let Some(ident) = path.path.get_ident() {
                        return path.qself.is_none() && params.contains(&ident.to_string());
                    }
                }
            }
        }
        false
    }

    impl<'ast> Visit<'ast> for EscapeVisitor<'_> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            // `&P` / `&mut P` / `&mut *P`: a (re)borrow of the referent escapes —
            // the new reference may carry a mutation the caller cannot see.
            if let Expr::Reference(reference) = expr {
                if let Some(name) = place_root_param(&reference.expr, self.params) {
                    self.escaped.insert(name);
                }
                syn::visit::visit_expr(self, expr);
                return;
            }
            // `*P` is an in-place read/write of the referent, NOT a reference
            // escape: stop here so the inner `P` path is not counted.
            if deref_of_param(expr, self.params) {
                return;
            }
            if let Expr::Path(path) = expr {
                if path.qself.is_none() {
                    if let Some(ident) = path.path.get_ident() {
                        let name = ident.to_string();
                        if self.params.contains(&name) {
                            self.escaped.insert(name);
                        }
                    }
                }
            }
            syn::visit::visit_expr(self, expr);
        }

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = EscapeVisitor {
        params,
        escaped: BTreeSet::new(),
    };
    visitor.visit_block(block);
    visitor.escaped
}

fn contains_return_expr(expr: &Expr) -> bool {
    struct ReturnVisitor {
        found: bool,
    }

    impl<'ast> Visit<'ast> for ReturnVisitor {
        fn visit_expr_return(&mut self, _expr: &'ast syn::ExprReturn) {
            self.found = true;
        }

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = ReturnVisitor { found: false };
    visitor.visit_expr(expr);
    visitor.found
}

/// True when a statement contains a `return` expression that is not nested
/// inside a closure or item boundary. Used to reject `return` inside an exec
/// `proof_block!()` (Verus forbids return inside a proof block).
fn stmt_contains_return(stmt: &Stmt) -> bool {
    struct ReturnVisitor {
        found: bool,
    }

    impl<'ast> Visit<'ast> for ReturnVisitor {
        fn visit_expr_return(&mut self, _expr: &'ast syn::ExprReturn) {
            self.found = true;
        }

        // Do not descend into nested closures/items: a `return` there belongs to
        // the inner control-flow scope, not the proof block.
        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {}

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = ReturnVisitor { found: false };
    visitor.visit_stmt(stmt);
    visitor.found
}

fn is_side_effect_free_guard(expr: &Expr) -> bool {
    struct GuardVisitor {
        has_side_effect: bool,
    }

    impl<'ast> Visit<'ast> for GuardVisitor {
        fn visit_expr_assign(&mut self, _expr: &'ast syn::ExprAssign) {
            self.has_side_effect = true;
        }

        fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
            if is_assignment_binop(&expr.op) {
                self.has_side_effect = true;
            } else {
                visit::visit_expr_binary(self, expr);
            }
        }

        fn visit_expr_block(&mut self, _expr: &'ast syn::ExprBlock) {
            self.has_side_effect = true;
        }

        fn visit_expr_call(&mut self, _expr: &'ast syn::ExprCall) {
            self.has_side_effect = true;
        }

        fn visit_expr_method_call(&mut self, _expr: &'ast syn::ExprMethodCall) {
            self.has_side_effect = true;
        }

        fn visit_expr_macro(&mut self, _expr: &'ast syn::ExprMacro) {
            self.has_side_effect = true;
        }

        fn visit_expr_break(&mut self, _expr: &'ast syn::ExprBreak) {
            self.has_side_effect = true;
        }

        fn visit_expr_continue(&mut self, _expr: &'ast syn::ExprContinue) {
            self.has_side_effect = true;
        }

        fn visit_expr_return(&mut self, _expr: &'ast syn::ExprReturn) {
            self.has_side_effect = true;
        }

        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {
            self.has_side_effect = true;
        }
    }

    let mut visitor = GuardVisitor {
        has_side_effect: false,
    };
    visitor.visit_expr(expr);
    !visitor.has_side_effect
}

fn calc_encoding_error(detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: detail.into(),
    }
}

struct ExternalAssignmentCollector {
    local_scopes: Vec<BTreeSet<String>>,
    local_macros: Vec<BTreeMap<String, LocalMacroDefinition>>,
    macro_expansion_depth: usize,
    external_assignments: BTreeSet<String>,
    /// Names whose modeled type is a (mutable-capable) collection. The IR
    /// collapses mutable exec containers onto their ghost views (`Vec`/`[T]` =>
    /// `Seq`, `HashSet`/`BTreeSet` => `Set`, `HashMap`/`BTreeMap` => `Map`), so
    /// any name here may be mutated in place by a `&mut self` method.
    ///
    /// SOUNDNESS (the catastrophic loop collection-mutation gap): a method call
    /// on such a receiver that is NOT a recognized pure `&self` read is treated
    /// as a possible in-place mutation, so the receiver is recorded as modified
    /// (feeding the loop-frame havoc set). The positive `is_known_mutating_method`
    /// list omits in-place mutators such as `retain`/`drain`/`dedup`/`extend`/
    /// `sort`/`reverse`/`rotate_*`/`fill`/`split_off`, so keying solely on it
    /// leaves a mutated collection wrongly framed `recv == recv_pre`, trivially
    /// preserving a FALSE loop invariant about the receiver (escalating to a
    /// proven-false `ensures`/post-loop `assert`).
    collection_receivers: BTreeSet<String>,
    /// Names whose modeled type is a user struct/enum (`Datatype`), mapped to the
    /// base type name. The user-struct analog of `collection_receivers`: a method
    /// call on such a receiver that may mutate the caller's binding (`&mut self`,
    /// or an unresolved non-pure signature) is recorded as modified so the loop
    /// frame havocs it instead of pinning `recv == recv_pre` — closing the
    /// user-struct sibling of the #62/#63 collection loop-mutation false-Verified.
    struct_receivers: BTreeMap<String, String>,
    /// `(base_type_name, method_name)` -> `self` receiver kind, copied from the
    /// VC's file-wide impl-method registry so the collector can resolve whether a
    /// struct receiver-method call mutates the caller's binding.
    struct_self_receiver_kinds: HashMap<(String, String), SelfReceiverKind>,
    /// SOUNDNESS-CRITICAL (generic receiver × loop frame). Per-receiver
    /// `&mut self` trait-method names for bindings whose declared type is a bare
    /// type parameter (`fn g<T: Tr>(t: &mut T)`, and its `&mut impl Tr` sugar).
    /// Such a receiver is in NEITHER `struct_receivers` (a `Datatype` map) nor
    /// `collection_receivers`, so without this a `t.bump()` in a loop body left
    /// `t` out of the modified set, the frame pinned `t == t_pre`, and a FALSE
    /// invariant about `t.a()` was trivially "preserved". Built by
    /// `AssertionCollector::type_param_mut_methods_by_receiver`, which shares its
    /// bound walk with the straight-line havoc so the two cannot drift.
    type_param_mut_methods: BTreeMap<String, BTreeSet<String>>,
    /// Per-call `&mut`-argument positions for free functions called in the body
    /// (callee-signature derived; see `AssertionCollector::mut_ref_call_args`).
    /// SOUNDNESS-CRITICAL (free-call `&mut`-argument framing × loop/branch frame):
    /// a free call `push_helper(v)` mutating its `&mut` argument inside a loop
    /// body / branch must add `v` to the modified set so the loop frame / if-join
    /// havocs it — otherwise the frame pins `v == v_pre` and a false invariant /
    /// post-join assert about `v` is trivially "preserved". A `&`-shared argument
    /// is excluded by its callee signature (no over-rejection of a pure-read
    /// helper inside a loop).
    mut_ref_call_args: BTreeMap<String, Vec<bool>>,
    /// Per-ARGUMENT `&mut` positions of every method NAME the file declares, and
    /// the `&mut`-typed bindings of the function under extraction. The frame twin
    /// of `AssertionCollector::{method_arg_mut_flags, mut_ref_reborrowable_bindings}`:
    /// the straight-line havoc and the loop/join MODIFIED set must agree on which
    /// arguments a call may write through, or a loop frame pins `t == t_pre` for
    /// exactly the call the straight-line lane havocs.
    method_arg_mut_flags: BTreeMap<String, Vec<bool>>,
    mut_ref_reborrowable_bindings: BTreeSet<String>,
    /// Record bare external deref-write roots (`*p = v`) in the modified set
    /// (1c0cfb56: loop-frame havoc / invariant preservation; 2bdd29f9: a
    /// deref write inside a side-effecting index/RHS evaluation fails closed).
    /// Cleared ONLY by `externally_assigned_in_block` — the `if`/`else`/
    /// `match`-less block JOIN consumers, which keep the #83 deref-aliasing
    /// skip and leave the roots to the slice-C region havoc. See
    /// `externally_assigned_in_loop_body`.
    include_deref_roots: bool,
}

impl ExternalAssignmentCollector {
    fn new() -> Self {
        Self {
            local_scopes: Vec::new(),
            local_macros: vec![BTreeMap::new()],
            macro_expansion_depth: 0,
            external_assignments: BTreeSet::new(),
            collection_receivers: BTreeSet::new(),
            struct_receivers: BTreeMap::new(),
            struct_self_receiver_kinds: HashMap::new(),
            type_param_mut_methods: BTreeMap::new(),
            mut_ref_call_args: BTreeMap::new(),
            method_arg_mut_flags: BTreeMap::new(),
            mut_ref_reborrowable_bindings: BTreeSet::new(),
            include_deref_roots: true,
        }
    }

    /// The frame-side twin of
    /// `AssertionCollector::call_arg_may_be_written_through`. Kept literally
    /// parallel: the straight-line havoc and the loop/join modified set must
    /// answer the SAME question the same way, or a `&mut` argument gets havoced
    /// in one lane and frame-pinned in the other.
    fn call_arg_may_be_written_through(
        &self,
        resolved: Option<&[bool]>,
        index: usize,
        arg: &Expr,
    ) -> bool {
        if let Some(flags) = resolved {
            return flags.get(index).copied().unwrap_or(false);
        }
        expr_path_ident(arg).is_some_and(|name| self.mut_ref_reborrowable_bindings.contains(&name))
    }

    fn record_written_through_call_args(
        &mut self,
        args: &syn::punctuated::Punctuated<Expr, syn::Token![,]>,
        resolved: Option<&[bool]>,
    ) {
        for (index, arg) in args.iter().enumerate() {
            if !self.call_arg_may_be_written_through(resolved, index, arg) {
                continue;
            }
            if let Some(root) = field_index_projection_root(arg) {
                if !self.is_local(&root) {
                    self.external_assignments.insert(root);
                }
            }
        }
    }

    /// Whether `recv.method(..)` on a struct/enum receiver of type `struct_type`
    /// may mutate the CALLER's binding (so the receiver must join the loop's
    /// modified set). Mirrors `AssertionCollector::struct_method_mutates_caller`:
    /// `&mut self` mutates; `&self`/by-value `self` are pure; an UNKNOWN signature
    /// is conservatively treated as mutating unless it is a universally-pure read.
    fn struct_method_mutates_caller(&self, struct_type: &str, method: &str) -> bool {
        struct_method_mutates_caller_with_kinds(
            &self.struct_self_receiver_kinds,
            struct_type,
            method,
        )
    }

    fn with_macro_scopes(local_macros: &[BTreeMap<String, LocalMacroDefinition>]) -> Self {
        let mut collector = Self::new();
        collector.local_macros = if local_macros.is_empty() {
            vec![BTreeMap::new()]
        } else {
            local_macros.to_vec()
        };
        collector
    }

    fn is_local(&self, name: &str) -> bool {
        self.local_scopes
            .iter()
            .rev()
            .any(|scope| scope.contains(name))
    }

    fn bind_local(&mut self, pat: &Pat) {
        let names = bound_idents_from_pat(pat);
        if let Some(scope) = self.local_scopes.last_mut() {
            scope.extend(names);
        }
    }

    fn current_macro_scope_mut(&mut self) -> &mut BTreeMap<String, LocalMacroDefinition> {
        if self.local_macros.is_empty() {
            self.local_macros.push(BTreeMap::new());
        }
        let index = self.local_macros.len() - 1;
        &mut self.local_macros[index]
    }

    fn lookup_local_macro(&self, name: &str) -> Option<LocalMacroDefinition> {
        self.local_macros
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .cloned()
    }

    fn handle_nested_item(&mut self, item: &Item) {
        let Item::Macro(item_macro) = item else {
            return;
        };
        if super::path_last_segment(&item_macro.mac.path).as_deref() != Some("macro_rules") {
            return;
        }
        if let Ok((name, definition)) = parse_local_macro_rules_item(item_macro) {
            self.current_macro_scope_mut().insert(name, definition);
        }
    }

    fn expand_local_macro_stmt(&mut self, mac: &Macro) -> bool {
        let Some(name) = super::path_last_segment(&mac.path) else {
            return false;
        };
        let Some(definition) = self.lookup_local_macro(&name) else {
            return false;
        };
        if ensure_zero_arg_local_macro_invocation(mac, &name).is_err() {
            return false;
        }
        let Ok(block) = parse_local_macro_expansion_block(&name, &definition) else {
            return false;
        };
        if self.macro_expansion_depth >= LOCAL_MACRO_EXPANSION_LIMIT {
            return false;
        }
        self.macro_expansion_depth += 1;
        for stmt in &block.stmts {
            self.visit_stmt(stmt);
        }
        self.macro_expansion_depth -= 1;
        true
    }
}

impl<'ast> Visit<'ast> for ExternalAssignmentCollector {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.local_scopes.push(BTreeSet::new());
        self.local_macros.push(BTreeMap::new());
        for stmt in &block.stmts {
            self.visit_stmt(stmt);
        }
        self.local_macros.pop();
        self.local_scopes.pop();
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        match stmt {
            Stmt::Local(local) => {
                if let Some(init) = local.init.as_ref() {
                    self.visit_expr(&init.expr);
                    if let Some((_, diverge)) = &init.diverge {
                        self.visit_expr(diverge);
                    }
                }
                self.bind_local(&local.pat);
            }
            Stmt::Expr(expr, _) => self.visit_expr(expr),
            Stmt::Macro(stmt_macro) => {
                if !self.expand_local_macro_stmt(&stmt_macro.mac) {
                    self.visit_macro(&stmt_macro.mac);
                }
            }
            Stmt::Item(item) => {
                self.handle_nested_item(item);
                self.visit_item(item);
            }
        }
    }

    fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
        if let Some(name) = expr_path_ident(&assign.left) {
            if !self.is_local(&name) {
                self.external_assignments.insert(name);
            }
        } else if let Some((name, index, _)) =
            indexed_tuple_field_assignment_target(assign.left.as_ref())
        {
            if !self.is_local(&name) {
                self.external_assignments.insert(name);
            }
            self.visit_expr(index);
        } else if let Expr::Index(index_target) = strip_place_wrappers(assign.left.as_ref()) {
            if let Some((name, outer_index, inner_index)) =
                nested_index_assignment_target(index_target)
            {
                if !self.is_local(&name) {
                    self.external_assignments.insert(name);
                }
                self.visit_expr(outer_index);
                self.visit_expr(inner_index);
            } else if let Some(name) = expr_path_ident(&index_target.expr) {
                if !self.is_local(&name) {
                    self.external_assignments.insert(name);
                }
                self.visit_expr(&index_target.index);
            } else {
                self.visit_expr(&assign.left);
            }
        } else {
            // A direct scalar referent write `*p = v` mutates the ROOT binding
            // and therefore belongs in a loop's modified set. The main
            // AssertionCollector models the write itself, but loop-invariant
            // preservation is built from this read-only collector's set; omitting
            // `p` here frames it as unchanged and can make a non-inductive
            // `invariant!(*p == old)` verify. Restrict this to a bare external
            // alias: a block-local alias cannot be resolved to its outer target
            // in this collector and remains owned by the alias/deref fail-closed
            // machinery. LOOP frames only (`include_deref_roots`): at a
            // branch/match/block join the root is owned by the slice-C region
            // havoc, and inserting it here invalidates the alias target instead.
            if self.include_deref_roots {
                if let Some(name) = deref_assignment_target_alias(assign.left.as_ref()) {
                    if !self.is_local(&name) {
                        self.external_assignments.insert(name);
                    }
                }
            }
            // SOUNDNESS (round-2 audit P0-A): a named/tuple-field place write
            // `s.x = v` / `p.0 = v` / `s.inner.x = v` / `a[i].x = v` mutates the
            // ROOT binding, so it must be recorded as an external assignment.
            // Otherwise an `if`/`match` join never havocs the struct and a branch
            // field write is silently dropped, freezing the field at its entry
            // value -> false-Verified. Field and direct-deref places are handled
            // independently so an unresolved projected deref cannot be mistaken
            // for its syntactic alias name.
            if matches!(strip_place_wrappers(assign.left.as_ref()), Expr::Field(_)) {
                if let Some(name) =
                    index_access_root_ident(strip_place_wrappers(assign.left.as_ref()))
                {
                    if !self.is_local(&name) {
                        self.external_assignments.insert(name);
                    }
                }
            }
            self.visit_expr(&assign.left);
        }
        self.visit_expr(&assign.right);
    }

    fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
        if is_assignment_binop(&binary.op) {
            if let Expr::Index(index_target) = strip_place_wrappers(binary.left.as_ref()) {
                if let Some((name, outer_index, inner_index)) =
                    nested_index_assignment_target(index_target)
                {
                    if !self.is_local(&name) {
                        self.external_assignments.insert(name);
                    }
                    self.visit_expr(outer_index);
                    self.visit_expr(inner_index);
                } else if let Some(name) = expr_path_ident(&index_target.expr) {
                    if !self.is_local(&name) {
                        self.external_assignments.insert(name);
                    }
                    self.visit_expr(&index_target.index);
                } else {
                    self.visit_expr(&binary.left);
                }
            } else if let Some(name) = expr_path_ident(&binary.left) {
                if !self.is_local(&name) {
                    self.external_assignments.insert(name);
                }
            } else {
                if self.include_deref_roots {
                    if let Some(name) = deref_assignment_target_alias(binary.left.as_ref()) {
                        if !self.is_local(&name) {
                            self.external_assignments.insert(name);
                        }
                    }
                }
                // SOUNDNESS (round-2 audit P0-A, compound-assign sibling): a
                // field/tuple-field compound write `s.x += v` mutates the ROOT
                // binding -> record it so if/match joins havoc the struct (else
                // the branch write is dropped, freezing the field ->
                // false-Verified). A direct external `*p op= v` is likewise
                // loop-modifying even if the body model later rejects that
                // compound transition fail-closed.
                if matches!(strip_place_wrappers(binary.left.as_ref()), Expr::Field(_)) {
                    if let Some(name) =
                        index_access_root_ident(strip_place_wrappers(binary.left.as_ref()))
                    {
                        if !self.is_local(&name) {
                            self.external_assignments.insert(name);
                        }
                    }
                }
                self.visit_expr(&binary.left);
            }
            self.visit_expr(&binary.right);
        } else {
            visit::visit_expr_binary(self, binary);
        }
    }

    fn visit_expr_reference(&mut self, reference: &'ast syn::ExprReference) {
        self.visit_expr(&reference.expr);
        if reference.mutability.is_some() {
            if let Some(name) = expr_path_ident(&reference.expr) {
                if !self.is_local(&name) {
                    self.external_assignments.insert(name);
                }
            } else if matches!(
                strip_place_wrappers(&reference.expr),
                Expr::Field(_) | Expr::Index(_) | Expr::Unary(_)
            ) {
                // A `&mut` reborrow of a SUB-PLACE (`&mut *v`, `&mut o.inner`,
                // `&mut o.items[i]`) lets a later mutation flow through the alias to
                // the ROOT binding's referent, so the root must join the loop's
                // modified set. Otherwise the loop frame pins `v == v_pre` and a
                // false invariant / post-loop assert about `v` is trivially
                // "preserved" — the reborrow-alias-in-a-loop false `Verified`
                // (`while .. { let a = &mut *v; a.push(..); }`).
                if let Some(root) = field_index_projection_root(&reference.expr) {
                    if !self.is_local(&root) {
                        self.external_assignments.insert(root);
                    }
                }
            }
        }
    }

    fn visit_expr_method_call(&mut self, method_call: &'ast syn::ExprMethodCall) {
        self.visit_expr(&method_call.receiver);
        for arg in &method_call.args {
            self.visit_expr(arg);
        }
        let method = method_call.method.to_string();
        // ARGUMENTS FIRST, and unconditionally: a `&mut` non-self argument
        // (`h.hit(t)`) is modified by the call no matter what the RECEIVER
        // resolves to, and every `return` below this point would skip it.
        let resolved_args = self.method_arg_mut_flags.get(&method).cloned();
        self.record_written_through_call_args(&method_call.args, resolved_args.as_deref());
        // Resolve through an explicit deref `(*v).m(..)` as well as the
        // auto-deref form `v.m(..)`; `expr_path_ident` alone strips paren/group
        // but NOT `*`, which left the explicit-deref residual of the loop
        // collection-mutation gap (see `method_call_receiver_ident`).
        let Some(name) = method_call_receiver_ident(&method_call.receiver) else {
            return;
        };
        if self.is_local(&name) {
            return;
        }
        // A recognized in-place mutator always records its receiver.
        if is_known_mutating_method(&method) {
            self.external_assignments.insert(name);
            return;
        }
        // CONSERVATIVE collection-mutation default (the catastrophic loop gap):
        // `is_known_mutating_method` is a positive allow-list that OMITS in-place
        // mutators such as `retain`/`drain`/`dedup`/`extend`/`sort`/`reverse`/
        // `rotate_left`/`rotate_right`/`fill`/`split_off`. Keying solely on it
        // leaves a Vec mutated by one of those wrongly OUT of the modified set,
        // so the loop frame pins `recv == recv_pre` and ANY invariant about the
        // receiver is trivially "preserved" even when the body breaks it — a
        // false Verified. We therefore over-approximate: an unrecognized method
        // on a collection-typed receiver that is NOT a known pure `&self` read
        // is treated as a possible mutation. A genuine pure read (`len`/`get`/
        // `index`/`contains`/`iter`/…) is excluded so a true invariant about an
        // only-read collection is still framed (no over-rejection).
        if self.collection_receivers.contains(&name) && !is_pure_collection_read_method(&method) {
            self.external_assignments.insert(name);
            return;
        }
        // USER-STRUCT analog of the collection loop-mutation gap: a method call on
        // a struct/enum receiver that may mutate the caller's binding (`&mut self`,
        // or an unresolved non-pure signature) leaves the receiver OUT of the
        // modified set, so the loop frame pins `recv == recv_pre` and a false
        // invariant about `recv` is trivially "preserved". Record it so the frame
        // havocs it. A resolved `&self`/by-value `self` reader (a pure getter) is
        // NOT recorded — a true invariant about an only-read struct stays framed
        // (NO over-rejection).
        if let Some(struct_type) = self.struct_receivers.get(&name) {
            if self.struct_method_mutates_caller(struct_type, &method) {
                self.external_assignments.insert(name);
                return;
            }
        }
        // GENERIC-RECEIVER analog: a `&mut self` trait method on a receiver whose
        // declared type is a bare type parameter. Neither map above can see it (a
        // `TypeParam` has no `Datatype` and is not collection-like), so `t.bump()`
        // in a loop body left `t` frame-pinned and a false invariant about
        // `t.a()` was trivially preserved. Only methods the in-scope trait
        // declarations RESOLVE to `&mut self` are recorded, so a pure `&self`
        // read keeps a true invariant framed (NO over-rejection).
        if self
            .type_param_mut_methods
            .get(&name)
            .is_some_and(|methods| methods.contains(&method))
        {
            self.external_assignments.insert(name);
        }
    }

    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        self.visit_expr(&call.func);
        for arg in &call.args {
            self.visit_expr(arg);
        }
        // SOUNDNESS-CRITICAL (free-call `&mut`-argument framing × loop/branch
        // frame): a free function CALL `push_helper(v)` that mutates its `&mut`
        // argument must record the argument's root binding as modified, so the
        // enclosing loop frame / if-join havocs it. The default `Visit` recursion
        // records an EXPLICIT `&mut v` reborrow argument via `visit_expr_reference`,
        // but a BARE `v` argument (the auto-reborrow `push_helper(v)` /
        // `bump_scalar(x)` form) is a plain `Expr::Path` that the default never
        // records — exactly the gap that left a loop frame pinning `v == v_pre`.
        // The `&mut` positions come from the callee signature (`mut_ref_call_args`),
        // so a `&`-shared read argument (`read_helper(v)`) is excluded and a true
        // invariant about an only-read collection stays framed (no over-rejection).
        // UNRESOLVED is reported as unresolved, not as an empty flag vector:
        // `None` routes to the argument-type fallback so a file-level
        // `use m::bump2;` / an `H::zap(t)` associated fn / an external-crate
        // callee still records its reborrowed `&mut` argument as modified.
        let resolved = super::call_function_symbol(call)
            .and_then(|symbol| self.mut_ref_call_args.get(&symbol).cloned());
        self.record_written_through_call_args(&call.args, resolved.as_deref());
    }

    fn visit_expr_match(&mut self, expr_match: &'ast syn::ExprMatch) {
        self.visit_expr(&expr_match.expr);
        for arm in &expr_match.arms {
            self.local_scopes.push(bound_idents_from_pat(&arm.pat));
            if let Some((_, guard)) = &arm.guard {
                self.visit_expr(guard);
            }
            self.visit_expr(&arm.body);
            self.local_scopes.pop();
        }
    }

    fn visit_expr_for_loop(&mut self, expr_for_loop: &'ast syn::ExprForLoop) {
        self.visit_expr(&expr_for_loop.expr);
        self.local_scopes
            .push(bound_idents_from_pat(&expr_for_loop.pat));
        self.visit_block(&expr_for_loop.body);
        self.local_scopes.pop();
    }

    fn visit_expr_closure(&mut self, _closure: &'ast syn::ExprClosure) {}

    fn visit_item(&mut self, _item: &'ast Item) {}
}

struct BodyOptionClosureParam {
    name: syn::Ident,
    _ty: syn::Type,
}

struct BodyOptionEnsuresClause {
    result_name: syn::Ident,
    _result_ty: Option<syn::Type>,
    expr: Expr,
}

struct BodyOptionClosureContract {
    params: Vec<BodyOptionClosureParam>,
    _return_ty: Option<syn::Type>,
    requires: Option<Expr>,
    ensures: Option<BodyOptionEnsuresClause>,
    body: Expr,
}

impl BodyOptionClosureContract {
    fn has_contract_clause(&self) -> bool {
        self.requires.is_some() || self.ensures.is_some()
    }

    fn ensures_condition(&self) -> Option<Expr> {
        let ensures = self.ensures.as_ref()?;
        let mut condition = ensures.expr.clone();
        let mut substitutions = BTreeMap::new();
        substitutions.insert(
            ensures.result_name.to_string(),
            parenthesized_expr(self.body.clone()),
        );
        let erased_shared_ref_params = BTreeSet::new();
        let old_substitutions = BTreeMap::new();
        let erased_mut_ref_value_params = BTreeSet::new();
        ContractExprSubstituter {
            substitutions: &substitutions,
            erased_shared_ref_params: &erased_shared_ref_params,
            old_substitutions: &old_substitutions,
            erased_mut_ref_value_params: &erased_mut_ref_value_params,
            binder_scopes: Vec::new(),
            unscopable_binder: false,
        }
        .visit_expr_mut(&mut condition);
        Some(condition)
    }
}

impl syn::parse::Parse for BodyOptionClosureContract {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        if input.peek(Token![move]) {
            input.parse::<Token![move]>()?;
        }

        input.parse::<Token![|]>()?;
        let mut params = Vec::new();
        while !input.peek(Token![|]) {
            if !params.is_empty() {
                input.parse::<Token![,]>()?;
                if input.peek(Token![|]) {
                    break;
                }
            }
            if input.peek(Token![mut]) {
                input.parse::<Token![mut]>()?;
            }
            let name = input.parse::<syn::Ident>()?;
            input.parse::<Token![:]>()?;
            let ty = input.parse::<syn::Type>()?;
            params.push(BodyOptionClosureParam { name, _ty: ty });
        }
        input.parse::<Token![|]>()?;

        let return_ty = if input.peek(Token![->]) {
            input.parse::<Token![->]>()?;
            Some(input.parse::<syn::Type>()?)
        } else {
            None
        };

        let requires = parse_body_option_closure_clause(input, "requires")?
            .map(crate::chained_comparisons::parse_expr_tokens_with_chains)
            .transpose()?;
        let ensures = parse_body_option_closure_ensures(input)?;
        let body = input.parse::<Expr>()?;

        Ok(Self {
            params,
            _return_ty: return_ty,
            requires,
            ensures,
            body,
        })
    }
}

fn parse_body_option_closure_clause(
    input: syn::parse::ParseStream<'_>,
    name: &str,
) -> syn::Result<Option<TokenStream>> {
    if input.peek(syn::Ident) {
        let fork = input.fork();
        let ident: syn::Ident = fork.parse()?;
        if ident == name {
            input.parse::<syn::Ident>()?;
            let content;
            syn::parenthesized!(content in input);
            return Ok(Some(content.parse::<TokenStream>()?));
        }
    }
    Ok(None)
}

fn parse_body_option_closure_ensures(
    input: syn::parse::ParseStream<'_>,
) -> syn::Result<Option<BodyOptionEnsuresClause>> {
    if input.peek(syn::Ident) {
        let fork = input.fork();
        let ident: syn::Ident = fork.parse()?;
        if ident == "ensures" {
            input.parse::<syn::Ident>()?;
            let content;
            syn::parenthesized!(content in input);
            content.parse::<Token![|]>()?;
            let result_name = content.parse::<syn::Ident>()?;
            let result_ty = if content.peek(Token![:]) {
                content.parse::<Token![:]>()?;
                Some(content.parse::<syn::Type>()?)
            } else {
                None
            };
            content.parse::<Token![|]>()?;
            let expr = crate::chained_comparisons::parse_expr_tokens_with_chains(content.parse()?)?;
            return Ok(Some(BodyOptionEnsuresClause {
                result_name,
                _result_ty: result_ty,
                expr,
            }));
        }
    }
    Ok(None)
}

fn parenthesized_expr(expr: Expr) -> Expr {
    syn::parse_quote!((#expr))
}

fn option_none_branch_condition(receiver: &str, condition: &str) -> String {
    format!("match ({receiver}) {{ None => ({condition}), _ => true }}")
}

fn option_some_branch_condition(
    receiver: &str,
    contract: &BodyOptionClosureContract,
    condition: &str,
) -> String {
    let param = contract
        .params
        .first()
        .map(|param| param.name.to_string())
        .unwrap_or_else(|| "_".to_string());
    format!("match ({receiver}) {{ Some({param}) => ({condition}), _ => true }}")
}

fn option_closure_branch_condition(
    method: &str,
    receiver: &str,
    contract: &BodyOptionClosureContract,
    condition: &str,
) -> String {
    match method {
        "ok_or_else" | "unwrap_or_else" => option_none_branch_condition(receiver, condition),
        "and_then" => option_some_branch_condition(receiver, contract, condition),
        _ => unreachable!("unsupported Option closure contract method: {method}"),
    }
}

fn is_trust_vc_closure_expr_macro(expr_macro: &syn::ExprMacro) -> bool {
    let path = &expr_macro.mac.path;
    let mut segments = path.segments.iter();
    matches!(
        (segments.next(), segments.next(), segments.next()),
        (Some(first), Some(second), None) if first.ident == "trust_vc" && second.ident == "closure"
    )
}

/// Converts a closure param/result `syn::Type` to a modelable `TrustVcType`,
/// returning `None` (→ fail closed) for any type with no concrete sort (refs,
/// generics, unsupported types). Part of the file-path closure! wiring.
fn closure_modelable_type(ty: &syn::Type) -> Option<TrustVcType> {
    let rendered: String = ty
        .to_token_stream()
        .to_string()
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let parsed = TrustVcType::parse_or_opaque(&rendered);
    (!parsed.contains_opaque()).then_some(parsed)
}

/// A read-only `syn` visitor collecting `f.requires(..)` / `f.ensures(..)`
/// REFLECTION method calls over registered closure literals inside a condition
/// expression, so their GROUND definitional facts can be emitted. Recurses into
/// all sub-expressions (nested reflection, boolean structure). Part of the Phase
/// C reflection wiring.
struct ReflectionUseCollector<'a> {
    contracts: &'a HashMap<String, ClosureReflectionContract>,
    uses: Vec<syn::ExprMethodCall>,
}

impl<'ast> syn::visit::Visit<'ast> for ReflectionUseCollector<'_> {
    fn visit_expr_method_call(&mut self, mc: &'ast syn::ExprMethodCall) {
        if (mc.method == "requires" || mc.method == "ensures")
            && expr_path_ident(&mc.receiver).is_some_and(|name| self.contracts.contains_key(&name))
        {
            self.uses.push(mc.clone());
        }
        syn::visit::visit_expr_method_call(self, mc);
    }
}

/// A read-only `syn` visitor collecting DIRECT APPLICATION calls `f(arg)` over
/// registered closure literals inside an `assert!` / `assume!` condition, so the
/// call-site prove-requires + assume-ensures can be emitted (the straight-line
/// `visit_expr_call` walk never reaches a call inside a macro's tokens). Recurses
/// into all sub-expressions. Sibling of [`ReflectionUseCollector`]. Phase C part 2.
struct ClosureApplicationUseCollector<'a> {
    contracts: &'a HashMap<String, ClosureReflectionContract>,
    /// INCREMENT 2a: names of Fn-bound `SpecFn` parameters (see
    /// [`AssertionCollector::fn_bound_spec_fn_params`]) whose direct application
    /// inside an assert/assume also needs its call-site conditional assume.
    fn_bound_params: &'a BTreeSet<String>,
    uses: Vec<syn::ExprCall>,
}

impl<'ast> syn::visit::Visit<'ast> for ClosureApplicationUseCollector<'_> {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if super::call_function_symbol(call).is_some_and(|name| {
            self.contracts.contains_key(&name) || self.fn_bound_params.contains(&name)
        }) {
            self.uses.push(call.clone());
        }
        syn::visit::visit_expr_call(self, call);
    }
}

/// Fail-closed error for an unexpected internal failure minting a fresh closure
/// symbol (a declared fresh identifier that fails to re-parse). Part of the
/// file-path closure! wiring.
fn closure_internal_error(what: &str) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract closure contract",
        detail: format!("internal error constructing {what} for closure contract"),
    }
}

fn parse_helper_contract_expr(
    source: &str,
    helper_name: &str,
    role: &'static str,
) -> TrustVcResult<Expr> {
    syn::parse_str::<Expr>(source).map_err(|err| TrustVcError::Encoding {
        context: "extract sibling helper call contracts",
        detail: format!(
            "Failed to parse substituted {role} expression for sibling helper `{helper_name}`: {err}; expression: {source}"
        ),
    })
}

/// Substitutes call-site argument renderings into a helper contract clause.
///
/// TWO-STATE DIRECTIONALITY (slice D, SOUNDNESS-CRITICAL): `substitutions` is
/// the bare-`P` map (PRE-call for `requires`, POST-havoc for `ensures`);
/// `old_substitutions` binds `old(P)` forms of `&mut` scalar params and is
/// ALWAYS the PRE-call map. Both are applied in ONE simultaneous pass and the
/// substituter never recurses into a replacement, so a pre-value spliced for
/// `old(P)` can never be re-substituted with the post-call map (inverting
/// old/post would let a wrong caller chain verify).
fn substitute_helper_contract_clause(
    clause: &HelperContractClause,
    substitutions: &BTreeMap<String, Expr>,
    erased_shared_ref_params: &BTreeSet<String>,
    old_substitutions: &BTreeMap<String, Expr>,
    erased_mut_ref_value_params: &BTreeSet<String>,
) -> TrustVcResult<String> {
    let mut condition = clause.condition.clone();
    let mut substituter = ContractExprSubstituter {
        substitutions,
        erased_shared_ref_params,
        old_substitutions,
        erased_mut_ref_value_params,
        binder_scopes: Vec::new(),
        unscopable_binder: false,
    };
    substituter.visit_expr_mut(&mut condition);
    if substituter.unscopable_binder {
        // The clause binds names in a form whose scope this pass cannot delimit
        // exactly. Both available guesses are unsound (see
        // `ContractExprSubstituter::unscopable_binder`), so refuse: on the
        // `requires` side this drops no obligation (the whole call extraction
        // errors), and on the `ensures` side it assumes nothing.
        return Err(TrustVcError::Encoding {
            context: "substitute helper contract clause",
            detail: format!(
                "contract clause binds names in a scope this pass cannot delimit exactly \
                 (an opaque pattern, or an `if let`/`while let`); refusing to substitute \
                 call arguments into it rather than risk capturing a binder: `{}`",
                clause.condition.to_token_stream()
            ),
        });
    }
    Ok(condition.to_token_stream().to_string())
}

fn erase_shared_reference_argument(expr: Expr) -> Expr {
    match expr {
        Expr::Reference(reference) if reference.mutability.is_none() => *reference.expr,
        other => other,
    }
}

fn is_known_mutating_method(method: &str) -> bool {
    matches!(
        method,
        "push"
            | "push_back"
            | "pop"
            | "insert"
            | "remove"
            | "append"
            | "clear"
            | "truncate"
            | "resize"
            | "reserve"
            | "swap"
            | "swap_remove"
    )
}

/// Method names that are provably PURE `&self` reads on every std container the
/// IR collapses onto a collection type (`Vec`/`[T]` => `Seq`, `HashSet`/
/// `BTreeSet` => `Set`, `HashMap`/`BTreeMap` => `Map`) — they return a NEW value
/// or read through `&self` and CANNOT mutate the receiver in place.
///
/// Used by `ExternalAssignmentCollector` as the ONLY escape from the conservative
/// collection-mutation default: a method on a collection-typed receiver that is
/// NOT listed here is conservatively recorded as a possible in-place mutation
/// (so the loop frame havocs it). SOUNDNESS is fail-closed in the unknown
/// direction, so this list must contain ONLY methods that never mutate — adding
/// a `&mut self` method here would re-open the catastrophic loop gap. Methods
/// that return a mutable view (`get_mut`/`iter_mut`/`first_mut`/`last_mut`/
/// `as_mut_slice`/`entry`/`make_mut`) are deliberately EXCLUDED, since the
/// borrowed alias can mutate the receiver. The pure ghost-collection combinators
/// (`filter`/`map`/`union`/`len`/`contains`/`is_empty`/`first`/`last`/…) are
/// folded in via `pure_ghost_collection_combinator`.
fn is_pure_collection_read_method(method: &str) -> bool {
    if pure_ghost_collection_combinator(method) {
        return true;
    }
    matches!(
        method,
        // std container `&self` reads with no same-named in-place mutator.
        "get"
            | "get_key_value"
            | "index"
            | "iter"
            | "capacity"
            | "as_slice"
            | "as_bytes"
            | "binary_search"
            | "starts_with"
            | "ends_with"
            | "clone"
            | "to_vec"
            | "spec_index"
            | "view"
    )
}

/// Universally-pure method names used to classify an UNKNOWN-signature method
/// call on a user struct/enum receiver (one with no in-scope `impl` declaring it,
/// e.g. a derived or std `&self` method). These read through `&self` (or consume
/// by value) and never take `&mut self` on any reasonable type, so they cannot
/// mutate the caller's binding — recognizing them avoids over-rejecting a pure
/// read of a struct that is later asserted about (NO over-rejection).
///
/// SOUNDNESS: consulted ONLY for methods that are NOT resolved by
/// `struct_self_receiver_kind` — a method a source `impl` declares as `&mut self`
/// is already classified as mutating before this list is reached, so a
/// user-defined `&mut self` method that happens to share a name here is still
/// havocked. `&mut`-borrowing reads (`as_mut`/`as_mut_slice`/`borrow_mut`/
/// `iter_mut`/`get_mut`/`entry`/`make_mut`) are deliberately EXCLUDED.
/// Whether `recv.method(..)` on a struct/enum receiver of type `struct_type` may
/// mutate the caller's binding, given the file-wide receiver-kind registry.
/// Shared by the loop modified-var collector, the straight-line scoped havoc, and
/// the `&mut`-struct postcondition reject so all three agree on the classification:
/// `&mut self` mutates; `&self`/by-value `self` are pure; an UNKNOWN signature is
/// conservatively mutating unless it is a universally-pure read.
fn struct_method_mutates_caller_with_kinds(
    kinds: &HashMap<(String, String), SelfReceiverKind>,
    struct_type: &str,
    method: &str,
) -> bool {
    match kinds.get(&(struct_type.to_string(), method.to_string())) {
        Some(SelfReceiverKind::RefMut) => true,
        Some(SelfReceiverKind::Ref | SelfReceiverKind::Value) => false,
        None => !is_known_pure_struct_method(method),
    }
}

/// The subset of `param_struct_types` (each a `&mut <struct/enum>` parameter,
/// keyed to its base `Datatype` type-name) that is mutated IN PLACE by a method
/// call in the body — `P.m(..)` / `(*P).m(..)` where `m` may mutate the caller's
/// binding (a `&mut self` method, or an unresolved non-pure signature).
///
/// SOUNDNESS (the straight-line `&mut`-struct postcondition gap, the user-struct
/// sibling of `mut_ref_collection_params_method_mutated_in_body`): a bare `&mut S`
/// parameter in a postcondition resolves to its ENTRY snapshot (structs are not
/// `supported_mut_ref` scalars, so the two-state final-value rewrite never runs).
/// A method mutation (`s.bump()`) is not threaded into that snapshot, so the
/// postcondition is checked against the PRE-call state — a false `Verified`. The
/// caller uses this set to FAIL CLOSED on such postconditions. A pure `&self`/
/// by-value reader never enters the set (NO over-rejection).
pub(super) fn mut_ref_struct_params_method_mutated_in_body(
    block: &syn::Block,
    param_struct_types: &BTreeMap<String, String>,
    kinds: &HashMap<(String, String), SelfReceiverKind>,
    struct_types: &[StructDef],
) -> BTreeSet<String> {
    struct StructMethodMutationVisitor<'a> {
        param_struct_types: &'a BTreeMap<String, String>,
        kinds: &'a HashMap<(String, String), SelfReceiverKind>,
        struct_types: &'a [StructDef],
        mutated: BTreeSet<String>,
        /// Lexically-scoped local binding -> moved `&mut` parameter root. `None`
        /// is a non-alias shadow and blocks fallback to a same-named parameter.
        aliases: BTreeMap<String, Option<String>>,
    }

    /// Resolve the method receiver to a tracked `&mut` struct param plus whether
    /// the call is on the param DIRECTLY (`P.m()` / `(*P).m()`) or on a SUB-PLACE
    /// projection of it (`P.field.m()` / `P[i].m()`). A sub-place call mutates the
    /// root `P` exactly when it mutates that sub-field, but the sub-field's own
    /// type is not resolvable here, so the caller classifies a projection by the
    /// universal pure-method allow-list rather than the root type's receiver kind.
    impl StructMethodMutationVisitor<'_> {
        fn resolve_root_param(&self, ident: &str) -> Option<String> {
            match self.aliases.get(ident) {
                Some(root) => root.clone(),
                None => self
                    .param_struct_types
                    .contains_key(ident)
                    .then(|| ident.to_string()),
            }
        }

        fn method_receiver_param(&self, receiver: &Expr) -> Option<(String, bool)> {
            // `P.m()` / `(*P).m()` (and their let-move aliases) are direct.
            if let Some(ident) = method_call_receiver_ident(receiver) {
                return self.resolve_root_param(&ident).map(|root| (root, true));
            }
            // `P.field.m()` / `P[i].m()` mutate a sub-place of the root.
            let ident = field_index_projection_root(receiver)?;
            self.resolve_root_param(&ident).map(|root| (root, false))
        }
    }

    impl<'ast> Visit<'ast> for StructMethodMutationVisitor<'_> {
        fn visit_block(&mut self, block: &'ast syn::Block) {
            let saved = self.aliases.clone();
            syn::visit::visit_block(self, block);
            self.aliases = saved;
        }

        fn visit_local(&mut self, local: &'ast syn::Local) {
            let binding = local_binding_ident(&local.pat).map(|name| {
                let root = local.init.as_ref().and_then(|init| {
                    expr_path_ident(&init.expr).and_then(|ident| self.resolve_root_param(&ident))
                });
                (name, root)
            });
            syn::visit::visit_local(self, local);
            if let Some((name, root)) = binding {
                self.aliases.insert(name, root);
            }
        }

        fn visit_expr_method_call(&mut self, method_call: &'ast syn::ExprMethodCall) {
            if let Some((name, direct_receiver)) = self.method_receiver_param(&method_call.receiver)
            {
                let method = method_call.method.to_string();
                let mutates = if direct_receiver {
                    let struct_type = &self.param_struct_types[&name];
                    struct_method_mutates_caller_with_kinds(self.kinds, struct_type, &method)
                } else {
                    // Sub-field projection (`P.field.m()`): resolve the projected
                    // sub-field's OWN struct type from the file struct registry and
                    // classify by the SAME receiver-kind registry as a direct
                    // receiver — a pure `&self` getter on the sub-field, REGARDLESS
                    // of name, is NOT flagged (no over-rejection), while a `&mut
                    // self` (or unresolved-non-pure) method flags the ROOT param.
                    // Fall back to the conservative pure-name allow-list only when
                    // the sub-field type is UNRESOLVABLE (fail-closed).
                    let root_struct_type = &self.param_struct_types[&name];
                    match projected_param_field_struct_type(
                        &method_call.receiver,
                        root_struct_type,
                        self.struct_types,
                    ) {
                        Some(sub_type) => {
                            struct_method_mutates_caller_with_kinds(self.kinds, &sub_type, &method)
                        }
                        None => !is_known_pure_struct_method(&method),
                    }
                };
                if mutates {
                    self.mutated.insert(name);
                }
            }
            syn::visit::visit_expr_method_call(self, method_call);
        }

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut visitor = StructMethodMutationVisitor {
        param_struct_types,
        kinds,
        struct_types,
        mutated: BTreeSet::new(),
        aliases: BTreeMap::new(),
    };
    visitor.visit_block(block);
    visitor.mutated
}

fn is_known_pure_struct_method(method: &str) -> bool {
    if is_pure_collection_read_method(method) {
        return true;
    }
    matches!(
        method,
        // Conversions / borrows that return a NEW value or a shared view.
        "as_ref"
            | "as_str"
            | "as_path"
            | "as_os_str"
            | "to_owned"
            | "to_string"
            | "to_vec"
            | "borrow"
            | "clone"
            // Universally `&self` reads.
            | "len"
            | "is_empty"
            | "hash"
            | "fmt"
            | "eq"
            | "ne"
            | "cmp"
            | "partial_cmp"
            | "lt"
            | "le"
            | "gt"
            | "ge"
            | "contains"
            | "count"
    )
}

/// Method names that are PURE on ghost collections (`Set`/`Seq`/`Map`/
/// `Multiset`) — they return a NEW value or read through `&self` — AND have NO
/// same-named in-place mutator on any std container (`Vec`/`[T]`/`HashSet`/
/// `BTreeSet`/`HashMap`/`BTreeMap`). Calling such a method therefore leaves the
/// receiver value unchanged, which is what makes preserving the receiver binding
/// across the call SOUND even though the modeled type cannot distinguish an
/// immutable ghost collection from a mutable exec container (GAP2).
///
/// This is deliberately a POSITIVE allow-list, NOT the complement of
/// `is_known_mutating_method`: in-place mutators such as `Vec::sort`/`dedup`/
/// `retain`/`reverse`/`extend`/`drain` are absent from `is_known_mutating_method`
/// but still mutate, so the complement would be unsound. Names that ARE in-place
/// mutators on some container (`insert`/`remove`/`push`/`pop`/`clear`/`truncate`/
/// `append`/`swap`/`swap_remove`/`sort`/`dedup`/`retain`/`reverse`/`extend`/
/// `drain`/`resize`/`reserve`/`split_off`/`rotate_left`/`rotate_right`/`fill`)
/// are intentionally EXCLUDED — even where they are pure on a ghost `Set`/`Map`
/// — so that a mutable receiver is always conservatively invalidated.
fn pure_ghost_collection_combinator(method: &str) -> bool {
    matches!(
        method,
        // Set / Seq / Map transforming combinators (return a new collection).
        "filter"
            | "map"
            | "map_values"
            | "union"
            | "union_prefer_right"
            | "intersect"
            | "difference"
            | "complement"
            | "restrict"
            | "remove_keys"
            | "subrange"
            // NOTE: `take`/`skip` are deliberately NOT listed. `BTreeSet::take`
            // is a `&mut self` in-place remove, and a `BTreeSet` is modeled as
            // `Set` (collection-like), so listing `take` would let a mutated
            // `BTreeSet` carry stale state forward — unsound.
            | "drop_first"
            | "drop_last"
            | "add"
            | "sub"
            // Folds / reductions (return a scalar; consume by value).
            | "fold"
            | "fold_left"
            | "fold_right"
            // `&self` reads (non-mutating on every relevant container).
            | "len"
            | "contains"
            | "contains_key"
            | "contains_pair"
            | "is_empty"
            | "finite"
            | "choose"
            | "dom"
            | "values"
            | "keys"
            | "count"
            | "first"
            | "last"
            | "subset_of"
            | "disjoint"
    )
}

/// Methods that, applied to an expression ALREADY modeling an immutable ghost
/// collection, return ANOTHER ghost collection — but which are deliberately
/// excluded from [`pure_ghost_collection_combinator`] because they share a name
/// with an in-place mutator on an EXEC container (`Vec::push`, `Vec::insert`,
/// `HashSet::insert`/`remove`, ...).
///
/// SOUNDNESS: this predicate is consulted ONLY by
/// [`ExtractState::expr_models_ghost_collection`], whose recursion bottoms out at
/// a ghost CONSTRUCTOR (`Seq::empty`/`Seq::new`/`Set::new`/…) via
/// [`ghost_collection_constructor_path`]. An exec chain such as
/// `Vec::new().push(..)` bottoms out at `Vec::new`, which is NOT a ghost
/// constructor, so the recursion returns `false` before this predicate can mark
/// it — an exec container is never ghost-marked. It is NOT used for receiver
/// preservation ([`ExtractState::method_call_preserves_receiver`] keeps the
/// strict `pure_ghost_collection_combinator` gate), so a genuinely-mutated exec
/// receiver still cannot survive a call. Marking a ghost-rooted chain
/// (`Seq::empty().push(x).push(y)`) as a ghost collection is therefore sound and
/// lets a reused `let s = Seq::empty().push(..)..` survive a later pure
/// `s.map(..)`/`s.subrange(..)`.
fn ghost_collection_value_producing_method(method: &str) -> bool {
    matches!(method, "push" | "update" | "insert" | "remove")
}

/// Collects every single-segment value-position identifier referenced anywhere
/// in `expr` (the body of a closure). Multi-segment paths (`Set::new`), method
/// names, and field members are not value-position idents and are excluded, so
/// the result is the candidate set of names a closure body might capture.
fn closure_referenced_idents(expr: &Expr) -> BTreeSet<String> {
    struct IdentCollector {
        idents: BTreeSet<String>,
    }
    impl<'ast> Visit<'ast> for IdentCollector {
        fn visit_expr_path(&mut self, expr_path: &'ast syn::ExprPath) {
            if expr_path.qself.is_none() && expr_path.path.segments.len() == 1 {
                if let Some(segment) = expr_path.path.segments.first() {
                    self.idents.insert(segment.ident.to_string());
                }
            }
            visit::visit_expr_path(self, expr_path);
        }
    }
    let mut collector = IdentCollector {
        idents: BTreeSet::new(),
    };
    collector.visit_expr(expr);
    collector.idents
}

/// True when `ident` names one of the binary spec MARKER macros that
/// `chained_comparisons` lowers `==>` / `<==>` into (`__trust_vc_implies!(P, Q)`
/// / `__trust_vc_iff!(P, Q)`).
fn is_binary_spec_marker_ident(ident: &syn::Ident) -> bool {
    ident == crate::chained_comparisons::IMPLIES_MARKER_MACRO
        || ident == crate::chained_comparisons::IFF_MARKER_MACRO
}

/// Rewrites the binary spec MARKER macros (`__trust_vc_implies!(P, Q)` /
/// `__trust_vc_iff!(P, Q)`) in `expr` to same-named CALL expressions
/// (`__trust_vc_implies(P, Q)`), in place. A syn `Visit`/`VisitMut` pass does NOT
/// descend into a macro's opaque token stream, so a variable inside a `==>` /
/// `<==>` (e.g. the let-local `s` in `forall|k| s.contains(k) ==> ..`) is
/// invisible to scoped substitution and shadowing analysis. The call form exposes
/// `P`/`Q` as ordinary sub-expressions the visitors traverse. Purely structural;
/// inverse of [`denormalize_spec_markers`]. `parse_quote!` cannot fail here — a
/// `Punctuated<Expr, Comma>` interpolated into `ident(..)` is always a valid call.
fn normalize_spec_markers(expr: &mut Expr) {
    struct Norm;
    impl VisitMut for Norm {
        fn visit_expr_mut(&mut self, node: &mut Expr) {
            if let Expr::Macro(mac) = node {
                if let Some(ident) = mac.mac.path.get_ident() {
                    if is_binary_spec_marker_ident(ident) {
                        let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
                        if let Ok(args) = parser.parse2(mac.mac.tokens.clone()) {
                            if args.len() == 2 {
                                let ident = ident.clone();
                                *node = syn::parse_quote!(#ident(#args));
                            }
                        }
                    }
                }
            }
            // Recurse into children (the freshly-built call's args, or the
            // original node's children) so NESTED markers are normalized too.
            syn::visit_mut::visit_expr_mut(self, node);
        }
    }
    Norm.visit_expr_mut(expr);
}

/// Inverse of [`normalize_spec_markers`]: rewrites the same-named CALL forms back
/// to their `!` marker-macro form so the rendered obligation string is exactly
/// the shape the lowering expects. Bottom-up so nested calls denormalize first.
fn denormalize_spec_markers(expr: &mut Expr) {
    struct Denorm;
    impl VisitMut for Denorm {
        fn visit_expr_mut(&mut self, node: &mut Expr) {
            syn::visit_mut::visit_expr_mut(self, node);
            if let Expr::Call(call) = node {
                if let Expr::Path(path) = &*call.func {
                    if let Some(ident) = path.path.get_ident() {
                        if is_binary_spec_marker_ident(ident) && call.args.len() == 2 {
                            let ident = ident.clone();
                            let args = call.args.clone();
                            *node = syn::parse_quote!(#ident!(#args));
                        }
                    }
                }
            }
        }
    }
    Denorm.visit_expr_mut(expr);
}

/// Look through transparent `(.. )` / `group` wrappers to the inner expression.
/// Used to recognize a closure literal / called callee through grouping. Does NOT
/// peel references or other place wrappers (those change meaning).
fn strip_paren_group_expr(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(paren) => strip_paren_group_expr(&paren.expr),
        Expr::Group(group) => strip_paren_group_expr(&group.expr),
        other => other,
    }
}

/// A closure parameter that is a single bound identifier (`x`, `x: T`, `mut x`),
/// returning its name. Returns `None` for a destructuring / `ref` / `@`-subpattern
/// parameter, which the flat call-argument substitution cannot model exactly.
fn closure_param_simple_ident(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(pat_ident) if pat_ident.subpat.is_none() && pat_ident.by_ref.is_none() => {
            Some(pat_ident.ident.to_string())
        }
        Pat::Type(pat_type) => closure_param_simple_ident(&pat_type.pat),
        _ => None,
    }
}

/// An integer-literal value (through paren/group wrappers and a leading unary
/// `-`), or `None` for any non-integer-literal expression. Used by the concrete
/// ground-filter evaluator to recognise ground `seq![..]` elements and to fold
/// literal comparison operands. Deliberately NARROW: no named constants, no
/// arithmetic — only a written integer literal (optionally negated).
fn expr_as_int_literal(expr: &Expr) -> Option<i128> {
    match expr {
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(int_lit),
            ..
        }) => int_lit.base10_parse::<i128>().ok(),
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
            expr_as_int_literal(&unary.expr)?.checked_neg()
        }
        Expr::Paren(paren) => expr_as_int_literal(&paren.expr),
        Expr::Group(group) => expr_as_int_literal(&group.expr),
        _ => None,
    }
}

/// The explicit integer-type SUFFIX of a written integer literal (`"i32"` for
/// `45i32`, through a leading `-`/paren/group), or `None` when the literal is
/// unsuffixed (`45`) or not an integer literal. Used to give the empty
/// concrete-filter result an inferable element type (`Seq::<i32>::empty()`); an
/// unsuffixed element declines the empty rewrite (fail-closed).
fn int_literal_suffix(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(int_lit),
            ..
        }) => {
            let suffix = int_lit.suffix();
            (!suffix.is_empty()).then(|| suffix.to_string())
        }
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
            int_literal_suffix(&unary.expr)
        }
        Expr::Paren(paren) => int_literal_suffix(&paren.expr),
        Expr::Group(group) => int_literal_suffix(&group.expr),
        _ => None,
    }
}

/// Fold a substituted filter-predicate body to a DEFINITE bool, or `None` if it
/// is not exactly a boolean tree over integer-literal comparisons and boolean
/// combinators. SOUNDNESS-CRITICAL: this is the value that decides keep/drop, so
/// it must be EXACT — it folds only `intlit COMP intlit` (mathematical i128
/// comparison = the spec truth, no overflow because there is no arithmetic),
/// `bool` literals, `!`, `&&`, `||`. Any other leaf (a name, arithmetic, a cast,
/// a method call, a non-literal operand) returns `None`, which makes the caller
/// decline the whole rewrite and fall back to the opaque (Skolemized) filter.
fn fold_filter_predicate_to_bool(expr: &Expr) -> Option<bool> {
    match expr {
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Bool(b),
            ..
        }) => Some(b.value),
        Expr::Paren(paren) => fold_filter_predicate_to_bool(&paren.expr),
        Expr::Group(group) => fold_filter_predicate_to_bool(&group.expr),
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Not(_)) => {
            fold_filter_predicate_to_bool(&unary.expr).map(|b| !b)
        }
        Expr::Binary(bin) => {
            use syn::BinOp;
            match &bin.op {
                // Short-circuit is sound: `false && X == false`, `true || X == true`.
                BinOp::And(_) => Some(
                    fold_filter_predicate_to_bool(&bin.left)?
                        && fold_filter_predicate_to_bool(&bin.right)?,
                ),
                BinOp::Or(_) => Some(
                    fold_filter_predicate_to_bool(&bin.left)?
                        || fold_filter_predicate_to_bool(&bin.right)?,
                ),
                BinOp::Lt(_) => {
                    Some(expr_as_int_literal(&bin.left)? < expr_as_int_literal(&bin.right)?)
                }
                BinOp::Le(_) => {
                    Some(expr_as_int_literal(&bin.left)? <= expr_as_int_literal(&bin.right)?)
                }
                BinOp::Gt(_) => {
                    Some(expr_as_int_literal(&bin.left)? > expr_as_int_literal(&bin.right)?)
                }
                BinOp::Ge(_) => {
                    Some(expr_as_int_literal(&bin.left)? >= expr_as_int_literal(&bin.right)?)
                }
                BinOp::Eq(_) => {
                    Some(expr_as_int_literal(&bin.left)? == expr_as_int_literal(&bin.right)?)
                }
                BinOp::Ne(_) => {
                    Some(expr_as_int_literal(&bin.left)? != expr_as_int_literal(&bin.right)?)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The predicate closure of a `.filter(..)` argument: a bare `|x| ..` closure or
/// a `SpecFn::new(|x| ..)` wrapper (through paren/group). `None` for any other
/// shape (a named `SpecFn` variable, a `SpecFn::new(fn_path)`, …) — declines so
/// the caller falls back to the opaque filter.
fn filter_predicate_closure(arg: &Expr) -> Option<&syn::ExprClosure> {
    match arg {
        Expr::Closure(closure) => Some(closure),
        Expr::Paren(paren) => filter_predicate_closure(&paren.expr),
        Expr::Group(group) => filter_predicate_closure(&group.expr),
        Expr::Call(call) => {
            let Expr::Path(func_path) = &*call.func else {
                return None;
            };
            let segments = &func_path.path.segments;
            // `SpecFn::new(closure)` / `SpecFn::<..>::new(closure)`.
            if segments.last()?.ident != "new" || segments.len() < 2 {
                return None;
            }
            if segments[segments.len() - 2].ident != "SpecFn" {
                return None;
            }
            if call.args.len() != 1 {
                return None;
            }
            filter_predicate_closure(call.args.first()?)
        }
        _ => None,
    }
}

/// CONCRETE GROUND FILTER EVALUATION (recovery for the seq-`.filter`-membership
/// quantifier hang). Fires ONLY for `seq![intlit, ..].filter(pred)` where the
/// receiver is a ground `seq!` of integer literals and `pred` is a capture-free
/// unary closure whose body folds to a DEFINITE bool at each element. Returns the
/// concrete kept `seq![..]` rendering (same macro path as the receiver) so
/// downstream reads hit the working fixed-array path. Returns `None` — declining
/// to the opaque filter — for every shape that is not exactly evaluable:
/// non-`seq!` receiver, a non-literal element, a non-inline/captured/wrong-arity
/// predicate, a macro-bearing body, or any element whose predicate does not fold.
/// An all-dropped (empty) result also declines (an element-less `seq![]` has no
/// inferable element type) — sound: the opaque filter fails closed.
fn try_concrete_ground_filter(method_call: &syn::ExprMethodCall) -> Option<String> {
    let Expr::Macro(recv_macro) = &*method_call.receiver else {
        return None;
    };
    if recv_macro.mac.path.segments.last()?.ident != "seq" {
        return None;
    }
    let elements: Vec<Expr> = Punctuated::<Expr, Token![,]>::parse_terminated
        .parse2(recv_macro.mac.tokens.clone())
        .ok()?
        .into_iter()
        .collect();
    if elements.is_empty() {
        return None;
    }
    // Every element must be a written integer literal (the ground precondition).
    if elements.iter().any(|e| expr_as_int_literal(e).is_none()) {
        return None;
    }
    let closure = filter_predicate_closure(method_call.args.first()?)?;
    if closure_body_contains_macro(&closure.body) {
        return None;
    }
    if closure.inputs.len() != 1 {
        return None;
    }
    let param = closure_param_simple_ident(closure.inputs.first()?)?;
    let body_bound = closure_body_bound_idents(&closure.body);
    // Shadowing-safety: a param re-bound in the body must not be flat-substituted.
    if body_bound.contains(&param) {
        return None;
    }
    // Capture-freedom: every referenced ident is the param or bound in the body.
    let referenced = closure_body_referenced_path_idents(&closure.body);
    if referenced
        .iter()
        .any(|id| *id != param && !body_bound.contains(id))
    {
        return None;
    }
    let mut kept: Vec<String> = Vec::new();
    for element in &elements {
        let mut body = (*closure.body).clone();
        let subst: HashMap<String, Expr> =
            std::iter::once((param.clone(), element.clone())).collect();
        substitute_param_idents(&mut body, &subst);
        match fold_filter_predicate_to_bool(&body) {
            Some(true) => kept.push(element.to_token_stream().to_string()),
            Some(false) => {}
            // A predicate that does not fold to a definite bool — decline the
            // whole rewrite (fall back to the opaque filter, fail-closed).
            None => return None,
        }
    }
    let segments = &recv_macro.mac.path.segments;
    // Path prefix before the `seq` segment (e.g. `trust_vc_types`), reused so the
    // synthesized result carries the same module path as the source macro.
    let prefix: String = segments
        .iter()
        .take(segments.len() - 1)
        .map(|s| s.ident.to_string())
        .collect::<Vec<_>>()
        .join("::");
    if kept.is_empty() {
        // All elements dropped -> the empty seq. An element-less `seq![]` has no
        // inferable element type, so render `Seq::<T>::empty()` with T taken from
        // a written integer suffix; decline (fail-closed, stays NotProved) when no
        // element is suffixed.
        let suffix = elements.iter().find_map(int_literal_suffix)?;
        return Some(if prefix.is_empty() {
            format!("Seq::<{suffix}>::empty()")
        } else {
            format!("{prefix}::Seq::<{suffix}>::empty()")
        });
    }
    let elems = kept.join(", ");
    Some(if prefix.is_empty() {
        format!("seq![{elems}]")
    } else {
        format!("{prefix}::seq![{elems}]")
    })
}

/// Substitute each free single-ident occurrence of a parameter name in `expr`
/// with its mapped call-argument expression (used to instantiate an invoked exec
/// closure's body at the call site). The replacement argument is NOT recursively
/// re-substituted — it denotes a caller-scope expression that the obligation
/// emitter resolves against the current scope. Callers must have already excluded
/// bodies that re-bind a parameter name (shadowing-safety), so every remaining
/// occurrence of a mapped name is a genuine capture of that parameter.
fn substitute_param_idents(expr: &mut Expr, subst: &HashMap<String, Expr>) {
    struct ParamSubst<'a> {
        subst: &'a HashMap<String, Expr>,
    }
    impl VisitMut for ParamSubst<'_> {
        fn visit_expr_mut(&mut self, node: &mut Expr) {
            if let Expr::Path(path) = node {
                if path.qself.is_none() && path.path.segments.len() == 1 {
                    let name = path.path.segments[0].ident.to_string();
                    if let Some(replacement) = self.subst.get(&name) {
                        *node = replacement.clone();
                        return;
                    }
                }
            }
            syn::visit_mut::visit_expr_mut(self, node);
        }
    }
    ParamSubst { subst }.visit_expr_mut(expr);
}

/// True when a closure body contains a body-level `assume!` (`assume!` /
/// `trust_vc_assume!`) macro — the leak source for #74 cross-closure captured-var
/// contamination (a `trust_vc::closure!` `requires` / body relation lowers to an
/// `assume!`). Only such closures need their captured free vars freshened; an
/// `assume!`-free closure cannot leak a hypothesis to a sibling, so it is left
/// untouched (preserving any legitimate outer-fact dependency — no over-rejection).
fn closure_body_contains_assume(body: &Expr) -> bool {
    struct AssumeFinder {
        found: bool,
    }
    impl<'ast> Visit<'ast> for AssumeFinder {
        fn visit_macro(&mut self, mac: &'ast Macro) {
            if super::path_last_segment(&mac.path)
                .as_deref()
                .is_some_and(|name| matches!(name, "assume" | "trust_vc_assume"))
            {
                self.found = true;
            }
            visit::visit_macro(self, mac);
        }
    }
    let mut finder = AssumeFinder { found: false };
    finder.visit_expr(body);
    finder.found
}

/// Every identifier BOUND by a pattern (`Pat::Ident` binders anywhere within,
/// incl. subpatterns / tuple-struct / struct fields). Used to decide whether the
/// last arm of a wildcard-less match may be rendered `_` without dropping a
/// binding its body reads. NOTE: syn parses a bare unit-variant pattern (`None`)
/// as a `Pat::Ident` too, so this over-collects — that only makes the `_`
/// rewrite MORE conservative (it declines when the body reuses that name), never
/// less sound.
/// The `(enum, variant)` names of a QUALIFIED enum-variant pattern (`E::V`,
/// `E::V(..)`, `E::V { .. }`), or `None` for any other pattern. Used by
/// `match_is_exhaustive`.
fn pat_enum_variant(pat: &Pat) -> Option<(String, String)> {
    let path = match pat {
        Pat::TupleStruct(p) => &p.path,
        Pat::Struct(p) => &p.path,
        Pat::Path(p) => &p.path,
        _ => return None,
    };
    let segments = &path.segments;
    if segments.len() < 2 {
        return None;
    }
    Some((
        segments[segments.len() - 2].ident.to_string(),
        segments[segments.len() - 1].ident.to_string(),
    ))
}

/// The boolean value of a `true`/`false` literal pattern, or `None`.
fn pat_bool_literal(pat: &Pat) -> Option<bool> {
    let Pat::Lit(pat_lit) = pat else {
        return None;
    };
    match &pat_lit.lit {
        syn::Lit::Bool(b) => Some(b.value),
        _ => None,
    }
}

fn pat_bound_idents(pat: &Pat) -> BTreeSet<String> {
    struct PatIdentCollector {
        idents: BTreeSet<String>,
    }
    impl<'ast> Visit<'ast> for PatIdentCollector {
        fn visit_pat_ident(&mut self, pat_ident: &'ast syn::PatIdent) {
            self.idents.insert(pat_ident.ident.to_string());
            visit::visit_pat_ident(self, pat_ident);
        }
    }
    let mut collector = PatIdentCollector {
        idents: BTreeSet::new(),
    };
    collector.visit_pat(pat);
    collector.idents
}

/// True when a closure body contains ANY macro invocation. The syn visitors do
/// not descend into a macro's token stream, so a body carrying a macro is not
/// fully analyzable for its free identifiers — used to decline inlining such a
/// closure at a call site (its captures/callees could hide inside the macro).
fn closure_body_contains_macro(expr: &Expr) -> bool {
    struct MacroFinder {
        found: bool,
    }
    impl<'ast> Visit<'ast> for MacroFinder {
        fn visit_macro(&mut self, _mac: &'ast Macro) {
            self.found = true;
        }
    }
    let mut finder = MacroFinder { found: false };
    finder.visit_expr(expr);
    finder.found
}

/// Collect every identifier token in a raw token stream (recursing into
/// delimited groups). Unlike a syn `Visit`, this descends into MACRO tokens — the
/// `assume!` / `assert!` payloads where a closure's captured free variables live
/// — so the #74 capture-freshening can find them. Over-collects (type / method /
/// keyword idents); callers filter to declared variables.
fn collect_token_stream_idents(tokens: TokenStream, out: &mut BTreeSet<String>) {
    for tt in tokens {
        match tt {
            TokenTree::Ident(ident) => {
                out.insert(ident.to_string());
            }
            TokenTree::Group(group) => collect_token_stream_idents(group.stream(), out),
            _ => {}
        }
    }
}

/// Lexically free identifier candidates in one closure body, including names
/// that occur only inside opaque macro token streams. This is intentionally an
/// over-approximation (macro field/type identifiers are also seen), but it is
/// scope- and order-aware for ordinary Rust bindings: a `let` name enters scope
/// only after its initializer, block/match/for bindings do not escape, closure
/// parameters are bound from entry, and nested closures analyze themselves.
fn closure_free_ident_candidates(expr_closure: &syn::ExprClosure) -> BTreeSet<String> {
    struct Collector {
        scopes: Vec<BTreeSet<String>>,
        free: BTreeSet<String>,
    }

    impl Collector {
        fn is_bound(&self, name: &str) -> bool {
            self.scopes.iter().rev().any(|scope| scope.contains(name))
        }

        fn record(&mut self, name: String) {
            if !self.is_bound(&name) {
                self.free.insert(name);
            }
        }

        fn push_bindings(&mut self, bindings: BTreeSet<String>) {
            self.scopes.push(bindings);
        }
    }

    impl<'ast> Visit<'ast> for Collector {
        fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
            if path.qself.is_none() && path.path.segments.len() == 1 {
                if let Some(segment) = path.path.segments.first() {
                    self.record(segment.ident.to_string());
                }
            }
            visit::visit_expr_path(self, path);
        }

        fn visit_macro(&mut self, mac: &'ast Macro) {
            let mut raw = BTreeSet::new();
            collect_token_stream_idents(mac.tokens.clone(), &mut raw);
            for name in raw {
                self.record(name);
            }
        }

        fn visit_block(&mut self, block: &'ast syn::Block) {
            self.push_bindings(BTreeSet::new());
            for stmt in &block.stmts {
                self.visit_stmt(stmt);
            }
            self.scopes.pop();
        }

        fn visit_local(&mut self, local: &'ast syn::Local) {
            // Rust does not put a `let` pattern in scope for its initializer or
            // diverging `else` arm. Visit those under the prior environment.
            if let Some(init) = &local.init {
                self.visit_expr(&init.expr);
                if let Some((_, diverge)) = &init.diverge {
                    self.visit_expr(diverge);
                }
            }
            if let Some(scope) = self.scopes.last_mut() {
                scope.extend(bound_idents_from_pat(&local.pat));
            }
        }

        fn visit_expr_match(&mut self, expr_match: &'ast syn::ExprMatch) {
            self.visit_expr(&expr_match.expr);
            for arm in &expr_match.arms {
                self.push_bindings(bound_idents_from_pat(&arm.pat));
                if let Some((_, guard)) = &arm.guard {
                    self.visit_expr(guard);
                }
                self.visit_expr(&arm.body);
                self.scopes.pop();
            }
        }

        fn visit_expr_for_loop(&mut self, expr_for_loop: &'ast syn::ExprForLoop) {
            self.visit_expr(&expr_for_loop.expr);
            self.push_bindings(bound_idents_from_pat(&expr_for_loop.pat));
            self.visit_block(&expr_for_loop.body);
            self.scopes.pop();
        }

        // A nested closure owns its own capture isolation when the assertion
        // collector visits it; treating its binders/references as this closure's
        // would both blur scopes and unnecessarily freshen outer facts.
        fn visit_expr_closure(&mut self, _closure: &'ast syn::ExprClosure) {}

        fn visit_item(&mut self, _item: &'ast Item) {}
    }

    let mut entry_bindings = BTreeSet::new();
    for input in &expr_closure.inputs {
        entry_bindings.extend(bound_idents_from_pat(input));
    }
    let mut collector = Collector {
        scopes: vec![entry_bindings],
        free: BTreeSet::new(),
    };
    collector.visit_expr(&expr_closure.body);
    collector.free
}

/// Collects every identifier bound by a pattern anywhere within `expr` — nested
/// closure parameters, `let` bindings, and `match`/`for` patterns. Used to make
/// the flat closure-capture substitution shadowing-safe: a name re-bound in an
/// inner scope must not be rewritten to an outer value.
fn closure_body_bound_idents(expr: &Expr) -> BTreeSet<String> {
    struct BoundIdentCollector {
        idents: BTreeSet<String>,
    }
    impl<'ast> Visit<'ast> for BoundIdentCollector {
        fn visit_pat_ident(&mut self, pat_ident: &'ast syn::PatIdent) {
            self.idents.insert(pat_ident.ident.to_string());
            visit::visit_pat_ident(self, pat_ident);
        }
    }
    let mut collector = BoundIdentCollector {
        idents: BTreeSet::new(),
    };
    collector.visit_expr(expr);
    collector.idents
}

/// Every single-segment path identifier referenced in expression position within
/// `expr` — an over-approximation of its free variables AND free callees (a call
/// `g(..)` visits `g` as an `ExprPath`). Used to decide a closure body is a pure
/// function of its parameters (referenced ⊆ params ∪ body-bound) before inlining
/// it at a call site; any other referenced ident is a capture or free callee.
fn closure_body_referenced_path_idents(expr: &Expr) -> BTreeSet<String> {
    struct RefCollector {
        idents: BTreeSet<String>,
    }
    impl<'ast> Visit<'ast> for RefCollector {
        fn visit_expr_path(&mut self, ep: &'ast syn::ExprPath) {
            if ep.qself.is_none() && ep.path.segments.len() == 1 {
                self.idents.insert(ep.path.segments[0].ident.to_string());
            }
            visit::visit_expr_path(self, ep);
        }
    }
    let mut collector = RefCollector {
        idents: BTreeSet::new(),
    };
    collector.visit_expr(expr);
    collector.idents
}

/// True when `func` is a path call onto one of the ghost-collection types
/// (`Set`/`Seq`/`Map`/`Multiset`), e.g. `Set::new(..)`, `Set::<int>::empty()`,
/// or `trust_vc_types::Seq::empty()`. Exec constructors such as `Vec::new`,
/// `HashSet::new`, or `HashMap::new` deliberately do NOT match — their values
/// are mutable and must not be treated as immutable ghost collections.
fn ghost_collection_constructor_path(func: &Expr) -> bool {
    let Expr::Path(path) = func else {
        return false;
    };
    // The type sits in the second-to-last segment of an associated-function
    // path (`Type::assoc_fn`); the last segment is the function name.
    let segments = &path.path.segments;
    if segments.len() < 2 {
        return false;
    }
    let type_segment = &segments[segments.len() - 2];
    matches!(
        type_segment.ident.to_string().as_str(),
        "Set" | "Seq" | "Map" | "Multiset"
    )
}

fn helper_return_aliases_erased_shared_ref_param(contract: &HelperCallContract) -> bool {
    contract.ensures.iter().any(|clause| {
        direct_return_alias_param(&clause.condition, &contract.return_binding).is_some_and(
            |param| {
                contract
                    .params
                    .iter()
                    .zip(&contract.erased_shared_ref_params)
                    .any(|(candidate, erased)| *erased && candidate == &param)
            },
        )
    })
}

fn direct_return_alias_param(expr: &Expr, return_binding: &str) -> Option<String> {
    let Expr::Binary(binary) = strip_place_wrappers(expr) else {
        return None;
    };
    if !matches!(binary.op, syn::BinOp::Eq(_)) {
        return None;
    }
    let left = expr_path_ident(&binary.left);
    let right = expr_path_ident(&binary.right);
    match (left.as_deref(), right.as_deref()) {
        (Some(left), Some(right)) if left == return_binding => Some(right.to_string()),
        (Some(left), Some(right)) if right == return_binding => Some(left.to_string()),
        _ => None,
    }
}

struct ContractExprSubstituter<'a> {
    substitutions: &'a BTreeMap<String, Expr>,
    erased_shared_ref_params: &'a BTreeSet<String>,
    /// Two-state `old(P)` / `*old(P)` / `old(*P)` substitutions for `&mut`
    /// SCALAR params of a contracted helper (slice D): the whole `old` form is
    /// replaced ATOMICALLY by the PRE-call value rendering, never recursed
    /// into — while bare `P` keeps substituting from `substitutions` (the
    /// POST-call map in `ensures`). Empty everywhere except the helper-call
    /// contract path, so the closure-capture rewrite sites keep their
    /// pre-slice-D behavior byte-for-byte.
    old_substitutions: &'a BTreeMap<String, Expr>,
    /// `&mut` scalar params of a contracted helper. Their substitution values
    /// are referent VALUES (never references), so a contract `*P` erases the
    /// deref and substitutes the value directly, exactly like the erased
    /// shared-ref params.
    erased_mut_ref_value_params: &'a BTreeSet<String>,
    /// SCOPE STACK — the identifiers bound by the binders ENCLOSING the
    /// expression currently being visited (quantifier/spec-closure params,
    /// `let` locals, `match`-arm and `for` patterns). Always starts EMPTY at
    /// every construction site; it is pushed/popped by the visitor itself.
    ///
    /// SOUNDNESS (the reason this field exists). Every map here is keyed by
    /// BARE PARAMETER NAME. Without a scope stack the rewriter also rewrote
    /// occurrences that a binder inside the clause had RE-BOUND, so a callee
    /// contract `requires(forall|m: int| m <= 100)` on `fn callee(m: u64)`
    /// became `forall|m: int| ARG <= 100` at the call site — the caller then
    /// discharged a TAUTOLOGY instead of the (unsatisfiable) real clause and
    /// `callee(5)` verified. See the `contract_binder_capture_*` guards.
    ///
    /// The correction must stay EXACT in both directions: skipping too much is
    /// unsound too. Leaving a FREE param occurrence unsubstituted would let it
    /// re-bind to a same-named local in the CALLER's scope, so
    /// `requires(m <= 100)` checked at a call passing `200` inside a caller
    /// holding `let m = 5;` would wrongly pass (guard
    /// `free_occurrence_must_not_rebind_to_a_caller_local`). Bound occurrences
    /// are skipped; free ones are always substituted.
    binder_scopes: Vec<BTreeSet<String>>,
    /// STICKY POISON, set when a binder's bound names cannot be enumerated
    /// exactly (an opaque `Pat` form, or an `if let`/`while let` whose binding
    /// region this local view cannot delimit). Once set, every enclosing
    /// expression is replaced by [`unscopable_binder_marker`] as the visit
    /// unwinds, so the whole clause reaches the encoder as an unresolved
    /// symbol and fails CLOSED. `substitute_helper_contract_clause` reads the
    /// flag directly and returns a diagnostic instead.
    ///
    /// Guessing a region is not an option here: guessing WIDE drops a real
    /// substitution (unsound — the caller-scope re-bind above), guessing NARROW
    /// captures (unsound — the tautology above). Only refusing is safe.
    unscopable_binder: bool,
}

impl ContractExprSubstituter<'_> {
    /// True when `name` is RE-BOUND by a binder enclosing the current position,
    /// i.e. the occurrence denotes the binder's variable and NOT the contracted
    /// callee's parameter. Such occurrences must never be substituted.
    fn is_binder_bound(&self, name: &str) -> bool {
        self.binder_scopes.iter().any(|scope| scope.contains(name))
    }

    /// Handles the expression forms that INTRODUCE bindings, pushing the bound
    /// names for exactly the sub-expressions they scope over. Returns `true`
    /// when `expr` was fully handled here (the generic walk must not re-run).
    ///
    /// Returning `false` for a form that DOES bind is the failure direction, so
    /// the fallthrough is deliberately restricted to `syn`'s binder-free
    /// expression forms plus the block/loop wrappers, whose bindings all arrive
    /// through `visit_block_mut`.
    fn visit_binder_scope_expr(&mut self, expr: &mut Expr) -> bool {
        match expr {
            Expr::Closure(closure) => {
                let mut names = BTreeSet::new();
                let scopable = closure
                    .inputs
                    .iter()
                    .all(|input| collect_binder_names_from_pat(input, &mut names));
                for input in &mut closure.inputs {
                    syn::visit_mut::visit_pat_mut(self, input);
                }
                if !scopable {
                    self.unscopable_binder = true;
                    return true;
                }
                self.binder_scopes.push(names);
                self.visit_expr_mut(&mut closure.body);
                self.binder_scopes.pop();
                true
            }
            Expr::ForLoop(for_loop) => {
                // The iterated expression is evaluated OUTSIDE the pattern's
                // scope; only the body is under it.
                self.visit_expr_mut(&mut for_loop.expr);
                let mut names = BTreeSet::new();
                let scopable = collect_binder_names_from_pat(&for_loop.pat, &mut names);
                syn::visit_mut::visit_pat_mut(self, &mut for_loop.pat);
                if !scopable {
                    self.unscopable_binder = true;
                    return true;
                }
                self.binder_scopes.push(names);
                self.visit_block_mut(&mut for_loop.body);
                self.binder_scopes.pop();
                true
            }
            Expr::Match(expr_match) => {
                self.visit_expr_mut(&mut expr_match.expr);
                for arm in &mut expr_match.arms {
                    let mut names = BTreeSet::new();
                    let scopable = collect_binder_names_from_pat(&arm.pat, &mut names);
                    syn::visit_mut::visit_pat_mut(self, &mut arm.pat);
                    if !scopable {
                        self.unscopable_binder = true;
                        return true;
                    }
                    // An arm pattern scopes over the guard AND the body.
                    self.binder_scopes.push(names);
                    if let Some((_, guard)) = &mut arm.guard {
                        self.visit_expr_mut(guard);
                    }
                    self.visit_expr_mut(&mut arm.body);
                    self.binder_scopes.pop();
                }
                true
            }
            // `if let` / `while let` / a `let` chain: the pattern binds over a
            // region (the enclosing branch, the rest of the `&&` chain) that is
            // not visible from this node. Poison rather than guess.
            Expr::Let(_) => {
                self.unscopable_binder = true;
                true
            }
            _ => false,
        }
    }

    /// Replaces `expr` with the unresolvable marker once the poison is set, so
    /// the poison propagates outward to the whole clause.
    fn poison_if_unscopable(&self, expr: &mut Expr) {
        if self.unscopable_binder {
            *expr = unscopable_binder_marker();
        }
    }
}

/// Collects the identifiers `pat` binds, returning `false` when the pattern form
/// hides its binders. `syn::Pat` is `#[non_exhaustive]`, so the catch-all arm
/// covers macro/verbatim patterns AND every form a future `syn` may add: an
/// unseen binder is exactly the capture this machinery exists to prevent, so the
/// default answer is "cannot enumerate" and never "binds nothing".
fn collect_binder_names_from_pat(pat: &Pat, names: &mut BTreeSet<String>) -> bool {
    match pat {
        Pat::Ident(ident) => {
            names.insert(ident.ident.to_string());
            match &ident.subpat {
                Some((_, subpat)) => collect_binder_names_from_pat(subpat, names),
                None => true,
            }
        }
        Pat::Or(pat_or) => pat_or
            .cases
            .iter()
            .all(|case| collect_binder_names_from_pat(case, names)),
        Pat::Paren(paren) => collect_binder_names_from_pat(&paren.pat, names),
        Pat::Reference(reference) => collect_binder_names_from_pat(&reference.pat, names),
        Pat::Slice(slice) => slice
            .elems
            .iter()
            .all(|elem| collect_binder_names_from_pat(elem, names)),
        Pat::Struct(strukt) => strukt
            .fields
            .iter()
            .all(|field| collect_binder_names_from_pat(&field.pat, names)),
        Pat::Tuple(tuple) => tuple
            .elems
            .iter()
            .all(|elem| collect_binder_names_from_pat(elem, names)),
        Pat::TupleStruct(tuple_struct) => tuple_struct
            .elems
            .iter()
            .all(|elem| collect_binder_names_from_pat(elem, names)),
        Pat::Type(pat_type) => collect_binder_names_from_pat(&pat_type.pat, names),
        // Binder-free pattern forms, enumerated explicitly so the catch-all
        // below keeps meaning "unknown", not "harmless".
        Pat::Const(_)
        | Pat::Lit(_)
        | Pat::Path(_)
        | Pat::Range(_)
        | Pat::Rest(_)
        | Pat::Wild(_) => true,
        _ => false,
    }
}

/// The symbol spliced in place of a contract clause whose binder structure could
/// not be determined. It resolves to nothing at any call site, so the clause
/// fails closed in BOTH directions (an unprovable obligation to discharge, an
/// unencodable assumption to assume).
fn unscopable_binder_marker() -> Expr {
    syn::parse_quote!(__trust_vc_unscopable_binder)
}

impl VisitMut for ContractExprSubstituter<'_> {
    /// A block's `let`s bind over the REST of the block, so statements are
    /// walked in order: each initializer is substituted in the scope BEFORE its
    /// own binding, then the binding is pushed. The whole stack unwinds at the
    /// closing brace.
    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        let depth = self.binder_scopes.len();
        for stmt in &mut block.stmts {
            let syn::Stmt::Local(local) = stmt else {
                syn::visit_mut::visit_stmt_mut(self, stmt);
                continue;
            };
            if let Some(init) = &mut local.init {
                self.visit_expr_mut(&mut init.expr);
                if let Some((_, diverge)) = &mut init.diverge {
                    self.visit_expr_mut(diverge);
                }
            }
            let mut names = BTreeSet::new();
            let scopable = collect_binder_names_from_pat(&local.pat, &mut names);
            syn::visit_mut::visit_pat_mut(self, &mut local.pat);
            if !scopable {
                self.unscopable_binder = true;
                break;
            }
            self.binder_scopes.push(names);
        }
        self.binder_scopes.truncate(depth);
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // BINDER FORMS FIRST. None of them is a `Call`/`Unary`/`Path`, so the
        // three arms below are unreachable for them and the pre-existing
        // ordering is preserved byte-for-byte for every other shape.
        if self.visit_binder_scope_expr(expr) {
            self.poison_if_unscopable(expr);
            return;
        }
        // Two-state old() forms FIRST (they wrap a `Call`, which the bare
        // `Path` / deref-of-path arms below never match). Active only on the
        // helper-call contract path (`old_substitutions` non-empty): `old(P)`
        // etc. is replaced by the PRE-call value WITHOUT recursing into the
        // replacement (a rendered pre-value must never be re-substituted with
        // the post-call map — the directionality landmine). Any old() form we
        // cannot bind (non-`&mut`-scalar param, non-bare argument) is left
        // VERBATIM — never descended into — so it reaches the encoder as an
        // `old(..)` call and fails CLOSED there, instead of being silently
        // substituted with the wrong state.
        if !self.old_substitutions.is_empty() {
            match super::classify_old_call(expr) {
                super::OldCallShape::Param(name) => {
                    // A binder that RE-BINDS the param name owns this
                    // occurrence; `old(name)` then names the binder's variable,
                    // not the callee's pre-state, so leave it VERBATIM to fail
                    // closed at the encoder rather than splice a pre-value.
                    if !self.is_binder_bound(&name) {
                        if let Some(replacement) = self.old_substitutions.get(&name) {
                            *expr = replacement.clone();
                        }
                    }
                    return;
                }
                super::OldCallShape::BadArg => return,
                super::OldCallShape::NotOld => {}
            }
        }
        if let Expr::Unary(unary) = expr {
            if matches!(unary.op, syn::UnOp::Deref(_)) {
                if let Expr::Path(path) = unary.expr.as_ref() {
                    if path.qself.is_none() && path.path.segments.len() == 1 {
                        if let Some(segment) = path.path.segments.first() {
                            let name = segment.ident.to_string();
                            if !self.is_binder_bound(&name)
                                && (self.erased_shared_ref_params.contains(&name)
                                    || self.erased_mut_ref_value_params.contains(&name))
                            {
                                if let Some(replacement) = self.substitutions.get(&name) {
                                    *expr = replacement.clone();
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }
        let Expr::Path(path) = expr else {
            syn::visit_mut::visit_expr_mut(self, expr);
            self.poison_if_unscopable(expr);
            return;
        };
        if path.qself.is_none() && path.path.segments.len() == 1 {
            if let Some(segment) = path.path.segments.first() {
                let name = segment.ident.to_string();
                // SOUNDNESS: a name RE-BOUND by an enclosing binder inside this
                // clause is that binder's variable, not the callee's parameter.
                if !self.is_binder_bound(&name) {
                    if let Some(replacement) = self.substitutions.get(&name) {
                        *expr = replacement.clone();
                        return;
                    }
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
        self.poison_if_unscopable(expr);
    }
}

fn bound_idents_from_pat(pat: &Pat) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_bound_idents_from_pat(pat, &mut names);
    names
}

fn collect_bound_idents_from_pat(pat: &Pat, names: &mut BTreeSet<String>) {
    match pat {
        Pat::Ident(ident) => {
            names.insert(ident.ident.to_string());
            if let Some((_, subpat)) = &ident.subpat {
                collect_bound_idents_from_pat(subpat, names);
            }
        }
        Pat::Or(pat_or) => {
            for case in &pat_or.cases {
                collect_bound_idents_from_pat(case, names);
            }
        }
        Pat::Paren(paren) => collect_bound_idents_from_pat(&paren.pat, names),
        Pat::Reference(reference) => collect_bound_idents_from_pat(&reference.pat, names),
        Pat::Slice(slice) => {
            for elem in &slice.elems {
                collect_bound_idents_from_pat(elem, names);
            }
        }
        Pat::Struct(strukt) => {
            for field in &strukt.fields {
                collect_bound_idents_from_pat(&field.pat, names);
            }
        }
        Pat::Tuple(tuple) => {
            for elem in &tuple.elems {
                collect_bound_idents_from_pat(elem, names);
            }
        }
        Pat::TupleStruct(tuple_struct) => {
            for elem in &tuple_struct.elems {
                collect_bound_idents_from_pat(elem, names);
            }
        }
        Pat::Type(pat_type) => collect_bound_idents_from_pat(&pat_type.pat, names),
        _ => {}
    }
}

/// The "this arm matches" condition of a `match` arm pattern, evaluated against
/// the scrutinee's scoped value `scrutinee` (and optional datatype type). Used to
/// branch-guard the obligations emitted inside the arm body (P0-B: assume! /
/// call-`ensures` / arithmetic safety must hold only when the arm is selected,
/// not leak unconditionally into sibling arms or post-match straight-line code).
enum ArmMatchCond {
    /// Irrefutable pattern (`_`, a plain binding) — matches every scrutinee value.
    Always,
    /// Refutable pattern with a computable condition over the scrutinee (a literal
    /// `scrutinee == lit`, or a datatype variant test `scrutinee.is_V()`).
    Refutable(String),
    /// Pattern whose match condition cannot be soundly rendered (an opaque shape,
    /// or a variant pattern with no resolved scrutinee type).
    Unknown,
}

fn arm_pattern_match_condition(
    pat: &Pat,
    scrutinee: &str,
    scrutinee_ty: Option<&TrustVcType>,
) -> ArmMatchCond {
    match pat {
        Pat::Wild(_) => ArmMatchCond::Always,
        Pat::Rest(_) => ArmMatchCond::Always,
        Pat::Ident(ident) => {
            // `x @ subpat` — match condition is the subpattern's.
            if let Some((_, subpat)) = &ident.subpat {
                return arm_pattern_match_condition(subpat, scrutinee, scrutinee_ty);
            }
            // A bare binding `x` is irrefutable UNLESS the scrutinee is an enum and
            // `x` names a zero-field variant (e.g. `None` parsed as an ident).
            let name = ident.ident.to_string();
            if let Some(ty) = scrutinee_ty {
                if datatype_variant(ty, &name).is_some() {
                    return ArmMatchCond::Refutable(variant_match_condition(scrutinee, ty, &name));
                }
            }
            // NOT a resolved variant. A bare ident that Rust resolves to an ITEM
            // — a `const`, an associated const, a unit struct — is REFUTABLE:
            // the arm matches only scrutinees equal to that item's value.
            // Answering `Always` here does not merely over-approximate THIS
            // arm; it makes every later arm's prior-negation `!(true)`, i.e.
            // FALSE, so their obligations are vacuously discharged. That was a
            // cardinal false verify:
            //
            //     const K: u64 = 5;
            //     match n { K => {} _ => { assert!(false); } }   // VERIFIED
            //
            // while the identical `5 => {}` refutes. `const_pattern_desugar`
            // now folds a declared const pattern to its literal before this
            // runs, so the shapes reaching here are (a) the reserved marker for
            // a declared const whose value could not be folded, and (b) a const
            // this file does not declare (e.g. `use other::K`), which the
            // desugar's file-local scan cannot see. Both fail closed:
            // `Unknown` sets `prior_unrenderable`, leaving later arms UNGUARDED
            // — the sound direction.
            //
            // A snake_case ident with no marker prefix stays a binding. That is
            // the overwhelmingly common case and Rust's own convention: an
            // uppercase-initial BINDING is warned on (`non_snake_case`) and
            // `E0530` forbids one that shadows a constant.
            if crate::const_pattern_desugar::unmodeled_const_pat_name(&name).is_some()
                || name.starts_with(|c: char| c.is_uppercase())
            {
                return ArmMatchCond::Unknown;
            }
            ArmMatchCond::Always
        }
        Pat::Lit(lit) => {
            let lit_str = lit.lit.to_token_stream().to_string();
            ArmMatchCond::Refutable(format!("({scrutinee}) == ({lit_str})"))
        }
        Pat::Or(or) => {
            let mut parts = Vec::new();
            for case in &or.cases {
                match arm_pattern_match_condition(case, scrutinee, scrutinee_ty) {
                    ArmMatchCond::Always => return ArmMatchCond::Always,
                    ArmMatchCond::Refutable(c) => parts.push(c),
                    ArmMatchCond::Unknown => return ArmMatchCond::Unknown,
                }
            }
            if parts.is_empty() {
                ArmMatchCond::Unknown
            } else {
                ArmMatchCond::Refutable(format!("({})", parts.join(" || ")))
            }
        }
        Pat::Paren(paren) => arm_pattern_match_condition(&paren.pat, scrutinee, scrutinee_ty),
        Pat::Type(pat_type) => arm_pattern_match_condition(&pat_type.pat, scrutinee, scrutinee_ty),
        Pat::Reference(reference) => {
            arm_pattern_match_condition(&reference.pat, scrutinee, scrutinee_ty)
        }
        Pat::TupleStruct(_) | Pat::Path(_) | Pat::Struct(_) => match scrutinee_ty {
            Some(ty) => match pattern_match_condition_for_scoped_value(pat, scrutinee, ty) {
                Some(c) if c == "true" => ArmMatchCond::Always,
                Some(c) => ArmMatchCond::Refutable(c),
                None => ArmMatchCond::Unknown,
            },
            None => ArmMatchCond::Unknown,
        },
        _ => ArmMatchCond::Unknown,
    }
}

/// A tuple-struct/struct element or field pattern that does NOT refine which
/// scrutinees the arm matches: a plain binding (`v`), a wildcard (`_`), or a
/// rest (`..`). Anything else — a literal, range, nested constructor, path/const,
/// or an `@`-subpattern — is a refinement that the scoped-value match condition
/// cannot model, so the caller must fail closed rather than drop it.
fn pattern_elem_is_plain_binding(pat: &Pat) -> bool {
    match pat {
        Pat::Ident(ident) => ident.subpat.is_none(),
        Pat::Wild(_) | Pat::Rest(_) => true,
        Pat::Paren(inner) => pattern_elem_is_plain_binding(&inner.pat),
        _ => false,
    }
}

/// TRUE when `pat` matches EVERY value of its type with no refinement at all, so
/// its match condition is unconditionally `"true"` — a snake_case binder without
/// an `@`-subpattern, or a wildcard, looking through `(..)` and `: T` wrappers.
///
/// An UPPERCASE-initial bare ident is deliberately NOT counted: Rust resolves it
/// to a unit variant or a `const`, both of which refine the match (see the
/// `Pat::Ident` arm of [`pattern_match_condition_for_scoped_value`]).
fn pattern_is_irrefutable_binder(pat: &Pat) -> bool {
    match pat {
        Pat::Wild(_) => true,
        Pat::Ident(ident) => {
            ident.subpat.is_none()
                && !ident
                    .ident
                    .to_string()
                    .starts_with(|c: char| c.is_uppercase())
        }
        Pat::Paren(paren) => pattern_is_irrefutable_binder(&paren.pat),
        Pat::Type(pat_type) => pattern_is_irrefutable_binder(&pat_type.pat),
        _ => false,
    }
}

fn pattern_match_condition_for_scoped_value(
    pat: &Pat,
    base: &str,
    base_ty: &TrustVcType,
) -> Option<String> {
    match pat {
        Pat::TupleStruct(tuple_struct) => {
            let variant_name = tuple_struct
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string())?;
            // The variant tester alone is a SOUND arm condition ONLY when every
            // element is a plain binding/wildcard/rest. A nested REFINEMENT
            // (literal, range, nested constructor, @-subpattern, const/path)
            // further constrains which scrutinees the arm matches; lowering to
            // just the tester WIDENS the condition and, via prior_negations,
            // vacuously discharges a later same-variant arm's assert — a
            // false-verify (e.g. `Just(0)` then `Just(v) => assert!(v==0)`).
            // Fail closed (unguardable) so the arm's asserts fire unguarded,
            // which is the sound counterexample direction.
            if !tuple_struct.elems.iter().all(pattern_elem_is_plain_binding) {
                return None;
            }
            Some(variant_match_condition(base, base_ty, &variant_name))
        }
        Pat::Path(path) => {
            let variant_name = path.path.segments.last()?.ident.to_string();
            // A path pattern is a unit VARIANT only when the scrutinee's
            // datatype actually has a zero-field variant by that name. The other
            // things a path pattern can denote — a `const` or an
            // associated-const (`k::K`, `Self::LIMIT`) — are VALUE refinements
            // that no variant tester expresses, and `({base}).is_K()` is not
            // merely useless there but a claim about a variant that does not
            // exist. Fail closed instead. (Without this gate the const case
            // survived only because the encoder happened to reject the bogus
            // tester downstream — an accident, not a guarantee.)
            match datatype_variant(base_ty, &variant_name) {
                Some(variant) if variant.fields.is_empty() => {
                    Some(variant_match_condition(base, base_ty, &variant_name))
                }
                _ => None,
            }
        }
        Pat::Struct(struct_pat) => {
            let variant_name = struct_pat
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string())?;
            // Same refinement-drop hazard as the tuple-struct arm above: a
            // field-pattern refinement (`S { f: 0 }`) must not be dropped.
            if !struct_pat
                .fields
                .iter()
                .all(|field| pattern_elem_is_plain_binding(&field.pat))
            {
                return None;
            }
            if is_refutable_datatype_variant(base_ty, &variant_name) {
                Some(variant_match_condition(base, base_ty, &variant_name))
            } else {
                Some("true".to_string())
            }
        }
        Pat::Wild(_) => Some("true".to_string()),
        Pat::Ident(ident) => {
            // `x @ SUBPAT` carries a refinement the bare binder cannot express;
            // answering `true` would widen the condition to always-match — the
            // same drop the tuple-struct/struct arms above guard against.
            if ident.subpat.is_some() {
                return None;
            }
            let name = ident.ident.to_string();
            if !name.starts_with(|c: char| c.is_uppercase()) {
                return Some("true".to_string());
            }
            // An UPPERCASE-initial bare ident is not a binding: Rust resolves it
            // to a zero-field enum VARIANT when the scrutinee's datatype has one
            // by that name, and otherwise to a `const`/associated-const PATTERN.
            // Both are REFUTABLE, so `true` drops a real value refinement. Same
            // ruling, and same reasoning, as
            // `ir_lowering::match_lowering::lower_pattern` — which fails closed
            // on the const case because a snake_case binding is the only
            // idiomatic spelling of a genuine binder.
            match datatype_variant(base_ty, &name) {
                Some(variant) if variant.fields.is_empty() => {
                    Some(variant_match_condition(base, base_ty, &name))
                }
                _ => None,
            }
        }
        Pat::Type(pat_type) => {
            pattern_match_condition_for_scoped_value(&pat_type.pat, base, base_ty)
        }
        Pat::Paren(paren) => pattern_match_condition_for_scoped_value(&paren.pat, base, base_ty),
        _ => None,
    }
}

fn pattern_bindings_for_scoped_value(
    pat: &Pat,
    base: &str,
    base_ty: &TrustVcType,
) -> Option<Vec<(String, String)>> {
    let mut bindings = Vec::new();
    collect_pattern_bindings(pat, base, base_ty, &mut bindings)?;
    Some(
        bindings
            .into_iter()
            .map(|(name, value, _ty)| (name, value))
            .collect(),
    )
}

/// TRUE when `pat` can serve as a MERGEABLE or-pattern disjunct: its top level
/// is a constructor / struct / path / bare-ident / wildcard pattern whose
/// sub-patterns are all IRREFUTABLE binders (`x`, `_`, `..`). For such a "flat"
/// disjunct the variant tester rendered by
/// `pattern_match_condition_for_scoped_value` is EXACTLY "this disjunct
/// matches", which the first-match merge chain in the `Pat::Or` arm of
/// [`collect_pattern_bindings`] relies on. A disjunct with a nested REFUTABLE
/// sub-pattern (`A(B(x))`, `Some(1)`) would make that tester an
/// over-approximation, and a merged binder built over it could resolve to the
/// WRONG disjunct's value — so the merge fails closed on any non-flat disjunct.
fn or_disjunct_is_flat(pat: &Pat) -> bool {
    fn is_irrefutable_binder(pat: &Pat) -> bool {
        match pat {
            Pat::Ident(ident) => ident.subpat.is_none(),
            Pat::Wild(_) | Pat::Rest(_) => true,
            Pat::Paren(paren) => is_irrefutable_binder(&paren.pat),
            Pat::Type(pat_type) => is_irrefutable_binder(&pat_type.pat),
            _ => false,
        }
    }
    match pat {
        Pat::TupleStruct(tuple_struct) => tuple_struct.elems.iter().all(is_irrefutable_binder),
        Pat::Struct(struct_pat) => struct_pat
            .fields
            .iter()
            .all(|field| is_irrefutable_binder(&field.pat)),
        Pat::Path(_) | Pat::Wild(_) => true,
        Pat::Ident(ident) => ident.subpat.is_none(),
        Pat::Paren(paren) => or_disjunct_is_flat(&paren.pat),
        Pat::Type(pat_type) => or_disjunct_is_flat(&pat_type.pat),
        _ => false,
    }
}

fn collect_pattern_bindings(
    pat: &Pat,
    base: &str,
    base_ty: &TrustVcType,
    bindings: &mut Vec<(String, String, TrustVcType)>,
) -> Option<()> {
    match pat {
        Pat::Ident(ident)
            if ident.by_ref.is_none() && ident.mutability.is_none() && ident.subpat.is_none() =>
        {
            bindings.push((ident.ident.to_string(), base.to_string(), base_ty.clone()));
            Some(())
        }
        Pat::Ident(ident)
            if ident.by_ref.is_none() && ident.mutability.is_none() && ident.subpat.is_some() =>
        {
            // `n @ subpat` — an `@`-binding names the ENTIRE matched value, so `n`
            // binds to the base and the subpattern's own bindings project from the
            // SAME base. (The arm's "matches" condition already descends into the
            // subpattern via `arm_pattern_match_condition`, so this stays sound.)
            bindings.push((ident.ident.to_string(), base.to_string(), base_ty.clone()));
            let (_, subpat) = ident.subpat.as_ref()?;
            collect_pattern_bindings(subpat, base, base_ty, bindings)
        }
        Pat::Wild(_) => Some(()),
        // Or-pattern `P1 | P2 | …`: every disjunct binds the SAME names (a Rust
        // rule), but each disjunct may project a name from a DIFFERENT variant
        // of the scrutinee. Each name merges into a FIRST-MATCH `if`/`else`
        // chain over the disjuncts' own match conditions — exactly Rust's
        // left-to-right or-pattern selection — so the merged binder can never
        // resolve to the wrong disjunct's value. The LAST disjunct is the
        // `else` branch: every disjunct is flat, so the per-disjunct testers
        // are exact, and under the arm's selection guard reaching the `else`
        // means no earlier disjunct matched — hence the last one did. Outside
        // that guard (an unguardable arm) a mis-applied selector is an
        // UNCONSTRAINED value, which fails closed: bare `assume!`/call-ensures
        // are dropped in unguardable arms, so it can only feed ASSERT-side
        // obligations.
        //
        // Fails closed (`None`) when: any disjunct is non-flat (see
        // `or_disjunct_is_flat`), a disjunct's bindings cannot be projected,
        // the disjuncts disagree on the bound-name set, a name's projected
        // TYPE differs across disjuncts (incompatible payloads cannot share
        // one merged binder), or a needed per-disjunct match condition cannot
        // be rendered.
        Pat::Or(or_pat) => {
            if or_pat.cases.is_empty() || !or_pat.cases.iter().all(or_disjunct_is_flat) {
                return None;
            }
            let mut per_disjunct: Vec<Vec<(String, String, TrustVcType)>> =
                Vec::with_capacity(or_pat.cases.len());
            for case in &or_pat.cases {
                let mut case_bindings = Vec::new();
                collect_pattern_bindings(case, base, base_ty, &mut case_bindings)?;
                // A name bound twice within one disjunct is malformed; and every
                // disjunct must bind exactly as many names as the first (with
                // the per-name lookup below, this pins equal name SETS).
                for (index, (name, _, _)) in case_bindings.iter().enumerate() {
                    if case_bindings[..index]
                        .iter()
                        .any(|(seen, _, _)| seen == name)
                    {
                        return None;
                    }
                }
                if let Some(first) = per_disjunct.first() {
                    if case_bindings.len() != first.len() {
                        return None;
                    }
                }
                per_disjunct.push(case_bindings);
            }
            let conditions: Vec<Option<String>> = or_pat
                .cases
                .iter()
                .map(|case| pattern_match_condition_for_scoped_value(case, base, base_ty))
                .collect();
            let (first, rest) = per_disjunct.split_first()?;
            for (name, first_value, first_ty) in first {
                let mut values = vec![first_value.clone()];
                for case_bindings in rest {
                    let (_, value, ty) = case_bindings
                        .iter()
                        .find(|(case_name, _, _)| case_name == name)?;
                    if ty != first_ty {
                        return None;
                    }
                    values.push(value.clone());
                }
                let merged_value = if values.iter().all(|value| value == &values[0]) {
                    // Every disjunct projects the name identically (e.g. the
                    // same variant repeated, or a single-disjunct `| P` arm):
                    // no chain needed.
                    values[0].clone()
                } else {
                    // Right-fold the first-match chain: the last disjunct's
                    // value seeds the `else`, every earlier disjunct needs a
                    // renderable exact condition.
                    let mut chain = values.pop()?;
                    for (value, condition) in values.iter().zip(&conditions).rev() {
                        let condition = condition.as_ref()?;
                        chain = format!("if {condition} {{ {value} }} else {{ {chain} }}");
                    }
                    chain
                };
                bindings.push((name.clone(), merged_value, first_ty.clone()));
            }
            Some(())
        }
        Pat::TupleStruct(tuple_struct) => {
            let variant_name = tuple_struct
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string())?;
            let variant = datatype_variant(base_ty, &variant_name)?;
            // For a single-variant tuple struct, project fields by direct tuple
            // field access `(base).i` rather than the `get_V_i()` selector. Field
            // access resolves the CONCRETE field type, which is crucial for a
            // generic struct `S1<A, B>` instantiated as `S1<i32, i32>`: `(x).0`
            // is `i32`, whereas the selector's return type stays the type
            // parameter `A` whose uninterpreted sort fails overflow-assumption
            // encoding. A multi-variant enum keeps the variant selector (a field
            // is only valid under that variant's tester guard). Mirrors the
            // `Pat::Struct` arm's `use_field_access` handling.
            let use_field_access = is_single_variant_struct(base_ty, &variant_name);
            for (field_index, subpat) in tuple_struct_pattern_indices(&tuple_struct.elems, variant)?
            {
                let (field_name, field_ty) = variant.fields.get(field_index)?;
                let field_expr = if use_field_access {
                    scoped_field_access(base, field_name)
                } else {
                    enum_variant_selector(base, &variant_name, field_name)
                };
                collect_pattern_bindings(subpat, &field_expr, field_ty, bindings)?;
            }
            Some(())
        }
        Pat::Struct(struct_pat) => {
            let variant_name = struct_pat
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string())?;
            let variant = datatype_variant(base_ty, &variant_name)?;
            let use_field_access = is_single_variant_struct(base_ty, &variant_name);
            for field in &struct_pat.fields {
                let syn::Member::Named(member) = &field.member else {
                    return None;
                };
                let field_name = member.to_string();
                let (_, field_ty) = datatype_field(variant, &field_name)?;
                let field_expr = if use_field_access {
                    scoped_field_access(base, &field_name)
                } else {
                    enum_variant_selector(base, &variant_name, &field_name)
                };
                collect_pattern_bindings(&field.pat, &field_expr, field_ty, bindings)?;
            }
            Some(())
        }
        Pat::Type(pat_type) => collect_pattern_bindings(&pat_type.pat, base, base_ty, bindings),
        Pat::Paren(paren) => collect_pattern_bindings(&paren.pat, base, base_ty, bindings),
        _ => None,
    }
}

fn tuple_struct_pattern_indices<'a>(
    elems: &'a Punctuated<Pat, Token![,]>,
    variant: &DatatypeVariant,
) -> Option<Vec<(usize, &'a Pat)>> {
    let rest_index = elems.iter().position(|pat| matches!(pat, Pat::Rest(_)));
    let field_count = variant.fields.len();
    let explicit_count = elems
        .iter()
        .filter(|pat| !matches!(pat, Pat::Rest(_)))
        .count();
    if rest_index.is_none() && explicit_count != field_count {
        return None;
    }
    if rest_index.is_some() && explicit_count > field_count {
        return None;
    }

    let mut result = Vec::with_capacity(explicit_count);
    let mut front_index = 0usize;
    let mut back_index = match rest_index {
        Some(rest) => field_count.checked_sub(elems.len().saturating_sub(rest + 1))?,
        None => field_count,
    };
    for (index, pat) in elems.iter().enumerate() {
        if matches!(pat, Pat::Rest(_)) {
            continue;
        }
        let field_index = if rest_index.is_some_and(|rest| index > rest) {
            let current = back_index;
            back_index += 1;
            current
        } else {
            let current = front_index;
            front_index += 1;
            current
        };
        result.push((field_index, pat));
    }
    Some(result)
}

fn datatype_variant<'a>(ty: &'a TrustVcType, variant_name: &str) -> Option<&'a DatatypeVariant> {
    let TrustVcType::Datatype { variants, .. } = ty else {
        return None;
    };
    variants.iter().find(|variant| variant.name == variant_name)
}

fn datatype_field<'a>(
    variant: &'a DatatypeVariant,
    field_name: &str,
) -> Option<(usize, &'a TrustVcType)> {
    variant
        .fields
        .iter()
        .enumerate()
        .find(|(_, (name, _))| name == field_name)
        .map(|(index, (_, ty))| (index, ty))
}

fn is_single_variant_struct(ty: &TrustVcType, variant_name: &str) -> bool {
    matches!(
        ty,
        TrustVcType::Datatype { name, variants }
            if name == variant_name
                && matches!(variants.as_slice(), [variant] if variant.name == variant_name)
    )
}

fn is_refutable_datatype_variant(ty: &TrustVcType, variant_name: &str) -> bool {
    matches!(
        ty,
        TrustVcType::Datatype { variants, .. }
            if variants.len() > 1 && variants.iter().any(|variant| variant.name == variant_name)
    )
}

fn variant_match_condition(base: &str, base_ty: &TrustVcType, variant_name: &str) -> String {
    if let TrustVcType::Datatype { name, .. } = base_ty {
        if name.starts_with("Option<") {
            return match variant_name {
                "Some" => format!("({base}).is_some()"),
                "None" => format!("({base}).is_none()"),
                _ => format!("({base}).is_{variant_name}()"),
            };
        }
    }
    format!("({base}).is_{variant_name}()")
}

fn enum_variant_selector(base: &str, variant_name: &str, field_name: &str) -> String {
    format!("({base}).get_{variant_name}_{field_name}()")
}

/// Normalizes an inferred scoped struct/enum type-name string to the bare base
/// name used to register user types. Strips any turbofish/generic-argument
/// suffix (`Pair :: < bool , bool >` -> `Pair`), surrounding whitespace, a
/// trailing turbofish `::`, and any module-path prefix (`m::Pair` -> `Pair`).
fn scoped_struct_type_base_name(type_name: &str) -> String {
    let before_generics = type_name.split('<').next().unwrap_or(type_name);
    let without_whitespace: String = before_generics
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    without_whitespace
        .trim_end_matches("::")
        .rsplit("::")
        .next()
        .unwrap_or(&without_whitespace)
        .to_string()
}

fn scoped_field_access(base: &str, field_name: &str) -> String {
    format!("({base}).{field_name}")
}

fn is_assignment_binop(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::AddAssign(_)
            | BinOp::SubAssign(_)
            | BinOp::MulAssign(_)
            | BinOp::DivAssign(_)
            | BinOp::RemAssign(_)
            | BinOp::BitXorAssign(_)
            | BinOp::BitAndAssign(_)
            | BinOp::BitOrAssign(_)
            | BinOp::ShlAssign(_)
            | BinOp::ShrAssign(_)
    )
}

/// Collect the OUTERMOST value-position array/slice/map index ACCESS expressions
/// reachable in `expr`, looking through transparent value wrappers
/// (paren/group/unary/cast/shared-reference/field), the operands of a
/// non-assignment binary operator, and every UNCONDITIONALLY-evaluated
/// aggregate / call sub-position — tuple / array-literal / array-repeat /
/// struct-literal elements, and call / method-call arguments (plus the
/// callee/receiver). Used by
/// [`BodyExtractor::emit_exec_index_bounds_checks_in_expr`] to decide which
/// `a[i]` accesses need an exec index-bounds obligation (#81).
///
/// Recursing into the aggregate / call sub-positions closes the narrower
/// residual of #81: an index access nested in a tuple / array / struct literal
/// or a call/method argument (e.g. `let _ = (ar[i], 0);`, `f(ar[i]);`,
/// `[ar[i]; 1]`, `S { x: ar[i] }`) is evaluated — and can panic OOB — just like
/// a top-level access, yet the original collector only saw the TOP-LEVEL value
/// position and silently `Verified` it. Each such sub-position is read in
/// straight-line order at this program point, so its bound is sound to pin here;
/// the per-access `index_receiver_is_modelable` + side-effect gates in the caller
/// keep an un-modelable receiver or a side-effecting index from perturbing the
/// (independently fail-closed) outcome.
///
/// Only the OUTERMOST index in each wrapper chain is collected: resolving
/// `a[a[0]]` (or `a[i][j]`) already fires the bound for every index nested in its
/// receiver/index position, so re-collecting the inner access would be
/// redundant. Assignment binary operators (`+= … <<=`) are NOT descended (the
/// write SITE handles their bound + element safety), and CONDITIONALLY-evaluated
/// or opaque value producers (closures / blocks / `if` / `match` / loops /
/// macros / short-circuit branches) are NOT descended into — an access there is
/// not unconditionally reached at this program point, so pinning its bound in the
/// straight-line entry context would be a spurious counterexample (the loop /
/// branch encoding owns those).
fn collect_value_position_index_exprs<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
    match expr {
        Expr::Index(_) => out.push(expr),
        Expr::Paren(paren) => collect_value_position_index_exprs(&paren.expr, out),
        Expr::Group(group) => collect_value_position_index_exprs(&group.expr, out),
        Expr::Unary(unary) => collect_value_position_index_exprs(&unary.expr, out),
        Expr::Cast(cast) => collect_value_position_index_exprs(&cast.expr, out),
        Expr::Reference(reference) if reference.mutability.is_none() => {
            collect_value_position_index_exprs(&reference.expr, out)
        }
        Expr::Field(field) => collect_value_position_index_exprs(&field.base, out),
        Expr::Binary(binary) if !is_assignment_binop(&binary.op) => {
            collect_value_position_index_exprs(&binary.left, out);
            collect_value_position_index_exprs(&binary.right, out);
        }
        Expr::Tuple(tuple) => {
            for elem in &tuple.elems {
                collect_value_position_index_exprs(elem, out);
            }
        }
        Expr::Array(array) => {
            for elem in &array.elems {
                collect_value_position_index_exprs(elem, out);
            }
        }
        Expr::Repeat(repeat) => {
            collect_value_position_index_exprs(&repeat.expr, out);
            collect_value_position_index_exprs(&repeat.len, out);
        }
        // A `Range` / `RangeInclusive` value eagerly evaluates every present bound at
        // construction, so an OOB index in either bound (`0..arr[i]`) is an
        // unconditionally-evaluated value-position access — descend into both bounds
        // (sibling of the arith collector's `Expr::Range` arm).
        Expr::Range(range) => {
            if let Some(start) = &range.start {
                collect_value_position_index_exprs(start, out);
            }
            if let Some(end) = &range.end {
                collect_value_position_index_exprs(end, out);
            }
        }
        Expr::Struct(struct_expr) => {
            for field in &struct_expr.fields {
                collect_value_position_index_exprs(&field.expr, out);
            }
            if let Some(rest) = &struct_expr.rest {
                collect_value_position_index_exprs(rest, out);
            }
        }
        Expr::Call(call) => {
            collect_value_position_index_exprs(&call.func, out);
            for arg in &call.args {
                collect_value_position_index_exprs(arg, out);
            }
        }
        Expr::MethodCall(method_call) => {
            collect_value_position_index_exprs(&method_call.receiver, out);
            for arg in &method_call.args {
                collect_value_position_index_exprs(arg, out);
            }
        }
        _ => {}
    }
}

/// A single short-circuit reachability guard: the LEFT operand of an enclosing
/// `&& / ||` under which a collected arithmetic site is evaluated. `negate` is set
/// for `||` (whose right operand runs when the left is FALSE), so the rendered path
/// condition is `cond` for `&&` and `!(cond)` for `||`.
#[derive(Clone, Copy)]
struct ArithGuard<'a> {
    cond: &'a Expr,
    negate: bool,
}

/// A value-position arithmetic / shift site collected by
/// [`collect_value_position_arith_exprs`], paired with the stack of enclosing
/// short-circuit reachability guards (innermost last) under which it is evaluated.
struct ArithSite<'a> {
    site: &'a Expr,
    guards: Vec<ArithGuard<'a>>,
}

/// SOUNDNESS-CRITICAL (exec scalar arithmetic panic-freedom) — the
/// arithmetic-safety sibling of [`collect_value_position_index_exprs`].
///
/// Collect every UNCONDITIONALLY-evaluated value-position checked-arithmetic
/// (`+ - * / %`) or bit-shift (`<< >>`) expression reachable in `expr`, looking
/// through the same transparent value wrappers (paren / group / unary / cast /
/// shared-reference / field), the operands of comparison / bitwise binaries, BOTH
/// operands of a short-circuit `&& / ||` (the right one reachability-guarded, see
/// below), and every aggregate / call
/// sub-position — tuple / array-literal / array-repeat / struct-literal elements,
/// call / method-call arguments (plus the callee / receiver), and the
/// receiver / index of an `a[i]` access. Used by
/// [`BodyExtractor::emit_exec_arith_safety_checks_in_expr`] to decide which
/// arithmetic sites need an exec arithmetic-safety obligation (the #82 analog of
/// the index-bounds collector, closing the discarded / nested scalar-arithmetic
/// false-`Verified` surface).
///
/// Only the OUTERMOST arithmetic / shift node in each chain is collected (it is
/// pushed and NOT descended into): the caller's reflexive `(node) == (node)`
/// obligation re-lowers the whole node, so the encoder fires the overflow /
/// divide-by-zero / shift-bounds precheck for THIS operator and recursively for
/// every arithmetic / index nested in its operands — re-collecting an inner term
/// would be redundant (mirrors the OUTERMOST-only `Expr::Index` rule).
///
/// The RIGHT operand of a short-circuit `&& / ||` IS descended into, but its
/// arithmetic is collected REACHABILITY-GUARDED by the left operand: for `&&` the
/// right runs exactly when the left is TRUE, for `||` exactly when the left is
/// FALSE. Each collected [`ArithSite`] therefore carries the stack of enclosing
/// short-circuit guards ([`ArithGuard`]), which the emitter renders into path
/// conditions so the encoder's `encode_with_overflow_guard` weakens the right
/// operand's overflow / divide-by-zero / shift-bounds precheck to fire ONLY on the
/// path that reaches it. This is SOUNDNESS-CRITICAL and direction-correct: the SAFE
/// `b != 0 && a / b > 0` (right's `a / b` checked under `b != 0`) still verifies,
/// while the UNSAFE `b == 0 && a / b > 0` / `b != 0 || a / b > 0` (right's `a / b`
/// checked under `b == 0`) is a divide-by-zero counterexample — neither is silently
/// dropped. (The earlier blanket left-only descent dropped the right operand
/// outright, false-`Verified`ing every panicking short-circuit right operand; the
/// "short-circuit encoding owns those" rationale was wrong — nothing re-emitted it.)
///
/// CONDITIONALLY-evaluated or opaque value producers (closures / blocks / `if` /
/// `match` / loops / macros) are NOT descended into here: arithmetic there is not a
/// straight-line value-position site at this program point (the loop / branch /
/// closure encoding owns those). Assignment binary operators (`+= … <<=`) are NOT
/// descended (their write site emits the compound element-safety obligation
/// directly).
///
/// `guards` is the running stack of enclosing short-circuit reachability guards
/// (innermost last); it is mutated in place (push before descending a guarded
/// right operand, pop after) and SNAPSHOTTED into each collected site.
fn collect_value_position_arith_exprs<'a>(
    expr: &'a Expr,
    guards: &mut Vec<ArithGuard<'a>>,
    out: &mut Vec<ArithSite<'a>>,
) {
    match expr {
        Expr::Binary(binary)
            if matches!(
                binary.op,
                BinOp::Add(_)
                    | BinOp::Sub(_)
                    | BinOp::Mul(_)
                    | BinOp::Div(_)
                    | BinOp::Rem(_)
                    | BinOp::Shl(_)
                    | BinOp::Shr(_)
            ) =>
        {
            out.push(ArithSite {
                site: expr,
                guards: guards.clone(),
            });
        }
        Expr::Binary(binary) if matches!(binary.op, BinOp::And(_) | BinOp::Or(_)) => {
            // The LEFT operand is evaluated unconditionally at this point.
            collect_value_position_arith_exprs(&binary.left, guards, out);
            // The RIGHT operand runs iff the short-circuit does not short out: for
            // `&&` when LEFT is true, for `||` when LEFT is false. Guard any
            // arithmetic in RIGHT by the left-operand condition (negated for `||`),
            // exactly mirroring the `if cond { right }` / `if !cond { right }` path
            // condition the branch handler threads.
            let negate = matches!(binary.op, BinOp::Or(_));
            guards.push(ArithGuard {
                cond: &binary.left,
                negate,
            });
            collect_value_position_arith_exprs(&binary.right, guards, out);
            guards.pop();
        }
        Expr::Binary(binary) if !is_assignment_binop(&binary.op) => {
            collect_value_position_arith_exprs(&binary.left, guards, out);
            collect_value_position_arith_exprs(&binary.right, guards, out);
        }
        Expr::Paren(paren) => collect_value_position_arith_exprs(&paren.expr, guards, out),
        Expr::Group(group) => collect_value_position_arith_exprs(&group.expr, guards, out),
        // SOUNDNESS-CRITICAL (exec negation panic-freedom): a unary negation
        // `-x` of a fixed-width signed operand is a checked-arithmetic site
        // (`-x` overflows at `x == TYPE::MIN`). Push the OUTERMOST `-` node and
        // do NOT descend — the caller's reflexive `(-x) == (-x)` obligation
        // re-lowers the whole node, firing the negation-overflow precheck for
        // THIS `-` and recursively for any arithmetic/index nested in the
        // operand (mirrors the OUTERMOST-only Binary rule). This closes the
        // discarded-negation false `Verified` at every value position (tuple /
        // array / struct-literal element, call argument, match arm, ...).
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
            out.push(ArithSite {
                site: expr,
                guards: guards.clone(),
            });
        }
        Expr::Unary(unary) => collect_value_position_arith_exprs(&unary.expr, guards, out),
        Expr::Cast(cast) => collect_value_position_arith_exprs(&cast.expr, guards, out),
        Expr::Reference(reference) if reference.mutability.is_none() => {
            collect_value_position_arith_exprs(&reference.expr, guards, out)
        }
        Expr::Field(field) => collect_value_position_arith_exprs(&field.base, guards, out),
        Expr::Index(index) => {
            collect_value_position_arith_exprs(&index.expr, guards, out);
            collect_value_position_arith_exprs(&index.index, guards, out);
        }
        // SOUNDNESS-CRITICAL (range-bound arithmetic panic-freedom): constructing a
        // `Range` / `RangeInclusive` value (`lo..hi`, `lo..=hi`, `..hi`, `lo..`)
        // EAGERLY evaluates every present bound, so an arithmetic / shift / negation
        // site in either bound is an unconditionally-evaluated value-position site
        // at this program point (the bound is computed before the range value
        // exists). Descend into both bounds. Reached from the for-loop iterator
        // (`for _ in 0..(a / b)`), a bare range value (`let _ = 0..(a / b)`), and any
        // aggregate / call sub-position nesting a range. The earlier "loops own
        // those" exclusion was wrong for the bounds themselves: a range bound is NOT
        // conditionally evaluated — it always runs exactly once at construction.
        Expr::Range(range) => {
            if let Some(start) = &range.start {
                collect_value_position_arith_exprs(start, guards, out);
            }
            if let Some(end) = &range.end {
                collect_value_position_arith_exprs(end, guards, out);
            }
        }
        Expr::Tuple(tuple) => {
            for elem in &tuple.elems {
                collect_value_position_arith_exprs(elem, guards, out);
            }
        }
        Expr::Array(array) => {
            for elem in &array.elems {
                collect_value_position_arith_exprs(elem, guards, out);
            }
        }
        Expr::Repeat(repeat) => {
            collect_value_position_arith_exprs(&repeat.expr, guards, out);
            collect_value_position_arith_exprs(&repeat.len, guards, out);
        }
        Expr::Struct(struct_expr) => {
            for field in &struct_expr.fields {
                collect_value_position_arith_exprs(&field.expr, guards, out);
            }
            if let Some(rest) = &struct_expr.rest {
                collect_value_position_arith_exprs(rest, guards, out);
            }
        }
        Expr::Call(call) => {
            collect_value_position_arith_exprs(&call.func, guards, out);
            for arg in &call.args {
                collect_value_position_arith_exprs(arg, guards, out);
            }
        }
        Expr::MethodCall(method_call) => {
            collect_value_position_arith_exprs(&method_call.receiver, guards, out);
            for arg in &method_call.args {
                collect_value_position_arith_exprs(arg, guards, out);
            }
        }
        // `return EXPR;` — the returned expression is a value position whose
        // arithmetic must be overflow/div0-checked. Without this arm it fell to
        // `_ => {}`, so `return a * b;` (or `a / b`) silently dropped its safety
        // obligation while the TAIL form `a * b` (walker-instrumented) is checked
        // — a false-verify. Recurse into the returned expression.
        Expr::Return(ret) => {
            if let Some(value) = &ret.expr {
                collect_value_position_arith_exprs(value, guards, out);
            }
        }
        _ => {}
    }
}

/// The leftmost (root) receiver identifier of an index ACCESS expression,
/// looking through the same transparent value wrappers as
/// [`collect_value_position_index_exprs`]. Returns `None` when the receiver is
/// not anchored at a plain variable (e.g. a method-call or literal receiver).
/// Used to gate exec index-bounds emission on the access being rooted at a
/// declared variable: an access whose root is not a known scoped name (e.g.
/// `left`/`right` bound by an unsupported `split_at_mut`) cannot be faithfully
/// modeled, so instrumenting it would only emit an un-lowerable obligation —
/// the access's own unsupported feature already fails the function closed (#81).
/// True when `expr` contains a (possibly nested, possibly block-embedded)
/// assignment or compound-assignment — i.e., evaluating it has a side effect.
/// Used to skip exec compound-write element-safety emission for an unsupported
/// side-effecting evaluation-order case (`x[{ *r = 1; 0 }] += { *r = 2; 2 }`),
/// which fails closed on its own; pinning an obligation there only perturbs the
/// (sound) blocked outcome and shifts user-assertion program-point indices (#81).
fn expr_contains_assignment(expr: &Expr) -> bool {
    struct V {
        found: bool,
    }
    impl<'ast> syn::visit::Visit<'ast> for V {
        fn visit_expr_assign(&mut self, node: &'ast syn::ExprAssign) {
            self.found = true;
            syn::visit::visit_expr_assign(self, node);
        }
        fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
            if is_assignment_binop(&node.op) {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, node);
        }
    }
    let mut visitor = V { found: false };
    syn::visit::Visit::visit_expr(&mut visitor, expr);
    visitor.found
}

/// True when `expr` contains a (possibly nested, possibly block-embedded)
/// assignment whose TARGET is a dereference — i.e. a write THROUGH a reference
/// (`*r = …` / `*r OP= …`), the mut-ref aliasing-evaluation-order case.
///
/// SOUNDNESS / SCOPE (#83): this is the strict subset of `expr_contains_assignment`
/// that trust-vc cannot faithfully model when it appears inside a compound-write
/// index/RHS — the aliased value is reverted by the throwaway scoped evaluation,
/// exactly the unsupported `x[{ *r = 1; 0 }] += …` case the write path already
/// treats as failing closed "on its own" (the aliased binding is unresolved in
/// any later observation). The #83 fix pins the write-index/element-overflow
/// obligation only for side effects that are PLAIN (non-deref) local assignments,
/// which DO fold to a re-usable pure value; a deref-write side effect keeps the
/// pre-existing skip so it neither shifts the (independently failing) obligation
/// program points nor pretends to model the alias.
fn expr_contains_deref_assignment(expr: &Expr) -> bool {
    struct V {
        found: bool,
    }
    impl<'ast> syn::visit::Visit<'ast> for V {
        fn visit_expr_assign(&mut self, node: &'ast syn::ExprAssign) {
            if is_deref_assignment_target(node.left.as_ref()) {
                self.found = true;
            }
            syn::visit::visit_expr_assign(self, node);
        }
        fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
            if is_assignment_binop(&node.op) && is_deref_assignment_target(node.left.as_ref()) {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, node);
        }
    }
    let mut visitor = V { found: false };
    syn::visit::Visit::visit_expr(&mut visitor, expr);
    visitor.found
}

/// True when an ALREADY-RESOLVED value string carries no re-executable
/// assignment side effect — it parses as an expression containing no `=` / `OP=`.
///
/// SOUNDNESS (#83): a compound-write index/RHS whose source `expr_contains_assignment`
/// is only safe to reuse across the element read + `update`-chain rewrite (which
/// mention the index/RHS more than once) if the side effect has been FOLDED away
/// by scoped evaluation — `eval_block_expr` applies a block-embedded assignment to
/// its own throwaway scope and renders only the resulting value, leaving a pure
/// string. When the effect instead SURVIVES in the rendered string (the scoped
/// evaluator fell back to the raw source, e.g. a bare `ar[(j = i)] += 1`), or the
/// string is not parseable, this returns `false` so the caller fails the write
/// closed rather than re-embedding (and thus duplicating) the effect. Conservative
/// by design: an un-parseable but genuinely-pure resolution is rare and a
/// fail-closed verdict there is sound.
fn resolved_value_is_side_effect_free(rendered: &str) -> bool {
    syn::parse_str::<Expr>(rendered)
        .map(|expr| !expr_contains_assignment(&expr))
        .unwrap_or(false)
}

fn index_access_root_ident(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(_) => expr_path_ident(expr),
        Expr::Index(index) => index_access_root_ident(&index.expr),
        Expr::Paren(paren) => index_access_root_ident(&paren.expr),
        Expr::Group(group) => index_access_root_ident(&group.expr),
        Expr::Unary(unary) => index_access_root_ident(&unary.expr),
        Expr::Cast(cast) => index_access_root_ident(&cast.expr),
        Expr::Reference(reference) => index_access_root_ident(&reference.expr),
        Expr::Field(field) => index_access_root_ident(&field.base),
        _ => None,
    }
}

/// True when `expr` is a scalar checked-arithmetic expression (`+ - * / %`),
/// looking through parentheses, groups, and unary operators. Bit-shifts are
/// handled separately by [`rhs_is_checked_bit_shift`] because their safety
/// obligation is the bit-shift-bounds check rather than additive/mul overflow.
/// Used to decide whether an exec `let`/assignment site needs an
/// arithmetic-safety obligation.
fn rhs_is_checked_scalar_arithmetic(expr: &Expr) -> bool {
    match expr {
        Expr::Binary(binary) => matches!(
            binary.op,
            BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_) | BinOp::Div(_) | BinOp::Rem(_)
        ),
        Expr::Paren(paren) => rhs_is_checked_scalar_arithmetic(&paren.expr),
        Expr::Group(group) => rhs_is_checked_scalar_arithmetic(&group.expr),
        // SOUNDNESS-CRITICAL (exec negation panic-freedom): a bare unary
        // negation `-x` of a fixed-width SIGNED operand carries a
        // negation-overflow obligation (`-x` overflows at `x == TYPE::MIN`,
        // e.g. `-i32::MIN` is unrepresentable). It is a checked-arithmetic site
        // in its own right, NOT merely a wrapper over its operand: the reflexive
        // `(-x) == (-x)` obligation re-lowers `-x`, and the encoder fires the
        // negation-overflow precheck while resolving it (the same precheck it
        // already runs when `-x` reaches a user assertion). A literal negation
        // (`-5i32`) const-folds and emits no check, and a math-typed / float
        // operand returns before the check, so a safe negation still verifies.
        // (The previous `Unary` arm recursed into the operand, so a bare
        // `Neg(path)` returned `false` and no obligation was emitted — a real
        // discarded-negation-overflow false `Verified`.)
        Expr::Unary(unary) => {
            matches!(unary.op, syn::UnOp::Neg(_)) || rhs_is_checked_scalar_arithmetic(&unary.expr)
        }
        _ => false,
    }
}

/// True when `expr` is a bit-shift expression (`<<` / `>>`), looking through
/// parentheses, groups, and unary operators. A discarded-result exec shift site
/// (`let z = x << y;`) carries the same bit-shift-bounds obligation Verus checks
/// (`0 <= b < width`, plus unsigned over-shift), so it needs the auto-emitted
/// arithmetic-safety obligation exactly as scalar `+ - * / %` does. Kept
/// distinct from [`rhs_is_checked_scalar_arithmetic`] so the scalar predicate's
/// "no bit-shifts" contract stays intact and the shift policy is explicit. Part
/// of #2778 (`bit_shift_overflow` / `bit_shift_width_mismatch` families).
fn rhs_is_checked_bit_shift(expr: &Expr) -> bool {
    match expr {
        Expr::Binary(binary) => matches!(binary.op, BinOp::Shl(_) | BinOp::Shr(_)),
        Expr::Paren(paren) => rhs_is_checked_bit_shift(&paren.expr),
        Expr::Group(group) => rhs_is_checked_bit_shift(&group.expr),
        Expr::Unary(unary) => rhs_is_checked_bit_shift(&unary.expr),
        _ => false,
    }
}

fn local_ident(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(ident) => Some(ident.ident.to_string()),
        Pat::Type(pat_type) => local_ident(&pat_type.pat),
        _ => None,
    }
}

fn scoped_option_none_value(local: &syn::Local, init: &Expr) -> Option<String> {
    if !expr_is_unqualified_none(init) {
        return None;
    }
    let inner_ty = local_pat_option_inner_type(&local.pat)?;
    Some(format!(
        "Option::<{}>::None",
        inner_ty.to_token_stream().to_string().replace(' ', "")
    ))
}

fn typed_empty_std_collection_scoped_value(local: &syn::Local, init: &Expr) -> Option<String> {
    let init_kind = expr_empty_std_collection_call_kind(init)?;
    let (path_prefix, generic_args, pat_kind) = local_pat_std_collection_type_args(&local.pat)?;
    if init_kind != pat_kind {
        return None;
    }
    Some(format!("{path_prefix}::<{generic_args}>::new()"))
}

fn expr_empty_std_collection_call_kind(expr: &Expr) -> Option<&'static str> {
    let Expr::Call(call) = expr else {
        return None;
    };
    let Expr::Path(path) = call.func.as_ref() else {
        return None;
    };
    if path.qself.is_some() || !call.args.is_empty() {
        return None;
    }
    let mut segments = path.path.segments.iter().rev();
    let method = segments.next()?;
    if method.ident != "new" && method.ident != "default" {
        return None;
    }
    let receiver = segments.next()?;
    match receiver.ident.to_string().as_str() {
        "Vec" => Some("Vec"),
        "HashMap" => Some("HashMap"),
        "HashSet" => Some("HashSet"),
        _ => None,
    }
}

fn typed_tuple_default_scoped_value(local: &syn::Local, init: &Expr) -> Option<String> {
    let local_tuple = local_pat_tuple_type(&local.pat)?;
    let init_tuple = expr_tuple_default_qself_type(init)?;
    if local_tuple.elems.len() != init_tuple.elems.len() || local_tuple.elems.is_empty() {
        return None;
    }
    let mut defaults = Vec::with_capacity(local_tuple.elems.len());
    for (local_ty, init_ty) in local_tuple.elems.iter().zip(init_tuple.elems.iter()) {
        if !syn_type_tokens_match(local_ty, init_ty) {
            return None;
        }
        defaults.push(default_literal_for_tuple_element(local_ty)?);
    }
    let suffix = if defaults.len() == 1 { "," } else { "" };
    Some(format!("({}{suffix})", defaults.join(", ")))
}

fn local_pat_tuple_type(pat: &Pat) -> Option<&syn::TypeTuple> {
    match pat {
        Pat::Type(pat_type) => match pat_type.ty.as_ref() {
            syn::Type::Tuple(tuple) => Some(tuple),
            _ => local_pat_tuple_type(&pat_type.pat),
        },
        Pat::Paren(paren) => local_pat_tuple_type(&paren.pat),
        _ => None,
    }
}

/// Scoped substitution value for a `let v: <intty> = <bare int literal>;`
/// binding that preserves the declared integer width (#2778).
///
/// Returns `Some("<digits><suffix>")` (e.g. `"16u16"`) only when the `let` has
/// an explicit primitive-integer type annotation AND the initializer is a
/// non-negative integer literal with NO existing suffix. Suffixed source
/// literals already carry their width (quote-preserved), and any non-literal
/// initializer is handled by the normal scoped-string path, so both return
/// `None` here. The suffix is the annotation spelled verbatim, so `usize` /
/// `isize` round-trip through `pointer_width()` and honor a `global size_of`
/// directive rather than freezing a concrete width.
fn declared_width_int_literal_scoped_value(local: &syn::Local) -> Option<String> {
    let suffix = local_pat_declared_int_suffix(&local.pat)?;
    let init = local.init.as_ref()?;
    let digits = unsuffixed_int_literal_digits(&init.expr)?;
    Some(format!("{digits}{suffix}"))
}

/// The verbatim Rust integer-type suffix of a `let` pattern's type annotation,
/// when that annotation is a bare primitive integer type (`u8`..`u128`,
/// `usize`, `i8`..`i128`, `isize`). Returns `None` for references, qualified or
/// multi-segment paths, generic arguments, and non-integer types.
fn local_pat_declared_int_suffix(pat: &Pat) -> Option<&'static str> {
    let ty = match pat {
        Pat::Type(pat_type) => pat_type.ty.as_ref(),
        Pat::Paren(paren) => return local_pat_declared_int_suffix(&paren.pat),
        _ => return None,
    };
    let syn::Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() || type_path.path.segments.len() != 1 {
        return None;
    }
    let segment = type_path.path.segments.first()?;
    if !matches!(segment.arguments, syn::PathArguments::None) {
        return None;
    }
    match segment.ident.to_string().as_str() {
        "u8" => Some("u8"),
        "u16" => Some("u16"),
        "u32" => Some("u32"),
        "u64" => Some("u64"),
        "u128" => Some("u128"),
        "usize" => Some("usize"),
        "i8" => Some("i8"),
        "i16" => Some("i16"),
        "i32" => Some("i32"),
        "i64" => Some("i64"),
        "i128" => Some("i128"),
        "isize" => Some("isize"),
        _ => None,
    }
}

/// The normalized base-10 digits of a non-negative integer literal initializer
/// that carries NO type suffix, peeling `(..)`/group wrappers. Returns `None`
/// for suffixed literals, negative/`Unary` expressions, or any non-literal.
fn unsuffixed_int_literal_digits(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(int_lit),
            ..
        }) if int_lit.suffix().is_empty() => Some(int_lit.base10_digits().to_string()),
        Expr::Paren(paren) => unsuffixed_int_literal_digits(&paren.expr),
        Expr::Group(group) => unsuffixed_int_literal_digits(&group.expr),
        _ => None,
    }
}

fn expr_tuple_default_qself_type(expr: &Expr) -> Option<&syn::TypeTuple> {
    let Expr::Call(call) = expr else {
        return None;
    };
    if !call.args.is_empty() {
        return None;
    }
    let Expr::Path(path) = call.func.as_ref() else {
        return None;
    };
    let qself = path.qself.as_ref()?;
    if path
        .path
        .segments
        .last()
        .is_none_or(|segment| segment.ident != "default")
    {
        return None;
    }
    match qself.ty.as_ref() {
        syn::Type::Tuple(tuple) => Some(tuple),
        _ => None,
    }
}

fn syn_type_tokens_match(left: &syn::Type, right: &syn::Type) -> bool {
    left.to_token_stream().to_string().replace(' ', "")
        == right.to_token_stream().to_string().replace(' ', "")
}

fn default_literal_for_tuple_element(ty: &syn::Type) -> Option<&'static str> {
    let syn::Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() || type_path.path.segments.len() != 1 {
        return None;
    }
    let segment = &type_path.path.segments[0];
    if !matches!(segment.arguments, syn::PathArguments::None) {
        return None;
    }
    match segment.ident.to_string().as_str() {
        "u32" => Some("0u32"),
        "bool" => Some("false"),
        "char" => Some("'\\0'"),
        _ => None,
    }
}

fn local_pat_std_collection_type_args(pat: &Pat) -> Option<(String, String, &'static str)> {
    let Pat::Type(pat_type) = pat else {
        return None;
    };
    let syn::Type::Path(type_path) = pat_type.ty.as_ref() else {
        return None;
    };
    if type_path.qself.is_some() {
        return None;
    }
    let last = type_path.path.segments.last()?;
    let kind = match last.ident.to_string().as_str() {
        "Vec" => "Vec",
        "HashMap" => "HashMap",
        "HashSet" => "HashSet",
        _ => return None,
    };
    let syn::PathArguments::AngleBracketed(args) = &last.arguments else {
        return None;
    };
    let path_prefix = type_path
        .path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>()
        .join("::");
    let generic_args = args
        .args
        .iter()
        .map(|arg| arg.to_token_stream().to_string().replace(' ', ""))
        .collect::<Vec<_>>()
        .join(", ");
    Some((path_prefix, generic_args, kind))
}

fn expr_is_unqualified_none(expr: &Expr) -> bool {
    let Expr::Path(path) = expr else {
        return false;
    };
    path.qself.is_none()
        && path.path.segments.len() == 1
        && path
            .path
            .segments
            .first()
            .is_some_and(|segment| segment.ident == "None")
}

fn local_pat_option_inner_type(pat: &Pat) -> Option<&syn::Type> {
    match pat {
        Pat::Type(pat_type) => {
            option_inner_type(&pat_type.ty).or_else(|| local_pat_option_inner_type(&pat_type.pat))
        }
        Pat::Paren(paren) => local_pat_option_inner_type(&paren.pat),
        _ => None,
    }
}

fn option_inner_type(ty: &syn::Type) -> Option<&syn::Type> {
    let syn::Type::Path(type_path) = ty else {
        return None;
    };
    let segment = type_path.path.segments.last()?;
    if segment.ident != "Option" {
        return None;
    }
    let syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
        return None;
    };
    args.args.iter().find_map(|arg| match arg {
        syn::GenericArgument::Type(ty) => Some(ty),
        _ => None,
    })
}

fn local_pat_is_mut_reference(pat: &Pat) -> bool {
    match pat {
        Pat::Type(pat_type) => {
            matches!(pat_type.ty.as_ref(), syn::Type::Reference(reference) if reference.mutability.is_some())
                || local_pat_is_mut_reference(&pat_type.pat)
        }
        Pat::Paren(paren) => local_pat_is_mut_reference(&paren.pat),
        _ => false,
    }
}

fn local_pat_is_shared_reference(pat: &Pat) -> bool {
    match pat {
        Pat::Type(pat_type) => {
            matches!(pat_type.ty.as_ref(), syn::Type::Reference(reference) if reference.mutability.is_none())
                || local_pat_is_shared_reference(&pat_type.pat)
        }
        Pat::Paren(paren) => local_pat_is_shared_reference(&paren.pat),
        _ => false,
    }
}

fn local_init_is_mut_reference(local: &syn::Local) -> bool {
    local
        .init
        .as_ref()
        .is_some_and(|init| expr_is_mut_reference(&init.expr))
}

/// Detects an `old(...)` call anywhere within an expression tree (`old(x)`,
/// `*old(x)`, `... && *old(x) == 5`, …). Matches the tail path segment `old`,
/// consistent with the two-state operator recognition elsewhere in extraction
/// (`path_last_segment(..) == Some("old")`, body_extract.rs:5005). Used to
/// fail-closed on `old` inside a `by(bit_vector)` assert (Verus parity,
/// upstream bitvector.rs::test_old_not_supported).
#[derive(Default)]
struct OldCallFinder {
    found: bool,
}

impl<'ast> syn::visit::Visit<'ast> for OldCallFinder {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let Expr::Path(path) = &*call.func {
            if path.qself.is_none()
                && path
                    .path
                    .segments
                    .last()
                    .is_some_and(|seg| seg.ident == "old")
            {
                self.found = true;
            }
        }
        syn::visit::visit_expr_call(self, call);
    }
}

fn expr_uses_old_call(expr: &Expr) -> bool {
    let mut finder = OldCallFinder::default();
    syn::visit::Visit::visit_expr(&mut finder, expr);
    finder.found
}

fn block_uses_old_call(block: &syn::Block) -> bool {
    let mut finder = OldCallFinder::default();
    syn::visit::Visit::visit_block(&mut finder, block);
    finder.found
}

fn expr_is_call_result(expr: &Expr) -> bool {
    match expr {
        Expr::Call(_) => true,
        Expr::Paren(paren) => expr_is_call_result(&paren.expr),
        Expr::Group(group) => expr_is_call_result(&group.expr),
        _ => false,
    }
}

fn expr_is_mut_reference(expr: &Expr) -> bool {
    match expr {
        Expr::Reference(reference) => reference.mutability.is_some(),
        Expr::Paren(paren) => expr_is_mut_reference(&paren.expr),
        Expr::Group(group) => expr_is_mut_reference(&group.expr),
        _ => false,
    }
}

/// True iff the call's `func` is a qualified-UFCS path `<S as T>::f` (an
/// `Expr::Path` whose `qself` is present). Used to route such calls to the
/// unit-4 discharge instead of the path-form helper-call handler.
fn call_func_is_qualified_path(call: &syn::ExprCall) -> bool {
    matches!(&*call.func, Expr::Path(func_path) if func_path.qself.is_some())
}

/// Decomposes a UFCS-style associated-fn call func path into its
/// `(optional type/trait segment, method name)`. The method name is the LAST
/// path segment; the type/trait segment is the immediately-preceding plain path
/// segment when present (`None` for a `<Type>::method` qself form whose path is
/// just `method`). Returns `None` for a bare single-segment free-fn call with no
/// `qself` (`foo(x)`) — those are handled by `havoc_mut_ref_call_arg_referents`
/// — and for any non-path callee. Used by `havoc_ufcs_receiver_mutation` to give
/// a UFCS associated-fn call the same `&mut self`/collection-mutator framing as
/// the equivalent `recv.method(..)` method call (round-8 findings 6–10).
fn ufcs_call_assoc_fn(call: &syn::ExprCall) -> Option<(Option<String>, String)> {
    let Expr::Path(func_path) = &*call.func else {
        return None;
    };
    let is_qself = func_path.qself.is_some();
    let segments: Vec<String> = func_path
        .path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    let method = segments.last()?.clone();
    // A bare single-segment, non-qualified path is a free-fn call, not a UFCS
    // associated-fn call — there is no `Type::`/`<Type>::`/`Trait::` qualifier.
    if !is_qself && segments.len() < 2 {
        return None;
    }
    let type_segment = (segments.len() >= 2).then(|| segments[segments.len() - 2].clone());
    Some((type_segment, method))
}

/// True for the std container type names the IR collapses onto a ghost
/// collection (`Vec`/`[T]` => `Seq`, `HashSet`/`BTreeSet` => `Set`,
/// `HashMap`/`BTreeMap` => `Map`, `VecDeque` => `Seq`). Used to gate the UFCS
/// collection-mutator framing (`Vec::push(v, ..)`) so a user fn that merely
/// takes a collection argument is never mistaken for an in-place mutator.
fn is_std_collection_type_name(name: &str) -> bool {
    matches!(
        name,
        "Vec" | "VecDeque" | "HashSet" | "BTreeSet" | "HashMap" | "BTreeMap"
    )
}

fn expr_path_ident(expr: &Expr) -> Option<String> {
    let expr = strip_place_wrappers(expr);
    let Expr::Path(path) = expr else {
        return None;
    };
    if path.path.segments.len() == 1 {
        path.path
            .segments
            .first()
            .map(|segment| segment.ident.to_string())
    } else {
        None
    }
}

/// The single binding identifier of a `let` pattern (`let q`, `let mut q`, or
/// `let q: T`). Destructuring and `@` subpatterns deliberately return `None`:
/// the alias analyses cannot assign one initializer place to multiple bindings.
fn local_binding_ident(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(pat_ident) if pat_ident.subpat.is_none() => Some(pat_ident.ident.to_string()),
        Pat::Type(pat_type) => local_binding_ident(&pat_type.pat),
        _ => None,
    }
}

fn struct_field_index_assignment_target(expr: &Expr) -> Option<(String, String)> {
    let Expr::Field(field) = strip_place_wrappers(expr) else {
        return None;
    };
    let syn::Member::Named(member) = &field.member else {
        return None;
    };
    let owner = expr_path_ident(&field.base)?;
    Some((owner, member.to_string()))
}

/// A field-place assignment target `root.f1.f2…fn` (named or tuple fields,
/// possibly nested) decomposed into the root identifier and the field members in
/// root->leaf order. Returns `None` when the place is not a chain of field
/// accesses anchored at a plain variable (e.g. an index access in the path, or a
/// non-ident root). Used by [`BodyExtractor::assign_direct_field_expr`].
fn field_assignment_path(expr: &Expr) -> Option<(String, Vec<String>)> {
    let Expr::Field(field) = strip_place_wrappers(expr) else {
        return None;
    };
    let member = match &field.member {
        syn::Member::Named(ident) => ident.to_string(),
        syn::Member::Unnamed(index) => index.index.to_string(),
    };
    if let Some(root) = expr_path_ident(&field.base) {
        Some((root, vec![member]))
    } else {
        let (root, mut members) = field_assignment_path(&field.base)?;
        members.push(member);
        Some((root, members))
    }
}

fn indexed_tuple_field_assignment_target(expr: &Expr) -> Option<(String, &Expr, usize)> {
    let Expr::Field(field) = strip_place_wrappers(expr) else {
        return None;
    };
    let syn::Member::Unnamed(member) = &field.member else {
        return None;
    };
    let Expr::Index(index) = strip_place_wrappers(&field.base) else {
        return None;
    };
    let owner = expr_path_ident(&index.expr)?;
    Some((owner, &index.index, member.index as usize))
}

fn nested_index_assignment_target(expr: &syn::ExprIndex) -> Option<(String, &Expr, &Expr)> {
    let inner = match strip_place_wrappers(&expr.expr) {
        Expr::Index(inner) => inner,
        _ => return None,
    };
    let owner = expr_path_ident(&inner.expr)?;
    Some((owner, &inner.index, &expr.index))
}

fn mut_ref_path_ident(expr: &Expr) -> Option<String> {
    let Expr::Reference(reference) = strip_place_wrappers(expr) else {
        return None;
    };
    reference.mutability.as_ref()?;
    expr_path_ident(&reference.expr)
}

/// Resolve a method-call receiver to its underlying single-segment variable
/// ident, looking through paren/group wrappers (via `expr_path_ident`) AND an
/// explicit deref `*` (`(*v).m(..)`), so the explicit-deref receiver form
/// resolves to the same `v` as the auto-deref form `v.m(..)`.
///
/// SOUNDNESS (the explicit-deref residual of the loop collection-mutation gap):
/// `expr_path_ident` strips paren/group but NOT the deref operator, so a method
/// call written `(*v).<mutator>()` in a loop body resolved to `None` and was
/// never recorded as modifying `v`. The loop frame then pinned `v == v_pre`,
/// trivially "preserving" a false invariant about `v` — even for a recognized
/// in-place mutator such as `(*v).clear()`. Stripping the deref here makes the
/// receiver resolve to `v`, feeding the existing conservative-mutation logic
/// (havoc on a non-pure method). Mirrors the straight-line path's
/// `method_receiver_param`.
fn method_call_receiver_ident(receiver: &Expr) -> Option<String> {
    if let Expr::Unary(unary) = strip_place_wrappers(receiver) {
        if matches!(unary.op, syn::UnOp::Deref(_)) {
            return expr_path_ident(&unary.expr);
        }
    }
    expr_path_ident(receiver)
}

fn strip_place_wrappers(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(paren) => strip_place_wrappers(&paren.expr),
        Expr::Group(group) => strip_place_wrappers(&group.expr),
        _ => expr,
    }
}

/// True for a call argument of the literal shape `&mut &expr` (any paren/group
/// wrapping): a MUTABLE reference to a TEMPORARY shared reference. The callee
/// receiving `&mut &T` can only rebind the temporary `&T` — the inner shared
/// referent is immutable through it — so no caller binding is mutated and the
/// `&mut`-arg havoc must not fire. Deliberately does NOT match `&mut r` where
/// `r` is a binding holding a reference (the callee CAN rebind `r`'s value) or
/// `&mut &mut x` (writes reach `x` through the inner `&mut`).
fn mut_ref_arg_is_shared_ref_temporary(arg: &Expr) -> bool {
    let Expr::Reference(outer) = strip_place_wrappers(arg) else {
        return false;
    };
    if outer.mutability.is_none() {
        return false;
    }
    matches!(
        strip_place_wrappers(&outer.expr),
        Expr::Reference(inner) if inner.mutability.is_none()
    )
}

/// The anchoring identifier of a place expression, peeling field / index / deref
/// / reference / paren / group wrappers (e.g. `o.inner.x` / `o.items[i]` / `*o` →
/// `o`). Used to resolve the ROOT parameter of a `&mut self` method call
/// laundered through a sub-place projection (`o.inner.bump()`).
fn field_index_projection_root(expr: &Expr) -> Option<String> {
    match strip_place_wrappers(expr) {
        Expr::Field(field) => field_index_projection_root(&field.base),
        Expr::Index(index) => field_index_projection_root(&index.expr),
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            field_index_projection_root(&unary.expr)
        }
        Expr::Reference(reference) => field_index_projection_root(&reference.expr),
        path @ Expr::Path(_) => expr_path_ident(path),
        _ => None,
    }
}

/// The NAMED-FIELD projection path of a place expression, from its anchoring root
/// identifier to the leaf (`o.inner.x` → `("o", ["inner", "x"])`, `*o` →
/// `("o", [])`), peeling deref / reference / paren / group wrappers at each step.
/// Returns `None` when the place contains a step this resolver cannot follow to a
/// declared struct field — a TUPLE field (`o.0`) or an INDEX (`o.items[i]`) — so
/// the caller treats the projected sub-place's struct type as UNRESOLVABLE and
/// falls back to the conservative pure-name classification rather than
/// mis-resolving. Paired with [`projected_field_struct_type`] to resolve the TYPE
/// of a method receiver laundered through a field projection (`o.inner.method()`).
fn receiver_field_projection_path(expr: &Expr) -> Option<(String, Vec<String>)> {
    match strip_place_wrappers(expr) {
        Expr::Field(field) => {
            let syn::Member::Named(member) = &field.member else {
                return None;
            };
            let (root, mut path) = receiver_field_projection_path(&field.base)?;
            path.push(member.to_string());
            Some((root, path))
        }
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            receiver_field_projection_path(&unary.expr)
        }
        Expr::Reference(reference) => receiver_field_projection_path(&reference.expr),
        path @ Expr::Path(_) => Some((expr_path_ident(path)?, Vec::new())),
        _ => None,
    }
}

/// Walks the named-field `path` from a starting `Datatype` to its leaf field's
/// struct/enum type-NAME, using each step's single-variant field list. Returns
/// `None` when `path` is EMPTY (no projection — the bare root is a DIRECT
/// receiver, classified by the root type itself), when an intermediate step is
/// not a single-variant struct, when a named field is absent, or when the leaf
/// field is NOT itself a struct/enum (a scalar/collection field has no
/// receiver-kind table) — the caller then falls back to the conservative
/// pure-name classification (fail-closed).
fn projected_field_struct_type(root_ty: &TrustVcType, path: &[String]) -> Option<String> {
    if path.is_empty() {
        return None;
    }
    let mut current = root_ty.clone();
    for field in path {
        let TrustVcType::Datatype { variants, .. } = &current else {
            return None;
        };
        let [variant] = variants.as_slice() else {
            return None;
        };
        let (_, field_ty) = datatype_field(variant, field)?;
        current = field_ty.clone();
    }
    match current {
        TrustVcType::Datatype { name, .. } => Some(name),
        _ => None,
    }
}

/// Resolves the struct/enum type-NAME of a `&mut`-param method receiver place
/// `P.field.m()` by walking the named-field projection path from `P`'s root
/// struct type (`root_struct_type`) through the file struct registry. The
/// free-function sibling of [`AssertionCollector::projected_receiver_struct_type`]
/// for the postcondition-reject path, which has no `AssertionCollector` in scope.
/// Returns `None` when the receiver is the bare param, the root type is not a
/// registered struct, or the projection cannot be followed to a struct sub-field.
fn projected_param_field_struct_type(
    receiver: &Expr,
    root_struct_type: &str,
    struct_types: &[StructDef],
) -> Option<String> {
    let (_, path) = receiver_field_projection_path(receiver)?;
    let root_def = struct_types
        .iter()
        .find(|def| def.name == root_struct_type)?;
    projected_field_struct_type(&root_def.to_datatype_type(), &path)
}

fn is_stable_vec_insert_index_expr(expr: &Expr) -> bool {
    match strip_place_wrappers(expr) {
        Expr::Path(_) => expr_path_ident(expr).is_some(),
        Expr::Lit(_) => true,
        Expr::Cast(cast) => is_stable_vec_insert_index_expr(&cast.expr),
        _ => false,
    }
}

fn is_scoped_vec_receiver_model(receiver: &str) -> bool {
    let compact = receiver
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    let trimmed = compact.trim_matches(|ch| ch == '(' || ch == ')');
    trimmed.starts_with("Vec::")
        || trimmed.starts_with("std::vec::Vec::")
        || trimmed.starts_with("alloc::vec::Vec::")
}

/// True when a scoped model string is a recognized sequence-shaped value
/// (an array literal `[ ... ]`, or a value our own lowering derives from a
/// sequence place through `update`/`push`/`subrange`/`add`). Used to route a
/// `.set(idx, val)` on a local without a declared type only when the modeled
/// state is genuinely sequence-like, never a user `.set` on an unrelated type.
fn is_scoped_sequence_shaped_model(receiver: &str) -> bool {
    let compact = receiver
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    let trimmed = compact.trim_matches(|ch| ch == '(' || ch == ')');
    // Array / slice literal, e.g. `[0u64,1u64]`.
    if trimmed.starts_with('[') && trimmed.ends_with(']') {
        return true;
    }
    // A value already produced by our sequence-place lowering: the outermost
    // call is one of the sequence operations whose receiver is itself a
    // sequence place. These models are only ever emitted for sequence places.
    compact.ends_with(").update")
        || compact.contains(").update(")
        || compact.contains(").push(")
        || compact.contains(").subrange(")
        || compact.contains(").add(")
}

fn scoped_vec_literal_len(receiver: &str) -> Option<usize> {
    let compact = receiver
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    let trimmed = compact.trim_matches(|ch| ch == '(' || ch == ')');
    let inner = trimmed.strip_prefix("vec![")?.strip_suffix(']')?;
    if inner.is_empty() {
        return Some(0);
    }

    let mut depth = 0usize;
    let mut count = 1usize;
    for ch in inner.chars() {
        match ch {
            '[' | '(' | '{' => depth = depth.saturating_add(1),
            ']' | ')' | '}' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => count += 1,
            _ => {}
        }
    }
    Some(count)
}

fn literal_usize_index_expr(expr: &Expr) -> Option<usize> {
    match strip_place_wrappers(expr) {
        Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(value) => value.base10_parse().ok(),
            _ => None,
        },
        Expr::Cast(cast) => literal_usize_index_expr(&cast.expr),
        _ => None,
    }
}

fn is_deref_assignment_target(expr: &Expr) -> bool {
    matches!(
        strip_place_wrappers(expr),
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_))
    )
}

fn deref_assignment_target_alias(expr: &Expr) -> Option<String> {
    let Expr::Unary(unary) = strip_place_wrappers(expr) else {
        return None;
    };
    if !matches!(unary.op, syn::UnOp::Deref(_)) {
        return None;
    }
    expr_path_ident(&unary.expr)
}

fn assignment_target_uses_erased_mut_ref_alias(
    expr: &Expr,
    collector: &AssertionCollector<'_>,
) -> bool {
    match strip_place_wrappers(expr) {
        Expr::Path(_) => expr_path_ident(expr)
            .as_deref()
            .is_some_and(|name| collector.is_erased_mut_ref_name(name)),
        Expr::Field(field) => assignment_target_uses_erased_mut_ref_alias(&field.base, collector),
        Expr::Index(index) => assignment_target_uses_erased_mut_ref_alias(&index.expr, collector),
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
            expr_path_ident(&unary.expr)
                .as_deref()
                .is_some_and(|name| collector.is_erased_mut_ref_name(name))
        }
        _ => false,
    }
}

fn field_member_name(member: &syn::Member) -> String {
    match member {
        syn::Member::Named(ident) => ident.to_string(),
        syn::Member::Unnamed(index) => index.index.to_string(),
    }
}

#[cfg(test)]
mod b2_contains_break_tests {
    use super::contains_break;

    #[test]
    fn b2_break_targeting_inner_or_outer() {
        // Unlabeled break inside a NESTED inner loop targets the inner loop,
        // NOT this loop -> must return false (the outer normal-exit fact stays).
        let nested: syn::Block = syn::parse_quote!({
            let mut j = 0;
            while j < 5 {
                if j == 3 {
                    break;
                }
                j += 1;
            }
            i += 1;
        });
        assert!(
            !contains_break(&nested),
            "nested-inner break must NOT exit the outer loop"
        );

        // A direct unlabeled break (no nested loop) targets THIS loop -> true.
        let direct: syn::Block = syn::parse_quote!({
            if x {
                break;
            }
            i += 1;
        });
        assert!(contains_break(&direct), "direct break exits this loop");

        // A labeled break to an enclosing loop (label not nested here) -> true.
        let labeled_outer: syn::Block = syn::parse_quote!({
            while c {
                break 'outer;
            }
        });
        assert!(
            contains_break(&labeled_outer),
            "labeled break to outer loop exits this loop"
        );

        // A labeled break to a nested labeled inner loop -> false.
        let labeled_inner: syn::Block = syn::parse_quote!({
            'inner: while c {
                break 'inner;
            }
            i += 1;
        });
        assert!(
            !contains_break(&labeled_inner),
            "labeled break to nested inner loop does NOT exit this loop"
        );
    }
}

#[cfg(test)]
mod closure_reflection_scope_tests {
    use super::{AssertionCollector, ClosureReflectionContract, VerificationContext};
    use crate::ir::TrustVcType;

    fn contract(label: &str) -> ClosureReflectionContract {
        ClosureReflectionContract {
            params: vec![label.to_string()],
            arg_tys: vec![TrustVcType::Uint { width: 64 }],
            requires: None,
            ensures: None,
        }
    }

    #[test]
    fn lexical_shadow_hide_and_snapshot_restore_are_exact() {
        let mut vc = VerificationContext::new();
        let mut collector = AssertionCollector::new(&mut vc, 0, None);

        collector.replace_closure_reflection_contract("c".to_string(), contract("outer"));
        assert_eq!(
            collector.closure_reflection_contracts["c"].params,
            ["outer"]
        );

        collector.push_scope();
        collector.replace_closure_reflection_contract("c".to_string(), contract("inner"));
        assert_eq!(
            collector.closure_reflection_contracts["c"].params,
            ["inner"]
        );
        collector.pop_scope();
        assert_eq!(
            collector.closure_reflection_contracts["c"].params,
            ["outer"]
        );

        collector.push_scope();
        collector.shadow_name("c");
        assert!(!collector.closure_reflection_contracts.contains_key("c"));
        collector.pop_scope();
        assert_eq!(
            collector.closure_reflection_contracts["c"].params,
            ["outer"]
        );

        let snapshot = collector.scope_snapshot();
        collector.push_scope();
        collector.replace_closure_reflection_contract("proof_only".to_string(), contract("proof"));
        assert!(collector
            .closure_reflection_contracts
            .contains_key("proof_only"));
        collector.restore_scope_snapshot(snapshot);
        assert!(!collector
            .closure_reflection_contracts
            .contains_key("proof_only"));
        assert_eq!(
            collector.closure_reflection_contracts["c"].params,
            ["outer"]
        );
    }
}
