// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deterministic canonical writer for prepared verification contexts.
//!
//! Emits a stable textual payload with explicit ordering rules:
//! - vectors keep semantic order
//! - `HashMap` entries are sorted by key before writing
//! - `HashSet` values are sorted before writing
//! - enums are written by stable tag names, not discriminant integers
//!
//! Part of #2646.

use std::fmt::Write as FmtWrite;

#[path = "cache_canonical_expr.rs"]
mod expr_writer;
use expr_writer::write_expr;

use crate::ir::{
    ConformanceMethodBody, StructDef, TraitBound, TraitDecl, TraitImplDecl, TraitMethodDecl,
};
use crate::prepared_context::{PreparedObligation, PreparedTrigger, PreparedVerificationContext};
use crate::vc::{
    BitshiftBehavior, ConditionOrigin, Div0Behavior, FunctionContext, InvariantMask,
    ObligationKind, OverflowBehavior, ProofStepMeta, SolverMode, VariableDecl, VerificationMode,
};

pub(super) fn write_context(
    out: &mut String,
    ctx: &PreparedVerificationContext,
    schema: u32,
    build_source_identity: &str,
) {
    assert_cache_field_classification_is_exhaustive(ctx);
    let _ = writeln!(out, "schema:{schema}");
    write_semantic_profile(out, build_source_identity);
    write_verification_mode(out, ctx.verification_mode);
    write_overflow_behavior(out, ctx.overflow_behavior);
    write_div0_behavior(out, ctx.div0_behavior);
    write_bitshift_behavior(out, ctx.bitshift_behavior);
    let _ = writeln!(out, "has_collection:{}", ctx.has_collection_context);
    let _ = writeln!(out, "rlimit:{:?}", ctx.rlimit_ms);
    // The DETERMINISTIC budget is verdict-semantic in exactly the way the
    // wall backstop above is: a Verified obtained under a larger conflict
    // allowance must never be served to a context that grants less.
    let _ = writeln!(
        out,
        "rlimit_conflicts:{:?}",
        ctx.rlimit_conflicts.map(|budget| budget.conflicts())
    );
    // Retry policy is verdict-semantic: demand inlining and the timeout /
    // E-matching cascades can recover an otherwise fail-closed Unknown as
    // Verified. A Verified produced under stronger retry settings must never
    // be served to a context that disables or bounds those retries.
    let (inline_enabled, inline_depth, inline_max_callees) = ctx.demand_inline.cache_key_parts();
    let _ = writeln!(
        out,
        "demand_inline:{inline_enabled}:{inline_depth}:{inline_max_callees}"
    );
    let _ = writeln!(out, "skip_retry_cascade:{}", ctx.skip_retry_cascade);

    write_sorted_set(out, "broadcast_use_groups", &ctx.broadcast_use_groups);
    write_sorted_set(out, "revealed_fns", &ctx.revealed_fns);
    // hidden_fns MUST be part of the fingerprint: a cached `verified` computed
    // without `hide!(f)` must never replay for a query that hides `f` (the
    // hidden body could have carried the proof — an unsound replay).
    write_sorted_set(out, "hidden_fns", &ctx.hidden_fns);
    // Recursive demand-inline may adopt a model only with checked source
    // definition provenance. Replaying across a context without the same
    // authority could turn a fail-closed Unknown into a false Counterexample.
    write_sorted_set(
        out,
        "source_catalog_admitted_definitions",
        &ctx.source_catalog_admitted_definitions,
    );
    write_sorted_set(out, "tracked_params", &ctx.tracked_params);

    write_invariant_mask(out, &ctx.invariant_mask);

    let _ = writeln!(out, "variables:{}", ctx.variables.len());
    for var in &ctx.variables {
        write_variable_decl(out, var);
    }

    {
        let mut keys: Vec<_> = ctx.forall_bound_vars.keys().collect();
        keys.sort();
        let _ = writeln!(out, "forall_bound_vars:{}", keys.len());
        for key in keys {
            let _ = writeln!(out, "scope:{key}");
            if let Some(vars) = ctx.forall_bound_vars.get(key) {
                for var in vars {
                    write_variable_decl(out, var);
                }
            }
        }
    }

    match &ctx.function_context {
        Some(fc) => {
            let _ = write!(out, "function_context:");
            write_function_context(out, fc);
        }
        None => {
            let _ = writeln!(out, "function_context:none");
        }
    }

    let _ = writeln!(
        out,
        "helper_functions:{}",
        ctx.helper_function_contexts.len()
    );
    for fc in &ctx.helper_function_contexts {
        write_function_context(out, fc);
    }

    let _ = writeln!(out, "obligations:{}", ctx.obligations.len());
    for obligation in &ctx.obligations {
        write_obligation(out, obligation);
    }

    {
        let mut keys: Vec<_> = ctx.assert_by_scopes.keys().collect();
        keys.sort();
        let _ = writeln!(out, "assert_by_scopes:{}", keys.len());
        for key in keys {
            let _ = writeln!(out, "scope:{key}");
            if let Some(obligations) = ctx.assert_by_scopes.get(key) {
                let _ = writeln!(out, "count:{}", obligations.len());
                for obligation in obligations {
                    write_obligation(out, obligation);
                }
            }
        }
    }

    {
        // Entry assumptions participate in a loop invariant's base-case VC.
        // Replaying a result across different entry scopes could therefore
        // turn a proof under a stronger pre-loop fact into a false cache hit.
        let mut keys: Vec<_> = ctx.loop_entry_scopes.keys().collect();
        keys.sort();
        let _ = writeln!(out, "loop_entry_scopes:{}", keys.len());
        for key in keys {
            let _ = writeln!(out, "scope:{key}");
            if let Some(obligations) = ctx.loop_entry_scopes.get(key) {
                let _ = writeln!(out, "count:{}", obligations.len());
                for obligation in obligations {
                    write_obligation(out, obligation);
                }
            }
        }
    }

    {
        let mut keys: Vec<_> = ctx.loop_guards.keys().collect();
        keys.sort();
        let _ = writeln!(out, "loop_guards:{}", keys.len());
        for key in keys {
            if let Some(value) = ctx.loop_guards.get(key) {
                let _ = writeln!(out, "guard:{key}={value}");
            }
        }
    }

    {
        // Which invariants belong to a NESTED loop (their base case drops the
        // function-entry facts about the modified vars) — part of the verdict,
        // so part of the key.
        let mut nested: Vec<_> = ctx.loop_nested_entry_invariants.iter().collect();
        nested.sort();
        let _ = writeln!(out, "loop_nested_entry_invariants:{}", nested.len());
        for name in nested {
            let _ = writeln!(out, "nested_entry:{name}");
        }
    }

    {
        let mut keys: Vec<_> = ctx.loop_modified_vars.keys().collect();
        keys.sort();
        let _ = writeln!(out, "loop_modified_vars:{}", keys.len());
        for key in keys {
            if let Some(vars) = ctx.loop_modified_vars.get(key) {
                let _ = writeln!(out, "modified:{key}={}", vars.join(","));
            }
        }
    }

    {
        // Which loop each loop-lane obligation belongs to decides which
        // invariants its step assumes — part of the verdict, so part of the key.
        let mut keys: Vec<_> = ctx.loop_invariant_groups.keys().collect();
        keys.sort();
        let _ = writeln!(out, "loop_invariant_groups:{}", keys.len());
        for key in keys {
            if let Some(group) = ctx.loop_invariant_groups.get(key) {
                let _ = writeln!(out, "group:{key}={group}");
            }
        }
    }

    {
        // Body transitions distinguish loops with identical modified-var sets
        // and guards but different bodies (e.g. `i = i + 1` vs `i = i + 2`),
        // so they MUST be part of the cache key — otherwise a sound `i + 1`
        // result could be served for an unsound `i + 2` loop. Part of M4.
        let mut keys: Vec<_> = ctx.loop_body_transitions.keys().collect();
        keys.sort();
        let _ = writeln!(out, "loop_body_transitions:{}", keys.len());
        for key in keys {
            if let Some(transitions) = ctx.loop_body_transitions.get(key) {
                let joined = transitions
                    .iter()
                    .map(|(var, rhs)| format!("{var}:={rhs}"))
                    .collect::<Vec<_>>()
                    .join(";");
                let _ = writeln!(out, "transition:{key}={joined}");
            }
        }
    }

    let _ = writeln!(out, "trait_decls:{}", ctx.trait_decls.len());
    for decl in &ctx.trait_decls {
        write_trait_decl(out, decl);
    }

    let _ = writeln!(out, "trait_impl_decls:{}", ctx.trait_impl_decls.len());
    for decl in &ctx.trait_impl_decls {
        write_trait_impl_decl(out, decl);
    }

    {
        // The trait-impl method BODIES are decisive for conformance: the
        // conformance pass (trait_conformance.rs) binds an impl method's result
        // to the captured body and refutes the trait `ensures` against it. Two
        // contexts that differ ONLY in an impl body (e.g. conforming `true` vs
        // non-conforming `false`) must therefore NOT collide on a stale cache
        // key — otherwise a `Verified` computed for the conforming body is
        // served for the non-conforming one, a false-`Verified` on a cache hit.
        // Analogous to `loop_body_transitions` above. Part of the cache-key
        // soundness fix (round-6).
        let mut keys: Vec<_> = ctx.trait_impl_method_bodies.keys().collect();
        keys.sort();
        let _ = writeln!(
            out,
            "trait_impl_method_bodies:{}",
            ctx.trait_impl_method_bodies.len()
        );
        for key in keys {
            if let Some(body) = ctx.trait_impl_method_bodies.get(key) {
                write_conformance_method_body(out, &key.canonical_string(), body);
            }
        }
    }

    // Impl methods' OWN declared `ensures`. These change BOTH the conformance
    // verdict (an extra `body ⊨ impl_ensures` assert) AND the propagated
    // postcondition axiom seen by callers, so two contexts differing only in an
    // impl `ensures` must not collide on a stale cache key. Emit this section
    // ONLY when the map is non-empty: a context with no impl-declared `ensures`
    // has verification semantics identical to a pre-capability context, so its
    // key must stay byte-identical (avoid gratuitously invalidating every
    // unrelated cache entry).
    if !ctx.trait_impl_method_ensures.is_empty() {
        let mut keys: Vec<_> = ctx.trait_impl_method_ensures.keys().collect();
        keys.sort();
        let _ = writeln!(
            out,
            "trait_impl_method_ensures:{}",
            ctx.trait_impl_method_ensures.len()
        );
        for key in keys {
            if let Some(ensures) = ctx.trait_impl_method_ensures.get(key) {
                let _ = writeln!(out, "  {}:{}", key.canonical_string(), ensures.len());
                for clause in ensures {
                    let _ = writeln!(out, "    {clause}");
                }
            }
        }
    }

    // Methods the conformance pass SKIPS (blocked by their own ill-formedness
    // error). Whether a method is exempt changes whether conformance runs for
    // it, so it must be part of the key.
    write_sorted_set(
        out,
        "conformance_exempt_methods",
        &ctx.conformance_exempt_methods,
    );

    let _ = writeln!(out, "struct_types:{}", ctx.struct_types.len());
    for s in &ctx.struct_types {
        write_struct_def(out, s);
    }

    {
        let mut keys: Vec<_> = ctx.type_invariants.keys().collect();
        keys.sort();
        let _ = writeln!(out, "type_invariants:{}", keys.len());
        for key in keys {
            if let Some(expr) = ctx.type_invariants.get(key) {
                let _ = write!(out, "inv:{key}=");
                write_expr(out, expr);
                let _ = writeln!(out);
            }
        }
    }
}

fn write_semantic_profile(out: &mut String, build_source_identity: &str) {
    // The default cache root is shared by debug/release, feature-distinct, and
    // cross-target builds. Bind every build mode that can select verifier code,
    // plus ambient inputs read by the encoder after context preparation.
    // Package versions are intentionally stable across development commits.
    // Bind the full clean-checkout Git identity as well, so a `Verified` from
    // an older verifier executable cannot authorize a changed implementation.
    let _ = writeln!(out, "source_revision:{build_source_identity}");
    let _ = writeln!(
        out,
        "build:{}:test={}:debug={}:arch={}:os={}:ptr={}",
        env!("CARGO_PKG_VERSION"),
        cfg!(test),
        cfg!(debug_assertions),
        std::env::consts::ARCH,
        std::env::consts::OS,
        usize::BITS,
    );
    let _ = writeln!(
        out,
        "features:trust_mc={}:ty={}:proof_certificates={}:named_assertions={}:native_seq={}:native_strings={}",
        cfg!(feature = "trust_mc"),
        cfg!(feature = "ty"),
        cfg!(feature = "proof-certificates"),
        cfg!(feature = "named-assertions"),
        cfg!(feature = "native-seq"),
        cfg!(feature = "native-strings"),
    );
    let _ = writeln!(
        out,
        "seq_flat_map_quantifiers:{}",
        crate::encoder::seq_flat_map_quantifiers_enabled()
    );
    let term_memory_mb = crate::encoder::configured_term_memory_mb();
    let _ = writeln!(out, "term_memory_mb:{term_memory_mb:?}");
}

/// Compile-time tripwire for cache-key completeness.
///
/// Most fields below are serialized by [`write_context`]. The two deliberate
/// exceptions are verdict-irrelevant: scoped reveals are derived entirely from
/// the serialized `assert_by_scopes`, while counterexample metadata affects
/// rendering only. Keeping this pattern exhaustive means adding a prepared
/// context field cannot silently create another under-keyed cache entry.
fn assert_cache_field_classification_is_exhaustive(ctx: &PreparedVerificationContext) {
    let PreparedVerificationContext {
        obligations: _,
        variables: _,
        function_context: _,
        trait_decls: _,
        trait_impl_decls: _,
        trait_impl_method_bodies: _,
        trait_impl_method_ensures: _,
        conformance_exempt_methods: _,
        verification_mode: _,
        overflow_behavior: _,
        div0_behavior: _,
        bitshift_behavior: _,
        broadcast_use_groups: _,
        assert_by_scopes: _,
        loop_entry_scopes: _,
        loop_nested_entry_invariants: _,
        assert_by_scope_revealed_fns: _,
        forall_bound_vars: _,
        loop_guards: _,
        loop_modified_vars: _,
        loop_invariant_groups: _,
        loop_body_transitions: _,
        has_collection_context: _,
        revealed_fns: _,
        hidden_fns: _,
        source_catalog_admitted_definitions: _,
        helper_function_contexts: _,
        struct_types: _,
        type_invariants: _,
        invariant_mask: _,
        tracked_params: _,
        rlimit_ms: _,
        rlimit_conflicts: _,
        demand_inline: _,
        counterexample_var_meta: _,
        skip_retry_cascade: _,
    } = ctx;
}

fn write_sorted_set(out: &mut String, label: &str, set: &std::collections::HashSet<String>) {
    let mut items: Vec<_> = set.iter().collect();
    items.sort();
    let _ = writeln!(out, "{}:{}", label, items.len());
    for item in items {
        let _ = writeln!(out, "  {item}");
    }
}

fn write_verification_mode(out: &mut String, mode: VerificationMode) {
    let tag = match mode {
        VerificationMode::BodyLevel => "BodyLevel",
        VerificationMode::CallSite => "CallSite",
    };
    let _ = writeln!(out, "verification_mode:{tag}");
}

fn write_overflow_behavior(out: &mut String, behavior: OverflowBehavior) {
    let tag = match behavior {
        OverflowBehavior::Error => "Error",
        OverflowBehavior::Truncate => "Truncate",
        OverflowBehavior::Allow => "Allow",
    };
    let _ = writeln!(out, "overflow:{tag}");
}

fn write_div0_behavior(out: &mut String, behavior: Div0Behavior) {
    let tag = match behavior {
        Div0Behavior::Error => "Error",
        Div0Behavior::Allow => "Allow",
    };
    let _ = writeln!(out, "div0:{tag}");
}

fn write_bitshift_behavior(out: &mut String, behavior: BitshiftBehavior) {
    let tag = match behavior {
        BitshiftBehavior::Error => "Error",
        BitshiftBehavior::Allow => "Allow",
    };
    let _ = writeln!(out, "bitshift:{tag}");
}

fn write_invariant_mask(out: &mut String, mask: &InvariantMask) {
    match mask {
        InvariantMask::Any => {
            let _ = writeln!(out, "invariant_mask:Any");
        }
        InvariantMask::None => {
            let _ = writeln!(out, "invariant_mask:None");
        }
        InvariantMask::Namespaces(ns) => {
            let mut sorted = ns.clone();
            sorted.sort();
            let _ = writeln!(
                out,
                "invariant_mask:Namespaces({})",
                sorted
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            );
        }
    }
}

fn write_variable_decl(out: &mut String, var: &VariableDecl) {
    let VariableDecl {
        name: _,
        ty: _,
        bounded_len: _,
    } = var;
    let _ = writeln!(
        out,
        "var:{}:{}:bounded_len={}",
        var.name,
        var.ty.to_type_string(),
        var.bounded_len
    );
}

fn write_function_context(out: &mut String, fc: &FunctionContext) {
    let FunctionContext {
        name: _,
        params: _,
        return_type: _,
        is_recursive: _,
        mode: _,
        trait_bounds: _,
    } = fc;
    let _ = writeln!(out, "fn:{}", fc.name());
    let _ = writeln!(out, "  recursive:{}", fc.is_recursive());
    let _ = writeln!(out, "  mode:{:?}", fc.mode());
    let _ = writeln!(out, "  return:{}", fc.return_type().to_type_string());
    let _ = writeln!(out, "  params:{}", fc.params().len());
    for (name, ty) in fc.params() {
        let _ = writeln!(out, "    {}:{}", name, ty.to_type_string());
    }
    let _ = writeln!(out, "  bounds:{}", fc.trait_bounds().len());
    for bound in fc.trait_bounds() {
        let TraitBound {
            type_param: _,
            trait_name: _,
        } = bound;
        let _ = writeln!(out, "    {}:{}", bound.type_param, bound.trait_name);
    }
}

fn write_obligation(out: &mut String, obligation: &PreparedObligation) {
    let PreparedObligation {
        name: _,
        kind: _,
        location: _,
        condition_origin: _,
        bound_vars: _,
        trigger_patterns: _,
        prepared_triggers: _,
        solver_mode: _,
        is_opaque: _,
        is_inline: _,
        broadcast_group: _,
        condition: _,
        expr: _,
        invariant_namespace: _,
        trigger_inference_mode: _,
        broadcast_guard: _,
        raw_broadcast_guard_count: _,
        step_meta: _,
    } = obligation;
    let _ = writeln!(out, "obl:{}", obligation.name);
    write_obligation_kind(out, obligation.kind);
    let _ = writeln!(out, "  loc:{:?}", obligation.location);
    write_condition_origin(out, obligation.condition_origin);
    let _ = writeln!(out, "  opaque:{}", obligation.is_opaque);
    let _ = writeln!(out, "  inline:{}", obligation.is_inline);
    let _ = writeln!(out, "  broadcast_group:{:?}", obligation.broadcast_group);
    let _ = writeln!(out, "  invariant_ns:{:?}", obligation.invariant_namespace);
    write_solver_mode(out, obligation.solver_mode);
    write_trigger_inference_mode(out, obligation.trigger_inference_mode);
    let _ = writeln!(
        out,
        "  raw_broadcast_guard_count:{}",
        obligation.raw_broadcast_guard_count
    );

    match &obligation.bound_vars {
        Some(vars) => {
            let _ = writeln!(out, "  bound_vars:{}", vars.join(","));
        }
        None => {
            let _ = writeln!(out, "  bound_vars:none");
        }
    }

    match &obligation.trigger_patterns {
        Some(groups) => {
            let _ = writeln!(out, "  trigger_groups:{}", groups.len());
            for group in groups {
                let _ = writeln!(out, "    [{}]", group.join(";"));
            }
        }
        None => {
            let _ = writeln!(out, "  trigger_groups:none");
        }
    }

    if let Some(ref groups) = obligation.prepared_triggers {
        let _ = writeln!(out, "  prepared_triggers:{}", groups.len());
        for group in groups {
            let _ = writeln!(out, "    group:{}", group.len());
            for trigger in group {
                let PreparedTrigger {
                    source: _,
                    expr: _,
                    head_symbol: _,
                } = trigger;
                let _ = writeln!(
                    out,
                    "      src:{} head:{:?}",
                    trigger.source, trigger.head_symbol
                );
                let _ = write!(out, "      expr:");
                write_expr(out, &trigger.expr);
                let _ = writeln!(out);
            }
        }
    }

    match &obligation.step_meta {
        Some(meta) => {
            let ProofStepMeta { key: _, label: _ } = meta;
            let _ = writeln!(out, "  step_meta:{}|{}", meta.key, meta.label);
        }
        None => {
            let _ = writeln!(out, "  step_meta:none");
        }
    }

    let _ = writeln!(out, "  condition:{}", obligation.condition);

    let _ = write!(out, "  expr:");
    write_expr(out, &obligation.expr);
    let _ = writeln!(out);

    match &obligation.broadcast_guard {
        Some(guard) => {
            let _ = write!(out, "  broadcast_guard:");
            write_expr(out, guard);
            let _ = writeln!(out);
        }
        None => {
            let _ = writeln!(out, "  broadcast_guard:none");
        }
    }
}

fn write_obligation_kind(out: &mut String, kind: ObligationKind) {
    let tag = match kind {
        ObligationKind::Assert => "Assert",
        ObligationKind::Assume => "Assume",
        ObligationKind::BroadcastAssume => "BroadcastAssume",
        ObligationKind::Requires => "Requires",
        ObligationKind::Ensures => "Ensures",
        ObligationKind::MeasureNonNegative => "MeasureNonNegative",
        ObligationKind::MeasureDecreases => "MeasureDecreases",
        ObligationKind::LoopInvariant => "LoopInvariant",
        ObligationKind::LoopGuard => "LoopGuard",
        ObligationKind::InvariantExceptBreak => "InvariantExceptBreak",
        ObligationKind::LoopEnsures => "LoopEnsures",
        ObligationKind::AssertBy => "AssertBy",
        ObligationKind::Reveal => "Reveal",
        ObligationKind::Hide => "Hide",
        ObligationKind::BroadcastUse => "BroadcastUse",
        ObligationKind::InvariantOpen => "InvariantOpen",
        ObligationKind::InvariantClose => "InvariantClose",
        ObligationKind::Recommends => "Recommends",
        ObligationKind::PostLoopAssume => "PostLoopAssume",
    };
    let _ = writeln!(out, "  kind:{tag}");
}

fn write_condition_origin(out: &mut String, origin: ConditionOrigin) {
    let tag = match origin {
        ConditionOrigin::LoweredFromCondition => "LoweredFromCondition",
        ConditionOrigin::TypedTrustVcExpr => "TypedTrustVcExpr",
        ConditionOrigin::PreBuiltExprCache => "PreBuiltExprCache",
        ConditionOrigin::LegacyTranslatedString => "LegacyTranslatedString",
    };
    let _ = writeln!(out, "  origin:{tag}");
}

fn write_solver_mode(out: &mut String, mode: Option<SolverMode>) {
    let tag = match mode {
        Some(SolverMode::Default) => "Default",
        Some(SolverMode::NonlinearArith) => "NonlinearArith",
        Some(SolverMode::BitVector) => "BitVector",
        Some(SolverMode::Compute) => "Compute",
        None => "none",
    };
    let _ = writeln!(out, "  solver_mode:{tag}");
}

fn write_trigger_inference_mode(
    out: &mut String,
    mode: Option<crate::trigger_inference::TriggerInferenceMode>,
) {
    let tag = match mode {
        Some(crate::trigger_inference::TriggerInferenceMode::Conservative) => "Conservative",
        Some(crate::trigger_inference::TriggerInferenceMode::Aggressive) => "Aggressive",
        None => "none",
    };
    let _ = writeln!(out, "  trigger_inference:{tag}");
}

fn write_trait_decl(out: &mut String, decl: &TraitDecl) {
    let TraitDecl {
        name: _,
        methods: _,
        supertraits: _,
        generics: _,
    } = decl;
    let _ = writeln!(out, "trait:{}", decl.name);
    // Emit supertraits in the fingerprint (unit 6): two trait decls differing
    // ONLY in their supertrait set produce different caller-side `requires`
    // obligations, so they must NOT collide on a stale cache entry.
    let _ = writeln!(out, "  supertraits:{}", decl.supertraits.len());
    for supertrait in &decl.supertraits {
        let _ = writeln!(out, "    {supertrait}");
    }
    let _ = writeln!(out, "  generics:{}", decl.generics.len());
    for generic in &decl.generics {
        let _ = writeln!(out, "    {generic}");
    }
    let _ = writeln!(out, "  methods:{}", decl.methods.len());
    for method in &decl.methods {
        let TraitMethodDecl {
            name: _,
            params: _,
            return_type: _,
            requires: _,
            ensures: _,
            has_default: _,
            default_body: _,
            default_ensures: _,
            generic_params: _,
        } = method;
        let _ = writeln!(out, "    method:{}", method.name);
        let _ = writeln!(out, "      return:{}", method.return_type.to_type_string());
        let _ = writeln!(out, "      has_default:{}", method.has_default);
        let _ = writeln!(out, "      default_body:{:?}", method.default_body);
        let _ = writeln!(out, "      params:{}", method.params.len());
        for (name, ty) in &method.params {
            let _ = writeln!(out, "        {}:{}", name, ty.to_type_string());
        }
        let _ = writeln!(out, "      requires:{}", method.requires.len());
        for r in &method.requires {
            let _ = writeln!(out, "        {r}");
        }
        let _ = writeln!(out, "      ensures:{}", method.ensures.len());
        for e in &method.ensures {
            let _ = writeln!(out, "        {e}");
        }
        let _ = writeln!(
            out,
            "      default_ensures:{}",
            method.default_ensures.len()
        );
        for e in &method.default_ensures {
            let _ = writeln!(out, "        {e}");
        }
        // H10 (method half): two declarations differing ONLY in the method's own
        // generic parameters lower differently — an uncarried one fails every
        // call closed — so they must not share a cache entry.
        let _ = writeln!(out, "      generic_params:{}", method.generic_params.len());
        for generic in &method.generic_params {
            let _ = writeln!(out, "        {generic}");
        }
    }
}

fn write_trait_impl_decl(out: &mut String, decl: &TraitImplDecl) {
    let TraitImplDecl {
        trait_name: _,
        concrete_type: _,
        method_bindings: _,
        assoc_type_bindings: _,
        is_external: _,
        trait_type_args: _,
        inherent_shadowed_methods: _,
        impl_group: _,
    } = decl;
    let _ = writeln!(
        out,
        "impl:{}:{}",
        decl.trait_name,
        decl.concrete_type.to_type_string()
    );
    let _ = writeln!(out, "  bindings:{}", decl.method_bindings.len());
    for (trait_method, concrete_fn) in &decl.method_bindings {
        let _ = writeln!(out, "    {trait_method}->{concrete_fn}");
    }
    // Associated-type bindings are semantic (they resolve `Self::X` in trait
    // method signatures), so they must participate in the cache key.
    let _ = writeln!(out, "  assoc_types:{}", decl.assoc_type_bindings.len());
    for (assoc_name, ty) in &decl.assoc_type_bindings {
        let _ = writeln!(out, "    {assoc_name}={}", ty.to_type_string());
    }
    let _ = writeln!(out, "  trait_type_args:{}", decl.trait_type_args.len());
    for ty in &decl.trait_type_args {
        let _ = writeln!(out, "    {}", ty.to_type_string());
    }
    // External impls skip body conformance (trusted specs) — semantic.
    let _ = writeln!(out, "  external:{}", decl.is_external);
    // SEMANTIC, and it must never be dropped from the key: a shadowed method
    // publishes NO linking axiom and NO concrete-sorted trait-ensures axiom, so
    // two otherwise-identical impls with different shadow sets encode to
    // different formulas. Omitting it would let a cached `Verified` from the
    // unshadowed encoding answer the shadowed one — reinstating the very false
    // verify the shadow set exists to close.
    let _ = writeln!(
        out,
        "  inherent_shadowed:{}",
        decl.inherent_shadowed_methods.len()
    );
    for method_name in &decl.inherent_shadowed_methods {
        let _ = writeln!(out, "    {method_name}");
    }
    // SEMANTIC for the same reason: a member of a sibling-impl group publishes
    // no linking / default-body / impl-ensures axiom and no concrete-receiver
    // resolution, and refuses its shared methods' conformance obligations.
    let _ = writeln!(
        out,
        "  impl_group:{}:{}",
        decl.impl_group.has_sibling_impl,
        decl.impl_group.shared_method_names.len()
    );
    for method_name in &decl.impl_group.shared_method_names {
        let _ = writeln!(out, "    {method_name}");
    }
}

fn write_conformance_method_body(out: &mut String, key: &str, body: &ConformanceMethodBody) {
    let ConformanceMethodBody {
        body_text: _,
        param_count: _,
    } = body;
    let _ = writeln!(out, "  body:{key}");
    let _ = writeln!(out, "    param_count:{}", body.param_count);
    let _ = writeln!(out, "    text:{}", body.body_text);
}

fn write_struct_def(out: &mut String, s: &StructDef) {
    let StructDef {
        name: _,
        fields: _,
        derived_partial_eq,
        derived_clone,
    } = s;
    let _ = writeln!(out, "struct:{}", s.name);
    // Derives affect `.eq()`/`.clone()` lowering, so they are part of the key.
    let _ = writeln!(
        out,
        "  derives:eq={derived_partial_eq},clone={derived_clone}"
    );
    let _ = writeln!(out, "  fields:{}", s.fields.len());
    for (name, ty) in &s.fields {
        let _ = writeln!(out, "    {}:{}", name, ty.to_type_string());
    }
}
