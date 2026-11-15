//! Typed encoder setup shared by assertion, vacuous-truth, and performance paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, HashSet};

use ay_dpll::api::{Logic, Term};

use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::{DatatypeVariant, TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};
use crate::ir_lowering::infer_expr_type;
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{ObligationKind, VariableDecl};

use super::VerificationSlices;

#[path = "setup_broadcasts.rs"]
pub(crate) mod setup_broadcasts;

const SETUP_CONTEXT: &str = "set up typed verification encoder";

fn current_state_var_terms(variables: &std::collections::HashMap<String, Term>) -> Vec<Term> {
    variables
        .iter()
        .filter(|(name, _)| !name.contains(super::PRE_STATE_SUFFIX))
        .map(|(_, &term)| term)
        .collect()
}

fn setup_encoding_error(detail: impl Into<String>) -> crate::error::TrustVcError {
    super::encoding_error(SETUP_CONTEXT, detail)
}

#[derive(Default)]
struct DatatypeUsageCollector {
    datatypes: BTreeMap<String, Vec<DatatypeVariant>>,
    conflicts: Vec<String>,
}

impl DatatypeUsageCollector {
    fn collect_expr(&mut self, expr: &TrustVcExpr) {
        self.visit_expr(expr);
    }

    fn collect_obligation(&mut self, obligation: &PreparedObligation) {
        self.collect_expr(&obligation.expr);
        if let Some(ref guard) = obligation.broadcast_guard {
            self.collect_expr(guard);
        }
        if let Some(ref trigger_groups) = obligation.prepared_triggers {
            for trigger in trigger_groups.iter().flatten() {
                self.collect_expr(&trigger.expr);
            }
        }
    }

    fn collect_type(&mut self, ty: &TrustVcType) {
        match ty {
            TrustVcType::Seq(inner)
            | TrustVcType::Array(inner, _)
            | TrustVcType::Set(inner)
            | TrustVcType::Multiset(inner) => self.collect_type(inner),
            TrustVcType::Map(key, value) => {
                self.collect_type(key);
                self.collect_type(value);
            }
            TrustVcType::SpecFn(args, ret) => {
                for arg in args {
                    self.collect_type(arg);
                }
                self.collect_type(ret);
            }
            TrustVcType::Datatype { name, variants } => {
                match self.datatypes.get(name) {
                    Some(existing) if existing != variants => {
                        self.conflicts.push(format!(
                            "Datatype '{name}' has conflicting variant metadata"
                        ));
                    }
                    Some(_) => {}
                    None => {
                        self.datatypes.insert(name.clone(), variants.clone());
                    }
                }
                for variant in variants {
                    for (_, field_ty) in &variant.fields {
                        self.collect_type(field_ty);
                    }
                }
            }
            _ => {}
        }
    }
}

impl TrustVcExprVisitor for DatatypeUsageCollector {
    fn visit_expr(&mut self, expr: &TrustVcExpr) {
        self.collect_type(&infer_expr_type(expr));
        match expr {
            TrustVcExpr::Let { ty, .. } => self.collect_type(ty),
            TrustVcExpr::Cast { from_ty, to_ty, .. } => {
                self.collect_type(from_ty);
                self.collect_type(to_ty);
            }
            TrustVcExpr::Quantifier { bound_vars, .. } => {
                for (_, ty) in bound_vars {
                    self.collect_type(ty);
                }
            }
            TrustVcExpr::SpecClosure { params, ty, .. } => {
                for (_, param_ty) in params {
                    self.collect_type(param_ty);
                }
                self.collect_type(ty);
            }
            TrustVcExpr::FnCall { return_ty, .. }
            | TrustVcExpr::IntConst { ty: return_ty, .. }
            | TrustVcExpr::ReadPlace { ty: return_ty, .. }
            | TrustVcExpr::ProphecyNew { ty: return_ty, .. } => {
                self.collect_type(return_ty);
            }
            _ => {}
        }
        walk_expr(self, expr);
    }
}

fn register_datatypes_from_prepared_context(
    encoder: &mut AYEncoder,
    ctx: &PreparedVerificationContext,
    extra_variables: &[VariableDecl],
) -> TrustVcResult<()> {
    let mut collector = DatatypeUsageCollector::default();

    for variable in ctx.variables.iter().chain(extra_variables.iter()) {
        collector.collect_type(&variable.ty);
    }
    for scoped_variables in ctx.forall_bound_vars.values() {
        for variable in scoped_variables {
            collector.collect_type(&variable.ty);
        }
    }
    if let Some(ref function_context) = ctx.function_context {
        for (_, param_ty) in &function_context.params {
            collector.collect_type(param_ty);
        }
        collector.collect_type(&function_context.return_type);
    }
    for helper_context in &ctx.helper_function_contexts {
        for (_, param_ty) in &helper_context.params {
            collector.collect_type(param_ty);
        }
        collector.collect_type(&helper_context.return_type);
    }
    for trait_decl in &ctx.trait_decls {
        for method in &trait_decl.methods {
            for (_, param_ty) in &method.params {
                collector.collect_type(param_ty);
            }
            collector.collect_type(&method.return_type);
        }
    }
    for trait_impl in &ctx.trait_impl_decls {
        collector.collect_type(&trait_impl.concrete_type);
    }
    for struct_def in &ctx.struct_types {
        collector.collect_type(&struct_def.to_datatype_type());
    }
    for invariant_body in ctx.type_invariants.values() {
        collector.collect_expr(invariant_body);
    }
    for obligation in &ctx.obligations {
        collector.collect_obligation(obligation);
    }
    for scoped_obligations in ctx.assert_by_scopes.values() {
        for obligation in scoped_obligations {
            collector.collect_obligation(obligation);
        }
    }

    if !collector.conflicts.is_empty() {
        return Err(setup_encoding_error(collector.conflicts.join("; ")));
    }

    // DEPENDENCY ORDER is load-bearing (same ay guard the struct loop in
    // `bootstrap_prepared` documents): declaring an OUTER datatype introduces
    // the sorts of its field types, and ay refuses to later re-declare such a
    // sort as a datatype ("sort 'Option<u64>' is already declared; re-declaring
    // it as a datatype would conflate ..."). The collector is a name-keyed
    // BTreeMap, so `Option<Option<u64>>` sorts BEFORE `Option<u64>` and
    // `(Option<u64>, bool)` before `Option<u64>` — registering in map order
    // declared the outer first and every nested Option/Result/tuple payload
    // (clone_method_spec `clone_nested_option` / `clone_tuple_option`) failed
    // setup. `register_datatypes_in_type` walks a datatype's fields before the
    // datatype itself and is idempotent per name, so it is the ordering
    // authority here too.
    for (name, variants) in collector.datatypes {
        let ty = TrustVcType::Datatype {
            name: name.clone(),
            variants,
        };
        encoder.register_datatypes_in_type(&ty).map_err(|err| {
            setup_encoding_error(format!("Failed to register datatype '{name}': {err}"))
        })?;
    }

    Ok(())
}

pub(in crate::encoder) struct BootstrapPreparedConfig<'a> {
    pub active_broadcasts: &'a [&'a PreparedObligation],
    pub active_assumptions: &'a [&'a PreparedObligation],
    pub verified_invariants: &'a [&'a PreparedObligation],
    pub verified_assert_by: &'a [&'a PreparedObligation],
    pub scoped_assumptions: &'a [&'a PreparedObligation],
    pub use_int_for_measures: bool,
    pub extra_variables: &'a [VariableDecl],
    pub assertion_focus: Option<&'a PreparedObligation>,
    pub enable_current_state_variable_slice: bool,
    pub inline_overrides: &'a [String],
    /// F3 point-interval length pinning gate. `true` only for the
    /// current-state setup path where the scanned assumptions are asserted
    /// verbatim; MUST be `false` in post-loop mode (assumptions are rewritten
    /// to pre-state variables, so an entry-fact pin on the current-state name
    /// would survive a loop that modifies the sequence — unsound) and for
    /// invariant bootstraps that supply their own assumption sets later.
    pub allow_finite_len_pins: bool,
}

/// F3 (point-interval length folding): pre-scan the assumption set this
/// encoder is about to assert for top-level length pins
/// (`assumption::finite_len_pin_binding` — `s == <finite chain>` /
/// `s.len() == N`), recording them for `declare_variable` to register the
/// Int literal directly.
///
/// SOUNDNESS: only obligations that WILL be asserted into this same encoder
/// are scanned (the caller passes the identical slice + pruning selection the
/// assumption-encoding loop uses), and only positive assumption kinds. Each
/// pin is therefore entailed by this query's own assumption set: every model
/// of the context has `s.len() == n`, so registering the literal changes no
/// verdict — it only removes the symbolic-length indirection ay cannot
/// decide. On conflicting pins (contradictory user bindings) the FIRST wins;
/// the second binding's length equality then encodes as a folded-`false`
/// conjunct, honestly surfacing the inconsistent context. Pins are keyed to
/// declared Seq variables only (checked at the `declare_variable` consumer).
fn collect_finite_len_pins(
    encoder: &mut AYEncoder,
    ctx: &PreparedVerificationContext,
    obligations: &[&PreparedObligation],
    selected_indices: Option<&[usize]>,
) {
    let mut scan = |obligation: &PreparedObligation| {
        if !matches!(
            obligation.kind,
            ObligationKind::Assume | ObligationKind::PostLoopAssume
        ) {
            return;
        }
        let Some((name, len)) = super::assumption::finite_len_pin_binding(&obligation.expr) else {
            return;
        };
        // Seq variables only (narrow F3 scope): fixed arrays already carry a
        // static length pin, and Set/Map cardinalities keep the incumbent
        // post-encode replacement path.
        if !ctx
            .variables
            .iter()
            .any(|var| var.name == name && matches!(var.ty, crate::ir::TrustVcType::Seq(_)))
        {
            return;
        }
        encoder.state.pinned_seq_lens.entry(name).or_insert(len);
    };
    if let Some(indices) = selected_indices {
        for &index in indices {
            if let Some(obligation) = obligations.get(index) {
                scan(obligation);
            }
        }
    } else {
        for obligation in obligations {
            scan(obligation);
        }
    }
}

fn encode_selected_obligations(
    encoder: &mut AYEncoder,
    obligations: &[&PreparedObligation],
    selected_indices: Option<&[usize]>,
    mut encode_one: impl FnMut(&mut AYEncoder, &PreparedObligation) -> TrustVcResult<()>,
) -> TrustVcResult<()> {
    if let Some(indices) = selected_indices {
        for &index in indices {
            let obligation = obligations.get(index).copied().ok_or_else(|| {
                setup_encoding_error(format!(
                    "Selected obligation index {index} out of range for {} obligations",
                    obligations.len()
                ))
            })?;
            encode_one(encoder, obligation)?;
        }
    } else {
        for obligation in obligations {
            encode_one(encoder, obligation)?;
        }
    }
    Ok(())
}

/// Names of every function applied inside a `Choose` predicate (the
/// `condition` and the multi-binder `also_assert` combined axiom) across the
/// prepared obligations and the assumption slices this bootstrap will encode.
/// See the suppression call site for why these must stay uninterpreted UFs.
fn choose_predicate_function_names(
    ctx: &PreparedVerificationContext,
    active_assumptions: &[&PreparedObligation],
    scoped_assumptions: &[&PreparedObligation],
) -> std::collections::BTreeSet<String> {
    struct ChooseFnCollector {
        names: std::collections::BTreeSet<String>,
    }
    impl crate::ir_expr_traversal::TrustVcExprVisitor for ChooseFnCollector {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if let TrustVcExpr::Choose {
                condition,
                also_assert,
                ..
            } = expr
            {
                self.names
                    .extend(super::body_support::referenced_function_names(condition));
                // The shared walker does not descend into `also_assert`;
                // visit it explicitly — the combined axiom is exactly where
                // the multi-binder predicate's fn calls live.
                if let Some(extra) = also_assert {
                    self.names
                        .extend(super::body_support::referenced_function_names(extra));
                    crate::ir_expr_traversal::walk_expr(self, extra);
                }
            }
            crate::ir_expr_traversal::walk_expr(self, expr);
        }
    }
    let mut collector = ChooseFnCollector {
        names: std::collections::BTreeSet::new(),
    };
    for obligation in ctx
        .obligations
        .iter()
        .chain(active_assumptions.iter().copied())
        .chain(scoped_assumptions.iter().copied())
    {
        crate::ir_expr_traversal::TrustVcExprVisitor::visit_expr(&mut collector, &obligation.expr);
    }
    collector.names
}

fn bootstrap_prepared_encoder_with_prune_plan(
    encoder: &mut AYEncoder,
    ctx: &PreparedVerificationContext,
    config: BootstrapPreparedConfig<'_>,
    prune_plan: &super::pruning::PrunePlan,
) -> TrustVcResult<()> {
    let BootstrapPreparedConfig {
        active_broadcasts,
        active_assumptions,
        scoped_assumptions,
        use_int_for_measures,
        extra_variables,
        inline_overrides,
        enable_current_state_variable_slice,
        assertion_focus,
        allow_finite_len_pins,
        ..
    } = config;
    let prune_traits = assertion_focus.is_some();

    // ELEMENT-DEMAND PRUNE (see `pruning::context_element_demand`). Install the
    // query-wide length-vs-elements verdict BEFORE any variable declaration or
    // assumption encoding, so every derived Seq carrier this encoder mints
    // observes it. `VerificationState::new` defaults the flag to `true`, so any
    // encoder that never runs this bootstrap keeps the full model.
    encoder.state.seq_element_model_demanded = matches!(
        prune_plan.element_demand(),
        super::pruning::ElementDemand::Observed
    );

    let current_state_slice = if enable_current_state_variable_slice {
        prune_plan.current_state_slice()
    } else {
        None
    };

    // F3 point-interval pins — must run BEFORE the variable declaration loop
    // so `declare_variable` can register pinned Seq lengths as Int literals.
    // Scans exactly the assumption sets (with the identical pruning
    // selection) that `setup_from_prepared_*` asserts into this encoder.
    if allow_finite_len_pins {
        collect_finite_len_pins(
            encoder,
            ctx,
            active_assumptions,
            current_state_slice.map(|slice| slice.selected_regular_assumptions.as_slice()),
        );
        collect_finite_len_pins(
            encoder,
            ctx,
            scoped_assumptions,
            current_state_slice.map(|slice| slice.selected_scoped_assumptions.as_slice()),
        );
    }
    // Hilbert-`choose` trigger preservation: a spec fn referenced inside a
    // choose predicate is the E-matching TRIGGER of that choose's guarded /
    // combined axiom (PATH-B marks those axioms `no_mbqi` — fire only on a
    // genuine ground witness). AY's definitional-forall macro adoption would
    // otherwise expand the fn's defining axiom into every application — the
    // marked axiom's body AND the ground witness (`assert(f(7))` becomes the
    // dropped truth `5 <= 7`) — leaving the discipline nothing to match, so a
    // Verus-verified case (choose.rs `test1`) degraded to
    // `quantifier-unhandled`. Suppression costs only the adoption
    // optimization: the defining axiom stays asserted verbatim, so `f(7)`
    // stays an f-application and both axioms fire exactly as in Verus.
    for name in choose_predicate_function_names(ctx, active_assumptions, scoped_assumptions) {
        encoder.solver.suppress_definitional_adoption(&name);
    }
    encoder.state.inline_bodies = active_broadcasts
        .iter()
        .filter_map(|broadcast| {
            super::body_support::extracted_inline_body_axiom(broadcast).map(|body_axiom| {
                (
                    body_axiom.function_name,
                    (
                        body_axiom.param_names,
                        body_axiom.param_types,
                        body_axiom.body,
                    ),
                )
            })
        })
        .collect();

    // Demand-inline overrides: promote non-inline body axioms to inline for
    // this encoder only. The override is attempt-local — it does not mutate
    // the source obligation. Part of #2655.
    encoder.state.demand_inline_overrides_active = !inline_overrides.is_empty();
    if !inline_overrides.is_empty() {
        for broadcast in active_broadcasts {
            if let Some(body_axiom) = super::body_support::extracted_body_axiom(broadcast) {
                if inline_overrides.contains(&body_axiom.function_name)
                    && !encoder
                        .state
                        .inline_bodies
                        .contains_key(&body_axiom.function_name)
                {
                    encoder.state.inline_bodies.insert(
                        body_axiom.function_name,
                        (
                            body_axiom.param_names,
                            body_axiom.param_types,
                            body_axiom.body,
                        ),
                    );
                    encoder.state.demand_inlined_bodies = true;
                }
            }
        }
    }
    // Hide gating for inline spec functions: an `#[inline]` spec fn has no
    // live body axiom to suppress — its body is substituted at every call site
    // — so `hide!(f)` must instead strip it from the substitution map. The
    // function then encodes as a plain UF (its name is no longer in
    // `inline_names`, so `register_function_context` declares it) with no
    // defining axiom: strictly uninterpreted, exactly like an unrevealed
    // opaque fn. Reveal wins over hide, mirroring the broadcast gate in
    // `setup_broadcasts.rs`. Demand-inline overrides are unaffected: the
    // catalog they draw from already excludes hidden-unrevealed bodies.
    if !ctx.hidden_fns.is_empty() {
        let hidden_unrevealed: Vec<String> = encoder
            .state
            .inline_bodies
            .keys()
            .filter(|name| {
                super::body_support::fn_name_named_in(name, &ctx.hidden_fns)
                    && !super::body_support::fn_name_named_in(name, &ctx.revealed_fns)
            })
            .cloned()
            .collect();
        for name in hidden_unrevealed {
            encoder.state.inline_bodies.remove(&name);
        }
    }
    let inline_names: HashSet<String> = encoder.state.inline_bodies.keys().cloned().collect();
    encoder.state.overflow_behavior = ctx.overflow_behavior;
    encoder.state.div0_behavior = ctx.div0_behavior;
    encoder.state.bitshift_behavior = ctx.bitshift_behavior;
    let mut declared_variables: Vec<&VariableDecl> = ctx
        .variables
        .iter()
        .filter(|var| match current_state_slice {
            Some(slice) => slice.reachable_variables.contains(&var.name),
            None => true,
        })
        .collect();
    declared_variables.extend(extra_variables.iter());

    // Register user-defined struct types as single-variant datatypes.
    //
    // ORDERING IS LOAD-BEARING (ay 0.4.0). This must precede variable
    // declaration and trait/impl registration, not merely
    // `register_builtin_datatypes` and assumption encoding. Declaring a
    // variable or impl over a user struct `S` introduces the sort `S`, and
    // ay 0.4.0 rejects a later datatype declaration for an already-declared
    // sort:
    //
    //   sort 'S' is already declared; re-declaring it as a datatype would
    //   conflate existing symbols over the old sort with the new datatype's
    //   members
    //
    // That guard is correct — conflating opaque-sort symbols with datatype
    // members is exactly the confusion it names — so the fix is to declare the
    // datatype FIRST and let everything downstream resolve against it, rather
    // than to weaken the check. Under ay 0.3.0 the collision was silent, which
    // is why this ordering was not previously forced.
    // DEPENDENCY ORDER within this loop is load-bearing for the same reason:
    // registering an OUTER struct introduces the sorts of its field types, so a
    // struct that appears as another's field must be declared as a datatype
    // FIRST or its own registration collides with the sort the outer one
    // created. Emit each struct after every in-context struct it references.
    let struct_order = {
        let names: std::collections::BTreeSet<&str> =
            ctx.struct_types.iter().map(|d| d.name.as_str()).collect();
        let mut emitted: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut order: Vec<&crate::ir::StructDef> = Vec::with_capacity(ctx.struct_types.len());
        // Bounded fixpoint: each pass emits every struct whose in-context
        // dependencies are already out. A cycle (mutually recursive structs)
        // stops making progress, and the remainder is emitted in declaration
        // order — no worse than the previous unordered behaviour.
        loop {
            let before = order.len();
            for def in &ctx.struct_types {
                if emitted.contains(&def.name) {
                    continue;
                }
                let ready = def.fields.iter().all(|(_, ty)| {
                    let dep = ty.to_type_string();
                    !names.contains(dep.as_str()) || dep == def.name || emitted.contains(&dep)
                });
                if ready {
                    emitted.insert(def.name.clone());
                    order.push(def);
                }
            }
            if order.len() == before {
                break;
            }
        }
        for def in &ctx.struct_types {
            if !emitted.contains(&def.name) {
                order.push(def);
            }
        }
        order
    };

    for struct_def in struct_order {
        let dt_type = struct_def.to_datatype_type();
        if matches!(dt_type, crate::ir::TrustVcType::Datatype { .. }) {
            // Register through the type walker rather than calling
            // `register_datatype` directly: declaring a datatype also
            // introduces its FIELD sorts, so a struct carrying a datatype-typed
            // field (a tuple carrier such as `(u64, u64)`, say) would introduce
            // that field's sort as opaque here and make the later datatype
            // declaration for it fail under ay 0.4.0. The walker declares
            // fields innermost-first, and is idempotent.
            encoder
                .register_datatypes_in_type(&dt_type)
                .map_err(|err| {
                    setup_encoding_error(format!(
                        "Failed to register struct type '{}': {}",
                        struct_def.name, err
                    ))
                })?;
        }
    }

    // Same ay 0.4.0 ordering constraint as the struct block above, for datatypes
    // that are not user structs: a GENERIC or ASSOCIATED-TRAIT type (e.g. an
    // associated type resolving to `Option<u8>`) has its sort introduced by
    // variable declaration or by `register_trait`, and a later datatype
    // declaration for that sort is then rejected. Register them first.
    register_datatypes_from_prepared_context(encoder, ctx, extra_variables)?;

    for var in &declared_variables {
        let var = *var;
        if use_int_for_measures {
            // Nat keeps its own type tag: it is already Int-sorted, and
            // `declare_variable` asserts its `>= 0` invariant natively.
            // Re-tagging Nat as MathInt made every IR expression that
            // references the variable (typed Nat by the lowering env) fail
            // `encode_var`'s IR-vs-context type consistency check in
            // by(nonlinear_arith) / measure queries (#2778).
            let declared_ty = match &var.ty {
                crate::ir::TrustVcType::Int { .. }
                | crate::ir::TrustVcType::Uint { .. }
                | crate::ir::TrustVcType::MathInt => crate::ir::TrustVcType::MathInt,
                other => other.clone(),
            };
            let adjusted_var = VariableDecl {
                name: var.name.clone(),
                ty: declared_ty,
                // Preserve the Vec/slice/array length-boundedness bit through the
                // int-measure re-tag (only Int/Uint/MathInt scalars are re-tagged;
                // a collection keeps its type and its bound).
                bounded_len: var.bounded_len,
            };
            encoder.declare_variable(&adjusted_var)?;
        } else {
            encoder.declare_variable(var)?;
        }
    }

    // Populate counterexample display metadata from prepared context.
    // Explicit aliases registered via register_counterexample_alias() take
    // precedence; defaults from the classifier fill in the rest. Part of #2651.
    for var in &declared_variables {
        if !ctx.counterexample_var_meta.contains_key(&var.name) {
            encoder.counterexample_var_meta.insert(
                var.name.clone(),
                crate::counterexample_names::default_meta(&var.name),
            );
        } else {
            encoder.counterexample_var_meta.insert(
                var.name.clone(),
                ctx.counterexample_var_meta[&var.name].clone(),
            );
        }
    }

    if use_int_for_measures {
        // Type-range invariants for Int-sorted query variables (#2778).
        //
        // In Int-arithmetic mode (`by(nonlinear_arith)` queries and
        // measure/termination checks) every fixed-width integer variable is
        // re-declared on the unbounded Int sort, losing its Rust type's value
        // range. Verus injects the exact range invariant of each query
        // variable's type as a query hypothesis; without the upper bounds,
        // bounded-product goals (upstream `nonlinear.rs` test5/test6) are
        // unprovable over unconstrained Int variables. Each bound below is a
        // true fact about every value the source variable can hold, so adding
        // it can never prove a statement that is false of the source program:
        //   * `uN`  →  0 <= x < 2^N
        //   * `iN`  →  -2^(N-1) <= x < 2^(N-1)
        //   * `char` →  0 <= x < 2^32 (chars are a subset of u32 values)
        //   * `nat` →  0 <= x
        for var in &declared_variables {
            let var = *var;
            let Some(&var_term) = encoder.variables.get(&var.name) else {
                continue;
            };
            let (lower, upper_exclusive) = match (&var.ty, var.ty.bit_width()) {
                (_, Some(width)) if width > 0 && var.ty.is_unsigned() => (
                    num_bigint::BigInt::from(0u8),
                    Some(num_bigint::BigInt::from(1u8) << width),
                ),
                (crate::ir::TrustVcType::Int { .. }, Some(width)) if width > 0 => (
                    -(num_bigint::BigInt::from(1u8) << (width - 1)),
                    Some(num_bigint::BigInt::from(1u8) << (width - 1)),
                ),
                (crate::ir::TrustVcType::Nat, _) => (num_bigint::BigInt::from(0u8), None),
                _ => continue,
            };
            let lower_term = encoder.solver.int_const_bigint(&lower);
            let ge_lower = encoder.solver.try_ge(var_term, lower_term).map_err(|e| {
                setup_encoding_error(format!(
                    "Failed to build type-range lower bound for {}: {}",
                    var.name, e
                ))
            })?;
            encoder.solver.try_assert_term(ge_lower).map_err(|e| {
                setup_encoding_error(format!(
                    "Failed to assert type-range lower bound for {}: {}",
                    var.name, e
                ))
            })?;
            if let Some(upper) = upper_exclusive {
                let upper_term = encoder.solver.int_const_bigint(&upper);
                let lt_upper = encoder.solver.try_lt(var_term, upper_term).map_err(|e| {
                    setup_encoding_error(format!(
                        "Failed to build type-range upper bound for {}: {}",
                        var.name, e
                    ))
                })?;
                encoder.solver.try_assert_term(lt_upper).map_err(|e| {
                    setup_encoding_error(format!(
                        "Failed to assert type-range upper bound for {}: {}",
                        var.name, e
                    ))
                })?;
            }
        }
    }

    if let Some(ref func_ctx) = ctx.function_context {
        if inline_names.contains(func_ctx.name.as_str()) {
            encoder.register_function_context_metadata_only(func_ctx)?;
        } else {
            encoder.register_function_context(func_ctx)?;
        }
    }

    // Register typed helper function contexts. Inline helpers keep their
    // type metadata but skip ay UF declaration because calls are substituted
    // before encoding. Part of #2431, #2488.
    for helper_ctx in &ctx.helper_function_contexts {
        if !prune_plan.is_helper_reachable(&helper_ctx.name) {
            continue;
        }
        if inline_names.contains(helper_ctx.name.as_str()) {
            encoder.register_function_context_metadata_only(helper_ctx)?;
        } else {
            encoder.register_function_context(helper_ctx)?;
        }
    }

    for trait_decl in &ctx.trait_decls {
        if prune_traits && !prune_plan.is_trait_reachable(trait_decl) {
            continue;
        }
        encoder.register_trait(trait_decl).map_err(|err| {
            setup_encoding_error(format!(
                "Failed to register trait '{}' from prepared context: {}",
                trait_decl.name, err
            ))
        })?;
    }

    // Register per-impl linking axioms. Must happen after trait declarations
    // and after function contexts (which provide concrete impl functions).
    // Skip impls with opaque concrete types — these are struct types that the
    // encoder has no ay representation for. Part of #2425.
    let collided_groups = crate::trait_impl_groups::collided_group_members(&ctx.trait_impl_decls);
    for (impl_decl, collided) in ctx.trait_impl_decls.iter().zip(collided_groups) {
        if impl_decl.concrete_type.contains_opaque()
            || (prune_traits && !prune_plan.is_trait_impl_reachable(impl_decl, &ctx.trait_decls))
        {
            continue;
        }
        // SIBLING-IMPL GROUP (`crate::trait_impl_groups`): another impl of this
        // trait exists for this self type, and every axiom below is keyed by
        // (trait, erased self type) — `Tr__m(Box_S(s))`, `S__m` — with no way to
        // say WHICH impl it describes. Publishing them lets one impl's body,
        // default or impl `ensures` answer a call to its sibling, or asserts two
        // incompatible definitions of one term. Publish NOTHING for the group;
        // the trait's own postcondition axioms (justified per impl by
        // conformance) are untouched, and concrete-receiver resolution for the
        // group is withheld in lockstep (`prepared_context::type_env`).
        if collided {
            continue;
        }
        encoder.register_trait_impl(impl_decl).map_err(|err| {
            setup_encoding_error(format!(
                "Failed to register trait impl '{}' for {}: {}",
                impl_decl.trait_name,
                impl_decl.concrete_type.to_type_string(),
                err
            ))
        })?;

        // Propagate the impl methods' OWN declared `ensures` to concrete/UFCS
        // callers as a `Box_S`-guarded postcondition axiom. Sound only because the
        // conformance-extension (which runs after the main verification) proves
        // `body ⊨ impl_ensures` — so never for an external impl, which that pass
        // skips. The clauses are positional (`__trust_vc_conf_arg_{i}`), bound by
        // the captured bodies' arity. The boxed-self guard discriminates impls of
        // DIFFERENT self types only: `Box_S` carries neither the trait arguments
        // nor the self type's references, which is why a sibling-impl group was
        // skipped above; for every other impl no single-impl gating is needed.
        encoder
            .assert_impl_postcondition_axioms(
                impl_decl,
                &ctx.trait_impl_method_ensures,
                &ctx.trait_impl_method_bodies,
            )
            .map_err(|err| {
                setup_encoding_error(format!(
                    "Failed to propagate impl ensures for '{}' on {}: {}",
                    impl_decl.trait_name,
                    impl_decl.concrete_type.to_type_string(),
                    err
                ))
            })?;

        // Propagate the TRAIT method `ensures` for associated-type-returning
        // methods to concrete-receiver callers, bound to the per-impl concrete
        // function with the projection resolved to its concrete sort (Phase A3
        // assoc-spec-fn client seam). Sound ONLY because the per-impl conformance
        // pass proves `body ⊨ trait_ensures` at exactly these sorts; a
        // non-conforming impl is refuted on its own conformance obligation.
        if let Some(trait_decl) = ctx
            .trait_decls
            .iter()
            .find(|decl| decl.name == impl_decl.trait_name)
        {
            encoder
                .assert_impl_trait_ensures_concrete_axioms(trait_decl, impl_decl)
                .map_err(|err| {
                    setup_encoding_error(format!(
                        "Failed to propagate associated-type trait ensures for '{}' on {}: {}",
                        impl_decl.trait_name,
                        impl_decl.concrete_type.to_type_string(),
                        err
                    ))
                })?;
        }
    }

    // Auto-register datatype UF symbols for Datatype-typed variables and for
    // datatypes that appear only inside prepared expressions. The expression
    // scan matters for constructor/tester calls such as `Some(1).is_some()`,
    // where no top-level variable carries the datatype. Must happen before
    // assumptions are encoded so those symbols are available to the encoder.
    // Part of #1942 Slice 4.
    // Idempotent re-run: everything reachable was already registered early (see
    // the ordering block above). Kept so any datatype introduced by the
    // intervening registration steps is still picked up.
    register_datatypes_from_prepared_context(encoder, ctx, extra_variables)?;
    encoder.register_builtin_datatypes()?;

    // Emit type invariant UFs and their defining axioms. Must happen after
    // datatype registration so selector functions are available for the
    // invariant body encoding. Part of #2419 Slice 2.
    for (type_name, invariant_body) in &ctx.type_invariants {
        encoder
            .emit_type_invariant(type_name, invariant_body)
            .map_err(|err| {
                setup_encoding_error(format!(
                    "Failed to emit type invariant for '{}': {}",
                    type_name, err
                ))
            })?;
    }

    // Assert type invariants on PARAMETERS of invariant-bearing types.
    // Part of #2419 Slice 2.
    //
    // SOUNDNESS-CRITICAL — the restriction to parameters is the whole
    // justification. `assert_type_invariant_on_term` asserts `inv_T(v)` as a
    // FREE axiom, i.e. an assumption that `v` satisfies its type invariant.
    // That is legitimate only for a value whose invariant somebody else already
    // ESTABLISHED: a parameter arrives from a caller that had to build it, so
    // assuming it here is the callee half of a contract. There is currently NO
    // establishment obligation anywhere, so for any value this function itself
    // CONSTRUCTS the same assertion is an unchecked assumption — and a locally
    // built value that violates its invariant makes the context contradictory
    // against the `inv_T(x) <==> body(x)` defining axiom, which proves
    // ANYTHING. This loop used to walk every entry of `ctx.variables`, locals
    // included, so the guard below is what keeps that from being a cardinal
    // false verify the moment the surface is wired up.
    //
    // FAIL CLOSED, not fail open: an invariant that cannot be justified is
    // simply not asserted. Dropping an ASSUMPTION is always sound (unlike
    // dropping a `requires`, which is a discharged obligation). So a context
    // with type invariants but no `function_context` — hence no parameter list
    // to check against — asserts none of them.
    let invariant_bearing_params: std::collections::HashSet<&str> = ctx
        .function_context
        .as_ref()
        .map(|fc| fc.param_names().collect())
        .unwrap_or_default();
    for var in &ctx.variables {
        if let crate::ir::TrustVcType::Datatype { name, .. } = &var.ty {
            if ctx.type_invariants.contains_key(name)
                && invariant_bearing_params.contains(var.name.as_str())
            {
                if let Some(&var_term) = encoder.variables.get(&var.name) {
                    encoder
                        .assert_type_invariant_on_term(name, var_term)
                        .map_err(|err| {
                            setup_encoding_error(format!(
                                "Failed to assert type invariant for parameter '{}': {}",
                                var.name, err
                            ))
                        })?;
                }
            }
        }
    }

    Ok(())
}

pub(in crate::encoder) fn bootstrap_prepared_encoder(
    encoder: &mut AYEncoder,
    ctx: &PreparedVerificationContext,
    config: BootstrapPreparedConfig<'_>,
) -> TrustVcResult<super::pruning::PrunePlan> {
    let prune_plan = if let Some(assertion) = config.assertion_focus {
        let slices = VerificationSlices::new(
            ctx,
            config.active_assumptions,
            config.active_broadcasts,
            config.verified_invariants,
            config.verified_assert_by,
            config.scoped_assumptions,
        );
        let plan = super::pruning::build_per_assertion_prune_plan(&slices, assertion);
        tracing::debug!(
            assertion = %assertion.name,
            reachable_functions = plan.reachable_functions.len(),
            reachable_variables = plan
                .current_state_slice()
                .map_or(0, |slice| slice.reachable_variables.len()),
            total_broadcasts = config.active_broadcasts.len(),
            "Per-assertion prune plan (#2649)",
        );
        plan
    } else {
        super::pruning::build_prune_plan(ctx, config.active_broadcasts)
    };
    bootstrap_prepared_encoder_with_prune_plan(encoder, ctx, config, &prune_plan)?;
    Ok(prune_plan)
}

impl AYEncoder {
    /// Creates a fresh encoder from a PreparedVerificationContext.
    ///
    /// When `post_loop_modified_vars` is `Some`, the encoder enters post-loop
    /// mode: assumptions are rewritten to pre-state variables, pre-state
    /// variables are declared, and frame conditions connect unmodified variables
    /// to the current state. Modified variables are left unconstrained so that
    /// entry facts about them are forgotten. Part of #2219, #2448.
    pub(in crate::encoder) fn setup_from_prepared(
        slices: &VerificationSlices<'_>,
        use_int_for_measures: bool,
        post_loop_modified_vars: Option<&HashSet<String>>,
    ) -> TrustVcResult<Self> {
        Self::setup_from_prepared_with_extra_variables(
            slices,
            use_int_for_measures,
            post_loop_modified_vars,
            &[],
            None,
        )
    }

    pub(in crate::encoder) fn setup_from_prepared_with_extra_variables(
        slices: &VerificationSlices<'_>,
        use_int_for_measures: bool,
        post_loop_modified_vars: Option<&HashSet<String>>,
        extra_variables: &[VariableDecl],
        assertion_focus: Option<&PreparedObligation>,
    ) -> TrustVcResult<Self> {
        Self::setup_from_prepared_with_extra_variables_and_prune_plan(
            slices,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
            assertion_focus,
            None,
        )
    }

    pub(in crate::encoder) fn setup_from_prepared_with_extra_variables_and_prune_plan(
        slices: &VerificationSlices<'_>,
        use_int_for_measures: bool,
        post_loop_modified_vars: Option<&HashSet<String>>,
        extra_variables: &[VariableDecl],
        assertion_focus: Option<&PreparedObligation>,
        cached_prune_plan: Option<&super::pruning::PrunePlan>,
    ) -> TrustVcResult<Self> {
        Self::setup_from_prepared_with_inline_overrides_and_prune_plan(
            slices,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
            assertion_focus,
            &[],
            cached_prune_plan,
        )
    }

    /// Setup variant that accepts demand-inline overrides. Overridden function
    /// names are promoted to inline substitution for this encoder only. Part of #2655.
    #[cfg(test)]
    pub(in crate::encoder) fn setup_from_prepared_with_inline_overrides(
        slices: &VerificationSlices<'_>,
        use_int_for_measures: bool,
        post_loop_modified_vars: Option<&HashSet<String>>,
        extra_variables: &[VariableDecl],
        assertion_focus: Option<&PreparedObligation>,
        inline_overrides: &[String],
    ) -> TrustVcResult<Self> {
        Self::setup_from_prepared_with_inline_overrides_and_prune_plan(
            slices,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
            assertion_focus,
            inline_overrides,
            None,
        )
    }

    pub(in crate::encoder) fn setup_from_prepared_with_inline_overrides_and_prune_plan(
        slices: &VerificationSlices<'_>,
        use_int_for_measures: bool,
        post_loop_modified_vars: Option<&HashSet<String>>,
        extra_variables: &[VariableDecl],
        assertion_focus: Option<&PreparedObligation>,
        inline_overrides: &[String],
        cached_prune_plan: Option<&super::pruning::PrunePlan>,
    ) -> TrustVcResult<Self> {
        Self::setup_from_prepared_with_logic(
            slices,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
            assertion_focus,
            inline_overrides,
            cached_prune_plan,
            Logic::All,
        )
    }

    /// Builds the isolated overflow helper with the narrowest sound logic.
    /// Mixed-theory contexts deliberately remain on `Logic::All`; only a
    /// conservatively classified quantifier-free Bool/BV context uses `QfBv`.
    pub(in crate::encoder) fn setup_overflow_from_prepared(
        slices: &VerificationSlices<'_>,
        assertion: &PreparedObligation,
        use_int_for_measures: bool,
        post_loop_modified_vars: Option<&HashSet<String>>,
        extra_variables: &[VariableDecl],
        assertion_focus: Option<&PreparedObligation>,
        cached_prune_plan: Option<&super::pruning::PrunePlan>,
    ) -> TrustVcResult<Self> {
        let logic = super::overflow_logic::isolated_overflow_logic(
            slices.ctx,
            assertion,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
        );
        let mut encoder = Self::setup_from_prepared_with_logic(
            slices,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
            assertion_focus,
            &[],
            cached_prune_plan,
            logic,
        )?;
        // Overflow helpers need a validated model when they find a violation,
        // but they do not need ay's readability-minimization probes.  Keep
        // model production enabled for counterexample diagnostics while making
        // this helper use the non-minimizing route; the user-facing main solver
        // remains on `Readable`.
        encoder
            .solver
            .set_counterexample_style(ay_dpll::CounterexampleStyle::Any);
        Ok(encoder)
    }

    #[allow(clippy::too_many_arguments)]
    fn setup_from_prepared_with_logic(
        slices: &VerificationSlices<'_>,
        use_int_for_measures: bool,
        post_loop_modified_vars: Option<&HashSet<String>>,
        extra_variables: &[VariableDecl],
        assertion_focus: Option<&PreparedObligation>,
        inline_overrides: &[String],
        cached_prune_plan: Option<&super::pruning::PrunePlan>,
        logic: Logic,
    ) -> TrustVcResult<Self> {
        let ctx = slices.ctx;
        super::test_hooks::bump_setup_from_prepared_count();
        let wall_backstop_ms = ctx
            .rlimit_ms
            .unwrap_or(super::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS);
        let conflict_budget = super::timeout::effective_conflict_budget(ctx.rlimit_conflicts);
        let mut encoder =
            Self::with_logic(logic).with_limits(wall_backstop_ms, conflict_budget, 512);
        encoder.state.unpruned_proof_fact_count = slices.assumptions.len()
            + slices.broadcast_assumptions.len()
            + slices.verified_invariants.len()
            + slices.verified_assert_by.len()
            + slices.scoped_assumptions.len();
        let config = BootstrapPreparedConfig {
            active_broadcasts: slices.broadcast_assumptions,
            active_assumptions: slices.assumptions,
            verified_invariants: slices.verified_invariants,
            verified_assert_by: slices.verified_assert_by,
            scoped_assumptions: slices.scoped_assumptions,
            use_int_for_measures,
            extra_variables,
            assertion_focus,
            enable_current_state_variable_slice: assertion_focus.is_some()
                && post_loop_modified_vars.is_none(),
            inline_overrides,
            // Post-loop mode rewrites assumptions to pre-state variables, so
            // current-state length pins from entry facts would be unsound
            // there (the loop may modify the sequence).
            allow_finite_len_pins: post_loop_modified_vars.is_none(),
        };
        let owned_prune_plan;
        let prune_plan = if let Some(plan) = cached_prune_plan {
            bootstrap_prepared_encoder_with_prune_plan(&mut encoder, ctx, config, plan)?;
            plan
        } else {
            owned_prune_plan = bootstrap_prepared_encoder(&mut encoder, ctx, config)?;
            &owned_prune_plan
        };
        let current_state_slice = if assertion_focus.is_some() && post_loop_modified_vars.is_none()
        {
            prune_plan.current_state_slice()
        } else {
            None
        };

        // Post-loop mode: declare pre-state variables and rewrite assumptions
        // to pre-state form so entry facts about modified variables are forgotten.
        // Part of #2448.
        if post_loop_modified_vars.is_some() {
            super::frame_state::declare_pre_state_variables(&mut encoder, &ctx.variables)?;
        }

        let mut eq_queue: Vec<crate::ir::TrustVcExpr> = Vec::new();

        if let Some(modified_vars) = post_loop_modified_vars {
            let modified_set: HashSet<&str> = modified_vars.iter().map(|s| s.as_str()).collect();

            // Alias framed collection variables before assumptions, broadcasts,
            // and ground seeding — identical to the inductive-step path
            // (invariants/frame_condition.rs). ay-dpll can't propagate array
            // equality through `select` (#2384), so encoding an unmodified
            // collection's frame as a two-distinct-array extensional `forall`
            // (e.g. `forall e. select(s,e) == select(s__pre,e)`) alongside the
            // Route-A Int length atoms drives ay's check_sat into unbounded
            // recursion. Making the framed post-state term *be* the pre-state ay
            // term turns the frame equality reflexive, removing the trigger
            // while keeping `s ≡ s__pre` (sound: only for genuinely unmodified
            // collections). Part of #2390 / #2779 regression fix.
            super::frame_state::alias_framed_collection_variables(
                &mut encoder,
                &ctx.variables,
                &modified_set,
            );

            // Rewrite assumptions to pre-state variables. Entry facts become
            // facts about the pre-loop state; frame conditions will connect
            // unmodified variables to the current state.
            // PostLoopAssume obligations are exempted — they represent
            // current-state (post-loop) facts like auto-generated exit
            // conditions (`i == n` after `for i in 0..n`). Part of #2502.
            let pre_state_targets = super::rewrite::collect_pre_state_target_names(&ctx.variables);
            for assumption in slices.assumptions {
                // THE READING GATE (see `arith_reading`).
                match super::arith_reading::fact_admission_for(assumption, use_int_for_measures) {
                    super::arith_reading::FactAdmission::AsIs => {}
                    super::arith_reading::FactAdmission::Guarded => {
                        // Pre-state rewriting and a conditional fact do not
                        // compose (the guard would speak of the post state), so
                        // the post-loop lane drops rather than guards.
                        continue;
                    }
                    super::arith_reading::FactAdmission::Drop => continue,
                }
                if assumption.kind == ObligationKind::PostLoopAssume {
                    // Current-state: no pre-state rewriting.
                    encoder.add_typed_assumption_with_solver_mode(
                        &assumption.name,
                        &assumption.expr,
                        Some(&mut eq_queue),
                        assumption.solver_mode,
                    )?;
                } else {
                    let pre_expr = super::rewrite::replace_vars_with_pre_typed_with_targets(
                        &assumption.expr,
                        &pre_state_targets,
                    );
                    encoder.add_typed_assumption_with_solver_mode(
                        &format!("{}_pre", assumption.name),
                        &pre_expr,
                        Some(&mut eq_queue),
                        assumption.solver_mode,
                    )?;
                }
            }

            // Frame conditions: unmodified vars have var == var__trust_vc_pre,
            // modified vars are left unconstrained.
            super::frame_state::add_unmodified_frame_conditions(
                &mut encoder,
                &ctx.variables,
                &modified_set,
                &mut eq_queue,
                SETUP_CONTEXT,
            )?;
        } else {
            // Current-state mode: encode assumptions directly.
            encode_selected_obligations(
                &mut encoder,
                slices.assumptions,
                current_state_slice.map(|slice| slice.selected_regular_assumptions.as_slice()),
                |encoder, assumption| {
                    // THE READING GATE (see `arith_reading`).
                    match super::arith_reading::fact_admission_for(assumption, use_int_for_measures)
                    {
                        super::arith_reading::FactAdmission::AsIs => {}
                        super::arith_reading::FactAdmission::Guarded => {
                            return encoder.add_cross_reading_guarded_assumption(
                                &assumption.name,
                                &assumption.expr,
                                assumption.solver_mode,
                                use_int_for_measures,
                            );
                        }
                        super::arith_reading::FactAdmission::Drop => return Ok(()),
                    }
                    encoder.add_typed_assumption_with_solver_mode(
                        &assumption.name,
                        &assumption.expr,
                        Some(&mut eq_queue),
                        assumption.solver_mode,
                    )
                },
            )?;
        }

        let var_terms = current_state_var_terms(&encoder.variables);
        setup_broadcasts::register_setup_broadcasts(
            &mut encoder,
            ctx,
            slices.broadcast_assumptions,
            prune_plan,
            &var_terms,
            assertion_focus,
            use_int_for_measures,
        )?;

        // Seed ground select terms at index 0 for collection variables so
        // ay-dpll's E-matching can instantiate quantified array properties.
        // Part of #2390.
        encoder.seed_collection_ground_selects()?;

        encode_selected_obligations(
            &mut encoder,
            slices.verified_invariants,
            current_state_slice.map(|slice| slice.selected_verified_invariants.as_slice()),
            |encoder, inv| {
                // THE READING GATE (see `arith_reading`).
                match super::arith_reading::fact_admission_for(inv, use_int_for_measures) {
                    super::arith_reading::FactAdmission::AsIs => {}
                    super::arith_reading::FactAdmission::Guarded => {
                        return encoder.add_cross_reading_guarded_assumption(
                            &inv.name,
                            &inv.expr,
                            inv.solver_mode,
                            use_int_for_measures,
                        );
                    }
                    super::arith_reading::FactAdmission::Drop => return Ok(()),
                }
                encoder.add_typed_assumption_with_solver_mode(
                    &inv.name,
                    &inv.expr,
                    Some(&mut eq_queue),
                    inv.solver_mode,
                )
            },
        )?;
        encode_selected_obligations(
            &mut encoder,
            slices.verified_assert_by,
            current_state_slice.map(|slice| slice.selected_verified_assert_by.as_slice()),
            |encoder, ab| {
                // THE READING GATE (see `arith_reading`). This is the site the
                // eight measured false-`Verified`s came through: a
                // `by(nonlinear_arith)` conclusion proved over unbounded `Int`
                // was asserted, unchanged, into the next obligation's
                // fixed-width solve.
                match super::arith_reading::fact_admission_for(ab, use_int_for_measures) {
                    super::arith_reading::FactAdmission::AsIs => {}
                    super::arith_reading::FactAdmission::Guarded => {
                        return encoder.add_cross_reading_guarded_assumption(
                            &ab.name,
                            &ab.expr,
                            ab.solver_mode,
                            use_int_for_measures,
                        );
                    }
                    super::arith_reading::FactAdmission::Drop => return Ok(()),
                }
                if let Some(bound_vars) = ctx
                    .forall_bound_vars
                    .get(&ab.name)
                    .filter(|bound_vars| !bound_vars.is_empty())
                {
                    let triggers = ab.prepared_triggers.as_ref().map(|groups| {
                        groups
                            .iter()
                            .map(|group| group.iter().map(|trigger| trigger.expr.clone()).collect())
                            .collect()
                    });
                    let quantified = crate::ir::TrustVcExpr::Quantifier {
                        kind: crate::ir::QuantifierKind::Forall,
                        bound_vars: bound_vars
                            .iter()
                            .map(|decl| (decl.name.clone(), decl.ty.clone()))
                            .collect(),
                        body: Box::new(ab.expr.clone()),
                        triggers,
                        trigger_inference_mode: ab.trigger_inference_mode,
                    };
                    encoder.add_typed_assumption_with_concrete_quantifier_sorts_and_solver_mode(
                        &ab.name,
                        &quantified,
                        Some(&mut eq_queue),
                        ab.solver_mode,
                    )
                } else {
                    encoder.add_typed_assumption_with_solver_mode(
                        &ab.name,
                        &ab.expr,
                        Some(&mut eq_queue),
                        ab.solver_mode,
                    )
                }
            },
        )?;
        encode_selected_obligations(
            &mut encoder,
            slices.scoped_assumptions,
            current_state_slice.map(|slice| slice.selected_scoped_assumptions.as_slice()),
            |encoder, scoped| {
                // THE READING GATE (see `arith_reading`).
                match super::arith_reading::fact_admission_for(scoped, use_int_for_measures) {
                    super::arith_reading::FactAdmission::AsIs => {}
                    super::arith_reading::FactAdmission::Guarded => {
                        return encoder.add_cross_reading_guarded_assumption(
                            &scoped.name,
                            &scoped.expr,
                            scoped.solver_mode,
                            use_int_for_measures,
                        );
                    }
                    super::arith_reading::FactAdmission::Drop => return Ok(()),
                }
                encoder.add_typed_assumption_with_solver_mode(
                    &scoped.name,
                    &scoped.expr,
                    Some(&mut eq_queue),
                    scoped.solver_mode,
                )
            },
        )?;

        // Re-encode equality assumptions with final bindings for
        // ordering-independent derived equalities. Part of #2386.
        encoder.reconcile_equality_assumptions(&eq_queue)?;

        Ok(encoder)
    }
}

#[cfg(test)]
#[path = "setup_tests.rs"]
mod tests;
