//! Trait-impl conformance obligation construction and lowering helpers.
//! Copyright 2026 Andrew Yates | Apache-2.0 | Author: Andrew Yates

use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use syn::visit_mut::VisitMut;

use super::super::body_support;
use super::super::encoding_error;
use super::specialize::{ContractBindings, IdentifierRenamer};
use super::CONFORMANCE_CONTEXT;
use crate::encoder::types::VerifyResult;
use crate::error::TrustVcError;
use crate::ir::{LogicOp, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcExpr};
use crate::ir_lowering::{lower_syn_expr, TypeEnv};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{FunctionContext, ObligationKind};

pub(super) fn clone_base_conformance_obligations(
    base: &PreparedVerificationContext,
) -> Vec<PreparedObligation> {
    base.obligations
        .iter()
        .filter(|obligation| obligation.kind == ObligationKind::Reveal)
        .cloned()
        .collect()
}

/// Clones the defining body-axiom BROADCAST obligations for every free function
/// referenced (at ANY arity / argument shape) by `contract_obligations`.
///
/// [`instantiate_referenced_body_axioms`] grounds only VARIABLE-argument calls
/// (`GroundFnCall` requires `Var` args), so a default body that calls a free
/// function with literal/constant arguments — `fn dm(&self) -> u32 { add(2, 5) }`
/// — has no body axiom instantiated for `add(2, 5)`, leaving the call an
/// unconstrained UF and over-rejecting a CONFORMING default. Carrying the
/// function's quantified body axiom (`forall a, b. add(a, b) == a + b`) as a
/// broadcast lets the solver's E-matching ground it on the concrete term
/// regardless of argument shape. These are pure definitional facts about free
/// functions (no trait UF), so they cannot make a non-conforming default pass —
/// a false `ensures` still Counterexamples.
pub(super) fn referenced_body_axiom_broadcasts(
    base: &PreparedVerificationContext,
    contract_obligations: &[PreparedObligation],
) -> Vec<PreparedObligation> {
    let mut referenced = HashSet::new();
    for obligation in contract_obligations {
        referenced.extend(body_support::referenced_function_names(&obligation.expr));
    }
    if referenced.is_empty() {
        return Vec::new();
    }

    base.obligations
        .iter()
        .filter(|obligation| {
            obligation.kind == ObligationKind::BroadcastAssume
                && body_support::is_body_axiom(obligation)
                && body_support::extracted_body_axiom(obligation)
                    .is_some_and(|axiom| referenced.contains(&axiom.function_name))
        })
        .cloned()
        .collect()
}

pub(super) fn instantiate_referenced_body_axioms(
    base: &PreparedVerificationContext,
    concrete_body_axioms: &[PreparedObligation],
    contract_obligations: &[PreparedObligation],
    env: &TypeEnv,
    obligation_name: &str,
    primary_function_name: &str,
) -> Result<Vec<PreparedObligation>, TrustVcError> {
    let mut pending = Vec::new();
    let mut seen_calls = HashSet::new();
    enqueue_ground_fn_calls_from_obligations(concrete_body_axioms, &mut pending, &mut seen_calls);
    enqueue_ground_fn_calls_from_obligations(contract_obligations, &mut pending, &mut seen_calls);
    let body_axioms_by_function = body_axiom_index(base);

    let mut instantiated = Vec::new();
    let mut seen_axioms = HashSet::new();
    let mut cursor = 0;

    while let Some(call) = pending.get(cursor).cloned() {
        cursor += 1;
        if call.name == primary_function_name {
            continue;
        }

        let Some(obligations) = body_axioms_by_function.get(&call.name) else {
            continue;
        };
        for obligation in obligations {
            let Some(bound_vars) = obligation.bound_vars.as_ref() else {
                continue;
            };
            if bound_vars.len() != call.arg_names.len() {
                continue;
            }

            let instance_key = (obligation.name.clone(), call.arg_names.clone());
            if !seen_axioms.insert(instance_key) {
                continue;
            }

            let renames = bound_vars
                .iter()
                .cloned()
                .zip(call.arg_names.iter().cloned())
                .collect::<HashMap<_, _>>();
            let (condition, expr) = lower_contract_expression(
                &obligation.condition,
                env,
                &renames,
                &format!("support body axiom {}", obligation.name),
            )?;
            let grounded = derived_prepared_obligation(
                obligation,
                format!(
                    "{obligation_name} support {}({})",
                    obligation.name,
                    call.arg_names.join(", ")
                ),
                ObligationKind::Assume,
                condition,
                expr,
            );
            enqueue_ground_fn_calls(&grounded.expr, &mut pending, &mut seen_calls);
            instantiated.push(grounded);
        }
    }

    Ok(instantiated)
}

fn body_axiom_index(
    base: &PreparedVerificationContext,
) -> HashMap<String, Vec<&PreparedObligation>> {
    let mut index: HashMap<String, Vec<&PreparedObligation>> = HashMap::new();
    for obligation in base.obligations.iter().filter(|obligation| {
        obligation.kind == ObligationKind::BroadcastAssume
            && body_support::is_body_axiom(obligation)
    }) {
        for key in body_axiom_index_keys(obligation) {
            index.entry(key).or_default().push(obligation);
        }
    }
    index
}

fn body_axiom_index_keys(obligation: &PreparedObligation) -> HashSet<String> {
    let mut keys = HashSet::new();
    if let Some(body_axiom) = body_support::extracted_body_axiom(obligation) {
        keys.insert(body_axiom.function_name);
    }

    if let Some(suffix) = obligation
        .name
        .strip_prefix(body_support::BODY_AXIOM_PREFIX)
    {
        keys.insert(suffix.to_string());
        if let Some((base_name, numeric_suffix)) = suffix.rsplit_once('_') {
            if !base_name.is_empty() && numeric_suffix.chars().all(|c| c.is_ascii_digit()) {
                keys.insert(base_name.to_string());
            }
        }
    }

    for trigger_fn in obligation.trigger_head_symbols() {
        keys.insert(trigger_fn.into_owned());
    }

    keys
}

pub(super) fn instantiate_current_body_axioms(
    base: &PreparedVerificationContext,
    concrete_fn_name: &str,
    obligation_name: &str,
    bindings: &ContractBindings,
    env: &TypeEnv,
    obligation_template: &PreparedObligation,
) -> Result<Vec<PreparedObligation>, TrustVcError> {
    let renames = bindings.rename_map();
    let mut obligations = Vec::new();

    for (index, obligation) in base
        .obligations
        .iter()
        .filter(|obligation| body_support::is_body_axiom_for_function(obligation, concrete_fn_name))
        .enumerate()
    {
        let (condition, expr) = lower_contract_expression(
            &obligation.condition,
            env,
            &renames,
            &format!("concrete impl body axiom {index}"),
        )?;
        obligations.push(derived_prepared_obligation(
            obligation_template,
            format!("{obligation_name} body axiom #{index}"),
            ObligationKind::Assume,
            condition,
            expr,
        ));
    }

    Ok(obligations)
}
pub(super) fn collect_helper_function_contexts(
    base: &PreparedVerificationContext,
    primary_function_name: &str,
) -> Vec<FunctionContext> {
    let mut contexts = Vec::new();
    let mut seen = HashSet::new();

    if let Some(func_ctx) = &base.function_context {
        if func_ctx.name != primary_function_name && seen.insert(func_ctx.name.clone()) {
            contexts.push(func_ctx.clone());
        }
    }

    for helper_ctx in &base.helper_function_contexts {
        if helper_ctx.name != primary_function_name && seen.insert(helper_ctx.name.clone()) {
            contexts.push(helper_ctx.clone());
        }
    }

    contexts
}

fn enqueue_ground_fn_calls_from_obligations(
    obligations: &[PreparedObligation],
    pending: &mut Vec<GroundFnCall>,
    seen_calls: &mut HashSet<GroundFnCall>,
) {
    for obligation in obligations {
        enqueue_ground_fn_calls(&obligation.expr, pending, seen_calls);
    }
}

fn enqueue_ground_fn_calls(
    expr: &TrustVcExpr,
    pending: &mut Vec<GroundFnCall>,
    seen_calls: &mut HashSet<GroundFnCall>,
) {
    match expr {
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. } => {}
        TrustVcExpr::Neg(inner)
        | TrustVcExpr::Not(inner)
        | TrustVcExpr::Cast { expr: inner, .. } => {
            enqueue_ground_fn_calls(inner, pending, seen_calls);
        }
        TrustVcExpr::SpecClosure { body, .. } => {
            enqueue_ground_fn_calls(body, pending, seen_calls);
        }
        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::Compare { left, right, .. }
        | TrustVcExpr::Logic { left, right, .. }
        | TrustVcExpr::SpecialArith { left, right, .. }
        | TrustVcExpr::WrappingArith { left, right, .. } => {
            enqueue_ground_fn_calls(left, pending, seen_calls);
            enqueue_ground_fn_calls(right, pending, seen_calls);
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            enqueue_ground_fn_calls(premise, pending, seen_calls);
            enqueue_ground_fn_calls(conclusion, pending, seen_calls);
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            enqueue_ground_fn_calls(cond, pending, seen_calls);
            enqueue_ground_fn_calls(then_branch, pending, seen_calls);
            enqueue_ground_fn_calls(else_branch, pending, seen_calls);
        }
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            enqueue_ground_fn_calls(scrutinee, pending, seen_calls);
            for arm in arms {
                enqueue_ground_fn_calls(&arm.body, pending, seen_calls);
            }
        }
        TrustVcExpr::Let { value, body, .. } => {
            enqueue_ground_fn_calls(value, pending, seen_calls);
            enqueue_ground_fn_calls(body, pending, seen_calls);
        }
        TrustVcExpr::CollectionOp { receiver, args, .. } => {
            enqueue_ground_fn_calls(receiver, pending, seen_calls);
            for arg in args {
                enqueue_ground_fn_calls(arg, pending, seen_calls);
            }
        }
        TrustVcExpr::Index {
            receiver, index, ..
        } => {
            enqueue_ground_fn_calls(receiver, pending, seen_calls);
            enqueue_ground_fn_calls(index, pending, seen_calls);
        }
        TrustVcExpr::Quantifier { body, triggers, .. } => {
            enqueue_ground_fn_calls(body, pending, seen_calls);
            if let Some(trigger_groups) = triggers {
                for group in trigger_groups {
                    for trigger in group {
                        enqueue_ground_fn_calls(trigger, pending, seen_calls);
                    }
                }
            }
        }
        TrustVcExpr::FnCall { name, args, .. } => {
            if let Some(call) = GroundFnCall::from_expr(name, args) {
                if seen_calls.insert(call.clone()) {
                    pending.push(call);
                }
            }
            for arg in args {
                enqueue_ground_fn_calls(arg, pending, seen_calls);
            }
        }
        TrustVcExpr::Choose { condition, .. } => {
            enqueue_ground_fn_calls(condition, pending, seen_calls);
        }
        TrustVcExpr::ReadPlace { place, .. } => {
            for proj in &place.projections {
                if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                    enqueue_ground_fn_calls(index, pending, seen_calls);
                }
            }
        }
        TrustVcExpr::PlaceDisjoint { left, right } => {
            for place in [left, right] {
                for proj in &place.projections {
                    if let crate::ir_place::PlaceProjection::Index { index, .. } = proj {
                        enqueue_ground_fn_calls(index, pending, seen_calls);
                    }
                }
            }
        }
        TrustVcExpr::ProphecyNew { .. } => {}
        TrustVcExpr::ProphecyResolve { value, .. } => {
            enqueue_ground_fn_calls(value, pending, seen_calls);
        }
    }
}

pub(super) fn build_contract_obligations(
    method: &TraitMethodDecl,
    concrete_fn_name: &str,
    obligation_name: &str,
    bindings: &ContractBindings,
    env: &TypeEnv,
    obligation_template: &PreparedObligation,
) -> Result<Vec<PreparedObligation>, TrustVcError> {
    let renames = bindings.rename_map();
    let mut obligations = Vec::with_capacity(method.requires.len() + 2);

    let mut args = Vec::with_capacity(bindings.params.len() + 1);
    args.push(bindings.receiver_name.clone());
    args.extend(
        bindings
            .params
            .iter()
            .map(|binding| binding.lowered_name.clone()),
    );

    let result_binding_condition = format!(
        "{} == {}({})",
        bindings.result_name,
        concrete_fn_name,
        args.join(", ")
    );
    obligations.push(derived_prepared_obligation(
        obligation_template,
        format!("{obligation_name} result"),
        ObligationKind::Assume,
        result_binding_condition.clone(),
        lower_expression(
            &result_binding_condition,
            env,
            &HashMap::new(),
            "result binding",
        )?,
    ));

    for (index, require) in method.requires.iter().enumerate() {
        let (condition, expr) = lower_contract_expression(
            require,
            env,
            &renames,
            &format!("trait precondition {index}"),
        )?;
        obligations.push(derived_prepared_obligation(
            obligation_template,
            format!("{obligation_name} requires #{index}"),
            ObligationKind::Assume,
            condition,
            expr,
        ));
    }

    let mut ensures = Vec::with_capacity(method.ensures.len());
    for (index, ensure) in method.ensures.iter().enumerate() {
        ensures.push(lower_contract_expression(
            ensure,
            env,
            &renames,
            &format!("trait postcondition {index}"),
        )?);
    }

    let (condition, expr) = combine_conjuncts(ensures);
    obligations.push(derived_prepared_obligation(
        obligation_template,
        obligation_name.to_string(),
        ObligationKind::Assert,
        condition,
        expr,
    ));

    Ok(obligations)
}

/// Builds the CONFORMANCE-EXTENSION `Assert` obligations for an impl method's
/// OWN declared `ensures` (the strengthened postcondition it adds on top of the
/// trait contract). Each clause becomes an independent `Assert` over the same
/// conformance surface as the trait `ensures` in [`build_contract_obligations`]:
/// `result` renames to `__trust_vc_impl_result`, which the result binding +
/// impl-body definition pin to the method's ACTUAL body value. So this verifies
/// `body ⊨ impl_ensures`.
///
/// SOUNDNESS (the cardinal step): the impl `ensures` must NEVER be assumed for a
/// caller without first being checked here. A body that violates its declared
/// `ensures` makes one of these asserts Counterexample, sinking the whole file —
/// exactly the required behavior. This is the sole justification that makes the
/// impl-postcondition PROPAGATION axiom (emitted by the encoder) sound to assert.
pub(super) fn build_impl_ensures_assert_obligations(
    impl_ensures: &[String],
    obligation_name: &str,
    bindings: &ContractBindings,
    env: &TypeEnv,
    obligation_template: &PreparedObligation,
) -> Result<Vec<PreparedObligation>, TrustVcError> {
    let renames = bindings.rename_map();
    let mut obligations = Vec::with_capacity(impl_ensures.len());
    for (index, ensure) in impl_ensures.iter().enumerate() {
        let (condition, expr) = lower_contract_expression(
            ensure,
            env,
            &renames,
            &format!("impl postcondition {index}"),
        )?;
        obligations.push(derived_prepared_obligation(
            obligation_template,
            format!("{obligation_name} impl ensures #{index}"),
            ObligationKind::Assert,
            condition,
            expr,
        ));
    }
    Ok(obligations)
}

/// Builds the definitional `Assume` `concrete_fn(self, args..) == <impl body>`
/// for an OVERRIDDEN trait-impl method whose body was captured at extraction.
///
/// The overridden-impl result binding (in [`build_contract_obligations`]) ties
/// `__trust_vc_impl_result` to the opaque UF `concrete_fn(receiver, params..)`,
/// and the trait `ensures` is asserted over it. Discharging that assert requires
/// knowing what `concrete_fn(..)` returns — normally the method's body axiom,
/// which is only emitted into the base context when the VERIFIED function
/// references the impl method. When it does not (e.g. an unrelated generic
/// trait-bound caller), no body axiom is in scope and a CONFORMING impl is
/// rejected against an unconstrained `@Poly` result. This obligation supplies
/// the missing definitional fact, instantiated at exactly the call args the
/// result binding uses, so the contract is checked against the real body.
///
/// Soundness: this is the impl method's TRUE definition (the captured text is a
/// single pure return — see [`crate::ir::ConformanceMethodBody`]), so a
/// non-conforming body still contradicts the `ensures` and Counterexamples; it
/// can never make a non-conforming impl pass. The canonical `self` /
/// `__trust_vc_conf_arg_{i}` placeholders are renamed onto the conformance
/// surface positionally, matching the result binding's `receiver`/param args.
pub(super) fn build_impl_body_definition_obligation(
    concrete_fn_name: &str,
    body: &crate::ir::ConformanceMethodBody,
    obligation_name: &str,
    bindings: &ContractBindings,
    env: &TypeEnv,
    obligation_template: &PreparedObligation,
) -> Option<PreparedObligation> {
    // The captured non-receiver param count must match the trait method's, or
    // the positional rename would be unsound — decline (keep prior path).
    if body.param_count != bindings.params.len() {
        return None;
    }

    let mut args = Vec::with_capacity(body.param_count + 1);
    args.push("self".to_string());
    for index in 0..body.param_count {
        args.push(format!("__trust_vc_conf_arg_{index}"));
    }
    let condition = format!(
        "{concrete_fn_name}({}) == ({})",
        args.join(", "),
        body.body_text
    );

    let mut renames = HashMap::with_capacity(body.param_count + 1);
    renames.insert("self".to_string(), bindings.receiver_name.clone());
    for (index, param) in bindings.params.iter().enumerate() {
        renames.insert(
            format!("__trust_vc_conf_arg_{index}"),
            param.lowered_name.clone(),
        );
    }

    // Lowering failure (e.g. the body references a symbol absent from this
    // context) is non-fatal: skip the definition and keep the prior path. Never
    // turn an over-rejection into a fail-closed error here.
    let (condition, expr) =
        lower_contract_expression(&condition, env, &renames, "impl body definition").ok()?;
    Some(derived_prepared_obligation(
        obligation_template,
        format!("{obligation_name} impl body definition"),
        ObligationKind::Assume,
        condition,
        expr,
    ))
}

/// Builds the conformance obligations for a NON-overridden trait default method.
///
/// Mirrors [`build_contract_obligations`] (the overridden-impl path) but binds
/// the result variable to the *inlined default body* instead of to a concrete
/// impl function call:
///
/// ```text
///   assume  __impl_result == (<default body>)   // body, with self/params renamed
///   assume  <requires>                          // trait preconditions
///   assert  <ensures>                           // trait postconditions
/// ```
///
/// This verifies that the default body establishes the trait `ensures` (given
/// the trait `requires`) — exactly the obligation an overridden impl method must
/// discharge. Without it, the global trait-postcondition axiom asserted by
/// `register_trait` encodes an `ensures` that no impl body is ever checked
/// against, which becomes a false-`Verified` the moment caller-side trait
/// dispatch instantiates a ground `Trait::method(..)` term.
pub(super) fn build_default_contract_obligations(
    method: &TraitMethodDecl,
    default_body: &str,
    obligation_name: &str,
    bindings: &ContractBindings,
    env: &TypeEnv,
    obligation_template: &PreparedObligation,
) -> Result<Vec<PreparedObligation>, TrustVcError> {
    let renames = bindings.rename_map();
    let mut obligations = Vec::with_capacity(method.requires.len() + 2);

    // result binding: `result == (<default body>)`, with `self`, the source
    // parameter names, and `result` renamed onto the concrete conformance
    // surface (`__trust_vc_impl_self`, `__trust_vc_impl_param_*`,
    // `__trust_vc_impl_result`) by the shared identifier renamer.
    let result_binding_condition = format!("result == ({default_body})");
    let (binding_condition, binding_expr) = lower_contract_expression(
        &result_binding_condition,
        env,
        &renames,
        "default body result binding",
    )?;
    obligations.push(derived_prepared_obligation(
        obligation_template,
        format!("{obligation_name} result"),
        ObligationKind::Assume,
        binding_condition,
        binding_expr,
    ));

    for (index, require) in method.requires.iter().enumerate() {
        let (condition, expr) = lower_contract_expression(
            require,
            env,
            &renames,
            &format!("trait precondition {index}"),
        )?;
        obligations.push(derived_prepared_obligation(
            obligation_template,
            format!("{obligation_name} requires #{index}"),
            ObligationKind::Assume,
            condition,
            expr,
        ));
    }

    let mut ensures = Vec::with_capacity(method.ensures.len() + method.default_ensures.len());
    for (index, ensure) in method.ensures.iter().enumerate() {
        ensures.push(lower_contract_expression(
            ensure,
            env,
            &renames,
            &format!("trait postcondition {index}"),
        )?);
    }

    // Decl-site `default_ensures`: the extra postcondition the trait DEFAULT
    // BODY must ALSO establish. Fold each clause into the SAME asserted
    // conjunction the default body is checked against. The body's
    // `result == (<default body>)` Assume is already pushed above, so with
    // `result` pinned to the body the added conjunct is refuted exactly when the
    // body violates `default_ensures` — a genuine Counterexample. The asserted
    // set only GROWS (the body must prove more); nothing is published to
    // callers here, so this cannot leak `default_ensures` as a caller-visible
    // axiom.
    for (index, clause) in method.default_ensures.iter().enumerate() {
        ensures.push(lower_contract_expression(
            clause,
            env,
            &renames,
            &format!("trait default_ensures {index}"),
        )?);
    }

    let (condition, expr) = combine_conjuncts(ensures);
    obligations.push(derived_prepared_obligation(
        obligation_template,
        obligation_name.to_string(),
        ObligationKind::Assert,
        condition,
        expr,
    ));

    Ok(obligations)
}

fn derived_prepared_obligation(
    template: &PreparedObligation,
    name: String,
    kind: ObligationKind,
    condition: String,
    expr: TrustVcExpr,
) -> PreparedObligation {
    let mut obligation = template.clone();
    obligation.name = name;
    obligation.kind = kind;
    obligation.location = None;
    obligation.bound_vars = None;
    obligation.trigger_patterns = None;
    obligation.prepared_triggers = None;
    obligation.solver_mode = None;
    obligation.is_opaque = false;
    obligation.is_inline = false;
    obligation.broadcast_group = None;
    obligation.condition = condition;
    obligation.expr = expr;
    obligation.broadcast_guard = None;
    obligation.raw_broadcast_guard_count = 0;
    obligation
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct GroundFnCall {
    name: String,
    arg_names: Vec<String>,
}

impl GroundFnCall {
    fn from_expr(name: &str, args: &[TrustVcExpr]) -> Option<Self> {
        let arg_names = args
            .iter()
            .map(|arg| match arg {
                TrustVcExpr::Var { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Self {
            name: name.to_string(),
            arg_names,
        })
    }
}

fn combine_conjuncts(parts: Vec<(String, TrustVcExpr)>) -> (String, TrustVcExpr) {
    let mut iter = parts.into_iter();
    let Some((mut condition, mut expr)) = iter.next() else {
        return ("true".to_string(), TrustVcExpr::BoolLit(true));
    };

    for (next_condition, next_expr) in iter {
        condition = format!("({condition}) && ({next_condition})");
        expr = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(expr),
            right: Box::new(next_expr),
        };
    }

    (condition, expr)
}

fn lower_contract_expression(
    condition: &str,
    env: &TypeEnv,
    renames: &HashMap<String, String>,
    label: &str,
) -> Result<(String, TrustVcExpr), TrustVcError> {
    let mut syn_expr: syn::Expr = syn::parse_str(condition).map_err(|err| {
        encoding_error(
            CONFORMANCE_CONTEXT,
            format!("failed to parse {label}: {err}"),
        )
    })?;
    IdentifierRenamer::new(renames).visit_expr_mut(&mut syn_expr);

    let lowered_condition = syn_expr.to_token_stream().to_string();
    let expr = lower_syn_expr(&syn_expr, env).map_err(|err| {
        encoding_error(
            CONFORMANCE_CONTEXT,
            format!("failed to lower {label}: {err}"),
        )
    })?;
    Ok((lowered_condition, expr))
}

fn lower_expression(
    condition: &str,
    env: &TypeEnv,
    renames: &HashMap<String, String>,
    label: &str,
) -> Result<TrustVcExpr, TrustVcError> {
    lower_contract_expression(condition, env, renames, label).map(|(_, expr)| expr)
}

pub(super) fn conformance_obligation_name(
    trait_decl: &TraitDecl,
    method: &TraitMethodDecl,
    impl_decl: &TraitImplDecl,
) -> String {
    format!(
        "trait impl conformance {}::{} for {}",
        trait_decl.name,
        method.name,
        impl_decl.concrete_type.to_type_string()
    )
}

pub(super) fn normalize_conformance_result(
    result: VerifyResult,
    obligation_name: &str,
) -> VerifyResult {
    match result {
        VerifyResult::Verified => VerifyResult::Verified,
        VerifyResult::Counterexample {
            model, bindings, ..
        } => VerifyResult::Counterexample {
            obligation_name: obligation_name.to_string(),
            model,
            bindings,
        },
        // Re-label through the same funnel that made this a `NotProved` in the
        // first place, so the incompleteness routing stays in exactly one place.
        VerifyResult::NotProved {
            reason, category, ..
        }
        | VerifyResult::Unknown {
            reason, category, ..
        } => VerifyResult::unknown(format!("{obligation_name}: {reason}"), Some(category)),
        VerifyResult::Error { message } => VerifyResult::Error {
            message: format!("{obligation_name}: {message}"),
        },
    }
}
