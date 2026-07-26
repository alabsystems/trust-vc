//! Validation boundary between prepared context and typed verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides the missing normalization/validation stage between
//! obligation lowering (`prepare_context`) and solver execution (`verify_typed`).
//! It classifies obligations into execution lanes once, validates structural
//! integrity of triggers and broadcast guards, and rejects legacy-translated
//! obligations that require structured metadata.
//!
//! Part of #1830 Slice 2.

use std::collections::HashSet;

use super::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{ConditionOrigin, ObligationKind, VerificationMode};

/// Errors from the validation boundary.
#[derive(Debug)]
pub(crate) enum ValidationError {
    /// Trigger patterns were declared but some were lost during lowering.
    MalformedTrigger {
        obligation_name: String,
        expected_groups: usize,
        lowered_groups: usize,
    },
    /// Broadcast guard clauses were declared but lost during lowering.
    DroppedBroadcastGuard { obligation_name: String },
    /// A legacy-translated obligation requires structured metadata that the
    /// string path cannot provide.
    LegacyStructuredObligation {
        obligation_name: String,
        kind: ObligationKind,
        reason: &'static str,
    },
    /// No obligations to verify.
    EmptyContext,
    /// Only assumptions — nothing to prove.
    OnlyAssumptions,
    /// Variables with unrecognized types that cannot be soundly encoded.
    OpaqueVariable { variables: Vec<(String, String)> },
    /// InvariantOpen without namespace.
    InvariantMissingNamespace { obligation_name: String },
    /// InvariantOpen for a namespace the function's mask disallows.
    InvariantMaskViolation {
        obligation_name: String,
        namespace: i64,
    },
    /// Same invariant namespace opened twice (re-entrancy).
    InvariantReentrancy {
        obligation_name: String,
        namespace: i64,
    },
    /// A `by(bit_vector)` proof references a value or performs an operation the
    /// bit-vector prover cannot model. The stored `message` is the byte-exact
    /// upstream Verus diagnostic (diagnostic parity for #2778); it is emitted
    /// verbatim so the ported Verus suite's `assert_vir_error_msg` substring
    /// assertions match.
    BitVectorParity {
        #[allow(dead_code)] // diagnostic-parity field (#2778)
        obligation_name: String,
        message: String,
    },
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedTrigger {
                obligation_name,
                expected_groups,
                lowered_groups,
            } => write!(
                f,
                "Obligation '{obligation_name}' declares {expected_groups} trigger group(s) \
                 but only {lowered_groups} survived lowering"
            ),
            Self::DroppedBroadcastGuard { obligation_name } => write!(
                f,
                "Broadcast obligation '{obligation_name}' had guard clauses that were \
                 lost during lowering"
            ),
            Self::LegacyStructuredObligation {
                obligation_name,
                kind,
                reason,
            } => write!(
                f,
                "Obligation '{obligation_name}' (kind: {kind:?}) reached the prepared boundary \
                 via legacy string translation but {reason}"
            ),
            Self::EmptyContext => write!(f, "Cannot verify empty context: no obligations to check"),
            Self::OnlyAssumptions => write!(
                f,
                "Cannot verify context with only assumptions and no assertions: \
                 nothing to prove (missing ensures, assert, or invariant)"
            ),
            Self::OpaqueVariable { variables } => {
                let formatted: Vec<_> = variables
                    .iter()
                    .map(|(name, ty)| format!("'{name}' (type: {ty})"))
                    .collect();
                write!(
                    f,
                    "Variables with unrecognized types that cannot be soundly encoded: {}",
                    formatted.join(", ")
                )
            }
            Self::InvariantMissingNamespace { obligation_name } => write!(
                f,
                "InvariantOpen obligation '{obligation_name}' has no namespace"
            ),
            Self::InvariantMaskViolation {
                obligation_name,
                namespace,
            } => write!(
                f,
                "Invariant namespace {namespace} not allowed by function mask for '{obligation_name}'"
            ),
            Self::InvariantReentrancy {
                obligation_name,
                namespace,
            } => write!(
                f,
                "Invariant namespace {namespace} opened twice in '{obligation_name}' (re-entrancy)"
            ),
            // Emit the byte-exact upstream diagnostic verbatim. The leading
            // obligation tag is dropped so the message *is* the upstream string
            // and substring assertions (`assert_vir_error_msg`) match exactly.
            Self::BitVectorParity { message, .. } => write!(f, "{message}"),
        }
    }
}

/// Pre-classified obligation plan produced once by validation.
///
/// The encoder consumes this plan instead of reclassifying obligations itself.
#[derive(Debug)]
pub(crate) struct VerificationPlan<'a> {
    pub(crate) assumptions: Vec<&'a PreparedObligation>,
    pub(crate) broadcast_assumptions: Vec<&'a PreparedObligation>,
    pub(crate) loop_invariants: Vec<&'a PreparedObligation>,
    pub(crate) loop_guards: Vec<&'a PreparedObligation>,
    pub(crate) loop_ensures: Vec<&'a PreparedObligation>,
    /// Loop-scoped `loop_decreases!` measure obligations (a `MeasureNonNegative`
    /// floor and a `MeasureDecreases` strict-descent, each carrying loop metadata
    /// registered in `loop_modified_vars`). Verified in `typed.rs` as WF1 (a
    /// direct single-state non-negativity entailment under the loop invariants +
    /// guard, in the measure's int sort) and WF2 (a frame-condition inductive
    /// step). A bare recursive `#[decreases]` measure has no loop metadata and
    /// stays in `assertions`. Part of the file-path `loop_decreases!` wiring.
    pub(crate) loop_measures: Vec<&'a PreparedObligation>,
    pub(crate) assert_by: Vec<&'a PreparedObligation>,
    pub(crate) assertions: Vec<&'a PreparedObligation>,
    pub(crate) recommends: Vec<&'a PreparedObligation>,
}

/// A validated prepared context: the plan the encoder should trust.
#[derive(Debug)]
pub(crate) struct ValidatedPreparedContext<'a> {
    pub(crate) plan: VerificationPlan<'a>,
    pub(crate) source: &'a PreparedVerificationContext,
}

/// Validate a prepared context and produce a pre-classified execution plan.
///
/// This is the boundary between `prepare_context()` and `verify_typed()`.
/// It runs once, fails closed on structural integrity violations, and
/// returns a plan the encoder can trust without re-partitioning obligations.
pub(crate) fn validate_prepared_context(
    ctx: &PreparedVerificationContext,
) -> Result<ValidatedPreparedContext<'_>, ValidationError> {
    // --- Variable checks (collect all, not just first) ---
    let opaque_vars: Vec<(String, String)> = ctx
        .variables
        .iter()
        .filter(|v| v.ty.contains_opaque())
        .map(|v| (v.name.clone(), v.ty.to_type_string()))
        .collect();
    if !opaque_vars.is_empty() {
        return Err(ValidationError::OpaqueVariable {
            variables: opaque_vars,
        });
    }

    // --- Per-obligation structural integrity ---
    for obligation in &ctx.obligations {
        validate_obligation_integrity(obligation)?;
    }
    for scope in ctx.assert_by_scopes.values() {
        for obligation in scope {
            validate_obligation_integrity(obligation)?;
        }
    }

    // --- Lane classification ---
    let plan = classify_obligations(ctx)?;

    // --- Emptiness guards ---
    let has_any = !plan.assertions.is_empty()
        || !plan.assumptions.is_empty()
        || !plan.broadcast_assumptions.is_empty()
        || !plan.loop_invariants.is_empty()
        || !plan.loop_guards.is_empty()
        || !plan.loop_ensures.is_empty()
        || !plan.loop_measures.is_empty()
        || !plan.assert_by.is_empty()
        || !plan.recommends.is_empty();
    if !has_any {
        return Err(ValidationError::EmptyContext);
    }
    if plan.assertions.is_empty()
        && plan.loop_invariants.is_empty()
        && plan.loop_ensures.is_empty()
        && plan.loop_measures.is_empty()
        && plan.assert_by.is_empty()
        && plan.recommends.is_empty()
    {
        return Err(ValidationError::OnlyAssumptions);
    }

    Ok(ValidatedPreparedContext { plan, source: ctx })
}

/// Validate structural integrity of a single obligation.
fn validate_obligation_integrity(obligation: &PreparedObligation) -> Result<(), ValidationError> {
    // Rule 3 (checked first): legacy-translated obligations with structured metadata.
    // If the obligation arrived via legacy string translation, it must not carry
    // structured metadata that the string path cannot faithfully represent.
    if obligation.condition_origin == ConditionOrigin::LegacyTranslatedString {
        if obligation.trigger_patterns.is_some() {
            return Err(ValidationError::LegacyStructuredObligation {
                obligation_name: obligation.name.clone(),
                kind: obligation.kind,
                reason: "requires trigger patterns that legacy translation cannot preserve",
            });
        }
        if obligation.bound_vars.is_some() && obligation.kind == ObligationKind::BroadcastAssume {
            return Err(ValidationError::LegacyStructuredObligation {
                obligation_name: obligation.name.clone(),
                kind: obligation.kind,
                reason: "is a quantified broadcast that requires typed bound variable metadata",
            });
        }
        if matches!(
            obligation.kind,
            ObligationKind::MeasureNonNegative | ObligationKind::MeasureDecreases
        ) {
            return Err(ValidationError::LegacyStructuredObligation {
                obligation_name: obligation.name.clone(),
                kind: obligation.kind,
                reason: "requires measure semantics that legacy translation cannot encode",
            });
        }
    }

    // Rule 1: trigger-bearing obligations must not lose trigger groups.
    if let Some(trigger_patterns) = &obligation.trigger_patterns {
        if let Some(prepared_triggers) = &obligation.prepared_triggers {
            if prepared_triggers.len() != trigger_patterns.len() {
                return Err(ValidationError::MalformedTrigger {
                    obligation_name: obligation.name.clone(),
                    expected_groups: trigger_patterns.len(),
                    lowered_groups: prepared_triggers.len(),
                });
            }
            for (raw_group, prepared_group) in trigger_patterns.iter().zip(prepared_triggers) {
                if prepared_group.len() != raw_group.len() {
                    return Err(ValidationError::MalformedTrigger {
                        obligation_name: obligation.name.clone(),
                        expected_groups: trigger_patterns.iter().map(Vec::len).sum(),
                        lowered_groups: prepared_triggers.iter().map(Vec::len).sum(),
                    });
                }
            }
        }
        // If trigger_patterns is present but prepared_triggers is None,
        // the triggers were never lowered — this is lossy.
        if obligation.prepared_triggers.is_none() && !trigger_patterns.is_empty() {
            return Err(ValidationError::MalformedTrigger {
                obligation_name: obligation.name.clone(),
                expected_groups: trigger_patterns.len(),
                lowered_groups: 0,
            });
        }
    }

    // Rule 2: broadcast guard clause loss. Broadcast obligations with raw
    // guard clauses must arrive with a lowered typed guard expression.
    if obligation.kind == ObligationKind::BroadcastAssume
        && obligation.raw_broadcast_guard_count > 0
        && obligation.broadcast_guard.is_none()
    {
        return Err(ValidationError::DroppedBroadcastGuard {
            obligation_name: obligation.name.clone(),
        });
    }

    // Rule 4 (#2778 diagnostic parity): a `by(bit_vector)` proof must reject
    // constructs the bit-vector prover cannot model, with the byte-exact
    // upstream Verus message.
    if obligation.solver_mode == Some(crate::vc::SolverMode::BitVector) {
        if let Some(message) = detect_bit_vector_parity_error(&obligation.expr) {
            return Err(ValidationError::BitVectorParity {
                obligation_name: obligation.name.clone(),
                message,
            });
        }
    }

    Ok(())
}

/// Detects, for a `by(bit_vector)` proof body, the first construct the
/// bit-vector prover provably cannot model, returning the byte-exact upstream
/// Verus diagnostic.
///
/// Two sound, faithful categories are detected (#2778):
///
/// 1. An operand whose *type* the bit-vector prover cannot model. This routes
///    the **actual operand type** (via [`infer_expr_type`]) through the
///    diagnostic-parity surface, so the message surfaces from the real upstream
///    operand — a bare variable, a spec-function call result, an indexed
///    element, a cast result, a let-bound value, etc. — rather than a downstream
///    sort-metadata surrogate produced by the encoder. Two sub-cases:
///    * Non-finite-width integers (`int`/`nat`) →
///      `expected finite-width integer` (upstream
///      `bitvector.rs::not_supported_int_in_by_bit_vector`). A *compile-time
///      constant* of `int`/`nat` type (e.g. `0int`, `0 as int`) is folded and
///      accepted by upstream (`const_int_in_by_bit_vector` is `Ok`), so constants
///      are never flagged — only symbolic (non-constant) `int`/`nat` operands.
///    * A user-defined datatype (struct/enum) →
///      `bit_vector prover cannot handle type `<typ>`` (upstream
///      `not_supported_datatype_in_by_bit_vector`). Datatypes are unmodellable
///      regardless of constness, so they are flagged unconditionally.
///
/// 2. A bit-shift (`<<`/`>>`) whose right-hand operand has a *signed* type. The
///    upstream bit-vector encoder sign-extends a signed RHS and rejects any
///    shift whose shift amount could be negative — upstream
///    `overflow.rs::spec_bitshift_negative` (`1i8 >> (-1i8)`). The check is
///    purely on the RHS *type* (signed ⇒ possibly negative), matching Verus's
///    `Extend::Sign` test rather than the concrete value, so it is sound and
///    never fires for an unsigned shift amount.
///
/// Returns `None` when no such construct is present (the proof is left to the
/// solver). This never fabricates a passing verdict — it only converts an
/// already-present, provably-unsupported construct into the parity message.
fn detect_bit_vector_parity_error(expr: &crate::ir_expr::TrustVcExpr) -> Option<String> {
    use crate::ir_expr::{SpecialArithOp, TrustVcExpr};
    use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

    struct BitVectorParityVisitor {
        error: Option<crate::ir_lowering::LoweringError>,
    }

    impl TrustVcExprVisitor for BitVectorParityVisitor {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if self.error.is_some() {
                return;
            }
            // Category 1: an operand of a type the bit-vector prover cannot
            // model. We key on the *inferred operand type* of the actual
            // upstream sub-expression (variable, call, index, cast, …) so the
            // parity message surfaces from the real operand rather than a
            // downstream encoder sort-metadata surrogate.
            if let Some(err) = unmodellable_operand_error(expr) {
                self.error = Some(err);
                return;
            }
            // Category 2: bit-shift with a signed (possibly-negative) RHS.
            if let TrustVcExpr::SpecialArith {
                op: SpecialArithOp::Shl | SpecialArithOp::Shr,
                right,
                ..
            } = expr
            {
                let rhs_ty = crate::ir_lowering::infer_expr_type(right);
                if matches!(rhs_ty, crate::ir::TrustVcType::Int { .. }) {
                    self.error =
                        Some(crate::ir_lowering::diagnostic_parity::bit_shift_possibly_negative());
                    return;
                }
            }
            walk_expr(self, expr);
        }
    }

    let mut visitor = BitVectorParityVisitor { error: None };
    visitor.visit_expr(expr);
    visitor.error.map(|err| err.to_string())
}

/// Returns the byte-exact parity error for an operand the bit-vector prover
/// cannot model, or `None` if `expr` is a modellable / bool-typed / structural
/// node.
///
/// The classification keys on the operand and its inferred type, faithfully
/// mirroring upstream's two distinct rejection sites:
///
/// - A **variable declared at non-finite-width integer type** (`int`/`nat`) →
///   `expected finite-width integer`. We match on `Var` here, *not* on the
///   inferred type, because an `as int` widening cast of a finite-width value
///   (e.g. `x as int` with `x: i8`) is modellable upstream — the source bit
///   width is known, so the bit-vector encoder widens it. Flagging by inferred
///   type would wrongly reject those verified `(x as int) / (-1 as int)` cases.
///   A bare `int`/`nat` *variable* has no source width and is genuinely
///   non-finite-width, matching `not_supported_int_in_by_bit_vector`. (An
///   `int`/`nat` *literal* like `0int` is an `IntLit`, never a `Var`, so it is
///   correctly accepted — `const_int_in_by_bit_vector`.)
///
/// - An **operand of user-defined datatype type** (struct/enum), via the
///   inferred operand type, so the rejection surfaces from the actual operand —
///   a bare variable, a spec-function call returning the datatype, an indexed
///   element, etc. — rather than a downstream encoder sort-metadata surrogate.
///   A datatype has no finite-width encoding by any route, so this is flagged
///   unconditionally → `bit_vector prover cannot handle type `<typ>`` (upstream
///   `not_supported_datatype_in_by_bit_vector`).
///
/// SOUNDNESS: this only fires when the operand is provably unmodellable by the
/// bit-vector solver; it converts an already-present, unsupported operand into
/// the parity message and never fabricates a passing verdict.
fn unmodellable_operand_error(
    expr: &crate::ir_expr::TrustVcExpr,
) -> Option<crate::ir_lowering::LoweringError> {
    use crate::ir_expr::TrustVcExpr;

    // Non-finite-width integer *variable* (declared `int`/`nat`, no source
    // width): `expected finite-width integer`.
    if let TrustVcExpr::Var {
        ty: ty @ (crate::ir::TrustVcType::MathInt | crate::ir::TrustVcType::Nat),
        ..
    } = expr
    {
        return Some(crate::ir_lowering::diagnostic_parity::bit_vector_expected_finite_width(ty));
    }

    // Any operand whose inferred type is a user-defined datatype is unmodellable
    // regardless of how it is produced (variable, call result, indexed element,
    // …). We emit the upstream `bit_vector prover cannot handle type` message
    // with this build's diagnostic type name. NOTE: trust-vc does not carry the
    // upstream crate prefix (`test_crate::`), so this is a SOUND fail-closed
    // rejection but is not claimed as byte-exact closure of
    // `not_supported_datatype_in_by_bit_vector`.
    match crate::ir_lowering::infer_expr_type(expr) {
        crate::ir::TrustVcType::Datatype { name, .. }
        | crate::ir::TrustVcType::RecursiveRef(name) => {
            Some(crate::ir_lowering::diagnostic_parity::bit_vector_cannot_handle_type(&name))
        }
        _ => None,
    }
}

/// Classify obligations into execution lanes.
fn classify_obligations(
    ctx: &PreparedVerificationContext,
) -> Result<VerificationPlan<'_>, ValidationError> {
    let mut assumptions = Vec::new();
    let mut broadcast_assumptions = Vec::new();
    let mut loop_invariants = Vec::new();
    let mut loop_guards = Vec::new();
    let mut loop_ensures = Vec::new();
    let mut loop_measures = Vec::new();
    let mut assert_by = Vec::new();
    let mut assertions = Vec::new();
    let mut recommends = Vec::new();
    let mut opened_namespaces: HashSet<i64> = HashSet::new();

    for obligation in &ctx.obligations {
        match obligation.kind {
            ObligationKind::Assume | ObligationKind::PostLoopAssume => {
                assumptions.push(obligation);
            }
            ObligationKind::LoopGuard => loop_guards.push(obligation),
            ObligationKind::Requires => match ctx.verification_mode {
                VerificationMode::BodyLevel => assumptions.push(obligation),
                VerificationMode::CallSite => assertions.push(obligation),
                #[allow(unreachable_patterns)]
                _ => assertions.push(obligation),
            },
            ObligationKind::BroadcastAssume => broadcast_assumptions.push(obligation),
            ObligationKind::LoopInvariant | ObligationKind::InvariantExceptBreak => {
                loop_invariants.push(obligation);
            }
            ObligationKind::LoopEnsures => loop_ensures.push(obligation),
            ObligationKind::AssertBy => assert_by.push(obligation),
            ObligationKind::Reveal => {} // Metadata — consumed by setup_from_prepared
            ObligationKind::Hide => {}   // Metadata — consumed by prepare() hidden_fns derivation
            // Metadata — a body-ordered broadcast-group activation marker,
            // consumed by the position-aware broadcast gate
            // (`active_broadcast_groups_before`). Carries no proof obligation.
            ObligationKind::BroadcastUse => {}
            ObligationKind::InvariantOpen => {
                let ns = match obligation.invariant_namespace {
                    Some(ns) => ns,
                    None => {
                        return Err(ValidationError::InvariantMissingNamespace {
                            obligation_name: obligation.name.clone(),
                        });
                    }
                };
                if !ctx.invariant_mask.allows(ns) {
                    return Err(ValidationError::InvariantMaskViolation {
                        obligation_name: obligation.name.clone(),
                        namespace: ns,
                    });
                }
                if !opened_namespaces.insert(ns) {
                    return Err(ValidationError::InvariantReentrancy {
                        obligation_name: obligation.name.clone(),
                        namespace: ns,
                    });
                }
                assumptions.push(obligation);
            }
            ObligationKind::InvariantClose => assertions.push(obligation),
            // A loop-scoped `loop_decreases!` measure (the non-negativity floor
            // AND its strict-descent companion) carries loop metadata —
            // registered under the obligation name in `loop_modified_vars` by the
            // file-path extractor. BOTH the `{m}_nonneg` and `{m}_decreases`
            // names must be registered there so NEITHER spills into the flat
            // `assertions` lane: the nonneg is verified in the measure's int sort
            // (WF1), and a loop-scoped int-mode nonneg in the shared assertions
            // lane would leave the loop variable typed `MathInt`, clashing with
            // the post-loop normal-exit `Uint` assumption. A bare recursive
            // `#[decreases]` obligation and a non-loop `MeasureNonNegative` have
            // no such metadata and stay in `assertions`.
            ObligationKind::MeasureDecreases | ObligationKind::MeasureNonNegative
                if ctx.loop_modified_vars.contains_key(&obligation.name) =>
            {
                loop_measures.push(obligation);
            }
            ObligationKind::Assert
            | ObligationKind::Ensures
            | ObligationKind::MeasureNonNegative
            | ObligationKind::MeasureDecreases => assertions.push(obligation),
            // SOUNDNESS-CRITICAL (recommends assumed in the body → false-verify):
            // `recommends` is ADVISORY — unlike `requires` it must NOT be assumed
            // when proving the function's OWN body/ensures (Verus proves the
            // ensures WITHOUT recommends; recommends is only a soft-warning check,
            // handled via the `recommends` list at typed.rs). Pushing it to
            // `assumptions` at BodyLevel assumed the recommends predicate as a
            // body hypothesis, so `#[recommends(x==0)] #[ensures(result==0)]
            // fn f(x)->i32 { x }` VERIFIED (real result is x). Always route it to
            // the soft-check `recommends` list — never a hard assumption.
            ObligationKind::Recommends => recommends.push(obligation),
            #[allow(unreachable_patterns)]
            _ => {
                // Fail-closed: unknown obligation kind is not silently ignored.
                return Err(ValidationError::LegacyStructuredObligation {
                    obligation_name: obligation.name.clone(),
                    kind: obligation.kind,
                    reason: "has an unrecognized obligation kind",
                });
            }
        }
    }

    Ok(VerificationPlan {
        assumptions,
        broadcast_assumptions,
        loop_invariants,
        loop_guards,
        loop_ensures,
        loop_measures,
        assert_by,
        assertions,
        recommends,
    })
}

#[cfg(test)]
#[path = "validation_tests.rs"]
mod tests;
