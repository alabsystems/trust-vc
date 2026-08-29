//! Direct defining axioms for recursive function unfolding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Instead of a circular `forall x. f(x) == body(f(x))`, emits a
//! direct defining axiom with E-matching trigger:
//!
//!   `forall x. {f(x)} f(x) == body(x)`
//!
//! ay-dpll's hard E-matching round limit (`MAX_EMATCHING_ROUNDS = 8`)
//! prevents infinite instantiation, providing implicit fuel=8 with a
//! single function name. This enables both concrete evaluation and
//! symbolic reasoning (e.g., `gcd(a,b) == gcd(b,a%b)`).
//!
//! Previously used Verus-style stratified fuel encoding (f__fuel_k),
//! but renamed functions break symbolic equality proofs. Part of #2155, #2187.

use ay_dpll::api::Term;

use super::ground_pool::GroundAxiom;
use super::AYEncoder;
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{CompareOp, TrustVcExpr};
use crate::prepared_context::PreparedObligation;
use crate::vc::FunctionContext;

/// Decomposes a body axiom expression `f(x) == <body>` into the LHS
/// function call args and the RHS body expression.
///
/// Returns `(lhs_args, body_rhs)` where `lhs_args` are the `TrustVcExpr`
/// arguments of the defining function call, and `body_rhs` is the body.
fn decompose_body_axiom<'a>(
    expr: &'a TrustVcExpr,
    func_name: &str,
) -> TrustVcResult<(&'a [TrustVcExpr], &'a TrustVcExpr)> {
    match expr {
        TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left,
            right,
        } => match left.as_ref() {
            TrustVcExpr::FnCall { name, args, .. } if name == func_name => Ok((args, right)),
            _ => Err(TrustVcError::Encoding {
                context: "fuel encoding",
                detail: format!(
                    "Body axiom LHS is not a call to '{}': {:?}",
                    func_name, left
                ),
            }),
        },
        _ => Err(TrustVcError::Encoding {
            context: "fuel encoding",
            detail: format!(
                "Body axiom is not an equality (Compare::Eq): {:?}",
                std::mem::discriminant(expr)
            ),
        }),
    }
}

/// Builds a trigger string for a function call pattern.
///
/// Given function name `"gcd"` and param names `["a", "b"]`,
/// returns `"gcd(a, b)"`.
fn fuel_trigger_string(func_name: &str, param_names: &[&str]) -> String {
    format!("{}({})", func_name, param_names.join(", "))
}

fn resolve_bound_var_terms(
    encoder: &AYEncoder,
    obligation_name: &str,
    bound_names: &[String],
) -> TrustVcResult<Vec<Term>> {
    let filtered: Vec<Term> = bound_names
        .iter()
        .filter_map(|name| encoder.variables.get(name).copied())
        .collect();
    if filtered.len() < bound_names.len() {
        let missing: Vec<&String> = bound_names
            .iter()
            .filter(|name| !encoder.variables.contains_key(name.as_str()))
            .collect();
        return Err(TrustVcError::Encoding {
            context: "fuel encoding",
            detail: format!(
                "Recursive body axiom '{}': {}/{} bound variables not found in scope: {:?}",
                obligation_name,
                missing.len(),
                bound_names.len(),
                missing,
            ),
        });
    }
    Ok(filtered)
}

/// Encodes recursive function body axioms using a direct defining axiom.
///
/// Instead of the circular `forall x. f(x) == body(f(x))`, emits:
/// 1. A direct defining axiom: `forall x. {f(x)} f(x) == body(x)` using the
///    ORIGINAL function name on both sides. ay-dpll's E-matching round limit
///    (`MAX_EMATCHING_ROUNDS = 8`) provides implicit fuel bounding.
/// 2. Ground-pool registration of the body axiom for one-step instantiation
///    on already-present calls `f(t1, ..., tn)`.
///
/// Previously used stratified fuel encoding (f__fuel_0..f__fuel_N + linking),
/// but the renamed functions break symbolic reasoning: `gcd_2(b, a%b)` cannot
/// equal `gcd_3(b, a%b)`. The direct axiom uses the same name on both sides,
/// enabling E-matching to chain: `gcd(a,b) → gcd(b,a%b) → ...`
///
pub(super) fn encode_fuel_axioms(
    encoder: &mut AYEncoder,
    func_ctx: &FunctionContext,
    body_axiom: &PreparedObligation,
    all_var_terms: &[Term],
) -> TrustVcResult<()> {
    let func_name = &func_ctx.name;

    // Decompose: f(x) == <body>
    let (lhs_args, body_rhs) = decompose_body_axiom(&body_axiom.expr, func_name)?;

    // Select quantifier variables: use bound_vars from the obligation if
    // present, otherwise fall back to all variables. This matches the
    // behavior of add_typed_broadcast (broadcast.rs:73-97) and avoids
    // over-quantification when extra variables exist in scope.
    let var_terms: Vec<Term> = if let Some(ref bound_names) = body_axiom.bound_vars {
        resolve_bound_var_terms(encoder, &body_axiom.name, bound_names)?
    } else {
        all_var_terms.to_vec()
    };

    // Collect param names for trigger string construction
    let param_names: Vec<&str> = func_ctx.params.iter().map(|(n, _)| n.as_str()).collect();

    // Step 1: Register the original recursive body axiom with the ground pool
    // so `flush_ground_axioms_to_fixpoint()` can materialize a one-step
    // equality for any concrete or symbolic call already present in the query.
    if let Some(bound_vars) = body_axiom.bound_vars.as_ref() {
        let seed_symbols: Vec<String> = body_axiom
            .eager_seed_symbols()
            .into_iter()
            .map(|symbol| symbol.into_owned())
            .collect();
        if !seed_symbols.is_empty() {
            encoder.state.ground_pool.register_axiom(GroundAxiom {
                name: body_axiom.name.clone(),
                seed_symbols,
                seed_triggers: Vec::new(),
                bound_vars: bound_vars.clone(),
                expr: body_axiom.expr.clone(),
            });
        }
    }

    // Step 2: Direct defining axiom for concrete and symbolic reasoning.
    //
    // forall x. {f(x)} f(x) == body(x) [with original function name]
    //
    // E-matching fires on any ground `f(t1, t2)` term, producing new terms
    // in the body. Recursive calls in the body create new trigger matches,
    // chaining up to MAX_EMATCHING_ROUNDS (8). This handles:
    //   - Concrete: gcd(6,4) → gcd(4,2) → gcd(2,0) → 2  (3 rounds)
    //   - Symbolic: gcd(a,b) → gcd(b,a%b)                 (1 round)
    //
    // Safety: ay-dpll's hard E-matching round limit (8) prevents infinite
    // instantiation. Equivalent to implicit fuel=8 with a single function
    // name, avoiding the stratified fuel name mismatch that blocks symbolic
    // equality proofs. Part of #2187.
    let direct_lhs = TrustVcExpr::FnCall {
        name: func_name.clone(),
        args: lhs_args.to_vec(),
        return_ty: func_ctx.return_type.clone(),
    };
    let direct_axiom = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(direct_lhs),
        right: Box::new(body_rhs.clone()),
    };

    // BINDER CAPTURE (CARDINAL), same shape as `add_typed_broadcast`: the body is
    // encoded here with every bound variable resolved as an ordinary top-level
    // term, and the `forall` over those terms is only built below. Announce the
    // pending closure so encoder helpers that would hoist a derived fact to the
    // solver top level decline instead of letting that binder capture it. See
    // `ir_encoder::match_encode::bind_datatype_match_result` for the measured
    // instance ("f is a CONSTANT function").
    //
    // The flag is a per-site OPT-IN and only two helpers take it, so the CLASS
    // is closed by the watermark instead: after the encode, before the
    // `forall`, ask whether anything asserted in between mentions a term the
    // binder will bind. See `crate::encoder::binder_capture`.
    let capture_watermark = encoder.assertion_watermark();
    let direct_term = crate::encoder::with_flag_unwind_safe!(
        encoder.state.pending_universal_closure,
        !var_terms.is_empty(),
        {
            crate::encoder::with_flag_unwind_safe!(encoder.state.in_assumption_context, true, {
                encoder.resolve_condition_typed(&direct_axiom)
            })
        }
    );
    let direct_term = direct_term.map_err(|e| TrustVcError::Encoding {
        context: "fuel encoding: direct defining axiom",
        detail: format!("Failed to encode direct axiom: {}", e),
    })?;

    if var_terms.is_empty() {
        encoder
            .solver
            .try_assert_term(direct_term)
            .map_err(|e| TrustVcError::Encoding {
                context: "fuel encoding: direct assert",
                detail: format!("Failed to assert direct axiom: {}", e),
            })?;
        return Ok(());
    }

    if let Some(capture) = encoder.binder_capture_since(capture_watermark, &var_terms) {
        // The defining axiom would be captured (measured instance:
        // `forall n. half(n) == __euclid_q_0`, which combined with the ground
        // replay of the same body makes the whole context INCONSISTENT and lets
        // `half(2) == 5` verify). Decline it: `func_name` stays uninterpreted
        // for symbolic reasoning while the ground-pool registration above —
        // which re-encodes per concrete instance and therefore cannot be
        // captured — is untouched.
        let site = format!("fuel:{func_name}");
        encoder.record_binder_capture(&site, &capture);
        return Ok(());
    }

    let trigger_str = fuel_trigger_string(func_name, &param_names);

    let direct_trigger =
        encoder
            .encode_trigger_typed(&trigger_str)
            .map_err(|e| TrustVcError::Encoding {
                context: "fuel encoding: direct trigger",
                detail: format!("Failed to encode direct trigger '{}': {}", trigger_str, e),
            })?;
    let direct_quantified = encoder
        .solver
        .try_forall_with_triggers(&var_terms, direct_term, &[&[direct_trigger]])
        .map_err(|e| TrustVcError::Encoding {
            context: "fuel encoding: direct forall",
            detail: format!("Failed to create forall for direct axiom: {}", e),
        })?;
    encoder
        .solver
        .try_assert_term(direct_quantified)
        .map_err(|e| TrustVcError::Encoding {
            context: "fuel encoding: direct assert",
            detail: format!("Failed to assert direct axiom: {}", e),
        })?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TrustVcType;

    #[test]
    fn test_decompose_body_axiom_valid() {
        let expr = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::FnCall {
                name: "fact".to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                }],
                return_ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Int { width: 32 },
            }),
        };
        let (args, body) = decompose_body_axiom(&expr, "fact").unwrap();
        assert_eq!(args.len(), 1);
        assert!(matches!(body, TrustVcExpr::IntLit { value: 1, .. }));
    }

    #[test]
    fn test_decompose_body_axiom_wrong_func_name() {
        let expr = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::FnCall {
                name: "other".to_string(),
                args: vec![],
                return_ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Int { width: 32 },
            }),
        };
        assert!(decompose_body_axiom(&expr, "fact").is_err());
    }

    #[test]
    fn test_decompose_body_axiom_not_equality() {
        let expr = TrustVcExpr::BoolLit(true);
        assert!(decompose_body_axiom(&expr, "fact").is_err());
    }

    #[test]
    fn test_fuel_trigger_string_single_param() {
        assert_eq!(fuel_trigger_string("fact", &["x"]), "fact(x)");
    }

    #[test]
    fn test_fuel_trigger_string_multi_param() {
        assert_eq!(fuel_trigger_string("gcd", &["a", "b"]), "gcd(a, b)");
    }
}
