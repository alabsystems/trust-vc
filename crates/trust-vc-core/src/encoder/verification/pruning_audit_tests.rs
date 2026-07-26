//! Strategic audit tests for pruning.rs (P1-581, #2520).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verifies edge cases found during Prover strategic audit of the
//! SMT reachability pruning module.

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use crate::encoder::verification::pruning::build_prune_plan;
    use crate::ir::{CompareOp, TrustVcExpr, TrustVcType};
    use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
    use crate::vc::ObligationKind;

    fn make_obligation(name: &str, expr: TrustVcExpr) -> PreparedObligation {
        PreparedObligation {
            name: name.to_string(),
            kind: ObligationKind::Assert,
            location: None,
            condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
            bound_vars: None,
            trigger_patterns: None,
            prepared_triggers: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            condition: String::new(),
            expr,
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            raw_broadcast_guard_count: 0,
            step_meta: None,
        }
    }

    fn make_broadcast(
        name: &str,
        expr: TrustVcExpr,
        triggers: Option<Vec<Vec<String>>>,
    ) -> PreparedObligation {
        PreparedObligation {
            name: name.to_string(),
            kind: ObligationKind::BroadcastAssume,
            location: None,
            condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
            bound_vars: Some(vec!["x".to_string()]),
            trigger_patterns: triggers,
            prepared_triggers: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            condition: String::new(),
            expr,
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            raw_broadcast_guard_count: 0,
            step_meta: None,
        }
    }

    fn fn_call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
        TrustVcExpr::FnCall {
            name: name.to_string(),
            args,
            return_ty: TrustVcType::Int { width: 32 },
        }
    }

    fn var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: TrustVcType::Int { width: 32 },
        }
    }

    fn make_ctx() -> PreparedVerificationContext {
        PreparedVerificationContext {
            obligations: Vec::new(),
            variables: Vec::new(),
            function_context: None,
            trait_decls: Vec::new(),
            trait_impl_decls: Vec::new(),
            verification_mode: crate::vc::VerificationMode::default(),
            overflow_behavior: crate::vc::OverflowBehavior::default(),
            div0_behavior: crate::vc::Div0Behavior::default(),
            bitshift_behavior: crate::vc::BitshiftBehavior::default(),
            broadcast_use_groups: HashSet::new(),
            assert_by_scopes: HashMap::new(),
            forall_bound_vars: HashMap::new(),
            loop_guards: HashMap::new(),
            loop_modified_vars: HashMap::new(),
            has_collection_context: false,
            revealed_fns: HashSet::new(),
            helper_function_contexts: Vec::new(),
            struct_types: Vec::new(),
            type_invariants: HashMap::new(),
            invariant_mask: crate::vc::InvariantMask::default(),
            tracked_params: HashSet::new(),
            rlimit_ms: None,
            demand_inline: crate::vc::DemandInlineConfig::new(),
            counterexample_var_meta: HashMap::new(),
            ..Default::default()
        }
    }

    /// Verify that inline body axioms ARE traversed during prune plan
    /// expansion. The `is_inline` flag is only checked in setup.rs AFTER
    /// the prune plan is built — build_prune_plan treats all broadcasts
    /// uniformly. This means helper functions referenced in inline body
    /// axioms remain reachable even though the body axiom itself is later
    /// filtered out (substituted at encoding time). Part of #2520 audit.
    #[test]
    fn test_prune_plan_expands_through_inline_body_axioms() {
        // Obligation calls inline_fn A. A's body axiom references helper B.
        // The prune plan traverses A's body axiom (is_inline is NOT checked
        // by build_prune_plan) and discovers B as transitively reachable.
        let assertion = make_obligation("assert_inline", fn_call("inline_fn_a", vec![var("x")]));
        let mut inline_body = make_broadcast(
            "__body_axiom_inline_fn_a",
            TrustVcExpr::Compare {
                op: CompareOp::Eq,
                left: Box::new(fn_call("inline_fn_a", vec![var("x")])),
                right: Box::new(fn_call("helper_b", vec![var("x")])),
            },
            Some(vec![vec!["inline_fn_a(x)".to_string()]]),
        );
        inline_body.is_inline = true;

        let broadcast_b = make_broadcast(
            "broadcast_helper_b",
            TrustVcExpr::Compare {
                op: CompareOp::Ge,
                left: Box::new(fn_call("helper_b", vec![var("x")])),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::Int { width: 32 },
                }),
            },
            Some(vec![vec!["helper_b(x)".to_string()]]),
        );

        let mut ctx = make_ctx();
        ctx.obligations = vec![assertion];
        let broadcasts: Vec<&PreparedObligation> = vec![&inline_body, &broadcast_b];

        let plan = build_prune_plan(&ctx, &broadcasts);

        // inline_fn_a IS reachable (directly called by obligation)
        assert!(
            plan.is_helper_reachable("inline_fn_a"),
            "inline_fn_a should be reachable — directly called by assertion"
        );
        // inline_body IS reachable (its trigger head matches inline_fn_a)
        assert!(
            plan.is_broadcast_reachable(&inline_body),
            "inline body axiom should be reachable — trigger matches"
        );
        // helper_b IS reachable because the prune plan DOES traverse the
        // inline body axiom's expression during fixed-point expansion
        // (the prune plan treats all broadcasts uniformly regardless of
        // is_inline; the inline filtering happens in setup.rs AFTER pruning).
        assert!(
            plan.is_broadcast_reachable(&broadcast_b),
            "helper_b's broadcast should be reachable — inline body references it"
        );
    }

    /// Verify that assert_by scope obligations are seeded into the
    /// prune plan's reachable set. Functions referenced only in
    /// assert_by scopes (not in top-level obligations) must still be
    /// considered reachable. Part of #2520 audit.
    #[test]
    fn test_prune_plan_seeds_from_assert_by_scopes() {
        let assertion = make_obligation("assert_main", var("x"));
        let scope_ob = make_obligation("scope_fact", fn_call("scope_helper", vec![var("x")]));

        let broadcast_scope = make_broadcast(
            "broadcast_scope_helper",
            TrustVcExpr::Compare {
                op: CompareOp::Ge,
                left: Box::new(fn_call("scope_helper", vec![var("x")])),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::Int { width: 32 },
                }),
            },
            Some(vec![vec!["scope_helper(x)".to_string()]]),
        );

        let mut ctx = make_ctx();
        ctx.obligations = vec![assertion];
        ctx.assert_by_scopes
            .insert("assert_by_block".to_string(), vec![scope_ob]);
        let broadcasts: Vec<&PreparedObligation> = vec![&broadcast_scope];

        let plan = build_prune_plan(&ctx, &broadcasts);

        assert!(
            plan.is_helper_reachable("scope_helper"),
            "scope_helper should be reachable — referenced in assert_by scope"
        );
        assert!(
            plan.is_broadcast_reachable(&broadcast_scope),
            "broadcast for scope_helper should be reachable"
        );
    }
}
