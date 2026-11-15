// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::vc::ObligationKind;

#[path = "tests/assume_scope_soundness.rs"]
mod assume_scope_soundness;
#[path = "tests/bar_form_quantifier_attrs.rs"]
mod bar_form_quantifier_attrs;
#[path = "tests/basic_contracts/mod.rs"]
mod basic_contracts;
#[path = "tests/call_ensures_branch_scope.rs"]
mod call_ensures_branch_scope;
#[path = "tests/choose_extensionality.rs"]
mod choose_extensionality;
#[path = "tests/closure_body_soundness.rs"]
mod closure_body_soundness;
#[path = "tests/closure_capture_soundness.rs"]
mod closure_capture_soundness;
#[path = "tests/composed_to_set_contains.rs"]
mod composed_to_set_contains;
#[path = "tests/control_flow_assertions.rs"]
mod control_flow_assertions;
#[path = "tests/direct_field_write_framing.rs"]
mod direct_field_write_framing;
#[path = "tests/exec_arith_faithful_overflow.rs"]
mod exec_arith_faithful_overflow;
#[path = "tests/exec_arith_safety_faithful.rs"]
mod exec_arith_safety_faithful;
#[path = "tests/exec_index_bounds_faithful.rs"]
mod exec_index_bounds_faithful;
#[path = "tests/generic_adt_destructure.rs"]
mod generic_adt_destructure;
#[path = "tests/ghost_collection_reuse_after_combinator.rs"]
mod ghost_collection_reuse_after_combinator;
#[path = "tests/impl_ensures_canonicalization.rs"]
mod impl_ensures_canonicalization;
#[path = "tests/inherent_impl_methods.rs"]
mod inherent_impl_methods;
#[path = "tests/match_arm_scope_soundness.rs"]
mod match_arm_scope_soundness;
#[path = "tests/match_plain_tuple_expression_soundness.rs"]
mod match_plain_tuple_expression_soundness;
#[path = "tests/match_rest_pattern_expression_soundness.rs"]
mod match_rest_pattern_expression_soundness;
#[path = "tests/mut_ref_two_state.rs"]
mod mut_ref_two_state;
#[path = "tests/mut_ref_vocabulary.rs"]
mod mut_ref_vocabulary;
#[path = "tests/pointer_width_directive.rs"]
mod pointer_width_directive;
#[path = "tests/proof_block_ghost_add.rs"]
mod proof_block_ghost_add;
#[path = "tests/recursion_call_graph.rs"]
mod recursion_call_graph;
#[path = "tests/returns_postcondition.rs"]
mod returns_postcondition;
#[path = "tests/seq_concrete_ext_eq.rs"]
mod seq_concrete_ext_eq;
#[path = "tests/seq_map_index_cast.rs"]
mod seq_map_index_cast;
#[path = "tests/silent_drop_regressions.rs"]
mod silent_drop_regressions;
#[path = "tests/spec_function_catalog.rs"]
mod spec_function_catalog;
#[path = "tests/unsafe_signature_rejection.rs"]
mod unsafe_signature_rejection;
#[path = "tests/verifier_rlimit_attr.rs"]
mod verifier_rlimit_attr;

/// Count assertions (ObligationKind::Assert) in a VerificationContext.
pub(super) fn count_asserts(vc: &VerificationContext) -> usize {
    vc.obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .count()
}

/// Collect assertion condition strings from a VerificationContext.
pub(super) fn collect_assert_conditions(vc: &VerificationContext) -> Vec<String> {
    vc.obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .filter(|o| !is_synthetic_overflow_check(o))
        .map(|o| o.condition.clone())
        .collect()
}

pub(super) fn collect_assert_and_assert_by_conditions(vc: &VerificationContext) -> Vec<String> {
    vc.obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert | ObligationKind::AssertBy))
        .filter(|o| !is_synthetic_overflow_check(o))
        .map(|o| o.condition.clone())
        .collect()
}

/// Exec-arithmetic safety obligations (#2778) ride on `ObligationKind::Assert`
/// with a reflexive `(v) == (v)` condition so the per-obligation overflow
/// precheck fires. They are synthetic safety checks, not user assertions, so
/// structural helpers that inspect the user's scoped assertion list skip them.
fn is_synthetic_overflow_check(o: &ProofObligation) -> bool {
    o.name().starts_with("overflow_check_") || o.name().starts_with("index_bounds_check_")
}
