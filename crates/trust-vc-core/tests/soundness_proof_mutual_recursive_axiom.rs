// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Soundness regression (round-8, mutual-recursion broadcast/proof lemma class):
//! a proof/broadcast lemma that participates in an ill-founded recursion CYCLE
//! (mutual `la -> lb -> la`, a longer `c1 -> c2 -> c3 -> c1`, or even direct
//! self-recursion observed from an external caller) with no `#[decreases]`
//! termination measure must never publish a usable `ensures` axiom (or, for a
//! value-returning helper, a usable single-return body axiom). Otherwise each
//! lemma's postcondition is discharged circularly from a mutual partner's
//! equally-unproven postcondition, and a false goal verifies vacuously.
//!
//! Sibling of `soundness_proof_recursive_axiom.rs` (direct self-recursion body
//! axiom) and `soundness_recursive_axiom.rs` (the `#[trust_vc::spec]` catalog
//! class). Gate lives in `vc_extraction.rs::ill_founded_recursive_function_names`,
//! consumed by `collect_referenced_sibling_helper_contracts` (call-site
//! `ensures`), `SiblingHelperDef::from_item_fn_with_name`, and
//! `InherentMethodDef::from_impl_method` (body axioms).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/proof_mutual_recursive_axiom_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

// ---- The hole: every false goal driven by an ill-founded recursive lemma ----

#[test]
fn mutually_recursive_broadcast_lemmas_must_not_prove_false() {
    let v = verdict("exploit_broadcast_mutual");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: op(3) = (3 > 100) = false certified via a mutually-recursive \
         broadcast lemma pair with no #[decreases]. Verdict: {v:?}"
    );
}

#[test]
fn mutually_recursive_proof_lemmas_must_not_prove_false() {
    let v = verdict("exploit_proof_mutual");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: false op(3) certified via a mutually-recursive plain #[proof] \
         lemma pair. Verdict: {v:?}"
    );
}

#[test]
fn self_recursive_lemma_ensures_must_not_be_trusted_by_external_caller() {
    let v = verdict("exploit_self_external");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: an external caller trusted the ensures of a self-recursive \
         lemma whose own postcondition is ill-founded (no #[decreases]). \
         Verdict: {v:?}"
    );
}

#[test]
fn three_function_cycle_must_not_prove_false() {
    let v = verdict("exploit_cycle3");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: false op(3) certified via a 3-function recursion cycle \
         c1 -> c2 -> c3 -> c1. Verdict: {v:?}"
    );
}

#[test]
fn value_returning_mutual_recursion_body_axiom_must_not_prove_false() {
    // fa(n) == fb(n)+1, fb(n) == fa(n)  =>  fa(n) == fa(n)+1  =>  false.
    let v = verdict("exploit_value_mutual");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: fa(3) == fa(3) + 100 certified via a contradictory \
         value-returning mutual-recursion body axiom. Verdict: {v:?}"
    );
}

// ---- Controls: the false / opaque goals must NOT verify WITHOUT a lemma ----

#[test]
fn control_op_without_lemma_does_not_verify() {
    let v = verdict("control_no_lemma");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "control: op(3) must be unprovable without any lemma; got {v:?}"
    );
}

#[test]
fn control_opaque_predicate_without_lemma_does_not_verify() {
    let v = verdict("control_nonrec_opaque");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "control: opaque p(3) must be unprovable without the lemma's ensures; \
         got {v:?}"
    );
}

// ---- No over-rejection: well-founded / non-recursive ensures stay TRUSTED ----

#[test]
fn well_founded_self_recursive_lemma_ensures_still_trusted() {
    // Discriminating: the caller can only learn the OPAQUE p(3) via wf_self's
    // ensures (control_opaque proves it is otherwise unprovable). A #[decreases]
    // cycle member must NOT be suppressed.
    assert!(
        matches!(verdict("caller_wf_self"), VerifyResult::Verified),
        "OVER-REJECTION: a well-founded (#[decreases]) self-recursive lemma's \
         opaque ensures must still be trusted at an external call site"
    );
}

#[test]
fn well_founded_mutual_recursion_with_decreases_still_verifies() {
    assert!(
        matches!(verdict("caller_wellfounded_mutual"), VerifyResult::Verified),
        "OVER-REJECTION: a well-founded mutually-recursive pair WITH #[decreases] \
         on every member must still be usable from a caller"
    );
}

#[test]
fn fn_value_routed_mutual_recursion_must_not_prove_false() {
    // S2: fv_a/fv_b recurse through fn-item VALUES (let f = partner; f(i)); the
    // direct-call graph misses that edge, so without the fn-value edge detector the
    // ill-founded cycle's circular ensures op(i) is trusted and op(3) = false verifies.
    let v = verdict("exploit_fnvalue_mutual");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "S2 FALSE-VERIFY: a mutual proof-fn cycle routed through fn-item values must \
         not publish its ensures; op(3) is false; got {v:?}"
    );
}

#[test]
fn fn_value_shadow_and_alias_cycle_must_not_prove_false() {
    let v = verdict("exploit_fnvalue_shadow_alias_mutual");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "FALSE-VERIFY: an outer fn-item binding lost after an inner shadow (and a \
         transitive/same-name alias) hid a mutual recursion cycle; got {v:?}"
    );
}

#[test]
fn reassigned_fn_value_cycle_must_fail_closed() {
    let v = verdict("exploit_fnvalue_reassignment");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "FALSE-VERIFY: a reassigned function-item local hid its recursive target; \
         the incomplete call graph must suppress the contract; got {v:?}"
    );
}

#[test]
fn unmodelable_decreases_cycle_must_fail_closed() {
    let v = verdict("exploit_unmodelable_ref_decreases");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "FALSE-VERIFY: a #[decreases] cycle whose reference signatures cannot be \
         modeled was trusted on semantic verdict None; got {v:?}"
    );
}

#[test]
fn non_cyclic_fn_value_call_ensures_still_trusted() {
    // Over-rejection guard for S2: a NON-recursive call through a fn-item value must
    // still bring the callee's ensures into scope. `fv_id` is a proof function,
    // which panics when the exec body calls it at run time, so the ghost-call
    // rule refuses the answer; it refuses only a `Verified` answer.
    let v = verdict("caller_fnvalue_noncyclic");
    assert!(
        matches!(
            &v,
            VerifyResult::Error { message }
                if message.contains("ghost function called from exec code")
        ),
        "OVER-REJECTION: a non-cyclic fn-item-value call must still trust the callee's \
         opaque ensures (a `Verified` answer, refused by the ghost-call rule); got {v:?}"
    );
}

#[test]
fn non_cyclic_fn_value_alias_and_shadow_ensures_still_trusted() {
    assert!(
        matches!(
            verdict("caller_fnvalue_alias_shadow_nonrecursive"),
            VerifyResult::Verified
        ),
        "OVER-REJECTION: scoped function-item aliases that resolve only to \
         non-recursive leaves must not suppress the enclosing helper's ensures"
    );
}

#[test]
fn mutually_recursive_bogus_decreases_must_not_prove_false() {
    // S1: both members carry #[decreases(i)] (Stage-1 structural gate passes), but the
    // measure does NOT shrink on the bogus_b -> bogus_a edge, so the cycle is not
    // termination-guarded. The semantic Stage-2 proof must catch it and suppress the
    // circular `ensures op(i)`, or op(3) = (3 > 100) = false verifies.
    let v = verdict("exploit_bogus_decreases_mutual");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "S1 FALSE-VERIFY: a mutual proof-fn cycle with a NON-shrinking #[decreases] \
         must not publish its ensures; op(3) is false; got {v:?}"
    );
}

#[test]
fn non_recursive_lemma_opaque_ensures_still_trusted() {
    assert!(
        matches!(verdict("caller_nonrec_opaque"), VerifyResult::Verified),
        "OVER-REJECTION: a non-recursive lemma's opaque ensures must still be \
         trusted at the call site"
    );
}

#[test]
fn non_recursive_value_helper_body_axiom_still_verifies() {
    assert!(
        matches!(verdict("caller_value_nonrec"), VerifyResult::Verified),
        "OVER-REJECTION: a non-recursive value-returning helper body axiom must \
         still prove inc(5) == 6"
    );
}
