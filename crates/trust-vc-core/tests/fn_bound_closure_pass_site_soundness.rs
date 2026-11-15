// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for INCREMENT 2b of Fn-bound closure
//! dispatch (cross-boundary PASS-SITE linkage): a caller passes a concrete
//! `trust_vc::closure!` literal `c` into an `F: Fn(u64) -> u64`-bounded callee
//! `g` whose contract REFLECTS it (`requires f.requires((a,))` /
//! `ensures f.ensures((a,), result)`).
//!
//! THE LINKAGE. At the pass site `g(c, 5)`, `g`'s reflection clauses substitute
//! to `c.requires((5,))` / `c.ensures((5,), g(c, 5))`, which lower to the OPAQUE
//! reflection UFs `call_requires%` / `call_ensures%`. Increment 2b emits the
//! DEFINITIONAL ground facts
//!
//!     call_requires%(c, (5,))          == (5 < 10)
//!     call_ensures%(c, (5,), g(c, 5))  == (g(c, 5) == 5 + 1)
//!
//! so the caller can PROVE `g`'s prove-`requires` (from `c`'s `5 < 10`) and USE
//! `g`'s assumed `ensures` (`c`'s `y == 6`).
//!
//! SOUNDNESS.
//! * GATE: the ground fact is emitted ONLY for a bare-ident arg registered in
//!   `closure_reflection_contracts` (⇔ `c`'s independent def-side obligation was
//!   emitted at its `let c = …`). A re-passed Fn-bound PARAMETER is not in that
//!   map ⇒ NO fact ⇒ fails closed (PARAM-REPASS trap). A lying closure sinks its
//!   DEFINING function via the def-side check, which 2b cannot mask (LYING-CLOSURE
//!   trap).
//! * CONSERVATIVE: each fact fixes the opaque UF's value, so a requires violation
//!   (`g(c, 50)`) and a false ensures use (`assert!(y == 7)`) both counterexample.
//!
//! CACHE DISCIPLINE (mandatory): every verdict is recomputed cache-off
//! (`TRUST_VC_DISABLE_VC_CACHE=1`) so a stale `Verified` can never mask a
//! false-verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/fn_bound_closure_pass_site_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    // SOUNDNESS-CRITICAL: recompute every verdict cache-off. A single stale
    // `Verified` would otherwise be served forever and mask a real false-verify.
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&repro_path(), func)
    })
}

fn verdict(func: &str) -> VerifyResult {
    verify(func).unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

/// Assert the refusal of a `Verified` answer for a callable parameter evaluated
/// more than once. Only a `Verified` answer produces it, so a refutation here
/// still fails the assertion.
fn assert_refused(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(
            &v,
            VerifyResult::Error { message } if message.starts_with("bodiless call repeated")
        ),
        "`{func}` should be REFUSED (a callable parameter evaluated twice); got {v:?}"
    );
}

fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should VERIFY (pass-site linkage discharges the callee's \
         prove-requires from the closure's concrete requires and pins the \
         callee's ensures to the closure's concrete ensures); got {v:?}"
    );
}

/// Assert an exact `Counterexample` — stronger than "not verified": it witnesses
/// that the linkage is LOAD-BEARING (a live obligation the solver can falsify).
fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "`{func}` should COUNTEREXAMPLE; got {v:?}"
    );
}

fn assert_not_verified(func: &str) {
    // An extraction Err (deferred / fail-closed lowering) or any solver
    // non-Verified verdict (incl. Unknown) is a sound non-verify.
    if let Ok(VerifyResult::Verified) = verify(func) {
        panic!("FN-BOUND PASS-SITE FALSE-VERIFY: `{func}` must not verify")
    }
}

#[test]
fn t1_positive_roundtrip_verified() {
    // POSITIVE: `let c = closure!(x < 10 ⊢ r == x + 1); let y = g(c, 5);
    // assert!(y == 6)`. The pass-site linkage discharges `g`'s prove-requires
    // (`5 < 10`) and pins `y == 6`. The load-bearing success signal.
    assert_verified("fnbound_2b_positive_roundtrip");
}

#[test]
fn t2_requires_violation_counterexample() {
    // REQUIRES-VIOLATION TRAP: `g(c, 50)` with `c` requiring `x < 10`. The
    // linkage pins `call_requires%(c, (50,)) == (50 < 10) == false`, so `g`'s
    // prove-requires is false. A `Verified` = admitting a precondition-violating
    // call = UNSOUND.
    assert_counterexample("fnbound_2b_requires_violation_cx");
}

#[test]
fn t3_false_ensures_use_counterexample() {
    // FALSE-ENSURES-USE TRAP: valid call, ensures linkage pins `y == 6`, but the
    // caller asserts `y == 7`. A `Verified` = the linked ensures did not
    // constrain the result = UNSOUND.
    assert_counterexample("fnbound_2b_false_ensures_use_cx");
}

#[test]
fn t4_lying_closure_counterexample() {
    // LYING-CLOSURE TRAP: `c` claims `ensures r == x + 1` but returns `x + 2`. The
    // closure's INDEPENDENT def-side obligation sinks the defining function; the
    // 2b linkage must NOT mask that counterexample.
    assert_counterexample("fnbound_2b_lying_closure_cx");
}

#[test]
fn t5_param_repass_fail_closed() {
    // FN-BOUND-PARAM-REPASS TRAP: an Fn-bound parameter `f` re-passed at
    // `g(f, 5)`. `f` is not a registered closure literal ⇒ no ground fact ⇒ `g`'s
    // prove-requires is the opaque UF with nothing to discharge it. MUST NOT
    // VERIFY (a linkage on a re-passed param would be unsound).
    assert_not_verified("fnbound_2b_param_repass_fail_closed");
}

#[test]
fn t6_determinism_regression_refused() {
    // REGRESSION (Increment 1 intact): `f(3) == f(3)` is still proved from the
    // congruent term alone, and that `Verified` answer is refused. A
    // Counterexample here = the pass-site pass over-constrained an unrelated call.
    assert_refused("fnbound_2b_determinism_regression");
}

#[test]
fn t6b_determinism_no_requires_counterexample() {
    // H6 twin: without the requires the call-site prove-requires is refuted.
    let v = verdict("fnbound_2b_determinism_no_requires_cx");
    match &v {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.starts_with("__call_requires_pp") => {}
        _ => panic!(
            "`fnbound_2b_determinism_no_requires_cx` should COUNTEREXAMPLE on the \
             call-site `__call_requires_pp*` obligation; got {v:?}"
        ),
    }
}

#[test]
fn t7_shadowed_closure_contract_does_not_escape_its_scope() {
    // SHADOW-RESTORATION TRAP: an inner closure named `c` must not replace the
    // outer `c`'s contract after the inner block ends. Accept either the precise
    // outer-contract Counterexample or a conservative extraction rejection, but
    // never Verified: proving `y == 7` would mean the inner `+ 2` contract leaked
    // onto the outer `+ 1` closure passed to the Fn-bound callee.
    assert_not_verified("fnbound_2b_shadowed_contract_must_not_escape");
}

#[test]
fn t8_closure_binding_shadows_outer_scalar_exactly() {
    // VALUE-SCOPE PARITY: the closure binding must hide the outer scalar model
    // while its block is active, then the scalar must be visible again after
    // the block. This catches a registry-only binding that leaves `lookup_scoped`
    // resolving `c` to the outer `99u64` at the Fn-bound pass site.
    assert_verified("fnbound_2b_closure_shadows_outer_scalar");
}
