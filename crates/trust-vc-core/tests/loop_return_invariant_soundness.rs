// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness suite for Phase E early-return-from-loop
//! (`vc_extraction/return_extract.rs`): a `return X` inside a `loop`/`while`/`for`
//! is admitted into the multiple-return disjunction ONLY when `X` is provably
//! LOOP-INVARIANT — a literal constant, or an immutable parameter that is never
//! written or rebound inside the loop.
//!
//! WHY THIS IS SOUND AND NON-TRIVIAL:
//! * A loop body is HAVOC'd across iterations (the invariant is the only fact
//!   carried), so a `return X` whose `X` reads loop-mutated state has an
//!   INDETERMINATE value. Adding `result == X` to the return over-approximation
//!   for such an `X` — with `X` bound to its pre-loop value — could FALSE-VERIFY
//!   a postcondition that is false in general.
//! * The loop-invariance restriction guarantees `X` is identical regardless of
//!   the havoc, so `result == X` is a sound member of the disjunction. Anything
//!   we cannot prove loop-invariant stays fail-closed (Ambiguous → extraction
//!   error), never admitted.
//!
//! CRUX (the two traps): `havoc_trap` returns a loop-MUTATED local and
//! `loop_written_param` returns a loop-WRITTEN parameter. Both are constructed so
//! that admitting the loop-return at its pre-loop / entry value would FALSE-VERIFY
//! a postcondition the real function violates. They MUST NOT verify. A `Verified`
//! on either is the cardinal false-verify this change could introduce.
//!
//! CACHE DISCIPLINE (mandatory): every verdict is recomputed cache-off
//! (`TRUST_VC_DISABLE_VC_CACHE=1`) so a stale `Verified` can never mask a
//! false-verify. Acceptance probes require exactly `Verified`; the false-
//! postcondition probe requires exactly `Counterexample`; fail-closed probes
//! treat an extraction `Err` and any solver non-`Verified` (incl. `Unknown`) as a
//! sound non-verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/loop_return_invariant_soundness_repro.rs",
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

/// Named oracle: acceptance probe requires exactly `Verified`.
fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should VERIFY (loop-invariant return admitted into the disjunction); got {v:?}"
    );
}

/// Named oracle: an exact, model-bearing `Counterexample`. Stronger than "not
/// verified" — it witnesses that the loop-return disjunction is genuinely MODELED
/// (not silently dropped) yet the probed postcondition is falsifiable.
fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "`{func}` should COUNTEREXAMPLE (one disjunct falsifies the postcondition); got {v:?}"
    );
}

/// Named oracle: fail-closed. An extraction `Err` (Ambiguous lowering) or any
/// solver non-`Verified` verdict (incl. `Unknown`) is a sound non-verify. Only an
/// exact `Verified` is a failure.
fn assert_not_verified(func: &str) {
    match verify(func) {
        Ok(VerifyResult::Verified) => {
            panic!("LOOP-RETURN FALSE-VERIFY: `{func}` must not verify")
        }
        _ => {}
    }
}

#[test]
fn t1_loop_const_return_disjunction_verified() {
    // POSITIVE: `loop { if flag { return 7 } break } 13` with
    // ensures(result == 7 || result == 13). Literal constant is loop-invariant.
    assert_verified("loop_const_return_disjunction_verified");
}

#[test]
fn t2_loop_invariant_param_return_disjunction_verified() {
    // POSITIVE: `return early` where `early` is an immutable, non-loop-written
    // parameter, joined with the tail param `late`. VERIFIES against the
    // disjunction result ∈ {early, late}.
    assert_verified("loop_invariant_param_return_disjunction_verified");
}

#[test]
fn t3_while_loop_const_return_verified() {
    // POSITIVE (while variant): `while flag { return 7 } 17`. VERIFIES.
    assert_verified("while_loop_const_return_verified");
}

#[test]
fn t4_for_loop_const_return_verified() {
    // POSITIVE (for variant): a literal-constant return inside a `for`. VERIFIES.
    assert_verified("for_loop_const_return_verified");
}

#[test]
fn t5_loop_const_return_false_postcondition_counterexample() {
    // FALSE-POSTCONDITION: the SAME shape as t1 with ensures(result == 7). The
    // fall-through value 13 is a live witness — the disjunction IS modeled, so
    // this MUST COUNTEREXAMPLE (a `Verified` would mean the tail value was
    // dropped).
    assert_counterexample("loop_const_return_false_postcondition_counterexample");
}

#[test]
fn t6_loop_mutated_local_return_havoc_trap_fail_closed() {
    // HAVOC FALSE-VERIFY TRAP (the crux): `return acc` where `acc` is a
    // loop-MUTATED local. Admitting it at the pre-loop value 0 would false-verify
    // ensures(result == 0). The loop-invariance gate rejects `acc` (loop-written)
    // → fail-closed. MUST NOT VERIFY.
    assert_not_verified("loop_mutated_local_return_havoc_trap_fail_closed");
}

#[test]
fn t7_loop_written_param_return_fail_closed() {
    // LOOP-INVARIANT-CHECK PROBE: `x` IS a parameter but is ASSIGNED in the loop
    // (`x = x + 1`). Admitting it at the entry value 5 would false-verify
    // ensures(result == 5 || result == 99). The loop-WRITTEN half of the gate
    // rejects `x` → fail-closed. MUST NOT VERIFY.
    assert_not_verified("loop_written_param_return_fail_closed");
}

#[test]
fn t8_for_loop_variable_return_fail_closed() {
    // LOOP-VARIABLE PROBE: the `for` loop variable is rebound every iteration and
    // is not a parameter, so `return value` is not provably loop-invariant and is
    // conservatively rejected → fail-closed. MUST NOT VERIFY (even though the
    // ensures happens to hold — soundness declines what it cannot prove).
    assert_not_verified("for_loop_variable_return_fail_closed");
}
