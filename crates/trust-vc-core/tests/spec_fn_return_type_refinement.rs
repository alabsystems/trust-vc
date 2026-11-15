// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! spec_fn return-type refinement: an opaque `spec_fn(..) -> T` apply result
//! inherits `T`'s type invariants — a `-> nat` apply is `>= 0`, a `-> u8` apply
//! is `0..256`. The apply UF carries no body axiom, so asserting its codomain
//! range is a sound consequence of the closure's type and can never contradict.
//!
//! Flagship: `f.call(x) >= 0` for `f: SpecFn<int, nat>` now VERIFIES (was
//! Counterexample — an unconstrained Int can be negative). Cardinal guards: the
//! result is refined, NOT pinned (`== 5` still Counterexample), the context is
//! NOT contradictory (`f(x) == f(x)+1` still Counterexample — no vacuity), and a
//! below-range assertion (`< 0`) is soundly refuted.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_sfr_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    // Cache-off: a stale Verified must never mask a false-verify. Serialize and
    // restore the process-wide override so parallel soundness tests cannot race.
    let r =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
                VerifyResult::Error {
                    message: e.to_string(),
                }
            })
        });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}
fn counterexample(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Counterexample { .. })
}

const SRC: &str = r#"
use trust_vc_types::{SpecFn, int, nat};

#[trust_vc::ensures(true)]
fn nat_ge0(f: SpecFn<int, nat>, x: int) {
    trust_vc::assert!(f.call(x) >= 0);
}
#[trust_vc::ensures(true)]
fn nat_lt0_liar(f: SpecFn<int, nat>, x: int) {
    trust_vc::assert!(f.call(x) < 0);
}
#[trust_vc::ensures(true)]
fn nat_no_vacuity(f: SpecFn<int, nat>, x: int) {
    trust_vc::assert!(f.call(x) == f.call(x) + 1);
}
#[trust_vc::ensures(true)]
fn nat_not_pinned(f: SpecFn<int, nat>, x: int) {
    trust_vc::assert!(f.call(x) == 5);
}
"#;

const PREFIX_SRC: &str = r#"
use trust_vc_types::{int, nat};
// A source function can legally use the old internal-looking prefix. Its body
// would pin the result to -1, so adding an opaque-closure nat range assertion
// here would make the query contradictory and false-verify the assertion (the
// body is now refused: a `nat` result cannot hold -1).
#[trust_vc::spec]
fn __trust_vc_spec_fn_apply_int_to_nat(x: int) -> nat { -1 }
#[trust_vc::ensures(true)]
fn source_prefix_is_not_opaque_apply(x: int) {
    trust_vc::assert!(__trust_vc_spec_fn_apply_int_to_nat(x) >= 0);
}
"#;

const COLLISION_SRC: &str = r#"
use trust_vc_types::{SpecFn, int, nat};

#[trust_vc::spec]
fn __trust_vc_spec_fn_apply_x696e74_to_x6e6174(f: SpecFn<int, nat>, x: int) -> nat { 5 }
#[trust_vc::ensures(true)]
fn internal_apply_collision_fails_closed(f: SpecFn<int, nat>, x: int) {
    // Keep the colliding source declaration in the reachable function set.
    // If it were unreachable, pruning it would also remove its body axiom and
    // there would be no live symbol collision to reject.
    trust_vc::assert!(__trust_vc_spec_fn_apply_x696e74_to_x6e6174(f, x) == 5);
    trust_vc::assert!(f.call(x) == 5);
}
"#;

const LOCAL_BINDING_SPOOF_SRC: &str = r#"
use trust_vc_types::{SpecFn, int, nat};

#[trust_vc::ensures(true)]
fn local_binding_cannot_spoof_internal_apply(
    f: SpecFn<int, nat>,
    x: int,
    __trust_vc_spec_fn_apply_x696e74_to_x6e6174: nat,
) {
    // This is invalid Rust: the long-named parameter is a `nat`, not a
    // callable value. Source lowering must not let its exact generated spelling
    // turn the call into the verifier's opaque internal SpecFn application.
    trust_vc::assert!(
        __trust_vc_spec_fn_apply_x696e74_to_x6e6174(f, x) >= 0
    );
}
"#;

const WRONG_ARGUMENT_TYPE_SRC: &str = r#"
use trust_vc_types::{SpecFn, int, nat};

#[trust_vc::ensures(true)]
fn wrong_argument_type_must_fail_closed(f: SpecFn<int, nat>, b: bool) {
    // Invalid Rust: `f` accepts `int`, not `bool`. The verifier must not let
    // the generated UF spelling confer `nat` codomain authority on this call.
    trust_vc::assert!(f(b) >= 0);
}

#[trust_vc::ensures(true)]
fn wrong_requires_argument_type_must_fail_closed(f: SpecFn<int, nat>, b: bool) {
    trust_vc::assert!(f.requires((b,)));
}

#[trust_vc::ensures(true)]
fn wrong_ensures_argument_type_must_fail_closed(
    f: SpecFn<int, nat>,
    b: bool,
    n: nat,
) {
    trust_vc::assert!(f.ensures((b,), n));
}

#[trust_vc::ensures(true)]
fn wrong_ensures_result_type_must_fail_closed(
    f: SpecFn<int, nat>,
    x: int,
    b: bool,
) {
    trust_vc::assert!(f.ensures((x,), b));
}
"#;

#[test]
fn nat_apply_is_nonnegative() {
    let result = verify("g", "nat_ge0", SRC);
    assert!(
        verified(&result),
        "spec_fn(int) -> nat apply result must be provably >= 0, got {result:?}"
    );
}

#[test]
fn nat_apply_below_zero_is_refuted() {
    let result = verify("l", "nat_lt0_liar", SRC);
    assert!(
        counterexample(&result),
        "CARDINAL: f(x) < 0 for a nat codomain must be refuted (Counterexample), got {result:?}"
    );
}

#[test]
fn nat_apply_context_is_not_contradictory() {
    // The load-bearing no-vacuity guard: the range assertion must not make the
    // context UNSAT (which would vacuously verify anything). `f(x) == f(x)+1` is
    // false, so it must Counterexample — a Verified here would prove the context
    // contradictory.
    let result = verify("v", "nat_no_vacuity", SRC);
    assert!(
        counterexample(&result),
        "CARDINAL: range refinement must NOT introduce a contradiction (no vacuity), got {result:?}"
    );
}

#[test]
fn nat_apply_is_refined_not_pinned() {
    let result = verify("p", "nat_not_pinned", SRC);
    assert!(
        counterexample(&result),
        "CARDINAL: the result is range-refined, not pinned to a concrete value, got {result:?}"
    );
}

/// A source function named with the internal apply prefix whose body is a
/// value its `nat` result cannot hold. It used to be a counterexample (its body
/// axiom admitted, no codomain axiom borrowed); the body axiom is now refused
/// before either can matter (design-trust-proof-backend.md §5b rule 6: a
/// `nat` result binds only a value a `nat` holds), and a well-typed `nat` body
/// satisfies the codomain range, so no borrowed range can contradict it.
#[test]
fn source_function_prefix_cannot_borrow_opaque_apply_refinement() {
    let result = verify("s", "source_prefix_is_not_opaque_apply", PREFIX_SRC);
    assert!(
        matches!(&result, VerifyResult::Error { message }
            if message.contains("declared to return `nat`, but its body is a value of type")),
        "CARDINAL: a named spec function with an internal-looking prefix must not \
         receive the opaque SpecFn codomain axiom or verify by contradiction; its `-1` body \
         at a `nat` result is refused, got {result:?}"
    );
}

#[test]
fn exact_source_collision_with_internal_apply_fails_closed() {
    let result = verify("c", "internal_apply_collision_fails_closed", COLLISION_SRC);
    assert!(
        matches!(&result, VerifyResult::Error { message } if message.contains("collides with a reserved internal closure UF")),
        "an exact source/internal UF collision must be rejected before a body axiom can \
         contaminate opaque application semantics, got {result:?}"
    );
}

#[test]
fn local_binding_cannot_spoof_internal_apply_provenance() {
    let result = verify(
        "local-spoof",
        "local_binding_cannot_spoof_internal_apply",
        LOCAL_BINDING_SPOOF_SRC,
    );
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "CARDINAL: a non-callable source binding with the exact generated UF name \
         must fail closed during lowering or encoding, got {result:?}",
    );
}

#[test]
fn spec_fn_apply_rejects_wrong_argument_types() {
    let result = verify(
        "wrong-arg-type",
        "wrong_argument_type_must_fail_closed",
        WRONG_ARGUMENT_TYPE_SRC,
    );
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "CARDINAL: an ill-typed SpecFn application must be rejected, got {result:?}",
    );
}

#[test]
fn spec_fn_reflection_rejects_wrong_argument_and_result_types() {
    for function in [
        "wrong_requires_argument_type_must_fail_closed",
        "wrong_ensures_argument_type_must_fail_closed",
        "wrong_ensures_result_type_must_fail_closed",
    ] {
        let result = verify(function, function, WRONG_ARGUMENT_TYPE_SRC);
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "CARDINAL: ill-typed SpecFn reflection `{function}` must be rejected, got {result:?}",
        );
    }
}
