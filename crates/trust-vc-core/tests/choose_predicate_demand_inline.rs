// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! TRIGGER-GATE PIN for a `choose` predicate over a spec fn, and the two twins
//! that caught the two ways of getting it wrong.
//!
//! BACKGROUND. Lowering `choose|i: T| p(i)` over a spec-fn predicate MOVES the
//! predicate out of `Choose::condition` (which becomes `BoolLit(true)`) and into
//! the combined Hilbert axiom in `Choose::also_assert`
//! (`ir_lowering/dispatch/macros.rs`). That axiom is marked `no_mbqi` at encode
//! time so it fires ONLY on a genuine ground witness and MBQI cannot FABRICATE
//! the witness a witnessless `choose` deliberately lacks — the control that
//! keeps upstream `choose.rs::test1_fails1` / `test1_fails1_tuple` refuted.
//!
//! The mark was decided by asking whether the axiom still mentions a `FnCall`.
//! `also_assert` reaches the encoder AFTER `substitute_inline_calls`, so that
//! question answers `false` for any predicate whose spec fn was inlined, and the
//! gate silently lapses. Measured: with the demand-inline retry (#2655) able to
//! select a callee that occurs only inside `also_assert`,
//! `evals/verus/ported/choose.rs::test1_fails1_tuple` flipped from upstream's
//! `counterexample` to `Verified`, deterministically, 4/4 runs — MBQI invented
//! the witness. The gate is now read off the LOWERED SHAPE (a trivial
//! `BoolLit(true)` condition beside the combined axiom), which substitution
//! cannot erase.
//!
//! AND IT IS SCOPED TO THE DEMAND-INLINE RETRY. An explicit
//! `#[trust_vc::inline]` predicate SHOULD lose the gate: Verus substitutes such
//! a body too and loses the trigger itself, and measured here that shape yields
//! a MODEL-VALIDATED refutation which keeping the mark demotes to a model-less
//! `quantifier-unhandled`. A demand-inline override is trust-vc's own retry,
//! invisible to the program, and must not change which facts are derivable.
//!
//! Each capability case below is paired with a twin that must not move.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> Result<VerifyResult, String> {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_cpdi_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
#![allow(dead_code)]

use trust_vc_types::int;

#[trust_vc::spec]
fn f(i: int) -> bool {
    5 <= i
}

#[trust_vc::spec]
fn f2(i: int, j: int) -> bool {
    i <= j
}

// An EXPLICITLY inline spec fn: the program says substitute me, so Verus would
// lose the trigger here too and so does trust-vc.
#[trust_vc::spec]
#[trust_vc::inline]
fn g(i: int) -> bool {
    5 <= i
}

// CONTROL — upstream `choose.rs::test1`, single binder. The ground witness
// `f(7)` is present, so the guarded Hilbert axiom fires and `5 <= i` follows.
#[trust_vc::ensures(true)]
fn witnessed_right_claim() {
    let i: int = trust_vc::choose!(|i: int| f(i));
    trust_vc::assert!(f(7));
    trust_vc::assert!(5 <= i);
}

// LIAR TWIN — upstream `test1_fails2` verbatim: `i == 7` is not entailed
// (i = 5 satisfies every hypothesis), and must be REJECTED.
#[trust_vc::ensures(true)]
fn witnessed_wrong_claim() {
    let i: int = trust_vc::choose!(|i: int| f(i));
    trust_vc::assert!(f(7));
    trust_vc::assert!(i == 7);
}

// CONTROL — upstream `test1_tuple`, two binders.
#[trust_vc::ensures(true)]
fn witnessed_right_claim_tuple() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j));
    trust_vc::assert!(f2(7, 8));
    trust_vc::assert!(i <= j);
}

// LIAR TWIN — upstream `test1_fails2_tuple` verbatim.
#[trust_vc::ensures(true)]
fn witnessed_wrong_claim_tuple() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j));
    trust_vc::assert!(f2(7, 8));
    trust_vc::assert!(i == 7);
}

// PARITY PIN, single binder — upstream `test1_fails1`. NO ground witness, so
// the `no_mbqi` combined axiom must never fire. Verus refutes this.
#[trust_vc::ensures(true)]
fn witnessless_single_binder() {
    let i: int = trust_vc::choose!(|i: int| f(i));
    trust_vc::assert!(5 <= i);
}

// PARITY PIN, two binders — upstream `test1_fails1_tuple`. THIS is the case
// that flipped to `Verified` when the gate was read off the inline-substituted
// axiom text instead of the lowered shape.
#[trust_vc::ensures(true)]
fn witnessless_tuple() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j));
    trust_vc::assert!(i <= j);
}

// SCOPE PIN — the same wrong claim over an EXPLICITLY `#[trust_vc::inline]`
// predicate. No definitional axiom is ever emitted for `g`, so ay has nothing
// it cannot certify and the refutation comes back WITH A MODEL. Keeping the
// `no_mbqi` mark for this shape demotes it to a model-less non-decision, which
// is why the gate consults the demand-inline flag and not merely the shape.
#[trust_vc::ensures(true)]
fn inline_predicate_wrong_claim() {
    let i: int = trust_vc::choose!(|i: int| g(i));
    trust_vc::assert!(g(7));
    trust_vc::assert!(i == 7);
}

// MEASURED COMPANION to the line above, and NOT asserted on: the TRUE twin
// `5 <= i` over the same inline predicate does NOT verify today
// (`(incomplete quantifier-unhandled)`), because substituting `g` turns the
// ground witness `g(7)` into the tautology `5 <= 7` and the Hilbert axiom is
// left with nothing to fire on. That is a pre-existing limitation of
// `#[trust_vc::inline]` under `choose` — it predates and is untouched by the
// trigger-gate change — and pinning it would forbid a later fix, so it is
// recorded here rather than asserted.
#[trust_vc::ensures(true)]
fn inline_predicate_right_claim() {
    let i: int = trust_vc::choose!(|i: int| g(i));
    trust_vc::assert!(g(7));
    trust_vc::assert!(5 <= i);
}

// PARITY PIN — a DECIDABLE arithmetic choose predicate mentions no spec fn, is
// not trigger-gated by either lowering path, and must keep verifying. This is
// the case the gate is deliberately narrow for: marking it would fail-close a
// legitimate proof.
#[trust_vc::ensures(true)]
fn arithmetic_choose_still_verifies() {
    let n: int = trust_vc::choose!(|n: int| n >= 10);
    trust_vc::assert!(n >= 10);
}

// LIAR TWIN for the line above: `n >= 11` does not follow from `n >= 10`, so an
// ungated arithmetic choose must still REFUSE the neighbouring false claim.
#[trust_vc::ensures(true)]
fn arithmetic_choose_wrong_claim() {
    let n: int = trust_vc::choose!(|n: int| n >= 10);
    trust_vc::assert!(n >= 11);
}
"#;

fn expect_verified(func: &str) {
    let r = verify(func, func, SRC);
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "{func} should verify, got {r:?}"
    );
}

/// Rejected, by any fail-closed route: a model-bearing `Counterexample`, or the
/// model-less `NotProved` that a `no_mbqi` universal forces ay to publish. The
/// one outcome forbidden is `Verified`.
fn expect_rejected(func: &str) {
    let r = verify(func, func, SRC);
    assert!(
        matches!(
            r,
            Ok(VerifyResult::Counterexample { .. }) | Ok(VerifyResult::NotProved { .. })
        ),
        "{func} should be rejected, got {r:?}"
    );
}

/// Strictly stronger than [`expect_rejected`]: a REFUTATION the solver actually
/// modelled. This is what the corpus gate's `is_refutation` accepts and what its
/// `is_undecided` rejects, so a demotion to a model-less non-decision here is a
/// measurable loss even though the VERDICT word does not change.
fn expect_model_bearing_counterexample(func: &str) {
    let r = verify(func, func, SRC);
    match &r {
        Ok(VerifyResult::Counterexample { model, .. }) => assert!(
            model.is_some(),
            "{func} must carry a MODEL; a model-less non-decision is what the \
             corpus gate rejects as UNDECIDED. Got {r:?}"
        ),
        _ => panic!("{func} should be a model-bearing Counterexample, got {r:?}"),
    }
}

/// Verus refutes these; trust-vc must not VERIFY them. The claims are valid in
/// the standard model — `exists i. 5 <= i` holds — so this is not a soundness
/// bound. It is the deliberate `no_mbqi` witness discipline, and it is the
/// property that lapses the moment the trigger gate is decided from
/// inline-substituted text.
fn expect_not_verified(func: &str) {
    let r = verify(func, func, SRC);
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "{func} must NOT verify — the witnessless choose axiom is `no_mbqi` and \
         MBQI may not fabricate the witness upstream requires; got {r:?}"
    );
}

#[test]
fn witnessed_single_binder_pair() {
    expect_verified("witnessed_right_claim");
    expect_rejected("witnessed_wrong_claim");
}

#[test]
fn witnessed_tuple_pair() {
    expect_verified("witnessed_right_claim_tuple");
    expect_rejected("witnessed_wrong_claim_tuple");
}

#[test]
fn witnessless_choose_must_not_verify() {
    expect_not_verified("witnessless_single_binder");
    expect_not_verified("witnessless_tuple");
}

#[test]
fn explicit_inline_predicate_keeps_its_model_bearing_refutation() {
    expect_model_bearing_counterexample("inline_predicate_wrong_claim");
}

#[test]
fn decidable_arithmetic_choose_is_not_trigger_gated() {
    expect_verified("arithmetic_choose_still_verifies");
    expect_rejected("arithmetic_choose_wrong_claim");
}
