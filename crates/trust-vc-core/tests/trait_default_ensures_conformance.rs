// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Phase A2-conformance — `default_ensures` DECL-SITE cluster.
//!
//! `default_ensures` is a trait DEFAULT method's extra postcondition that the
//! DEFAULT BODY must itself establish. This increment lands the declaration-site
//! clean cluster ONLY:
//!   * the token is harvested on a defaulted trait-method declaration, folded
//!     into the SAME asserted conjunction the default body is checked against
//!     (`build_default_contract_obligations`), so a body that violates it yields
//!     a genuine Counterexample; and
//!   * the token is REJECTED everywhere it is not a defaulted trait-method decl
//!     (decl-only, impl methods, free functions, extern specs).
//!
//! It DELIBERATELY does NOT publish `default_ensures` as a caller-visible axiom
//! (the inherit/override caller-publish half is deferred). Probe 5 is the
//! cardinal guard that pins that non-leak: a caller must NOT be able to assume
//! the strengthened default postcondition this increment never published.
//!
//! Native surface (`#[trust_vc::trait_spec]` / `#[trust_vc::ensures]` /
//! `#[trust_vc::default_ensures]`), run on the FILE path. These map to upstream
//! Verus `traits_extend_ensures.rs` cases `test_default_ensures1`,
//! `test_default_ensures_ret_val_collision`, and
//! `test_disallow_default_ensures1/3/5/6`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Unique temp path per fixture: fixtures share function/trait names across
/// DIFFERENT sources, so a name-keyed path would let parallel tests race on one
/// file and read it back truncated (same fix as `trait_conformance_body_shapes`).
fn write_fixture(src: &str, case: &str) -> std::path::PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_default_ensures_{}_{}_{case}.rs",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, src).expect("write fixture");
    path
}

/// Verify one named function on the file path. A hard extraction error (e.g. an
/// ill-formed `default_ensures`) surfaces as `VerifyResult::Error`.
fn verify(src: &str, func: &str, case: &str) -> VerifyResult {
    let path = write_fixture(src, case);
    let r = verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    r
}

/// The verdict of the file's DECL-SITE default-body conformance obligation
/// (`"trait default conformance {Trait}::{method} (no impl)"`, produced by the
/// impl-absent pass `verify_implless_trait_defaults`). Enumerate + verify BY
/// NAME, exactly as `cargo trust-vc check` drives conformance.
fn default_conformance_verdict(src: &str, case: &str) -> VerifyResult {
    let path = write_fixture(src, case);
    let out = (|| {
        let names = match trust_vc_core::list_trait_conformance_obligations(path.to_str().unwrap())
        {
            Ok(names) => names,
            Err(err) => {
                return VerifyResult::Error {
                    message: err.to_string(),
                }
            }
        };
        let Some(name) = names
            .iter()
            .find(|n| n.contains("trait default conformance"))
        else {
            return VerifyResult::Error {
                message: format!(
                    "no decl-site default-conformance obligation listed; got {names:?}"
                ),
            };
        };
        match trust_vc_core::verify_trait_conformance_obligation(path.to_str().unwrap(), name) {
            Ok(result) => result,
            Err(err) => VerifyResult::Error {
                message: err.to_string(),
            },
        }
    })();
    let _ = std::fs::remove_file(&path);
    out
}

/// A hard extraction/parse error string for a file whose ill-formedness is
/// detected during FILE-level context building (trait decls, impl blocks), via
/// the same enumeration `cargo trust-vc check` runs.
fn context_error(src: &str, case: &str) -> String {
    let path = write_fixture(src, case);
    let out = match trust_vc_core::list_trait_conformance_obligations(path.to_str().unwrap()) {
        Ok(names) => format!("UNEXPECTED OK: obligations listed without error: {names:?}"),
        Err(err) => err.to_string(),
    };
    let _ = std::fs::remove_file(&path);
    out
}

const NOT_ALLOWED: &str = "default_ensures not allowed here";

// ===========================================================================
// Probe 1 — default body FAILS its default_ensures (Counterexample).
// Upstream `test_default_ensures1`. Body `i` establishes `result <= i` but NOT
// `result == i/2`, so the added conjunct is refuted. MUST be a definitive
// Counterexample (single-pure-return body), never Unknown, never Verified.
// ===========================================================================
const PROBE1_FAILS: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::ensures(result <= i)]
    #[trust_vc::default_ensures(result == i / 2)]
    fn f(i: u32) -> u32 {
        i
    }
}
"#;

#[test]
fn probe1_default_body_violating_default_ensures_is_counterexample() {
    match default_conformance_verdict(PROBE1_FAILS, "probe1") {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "CARDINAL: a default body that violates its own `default_ensures` DISCHARGED \
             the decl-site conformance obligation — the added conjunct never entered the \
             asserted set."
        ),
        other => panic!(
            "expected a definitive Counterexample (single-pure-return body `i` refutes \
             `result == i/2`); an Unknown here signals the `default_ensures` conjunct was \
             not lowered into the asserted obligation. Got {other:?}"
        ),
    }
}

// ===========================================================================
// Probe 2 — default body SATISFIES both (Verified); binder collision.
// Upstream `test_default_ensures_ret_val_collision`. Return binder named `f`
// (colliding with the fn name) must be renamed to `result` in BOTH the
// `ensures` AND the `default_ensures` clause; body `i/2` establishes both.
// ===========================================================================
const PROBE2_SATISFIES: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::returns(f)]
    #[trust_vc::ensures(f <= i)]
    #[trust_vc::default_ensures(f == i / 2)]
    fn f(i: u32) -> u32 {
        i / 2
    }
}
"#;

#[test]
fn probe2_default_body_satisfying_default_ensures_verifies() {
    match default_conformance_verdict(PROBE2_SATISFIES, "probe2") {
        VerifyResult::Verified => {}
        other => panic!(
            "expected VERIFIED: default body `i/2` establishes both `f <= i` and \
             `f == i/2` after the return-binder `f` is renamed onto `result` in the \
             `default_ensures` clause. Over-rejection or a missed binder rename would \
             break this. Got {other:?}"
        ),
    }
}

// ===========================================================================
// Probe 3 — decl-only `default_ensures` rejected. Upstream
// `test_disallow_default_ensures1`. No body ⇒ nothing to check it against ⇒
// hard parse Error at the decl site.
// ===========================================================================
const PROBE3_DECL_ONLY: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::ensures(result <= i)]
    #[trust_vc::default_ensures(result == i / 2)]
    fn f(i: u32) -> u32;
}
"#;

#[test]
fn probe3_decl_only_default_ensures_rejected() {
    let err = context_error(PROBE3_DECL_ONLY, "probe3");
    assert!(
        err.contains(NOT_ALLOWED),
        "decl-only `default_ensures` (no body) must be a hard parse error carrying \
         {NOT_ALLOWED:?}; got {err:?}"
    );
}

// ===========================================================================
// Probe 4 — `default_ensures` rejected off the defaulted-decl surface.
// Upstream `test_disallow_default_ensures3/5/6`.
//   4a free `#[proof]` fn; 4b `#[trust_vc::trait_impl]` impl method; 4c impl
//   method OVERRIDING a defaulted trait method.
// ===========================================================================
const PROBE4_FREE_FN: &str = r#"
#[trust_vc::ensures(result == i)]
#[trust_vc::default_ensures(result == i / 2)]
fn f(i: u32) -> u32 {
    i
}
"#;

const PROBE4_IMPL_METHOD: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::ensures(result <= i)]
    fn f(&self, i: u32) -> u32;
}
struct S(u32);
#[trust_vc::trait_impl]
impl T for S {
    #[trust_vc::default_ensures(result == i / 2)]
    fn f(&self, i: u32) -> u32 {
        i
    }
}
"#;

const PROBE4_OVERRIDE_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::ensures(result <= i)]
    fn f(&self, i: u32) -> u32 {
        i
    }
}
struct S(u32);
#[trust_vc::trait_impl]
impl T for S {
    #[trust_vc::default_ensures(result == i / 2)]
    fn f(&self, i: u32) -> u32 {
        i / 2
    }
}
"#;

#[test]
fn probe4a_free_fn_default_ensures_rejected() {
    // The free fn is the verify TARGET; the guard fires at attribute extraction.
    let r = verify(PROBE4_FREE_FN, "f", "probe4a");
    let msg = match &r {
        VerifyResult::Error { message } => message.clone(),
        other => {
            panic!("expected an Error rejecting `default_ensures` on a free fn, got {other:?}")
        }
    };
    assert!(
        msg.contains(NOT_ALLOWED),
        "free-fn `default_ensures` must be rejected with {NOT_ALLOWED:?}; got {msg:?}"
    );
}

#[test]
fn probe4b_impl_method_default_ensures_rejected() {
    let err = context_error(PROBE4_IMPL_METHOD, "probe4b");
    assert!(
        err.contains(NOT_ALLOWED),
        "impl-method `default_ensures` must be rejected with {NOT_ALLOWED:?}; got {err:?}"
    );
}

#[test]
fn probe4c_override_default_ensures_rejected() {
    let err = context_error(PROBE4_OVERRIDE_DEFAULT, "probe4c");
    assert!(
        err.contains(NOT_ALLOWED),
        "an impl method OVERRIDING a defaulted trait method may not carry \
         `default_ensures`; must be rejected with {NOT_ALLOWED:?}; got {err:?}"
    );
}

// ===========================================================================
// Probe 5 — NO caller leak (cardinal-invariant guard, MANDATORY).
//
// An all-defaults concrete impl `impl T for S {}` plus GENERIC-bounded callers
// of the default method. This increment does NOT publish `default_ensures` to
// callers, so a caller knows only the REGULAR ensures `result <= i`. The
// generic-bounded receiver consuming the trait postcondition axiom is the proven
// default-method caller-axiom path (`trait_default_body_conformance`'s
// `default_body_satisfying_contract_lets_caller_verify`); a concrete receiver on
// an EMPTY impl does not resolve in spec context (no concrete method binding),
// which would make the guard vacuous. The `default_ensures` leak — if any —
// would ride the SAME postcondition axiom, so this path observes it exactly.
//
//   * `leak_probe`   `assert!(r == 3)` — the CARDINAL: it would need the
//     unpublished `default_ensures result == i/2` (6/2 == 3). MUST NOT verify.
//   * `regular_ok`   `assert!(r <= 6)`  — non-vacuity control: the REGULAR
//     ensures DOES reach the caller, so a leak WOULD be observable. Verifies.
//   * `vacuity`      `assert!(false)`   — the caller's axiom set stays
//     CONSISTENT (the added decl-site conjunct never reached it). Counterexample.
// ===========================================================================
const PROBE5_CALLER_LEAK: &str = r#"
#[trust_vc::trait_spec]
trait T: Sized {
    #[trust_vc::ensures(result <= i)]
    #[trust_vc::default_ensures(result == i / 2)]
    fn f(self, i: u32) -> u32 {
        i
    }
}
struct S(u32);
#[trust_vc::trait_impl]
impl T for S {}

#[trust_vc::ensures(true)]
fn leak_probe<X: T>(x: X) {
    let r = x.f(6);
    trust_vc::assert!(r == 3);
}

#[trust_vc::ensures(true)]
fn regular_ok<X: T>(x: X) {
    let r = x.f(6);
    trust_vc::assert!(r <= 6);
}

#[trust_vc::ensures(true)]
fn vacuity<X: T>(x: X) {
    let r = x.f(6);
    trust_vc::assert!(false);
}
"#;

#[test]
fn probe5_default_ensures_does_not_leak_to_callers() {
    // THE CARDINAL. A `Verified` here means `default_ensures` leaked to callers
    // unchecked-for-override — the false-verify this increment must never allow.
    match verify(PROBE5_CALLER_LEAK, "leak_probe", "probe5_leak") {
        VerifyResult::Verified => panic!(
            "CARDINAL FALSE-VERIFY — a caller VERIFIED `r == 3`, which is derivable ONLY \
             from the strengthened `default_ensures result == i/2` this increment did NOT \
             publish. `default_ensures` leaked to callers unchecked-for-override. HALT."
        ),
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        other => panic!(
            "expected the caller's `r == 3` to be NON-verified (Counterexample / fail-closed \
             NotProved / Unknown), got {other:?}"
        ),
    }
}

#[test]
fn probe5_regular_ensures_reaches_caller() {
    // Non-vacuity control: without this, the cardinal guard above could "pass"
    // for the vacuous reason that no contract axiom reaches the caller at all.
    match verify(PROBE5_CALLER_LEAK, "regular_ok", "probe5_regular") {
        VerifyResult::Verified => {}
        other => panic!(
            "the REGULAR ensures `result <= i` must reach the caller (proving the cardinal \
             guard is not vacuous); expected VERIFIED for `r <= 6`, got {other:?}"
        ),
    }
}

#[test]
fn probe5_caller_axiom_set_is_consistent() {
    // Vacuity control: the added decl-site conjunct must not make the caller's
    // axiom set inconsistent (which would prove anything, incl. `false`).
    match verify(PROBE5_CALLER_LEAK, "vacuity", "probe5_vacuity") {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "CARDINAL: `assert!(false)` VERIFIED after a default-method call — the caller's \
             axiom set is INCONSISTENT."
        ),
        other => panic!("expected a Counterexample on `assert!(false)`, got {other:?}"),
    }
}

// ===========================================================================
// Probe 6 — capture gate NOT loosened (linchpin regression guard).
//
// A defaulted method whose default body is MULTI-STATEMENT/stateful
// (`{ let a = 3u32; a }`) with `default_ensures result == 7`. The single-
// pure-return decline in `capture_conformance_method_body` must be intact and
// no false `concrete_fn == body` fact emitted: the obligation MUST be
// NON-verified — a Counterexample if the sequence lowers, else a fail-closed
// Unknown. A `Verified` here would mean the multi-statement body was wrongly
// treated as pure.
// ===========================================================================
const PROBE6_STATEFUL_BODY: &str = r#"
#[trust_vc::trait_spec]
trait T {
    #[trust_vc::ensures(result == 3)]
    #[trust_vc::default_ensures(result == 7)]
    fn f() -> u32 {
        let a = 3u32;
        a
    }
}
"#;

#[test]
fn probe6_stateful_default_body_not_verified() {
    match default_conformance_verdict(PROBE6_STATEFUL_BODY, "probe6") {
        VerifyResult::Verified => panic!(
            "LINCHPIN REGRESSION: a multi-statement default body with a violated \
             `default_ensures` VERIFIED — the single-pure-return capture gate was loosened \
             or a false `result == body` fact was emitted."
        ),
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        other => panic!(
            "expected a Counterexample (if the sequence lowers) or a fail-closed \
             NotProved/Unknown; got {other:?}"
        ),
    }
}
