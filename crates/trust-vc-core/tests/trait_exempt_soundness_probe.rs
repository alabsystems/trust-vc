// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ADVERSARIAL PROBE (round-2 adjudication): does an impl method that declares
//! its OWN `#[trust_vc::requires]` escape BOTH conformance nets and thereby
//! false-verify a body that violates the trait `ensures`?
//!
//! Two independent nets exist (see the conformance-attribution design note and
//! `conformance_attribution_soundness.rs`):
//!   NET A — direct verify by name (`verify_function_from_file`): an impl method
//!           that declares its own `requires` is supposed to fail CLOSED with the
//!           dedicated `inherited_trait_method_contracts` error.
//!   NET B — the conformance obligation (`list_/verify_trait_conformance_obligation`):
//!           `register_conformance_exempt_method` SKIPS a `requires`-declaring
//!           impl, on the PREMISE that net A already fails it closed.
//!
//! If net A's premise does not hold for a given method shape, BOTH nets are
//! bypassed and the violating body is certified — a CARDINAL false-verify. This
//! probe exercises the shapes that stress the net-A/net-B key mismatch (net A
//! matches by full token identity of a self-substituted `func`; net B exempts by
//! concrete UF name). A test FAILS iff the violating impl is clean under BOTH
//! nets.

use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

fn fixture(src: &str, case: &str) -> std::path::PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_exempt_probe_{}_{}_{case}.rs",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, src).expect("write fixture");
    path
}

fn verify_fn(path: &std::path::Path, func: &str) -> VerifyResult {
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    })
}

fn obligations(path: &std::path::Path) -> Vec<String> {
    list_trait_conformance_obligations(path.to_str().unwrap()).unwrap_or_default()
}

fn verify_obligation(path: &std::path::Path, name: &str) -> VerifyResult {
    verify_trait_conformance_obligation(path.to_str().unwrap(), name).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    })
}

/// True when this net leaves the violating impl CLEAN (Verified). An `Error` or a
/// `Counterexample` both mean the file does NOT falsely verify via this net.
fn is_clean_verify(result: &VerifyResult) -> bool {
    matches!(result, VerifyResult::Verified)
}

/// Runs BOTH nets on the impl method `method_name` (whose body violates the trait
/// `ensures`) and reports. The file is a false-verify iff net A returns a clean
/// `Verified` AND net B (if the obligation is even listed) is not a
/// counterexample. Emits a full diagnostic so the adjudication is legible.
fn adjudicate(label: &str, src: &str, method_name: &str, conformance_name: &str) {
    let path = fixture(src, label);
    let net_a = verify_fn(&path, method_name);
    let listed = obligations(&path);
    let net_b = if listed.iter().any(|n| n == conformance_name) {
        Some(verify_obligation(&path, conformance_name))
    } else {
        None
    };
    let _ = std::fs::remove_file(&path);

    eprintln!("---- {label} ----");
    eprintln!("  NET A verify_fn({method_name:?}) = {net_a:?}");
    eprintln!("  conformance obligations listed = {listed:?}");
    eprintln!("  NET B verify_obligation({conformance_name:?}) = {net_b:?}");

    let a_clean = is_clean_verify(&net_a);
    // Net B is "clean" if the obligation is not listed at all, or listed but
    // reports Verified. A counterexample or error means B caught it.
    let b_clean = match &net_b {
        None => true, // not even listed -> B does not check it
        Some(r) => is_clean_verify(r),
    };

    assert!(
        !(a_clean && b_clean),
        "{label}: CARDINAL FALSE-VERIFY — a contract-violating impl method is CLEAN under BOTH \
         nets. NET A (direct verify) = {net_a:?}; NET B (conformance) = {net_b:?}. The body \
         violates the trait `ensures`, yet nothing refutes it, so a caller trusting the trait \
         contract is unbacked."
    );
}

// ---------------------------------------------------------------------------
// Reading 2: MARKED, simple non-Self method with own `#[requires]`.
// Expectation per recon: net A's dedicated error FIRES -> not a false verify.
// ---------------------------------------------------------------------------
const R2_MARKED_SIMPLE: &str = r#"
#[trust_vc::trait_spec]
trait Getter {
    #[trust_vc::ensures(result > 0i32)]
    fn get(&self) -> i32;
}

struct Bad(i32);

#[trust_vc::trait_impl]
impl Getter for Bad {
    #[trust_vc::requires(true)]
    fn get(&self) -> i32 { -1i32 }
}
"#;

#[test]
fn r2_marked_simple_requires_does_not_false_verify() {
    adjudicate(
        "R2_MARKED_SIMPLE",
        R2_MARKED_SIMPLE,
        "get",
        "trait impl conformance Getter::get for Bad",
    );
}

// ---------------------------------------------------------------------------
// Reading 3: MARKED, but an explicitly-typed `self: Self` receiver — the
// self-substituter rewrites `Self`, so the token identity net A relies on may
// diverge from the raw method, defeating the dedicated error.
// ---------------------------------------------------------------------------
const R3_SELF_TYPED_RECEIVER: &str = r#"
#[trust_vc::trait_spec]
trait Getter {
    #[trust_vc::ensures(result > 0i32)]
    fn get(self: Self) -> i32;
}

struct Bad(i32);

#[trust_vc::trait_impl]
impl Getter for Bad {
    #[trust_vc::requires(true)]
    fn get(self: Self) -> i32 { -1i32 }
}
"#;

#[test]
fn r3_self_typed_receiver_requires_does_not_false_verify() {
    adjudicate(
        "R3_SELF_TYPED_RECEIVER",
        R3_SELF_TYPED_RECEIVER,
        "get",
        "trait impl conformance Getter::get for Bad",
    );
}

// NOTE on the UNMARKED shape (no `#[trait_spec]`/`#[trait_impl]`): that is NOT a
// false-verify and is deliberately not probed here. Without the markers trust-vc
// registers no trait relationship, so there is no published trait contract for
// any caller to trust; verifying the impl method against its own (no-`ensures`)
// contract to `Verified` is correct. The cardinal hole is the MARKED shapes
// (R2/R3), where a caller legitimately trusts the trait `ensures`.

// ---------------------------------------------------------------------------
// CONTROL: the SAME shape WITHOUT the own-`requires` exempt trigger must be
// refuted by net B (the established behavior in conformance_attribution_soundness).
// If this control does NOT refute, the probe's baseline is wrong.
// ---------------------------------------------------------------------------
const CONTROL_NO_REQUIRES: &str = r#"
#[trust_vc::trait_spec]
trait Getter {
    #[trust_vc::ensures(result > 0i32)]
    fn get(&self) -> i32;
}

struct Bad(i32);

#[trust_vc::trait_impl]
impl Getter for Bad {
    fn get(&self) -> i32 { -1i32 }
}
"#;

#[test]
fn control_no_requires_is_refuted_by_conformance() {
    let path = fixture(CONTROL_NO_REQUIRES, "CONTROL");
    let name = "trait impl conformance Getter::get for Bad";
    let listed = obligations(&path);
    let net_b = verify_obligation(&path, name);
    let _ = std::fs::remove_file(&path);
    eprintln!("---- CONTROL_NO_REQUIRES ----");
    eprintln!("  listed = {listed:?}");
    eprintln!("  NET B = {net_b:?}");
    assert!(
        matches!(net_b, VerifyResult::Counterexample { .. }),
        "CONTROL: a violating impl with NO own requires must be refuted by conformance; got \
         {net_b:?}"
    );
}

// ---------------------------------------------------------------------------
// DIAGNOSTIC: sibling-default-call all-defaults impl. `f()` default calls `g()`
// (default 5u8) and promises `>= 10`. Post-attribution the generic CALLER
// correctly Verifies (it trusts the trait ensures — Verus does the same); the
// violation must be caught by the SEPARATE conformance obligation on `Promise::f
// for S`. Prints both so we can tell "stale test (caller Verifies, conformance
// refutes)" from "real hole (nothing refutes)".
// ---------------------------------------------------------------------------
const BAD_SIBLING_CALL_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait Promise {
    fn g(&self) -> u8 {
        5u8
    }
    #[trust_vc::ensures(result >= 10)]
    fn f(&self) -> u8 {
        self.g()
    }
}
struct S;
#[trust_vc::trait_impl]
impl Promise for S {}
#[trust_vc::ensures(true)]
fn generic_caller_asserts_f_ge_10<A: Promise>(a: A) {
    trust_vc::assert!(a.f() >= 10);
}
"#;

#[test]
fn diagnostic_sibling_default_conformance_obligation() {
    let path = fixture(BAD_SIBLING_CALL_DEFAULT, "sibling");
    let listed = obligations(&path);
    let caller = verify_fn(&path, "generic_caller_asserts_f_ge_10");
    let obl_results: Vec<(String, VerifyResult)> = listed
        .iter()
        .map(|n| (n.clone(), verify_obligation(&path, n)))
        .collect();
    let _ = std::fs::remove_file(&path);
    eprintln!("---- BAD_SIBLING_CALL_DEFAULT ----");
    eprintln!("  caller verify_fn = {caller:?}");
    eprintln!("  conformance obligations listed = {listed:?}");
    for (n, r) in &obl_results {
        eprintln!("  obligation {n:?} = {r:?}");
    }
    // The file must fail closed SOMEWHERE: either the caller refutes (old
    // folding) OR a conformance obligation refutes (attribution design). If BOTH
    // the caller Verifies AND no obligation refutes, it is a real cardinal
    // false-verify.
    let caller_clean = matches!(caller, VerifyResult::Verified);
    let any_obl_refutes = obl_results
        .iter()
        .any(|(_, r)| matches!(r, VerifyResult::Counterexample { .. }));
    assert!(
        !(caller_clean && !any_obl_refutes),
        "CARDINAL: caller Verifies AND no conformance obligation refutes the non-conforming \
         all-defaults `Promise::f for S` (default f returns 5, ensures >= 10). Nothing catches \
         it. caller={caller:?}, obligations={obl_results:?}"
    );
}
