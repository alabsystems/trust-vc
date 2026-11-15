// Certificate tests — trust-vc's soundness edge over Verus, at the front-end seam.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Run with: targo --unverified test -p trust-vc-driver --features certificates
//
// These tests demonstrate the capability that makes trust-vc *better* than
// Verus rather than merely equal: a verified result carries an ay UNSAT proof
// (Alethe text) that the small, independent `trust-vc-kernel` re-checks. Verus
// trusts Z3's answer with no checkable artifact.
#![cfg(feature = "certificates")]

use trust_vc_core::ir::CompareOp;
use trust_vc_driver::lower::{add, cmp, lit, uint, var, Binding, DriverFn, Outcome};

fn u32t() -> trust_vc_core::ir::TrustVcType {
    uint(32)
}

/// A verified function produces a verdict AND an independently-checkable
/// certificate: the verdict is `Verified`, and any emitted certificate carries
/// Alethe proof text re-checked by trust-vc-kernel.
#[test]
fn verified_function_yields_checkable_certificate() {
    let f = DriverFn {
        name: "add_bounds".into(),
        params: vec![Binding::new("x", u32t()), Binding::new("y", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![
            cmp(CompareOp::Lt, var("x", u32t()), lit(100, u32t())),
            cmp(CompareOp::Lt, var("y", u32t()), lit(100, u32t())),
        ],
        body_value: Some(add(var("x", u32t()), var("y", u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(200, u32t()))],
    };

    let certified = f.verify_certified();
    assert_eq!(certified.outcome, Outcome::Verified);

    // The headline edge over Verus: the proven result carries an ay UNSAT proof
    // that trust-vc-kernel INDEPENDENTLY re-checked. Verus's black-box Z3 yields
    // no such artifact. (Empirically: Alethe proof ~350 chars, kernel_verified.)
    let cert = certified
        .certificate
        .expect("a verified result should carry a proof certificate");
    assert!(
        !cert.alethe.is_empty(),
        "the certificate must carry Alethe proof text"
    );
    assert!(
        cert.kernel_verified,
        "trust-vc-kernel must independently re-check the ay UNSAT proof"
    );
}

/// A refuted function is not certified: the verdict is `Refuted` and no proof
/// certificate is attached (there is no UNSAT proof for a false goal).
#[test]
fn refuted_function_has_no_certificate() {
    let f = DriverFn {
        name: "add_bounds_false".into(),
        params: vec![Binding::new("x", u32t()), Binding::new("y", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![
            cmp(CompareOp::Lt, var("x", u32t()), lit(100, u32t())),
            cmp(CompareOp::Lt, var("y", u32t()), lit(100, u32t())),
        ],
        body_value: Some(add(var("x", u32t()), var("y", u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(150, u32t()))],
    };

    let certified = f.verify_certified();
    assert_eq!(certified.outcome, Outcome::Refuted);
    assert!(
        certified.certificate.is_none(),
        "a refuted goal must not carry a proof certificate"
    );
}

/// A verified result distills into a portable, deterministic proof receipt that
/// attests independent kernel re-checking — a concrete token of trust-vc's
/// soundness edge over Verus's (artifact-free) black-box Z3.
#[test]
fn certificate_distills_to_deterministic_receipt() {
    let f = DriverFn {
        name: "add_bounds".into(),
        params: vec![Binding::new("x", u32t()), Binding::new("y", u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![
            cmp(CompareOp::Lt, var("x", u32t()), lit(100, u32t())),
            cmp(CompareOp::Lt, var("y", u32t()), lit(100, u32t())),
        ],
        body_value: Some(add(var("x", u32t()), var("y", u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(200, u32t()))],
    };
    let certified = f.verify_certified();
    assert_eq!(certified.outcome, Outcome::Verified);
    let cert = certified
        .certificate
        .expect("verified result carries a certificate");
    let r1 = cert.receipt();
    let r2 = cert.receipt();
    assert_eq!(r1, r2, "receipt must be deterministic");
    assert!(r1.kernel_verified, "receipt attests kernel re-checking");
    assert!(r1.alethe_len > 0, "receipt records a non-empty proof");
    assert_eq!(r1.alethe_len, cert.alethe.len());
}
