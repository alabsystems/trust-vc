// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! REGRESSION GUARD for a fixed soundness defect (was a defect WITNESS; the fix
//! landed and flipped `a_field_projection_receiver_is_failed_closed`).
//!
//! `record_trait_method_contract_call` is the only producer of call-site
//! precondition asserts, and it used to emit one only when the receiver was a
//! BARE IDENTIFIER:
//!
//! ```ignore
//! let Some(receiver_name) = expr_path_ident(&mc.receiver) else { return; };
//! ```
//!
//! So a call through `self.inner.f(x)`, `v[0].f(x)` or `make().f(x)` emitted
//! nothing, and a call VIOLATING the callee's `requires` was never flagged.
//!
//! What that was and was not. The caller gained no unearned FACT — the trait
//! postcondition axiom is itself `requires ==> ensures`, so an unestablished
//! precondition yields no `ensures` either. What it meant is that a
//! precondition-violating program PASSED verification instead of being rejected:
//! a missed bug report, not a false proof. Those are not interchangeable, and the
//! source comment used to assert "a missed obligation is conservative", which is
//! true for an ASSUMPTION and false for a `requires`.
//!
//! THE FIX: an unresolvable receiver fails closed — but only when a same-named
//! method with a NON-EMPTY `requires` is actually in scope. That guard is what
//! keeps the over-rejection proportionate to the evidence, and
//! `an_unresolvable_receiver_without_a_requires_bearing_contract_still_verifies`
//! pins it: without that test, "fail closed" could be tightened into rejecting
//! every unresolvable receiver in the language and no test would notice.
//!
//! Still open, same shape: the sibling ambiguity drop in `trait_contracts.rs`
//! removes the key for BOTH traits when two declare a same-named
//! requires-bearing method for one concrete type.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Both callees violate `#[requires(x < 10)]` with the same argument; the
/// functions differ only in the receiver's syntactic shape.
const SRC: &str = r#"
#[trust_vc::trait_spec]
pub trait Lim { #[trust_vc::requires(x < 10u64)] fn f(&self, x: u64) -> u64; }
pub struct S;
#[trust_vc::trait_impl]
impl Lim for S { fn f(&self, x: u64) -> u64 { x } }

pub struct Outer { inner: S }

#[trust_vc::ensures(true)]
pub fn bare_ident_receiver(s: &S) -> u64 { s.f(999u64) }

#[trust_vc::ensures(true)]
pub fn field_projection_receiver(o: &Outer) -> u64 { o.inner.f(999u64) }
"#;

/// Same unresolvable receiver shape, but the trait method declares NO `requires`.
/// Dropping this call site hides nothing, so it must NOT be rejected.
const NO_REQUIRES_SRC: &str = r#"
#[trust_vc::trait_spec]
pub trait Free { #[trust_vc::ensures(result == result)] fn g(&self, x: u64) -> u64; }
pub struct S2;
#[trust_vc::trait_impl]
impl Free for S2 { fn g(&self, x: u64) -> u64 { x } }

pub struct Outer2 { inner: S2 }

#[trust_vc::ensures(true)]
pub fn field_projection_no_requires(o: &Outer2) -> u64 { o.inner.g(999u64) }
"#;

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_rsp_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

/// The control. With a bare-identifier receiver the obligation IS emitted, and
/// `f(999)` against `#[requires(x < 10)]` is caught. This is what makes the
/// verdict below attributable to the receiver's SHAPE and nothing else — and it
/// also proves the fix did not simply reject everything.
#[test]
fn a_bare_identifier_receiver_catches_the_violated_precondition() {
    let result = verify("bare", "bare_ident_receiver", SRC);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "control: a violated precondition through a bare-ident receiver must be caught: \
         {result:?}"
    );
}

/// THE GUARD. Identical trait, identical impl, identical violating argument; the
/// receiver is `o.inner` rather than a bare identifier.
///
/// Before the fix this returned `Verified` — the call was skipped entirely. It
/// must now be anything BUT `Verified`. The verdict is a fail-closed extraction
/// error rather than a counterexample: trust-vc declines to verify a call whose
/// precondition it cannot site-check. Over-rejection is the correct direction; a
/// silently-skipped `requires` is not.
#[test]
fn a_field_projection_receiver_is_failed_closed() {
    let result = verify("field", "field_projection_receiver", SRC);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: a precondition-violating call through a non-bare-ident receiver must \
         never verify — the call-site precondition check would have been silently skipped. \
         Got: {result:?}"
    );
}

/// The narrowness pin. Same unresolvable receiver shape, but no `requires`
/// anywhere, so nothing can be hidden by dropping the call site — and the
/// program must still verify.
///
/// This is the test that stops "fail closed on unresolvable receivers" from being
/// widened into "reject every unresolvable receiver". If it starts failing, the
/// gate has lost its `!requires.is_empty()` condition and is now rejecting
/// programs that carry no precondition risk at all.
#[test]
fn an_unresolvable_receiver_without_a_requires_bearing_contract_still_verifies() {
    let result = verify("norq", "field_projection_no_requires", NO_REQUIRES_SRC);
    assert!(
        matches!(result, VerifyResult::Verified),
        "the fail-closed gate must fire only when a same-named requires-bearing method is in \
         scope; with no `requires` there is nothing to miss and this must still verify: \
         {result:?}"
    );
}
