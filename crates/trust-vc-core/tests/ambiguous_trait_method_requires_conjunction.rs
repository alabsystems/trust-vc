// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! END-TO-END guard for the ambiguous-`(type, method)` precondition drop.
//!
//! When two DIFFERENT traits declare a requires-bearing method of the same name
//! for one concrete type, `concrete_impl_method_requires` used to DROP the key
//! entirely — so NEITHER trait's precondition was checked and a violating call
//! passed unflagged. Both traits lost the obligation, not just the ambiguous one.
//!
//! CONJUNCTION, NOT DISJUNCTION. The source comment used to recommend emitting
//! the disjunction, and implementing that as written would have shipped a second
//! hole: the call resolves to exactly one candidate and we cannot tell which, so
//! the obligation must hold for WHICHEVER it is. That is `req_T && req_U` —
//! stronger than either, so it over-rejects rather than misses. The disjunction
//! is WEAKER than either: below, `T::f` requires `x < 10` and `U::f` requires
//! `x > 100`, so the violating call `s.f(5)` satisfies `5 < 10 || 5 > 100` and
//! would still pass.
//!
//! FIXTURE SHAPE IS LOAD-BEARING — the call sits in STATEMENT position
//! (`let _w = s.f(5); 0`) rather than tail position. With two impls in scope,
//! `s.f(..)` as the returned expression fails in return-value lowering
//! ("unsupported method `f` on type `S`") long before any call-site precondition
//! is considered, so a tail-position fixture is non-`Verified` at HEAD too and
//! measures nothing. The first version of this test made exactly that mistake and
//! passed without the fix.
//!
//! Measured four ways, cache-off, with the fix stashed and restored:
//!
//! | fixture                        | HEAD           | fixed          |
//! |--------------------------------|----------------|----------------|
//! | two traits, violating call     | **Verified**   | Counterexample |
//! | one trait, satisfying call     | Verified       | Verified       |
//! | one trait, violating call      | Counterexample | Counterexample |
//!
//! Only the ambiguous row moves, which is what makes the verdict attributable to
//! the merge and not to anything else in the fixture.
//!
//! The unit-level counterparts, including the mismatched-signature case that
//! still drops, live in `vc_extraction::trait_contracts::tests::
//! test_concrete_impl_method_requires_{conjoins,drops}_*`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// `S` impls BOTH traits, whose `f` preconditions cannot hold together.
const AMBIGUOUS: &str = r#"
#[trust_vc::trait_spec]
pub trait T { #[trust_vc::requires(x < 10u64)] fn f(&self, x: u64) -> u64; }
#[trust_vc::trait_spec]
pub trait U { #[trust_vc::requires(x > 100u64)] fn f(&self, x: u64) -> u64; }

pub struct S;
#[trust_vc::trait_impl]
impl T for S { fn f(&self, x: u64) -> u64 { x } }
#[trust_vc::trait_impl]
impl U for S { fn f(&self, x: u64) -> u64 { x } }

#[trust_vc::ensures(result == 0u64)]
pub fn calls_ambiguous(s: &S) -> u64 { let _w = s.f(5u64); 0u64 }
"#;

/// Only `T` is impl'd. `calls_single_ok` satisfies its lone precondition;
/// `calls_single_bad` violates it. Together these pin that the merge neither
/// over-rejects the ordinary single-trait call nor disturbs its refutation.
const SINGLE: &str = r#"
#[trust_vc::trait_spec]
pub trait T { #[trust_vc::requires(x < 10u64)] fn f(&self, x: u64) -> u64; }

pub struct S;
#[trust_vc::trait_impl]
impl T for S { fn f(&self, x: u64) -> u64 { x } }

#[trust_vc::ensures(result == 0u64)]
pub fn calls_single_ok(s: &S) -> u64 { let _w = s.f(5u64); 0u64 }

#[trust_vc::ensures(result == 0u64)]
pub fn calls_single_bad(s: &S) -> u64 { let _w = s.f(999u64); 0u64 }
"#;

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_ambig_{}_{}.rs", std::process::id(), tmp_id));
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

/// Control A. One trait, precondition satisfied, call verifies — so the merge
/// did not simply start rejecting trait-method calls.
#[test]
fn a_single_trait_call_satisfying_its_precondition_still_verifies() {
    let result = verify("ok", "calls_single_ok", SINGLE);
    assert!(
        matches!(result, VerifyResult::Verified),
        "control: `s.f(5)` against a lone `requires(x < 10)` must still verify: {result:?}"
    );
}

/// Control B. One trait, precondition violated, call refuted — so the ordinary
/// single-candidate check is intact.
#[test]
fn a_single_trait_call_violating_its_precondition_is_still_refuted() {
    let result = verify("bad", "calls_single_bad", SINGLE);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "control: `s.f(999)` against `requires(x < 10)` must still be refuted: {result:?}"
    );
}

/// THE GUARD. Same call, same argument as control A; the only difference is that
/// a second trait also declares a requires-bearing `f` for `S`.
///
/// At HEAD this returned `Verified` — the ambiguous key was dropped, so no
/// call-site obligation was emitted at all and BOTH preconditions went
/// unchecked. Under the conjunction `5 < 10 && 5 > 100` is false, so the call
/// must be refuted. The refuted obligation is `__call_requires_pp0_T__f_0_1`,
/// whose trailing `_1` is the clause index: it is the MERGED second clause, from
/// trait `U`, that fails.
#[test]
fn an_ambiguous_call_is_checked_against_both_traits() {
    let result = verify("ambig", "calls_ambiguous", AMBIGUOUS);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: with two requires-bearing `f` declarations in scope the call-site \
         precondition must be checked against BOTH; verifying means the ambiguous key was \
         dropped again and neither was checked. Got: {result:?}"
    );
}
