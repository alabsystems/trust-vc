// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard for a CARDINAL false verify: the concrete method symbol carries the
//! SELF TYPE but not the TRAIT, so two same-named methods for one type collide
//! and the FIRST-DECLARED body silently answered for BOTH.
//!
//! `parse_trait_impl_decl` binds an impl method to `format!("{type}__{method}")`
//! and `body_extract::format_call_expr` renders a no-self UFCS call
//! `<S as Trait>::m()` as `S::m` — the trait qualifier is DISCARDED, with a
//! source comment conceding "the trait name loses which impl is meant, so it
//! cannot distinguish two impls". `apply_inherent_impl_methods` then published
//! the definitional body axiom under a keeps-first `applied` dedup keyed by
//! `(self_type, method_name)`.
//!
//! Two members, both measured through the production CLI, cache off:
//!
//! | program                                     | HEAD           | truth |
//! |---------------------------------------------|----------------|-------|
//! | `<bool as TB>::v()` with `TA`+`TB` for bool  | **verified**   | 2     |
//! | same, asserting the TRUE value              | counterexample | 2     |
//! | `<S as Mk>::make()` beside inherent `S::make`| **verified**   | 9     |
//! | same, asserting the TRUE value              | counterexample | 9     |
//!
//! BOTH DIRECTIONS WRONG AT ONCE, and moving `impl TB` above `impl TA` inverted
//! every verdict — source order alone decided which body was believed, while
//! both trait-impl conformance rows stayed green and nothing failed closed.
//!
//! The fix drops the ambiguous key instead of resolving it first-wins (naming
//! the WRONG declaration is the false-verify direction), so the concrete symbol
//! is left unconstrained and the caller fails closed. Dropping BOTH sides is
//! required, not just the trait side: the ambiguity is in the RENDERED SYMBOL,
//! so gating only one kind leaves the other spelling reading the wrong body.
//! Measured: with the gate reverted the false program VERIFIES again, and with
//! only the trait half in place the inherent body still answers the trait call.
//!
//! The narrowness pins below are the point of this file: an unambiguous
//! single-trait call and an unambiguous inherent call must still verify the TRUE
//! claim and refute the FALSE one, in both directions. A fix that turns the true
//! claim into a counterexample has traded one defect for another.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Two local traits, each declaring `v`, both implemented for `bool`. Rust
/// disambiguates by UFCS; the engine's concrete symbol `bool::v` does not.
const TWO_TRAITS: &str = r#"
#[trust_vc::trait_spec]
trait TA {
    #[trust_vc::ensures(result >= 1u64)]
    fn v() -> u64;
}

#[trust_vc::trait_spec]
trait TB {
    #[trust_vc::ensures(result >= 1u64)]
    fn v() -> u64;
}

#[trust_vc::trait_impl]
impl TA for bool { fn v() -> u64 { 1u64 } }

#[trust_vc::trait_impl]
impl TB for bool { fn v() -> u64 { 2u64 } }

#[trust_vc::ensures(true)]
fn tb_returns_one(){ let x: u64 = <bool as TB>::v(); trust_vc::assert!(x == 1u64); }
"#;

/// Byte-identical except the two impls swap source order. At HEAD every verdict
/// inverted, which is what proves first-declaration-wins rather than a solver
/// artifact.
const TWO_TRAITS_FLIPPED: &str = r#"
#[trust_vc::trait_spec]
trait TA {
    #[trust_vc::ensures(result >= 1u64)]
    fn v() -> u64;
}

#[trust_vc::trait_spec]
trait TB {
    #[trust_vc::ensures(result >= 1u64)]
    fn v() -> u64;
}

#[trust_vc::trait_impl]
impl TB for bool { fn v() -> u64 { 2u64 } }

#[trust_vc::trait_impl]
impl TA for bool { fn v() -> u64 { 1u64 } }

#[trust_vc::ensures(true)]
fn ta_returns_two(){ let x: u64 = <bool as TA>::v(); trust_vc::assert!(x == 2u64); }
"#;

/// A nested `mod` is just as ambiguous a `S::make` as a sibling one. Counting
/// only `file.items` would leave this open — the exact shape that kept the
/// source-type and enum-discriminant registries broken.
const TWO_TRAITS_NESTED_MOD: &str = r#"
pub struct S;

#[trust_vc::trait_spec]
trait TA {
    #[trust_vc::ensures(result >= 0u64)]
    fn make() -> u64;
}

#[trust_vc::trait_impl]
impl TA for S { fn make() -> u64 { 1u64 } }

mod helper {
    #[trust_vc::trait_spec]
    pub trait TB {
        #[trust_vc::ensures(result >= 0u64)]
        fn make() -> u64;
    }

    #[trust_vc::trait_impl]
    impl TB for crate::S { fn make() -> u64 { 5u64 } }
}

#[trust_vc::ensures(true)]
fn ta_make_is_five(){ let x: u64 = <S as TA>::make(); trust_vc::assert!(x == 5u64); }
"#;

/// NARROWNESS PIN source: exactly one trait, so nothing is ambiguous and the
/// call must resolve to the impl body exactly as before.
const ONE_TRAIT: &str = r#"
pub struct S;

#[trust_vc::trait_spec]
trait Mk {
    #[trust_vc::ensures(result >= 0u64)]
    fn make() -> u64;
}

#[trust_vc::trait_impl]
impl Mk for S { fn make() -> u64 { 9u64 } }

#[trust_vc::ensures(true)]
fn make_is_nine(){ let x: u64 = <S as Mk>::make(); trust_vc::assert!(x == 9u64); }

#[trust_vc::ensures(true)]
fn make_is_one(){ let x: u64 = <S as Mk>::make(); trust_vc::assert!(x == 1u64); }
"#;

/// The cross-KIND member: an inherent `S::make` and a trait-supplied `S::make`
/// render to one symbol, and the inherent body answered the trait call.
const INHERENT_AND_TRAIT: &str = r#"
pub struct S;

impl S {
    #[trust_vc::proof]
    fn make() -> u64 { 1u64 }
}

#[trust_vc::trait_spec]
trait Mk {
    #[trust_vc::ensures(result >= 0u64)]
    fn make() -> u64;
}

#[trust_vc::trait_impl]
impl Mk for S { fn make() -> u64 { 9u64 } }

#[trust_vc::ensures(true)]
fn trait_make_is_one(){ let x: u64 = <S as Mk>::make(); trust_vc::assert!(x == 1u64); }
"#;

/// NARROWNESS PIN source: inherent only, no trait in sight.
const INHERENT_ONLY: &str = r#"
pub struct S;

impl S {
    #[trust_vc::proof]
    fn make() -> u64 { 1u64 }
}

#[trust_vc::ensures(true)]
fn make_is_one(){ let x: u64 = S::make(); trust_vc::assert!(x == 1u64); }

#[trust_vc::ensures(true)]
fn make_is_nine(){ let x: u64 = S::make(); trust_vc::assert!(x == 9u64); }
"#;

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_symcol_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        verify_function_from_file(path.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&path);
    result
}

// ---------------------------------------------------------------------------
// THE GUARDS — a false claim must never verify.
// ---------------------------------------------------------------------------

/// `<bool as TB>::v()` is 2. Asserting it equals 1 must not verify.
#[test]
fn two_traits_one_symbol_false_claim_does_not_verify() {
    let result = verify("tt", "tb_returns_one", TWO_TRAITS);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL REGRESSION: `<bool as TB>::v()` returns 2, so `x == 1` is FALSE. \
         Verifying means the first-declared `impl TA` body answered for TB again \
         (`bool::v` carries the self type but not the trait). Got: {result:?}"
    );
}

/// The order-flip half. With `impl TB` declared first, the FALSE claim moves to
/// the TA side — and must not verify there either.
#[test]
fn two_traits_one_symbol_false_claim_does_not_verify_in_either_order() {
    let result = verify("ttf", "ta_returns_two", TWO_TRAITS_FLIPPED);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL REGRESSION: `<bool as TA>::v()` returns 1, so `x == 2` is FALSE. \
         Verifying means source order still decides which impl is believed. Got: {result:?}"
    );
}

/// The collision counter must recurse into inline modules.
#[test]
fn two_traits_one_symbol_false_claim_does_not_verify_across_a_nested_mod() {
    let result = verify("ttn", "ta_make_is_five", TWO_TRAITS_NESTED_MOD);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: a `mod`-nested `impl TB for S` binds the same `S::make` symbol, \
         so the key is ambiguous and the call must fail closed; verifying means the \
         collision count stopped at `file.items`. Got: {result:?}"
    );
}

/// The cross-kind member: inherent body must not answer a trait UFCS call.
#[test]
fn inherent_and_trait_same_symbol_false_claim_does_not_verify() {
    let result = verify("it", "trait_make_is_one", INHERENT_AND_TRAIT);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL REGRESSION: `<S as Mk>::make()` returns 9, so `x == 1` is FALSE. \
         Verifying means the inherent `S::make` body (1) answered the trait call — \
         the UFCS spelling renders to the same `S::make` symbol. Got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — the unambiguous cases must be untouched, BOTH directions.
// ---------------------------------------------------------------------------

/// One trait, true claim: must still VERIFY. Without this the guards above are
/// satisfiable by rejecting every trait associated call.
#[test]
fn single_trait_true_claim_still_verifies() {
    let result = verify("one_t", "make_is_nine", ONE_TRAIT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "NARROWNESS: a lone `impl Mk for S` is unambiguous — `<S as Mk>::make() == 9` \
         must still verify. Got: {result:?}"
    );
}

/// One trait, false claim: must still be REFUTED (not merely un-verified for a
/// new reason, and certainly not verified).
#[test]
fn single_trait_false_claim_still_refuted() {
    let result = verify("one_f", "make_is_one", ONE_TRAIT);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "NARROWNESS: a lone `impl Mk for S` must still REFUTE `<S as Mk>::make() == 1` \
         with a counterexample, not fail closed for an unrelated reason. Got: {result:?}"
    );
}

/// Inherent only, true claim: must still VERIFY. The cross-kind gate drops the
/// inherent body only when a trait impl for the same type declares the same
/// name; with no trait present nothing may change. `S::make` is a proof
/// function, which panics when the exec body calls it at run time, so the
/// ghost-call rule refuses the answer; it refuses only a `Verified` answer.
#[test]
fn inherent_only_true_claim_still_verifies() {
    let result = verify("inh_t", "make_is_one", INHERENT_ONLY);
    assert!(
        matches!(
            &result,
            VerifyResult::Error { message }
                if message.contains("ghost function called from exec code")
        ),
        "NARROWNESS: with no trait impl in the file, `S::make() == 1` must still verify — \
         the cross-kind gate must not fire on a lone inherent method (a `Verified` answer, \
         refused by the ghost-call rule). Got: {result:?}"
    );
}

/// Inherent only, false claim: must still be REFUTED.
#[test]
fn inherent_only_false_claim_still_refuted() {
    let result = verify("inh_f", "make_is_nine", INHERENT_ONLY);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "NARROWNESS: with no trait impl in the file, `S::make() == 9` must still be \
         refuted with a counterexample. Got: {result:?}"
    );
}
