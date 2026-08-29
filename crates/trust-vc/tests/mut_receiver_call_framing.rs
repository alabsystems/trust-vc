// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A call through a MUTABLE receiver must not be a no-op.
//!
//! Three independent cardinal false verifies live here, each of which reported
//! `verified` for a program every real implementation refutes, and each measured
//! on its own (neuter one, the others still hold).
//!
//! 1. GENERIC RECEIVER (`fn g(t: &mut impl Ctr)`, and its written-out
//!    `fn g<T: Ctr>(t: &mut T)` form). A trait-bound method lowers to a UF *of
//!    the receiver term* (`Ctr__a(t)`), so two `t.a()` reads bracketing
//!    `t.bump()` collapsed to the SAME term and `y - x == 0` verified. The
//!    receiver-mutation framing that already handled a user STRUCT receiver was
//!    unreachable here: a `TypeParam` receiver has no `Datatype`, so
//!    `receiver_struct_type_name` returned `None` and the struct branch never
//!    fired. Introduced-by note: `61c1a9ba` widened the APIT desugar to `&` /
//!    `&mut` / paren wrappers and pinned only the "claims more than the bounds
//!    justify" axis — never MUTATION, which is the whole point of `&mut`. The
//!    hole predates it for the written-out `<T: Ctr>(t: &mut T)` spelling.
//!
//! 2. RETURN LANE (any receiver, including a plain concrete struct). The
//!    return-value render runs on its own collector over a throwaway context
//!    that carried the struct-type registry and NOTHING else — no declared
//!    variables, no receiver-kind registry. Every mutation test it performs
//!    reads declared types, so for a PARAMETER they all answered "unknown" and
//!    the tail expression rendered against the ENTRY symbol. The result was two
//!    lanes disagreeing about one program: `t.bump(); assert!(t.n == 0)` failed
//!    closed while `t.bump(); t.n` with `ensures(result == 0)` verified.
//!
//! 3. LOOP FRAME (generic receiver). The loop/branch modified-set collector
//!    classifies receivers through the same `Datatype` map plus a collection
//!    set, so a `TypeParam` receiver was in NEITHER and stayed frame-pinned
//!    (`t == t_pre`) across a loop body that mutates it. Live on its own: it
//!    still false-verified with (1) and (2) already in place.
//!
//! NARROWNESS PINS — the fix must not be bought with blanket rejection:
//!
//! * `immutable_*` — `&impl Tr`, by-value `impl Tr` and a `&self` method on a
//!   `&mut impl Tr` receiver are all PURE and must keep verifying true claims
//!   (the actual win of `61c1a9ba`), with their liars still refuted.
//! * `pure_read_across_mut_receiver_*` — a `&self` call does not havoc, so two
//!   reads bracketing it still collapse to one term.
//! * `mut_receiver_read_after_mutation_still_uses_trait_ensures` — the fix
//!   models the post-call receiver as ARBITRARY, not as unmodelable: a fact
//!   that holds of EVERY receiver (the trait's own `ensures`) must still be
//!   provable after the mutation.
//! * `unmutated_binding_survives_a_mutation_of_another` — mutating a binding
//!   the return value does not read costs nothing.
//! * `pure_generic_receiver_read_in_a_loop_stays_framed` — a pure call must not
//!   enter the loop's modified set, or every true invariant over an only-read
//!   generic receiver would be lost.

use trust_vc_core::{verify_function_from_file, VerifyResult};

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_mut_recv_{label}_{}_{}.rs",
        std::process::id(),
        FIXTURE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).expect("write mut-receiver fixture");
    path
}

fn verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result =
        verify_function_from_file(path_str, "g").unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

fn assert_verified(label: &str, source: &str) {
    let result = verdict(label, source);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label}: a TRUE claim must still verify — this is the narrowness pin \
         keeping the fix from being a blanket rejection; got: {result:?}"
    );
}

/// A claim that does NOT follow must be REFUTED, and refuted for a reason that
/// means the solver actually ran. `Counterexample` (a model), `NotProved` (the
/// obligation was put to the solver and not discharged) and `Unknown` all count.
/// `Verified` is the cardinal failure; a bare `Error` is excluded because a
/// fixture that never reached the pipeline would otherwise pass every pin in
/// this file vacuously.
fn assert_rejected(label: &str, source: &str) {
    let result = verdict(label, source);
    match result {
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE VERIFY — a call through a mutable receiver \
             was treated as a no-op on that receiver"
        ),
        other => panic!(
            "{label}: expected a refutation, got {other:?}. An `Error` here means \
             the fixture never reached the solver, so the pin proves nothing."
        ),
    }
}

/// `trait Ctr` with a pure reader whose only guarantee is `result >= 2`, and a
/// mutator. Every concrete `impl` whose `bump` changes what `a` reports refutes
/// `y - x == 0`, e.g. `n: int`, `a() = self.n`, `bump() { self.n += 1 }`.
const CTR: &str = "
#[trust_vc::trait_spec]
pub trait Ctr {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
    fn bump(&mut self);
}
";

// ---------------------------------------------------------------------------
// 1. Generic receiver — the reported reproducer and its spellings.
// ---------------------------------------------------------------------------

#[test]
fn apit_mut_receiver_mutation_is_not_a_no_op() {
    assert_rejected(
        "apit_mut",
        &format!(
            "{CTR}
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut impl Ctr) -> int {{ let x = t.a(); t.bump(); let y = t.a(); y - x }}
"
        ),
    );
}

/// The written-out form `&mut impl Ctr` desugars to. It has the SAME hole, which
/// is why the fix belongs in the receiver-mutation framing and not in the APIT
/// desugar that `61c1a9ba` touched.
#[test]
fn written_out_generic_mut_receiver_mutation_is_not_a_no_op() {
    assert_rejected(
        "written_out_mut",
        &format!(
            "{CTR}
#[trust_vc::ensures(result == 0)]
pub fn g<T: Ctr>(t: &mut T) -> int {{ let x = t.a(); t.bump(); let y = t.a(); y - x }}
"
        ),
    );
}

/// The in-body `assert!` lane, reached without going through the return value —
/// this is the half the return-lane seed does not cover, so it pins the
/// generic-receiver havoc on its own.
#[test]
fn apit_mut_receiver_mutation_is_not_a_no_op_in_an_assert() {
    assert_rejected(
        "apit_mut_assert",
        &format!(
            "{CTR}
#[trust_vc::ensures(result >= 0)]
pub fn g(t: &mut impl Ctr) -> int {{
    let x = t.a();
    t.bump();
    let y = t.a();
    assert!(y - x == 0);
    1
}}
"
        ),
    );
}

/// UFCS is the exact desugaring of the method call, so it must be framed
/// identically or the fix is one spelling wide.
#[test]
fn ufcs_spelling_of_the_mut_receiver_call_is_framed_too() {
    assert_rejected(
        "ufcs_mut",
        &format!(
            "{CTR}
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut impl Ctr) -> int {{ let x = t.a(); Ctr::bump(t); let y = t.a(); y - x }}
"
        ),
    );
}

/// A `&mut self` method reached through a SUPERTRAIT: `T: Ext` implies
/// `T: Base`, so `t.bump()` is a legal call whose mutation must be framed by the
/// same supertrait closure the method resolution uses.
#[test]
fn supertrait_declared_mut_method_is_framed() {
    assert_rejected(
        "supertrait_mut",
        "
#[trust_vc::trait_spec]
pub trait Base { fn bump(&mut self); }
#[trust_vc::trait_spec]
pub trait Ext: Base {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut impl Ext) -> int { let x = t.a(); t.bump(); let y = t.a(); y - x }
",
    );
}

/// The receiver-kind walk must descend into inline modules, or a trait declared
/// one `mod` deep silently returns to the unframed behaviour.
#[test]
fn trait_declared_in_an_inline_module_is_framed() {
    assert_rejected(
        "mod_trait_mut",
        "
pub mod m {
    #[trust_vc::trait_spec]
    pub trait Ctr {
        #[trust_vc::ensures(result >= 2)]
        fn a(&self) -> int;
        fn bump(&mut self);
    }
}
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut impl m::Ctr) -> int { let x = t.a(); t.bump(); let y = t.a(); y - x }
",
    );
}

// ---------------------------------------------------------------------------
// 2. Return lane — a CONCRETE receiver, where the in-body lane was already
//    correct and only the return render leaked.
// ---------------------------------------------------------------------------

/// The discriminator for the return lane specifically: this exact body already
/// failed CLOSED when the post-mutation read was written as an `assert!` (see
/// the sibling test below). Only the returned-value spelling verified.
#[test]
fn concrete_mut_ref_receiver_mutation_reaches_the_return_value() {
    assert_rejected(
        "concrete_mut_ref_return",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn bump(&mut self) { self.n = self.n + 1; }
}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 { t.bump(); t.n }
",
    );
}

/// Same body, post-mutation read written as an `assert!`. Already correct before
/// the fix — kept as the control that identifies the return lane as the leak.
#[test]
fn concrete_mut_ref_receiver_mutation_control_via_assert() {
    assert_rejected(
        "concrete_mut_ref_assert",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn bump(&mut self) { self.n = self.n + 1; }
}
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) { t.bump(); assert!(t.n == 0); }
",
    );
}

/// An OWNED struct parameter takes the same path — the leak was about the
/// return render having no declared types, not about the reference.
#[test]
fn owned_struct_receiver_mutation_reaches_the_return_value() {
    assert_rejected(
        "owned_struct_return",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn bump(&mut self) { self.n = self.n + 1; }
}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(mut t: C) -> u64 { t.bump(); t.n }
",
    );
}

// ---------------------------------------------------------------------------
// 3. Loop frame — the modified-set collector classifies receivers through a
//    `Datatype` map and a collection set, and a `TypeParam` receiver is in
//    NEITHER, so it stayed frame-pinned (`t == t_pre`) across a loop body that
//    mutates it. Live on its own: `loopnoinv` false-verified with the two
//    straight-line halves already in place.
// ---------------------------------------------------------------------------

#[test]
fn generic_receiver_mutated_in_a_loop_joins_the_modified_set() {
    assert_rejected(
        "loop_modset_generic",
        &format!(
            "{CTR}
#[trust_vc::requires(n == 3u64)]
pub fn g(t: &mut impl Ctr, mut i: u64, n: u64) {{
    let start = t.a();
    while i < n {{
        t.bump();
        i = i + 1u64;
    }}
    trust_vc::assert!(t.a() == start);
}}
"
        ),
    );
}

/// The in-loop-body read, which the straight-line havoc already covers. Kept so
/// a regression can be localised: if THIS one goes red the body framing broke,
/// if only the post-loop one does the modified-set seeding broke.
#[test]
fn generic_receiver_mutated_in_a_loop_body_read_is_framed() {
    assert_rejected(
        "loop_body_generic",
        &format!(
            "{CTR}
#[trust_vc::requires(n == 3u64)]
pub fn g(t: &mut impl Ctr, mut i: u64, n: u64) {{
    let start = t.a();
    while i < n {{
        trust_vc::invariant!(n == 3u64);
        t.bump();
        i = i + 1u64;
        trust_vc::assert!(t.a() == start);
    }}
}}
"
        ),
    );
}

/// NO over-rejection in a loop: a pure `&self` call must NOT put the receiver in
/// the modified set, so a true fact about an only-read generic receiver stays
/// framed across the loop.
#[test]
fn pure_generic_receiver_read_in_a_loop_stays_framed() {
    assert_verified(
        "loop_pure_generic",
        "
#[trust_vc::trait_spec]
pub trait Ctr {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
    fn peek(&self) -> int;
    fn bump(&mut self);
}
#[trust_vc::requires(t.a() == 2)]
#[trust_vc::requires(n == 3u64)]
pub fn g(t: &mut impl Ctr, mut i: u64, n: u64) {
    while i < n {
        trust_vc::invariant!(n == 3u64);
        let _p = t.peek();
        i = i + 1u64;
    }
    trust_vc::assert!(t.a() == 2);
}
",
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS
// ---------------------------------------------------------------------------

/// `&impl Tr` (immutable) — the actual capability `61c1a9ba` added. Reverting
/// that commit was the wrong answer precisely because this must keep working.
#[test]
fn immutable_shared_ref_apit_still_verifies() {
    assert_verified(
        "immutable_apit",
        "
#[trust_vc::trait_spec]
pub trait P1 {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}
#[trust_vc::ensures(result >= 2)]
pub fn g(t: &impl P1) -> int { t.a() }
",
    );
}

/// …and its liar is still refuted, at the exact bound boundary.
#[test]
fn immutable_shared_ref_apit_liar_still_refutes() {
    assert_rejected(
        "immutable_apit_liar",
        "
#[trust_vc::trait_spec]
pub trait P1 {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}
#[trust_vc::ensures(result >= 3)]
pub fn g(t: &impl P1) -> int { t.a() }
",
    );
}

/// By-value `impl Tr`, the other half of the same desugar.
#[test]
fn immutable_by_value_apit_still_verifies() {
    assert_verified(
        "immutable_by_value",
        "
#[trust_vc::trait_spec]
pub trait P1 {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}
#[trust_vc::ensures(result >= 2)]
pub fn g(t: impl P1) -> int { t.a() }
",
    );
}

/// A `&mut impl Tr` receiver that is only READ. The reference's mutability alone
/// must not cost anything — only an actual `&mut self` call may.
#[test]
fn pure_read_on_a_mut_receiver_still_verifies() {
    assert_verified(
        "pure_read_mut_recv",
        &format!(
            "{CTR}
#[trust_vc::ensures(result >= 2)]
pub fn g(t: &mut impl Ctr) -> int {{ t.a() }}
"
        ),
    );
}

/// Two reads bracketing a `&self` method: `peek` is PURE, so the receiver is not
/// havoced and the two `t.a()` terms still collapse. A fix that havoced on any
/// call — rather than on the resolved receiver kind — would break this.
#[test]
fn pure_read_across_mut_receiver_does_not_havoc() {
    assert_verified(
        "pure_call_no_havoc",
        "
#[trust_vc::trait_spec]
pub trait Ctr {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
    fn peek(&self) -> int;
    fn bump(&mut self);
}
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut impl Ctr) -> int { let x = t.a(); let _p = t.peek(); let y = t.a(); y - x }
",
    );
}

/// A value read BEFORE the mutation is unaffected by it.
#[test]
fn value_read_before_the_mutation_still_verifies() {
    assert_verified(
        "read_before_mutation",
        &format!(
            "{CTR}
#[trust_vc::ensures(result >= 2)]
pub fn g(t: &mut impl Ctr) -> int {{ let x = t.a(); t.bump(); x }}
"
        ),
    );
}

/// THE anti-blanket-rejection pin. After the mutation the receiver is modeled as
/// ARBITRARY — not as unmodelable — so a fact that holds of EVERY receiver (the
/// trait's own `ensures`) is still provable about the post-mutation read. An
/// implementation that declined the return model instead of minting a fresh
/// receiver symbol fails here while passing every test above.
#[test]
fn mut_receiver_read_after_mutation_still_uses_trait_ensures() {
    assert_verified(
        "read_after_mutation",
        &format!(
            "{CTR}
#[trust_vc::ensures(result >= 2)]
pub fn g(t: &mut impl Ctr) -> int {{ t.bump(); t.a() }}
"
        ),
    );
}

/// Mutating a binding the return value never reads costs nothing.
#[test]
fn unmutated_binding_survives_a_mutation_of_another() {
    assert_verified(
        "unrelated_mutation",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn bump(&mut self) { self.n = self.n + 1; }
}
#[trust_vc::requires(k == 7)]
#[trust_vc::ensures(result == 7)]
pub fn g(t: &mut C, k: u64) -> u64 { t.bump(); k }
",
    );
}

/// A `&self` method on a CONCRETE receiver is resolved as pure by the same
/// registry, so a straight-line read across it still verifies. Without the
/// receiver-kind seed in the return lane this would have to fail closed.
#[test]
fn concrete_pure_method_across_the_return_lane_still_verifies() {
    assert_verified(
        "concrete_pure_return",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn peek(&self) -> u64 { self.n }
}
#[trust_vc::requires(t.n == 3)]
#[trust_vc::ensures(result == 3)]
pub fn g(t: &mut C) -> u64 { let _p = t.peek(); t.n }
",
    );
}
