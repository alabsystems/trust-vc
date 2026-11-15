// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS: an impl method's own `ensures` is read in the IMPL's parameter
//! scope, and moves onto the trait method's call surface only BY POSITION.
//!
//! ## The hole (H5, measured at `ee37bb64`, cache off)
//!
//! Rust binds call arguments to an impl method's OWN parameters by position;
//! the trait's parameter NAMES carry no meaning inside the impl. An impl may
//! rename or permute them freely:
//!
//! ```text
//! #[trait_spec] trait T { fn f(&self, a: u64, b: u64) -> u64; }
//! #[trait_impl] impl T for S {
//!     #[ensures(result == a)]            // `a` is the impl's SECOND parameter
//!     fn f(&self, b: u64, a: u64) -> u64 { a }
//! }
//! ```
//!
//! `s.f(1, 2)` returns 2 (stock `trustc -Ztrust-verify=off`, run). The impl's
//! `ensures` was registered as raw text and then lowered by BOTH consumers in
//! the TRAIT's scope, where `a` is the FIRST parameter:
//!
//! * the caller axiom (`assert_impl_postcondition_axioms`) bound `a` to UF
//!   argument 0, so `s.f(1, 2) == 1` VERIFIED and `== 2` did not;
//! * the conformance extension (`build_impl_ensures_assert_obligations`)
//!   renamed through the trait names while the captured body is bound by
//!   POSITION, so the correct impl was REFUTED and an impl whose `ensures` is
//!   false as written (`{ b }`) PASSED.
//!
//! And the axiom carried no `is_external` gate, while conformance skips an
//! external impl, so `#[trait_impl] #[trust_vc::external] impl` published an
//! impl `ensures` that nothing checked. The two together are a FILE-LEVEL false
//! verify through the real CLI: `g` verifies directly in the impl's names, the
//! caller `e.g(1, 2) == 1` verifies through the axiom read in the trait's names,
//! and no conformance obligation exists to notice (runtime: `e.g(1, 2) == 2`,
//! the caller's `trust_vc::assert!` panics).
//!
//! ## The rule
//!
//! Registration rewrites the impl `ensures` onto the SAME positional
//! placeholders the captured body uses (`__trust_vc_conf_arg_i`), declining the
//! whole method whenever that rewrite cannot be exact (binder shadowing, a
//! parameter surviving in a macro token stream, a `result`/`__trust_vc_` param
//! name). Both consumers bind the placeholders by position and fail closed on an
//! arity mismatch; trait `requires`/`ensures` keep their own trait-scope map.
//! An external impl publishes no impl-`ensures` axiom (Verus parity: an
//! external impl is invisible), matching `assert_impl_trait_ensures_concrete_axioms`.
//!
//! Every pin below records the pre-fix verdict it replaced. Liars are asserted
//! REFUTED (`Counterexample`), not merely "not verified", wherever the fixed
//! engine refutes them; controls must VERIFY so a "fix" that simply stops
//! propagating permuted impls cannot pass.

use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn write_fixture(tag: &str, src: &str) -> String {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_implpos_{}_{tag}_{seq}.rs", std::process::id()));
    std::fs::write(&path, src).expect("write fixture");
    path.to_str().expect("utf8 path").to_string()
}

#[derive(Debug, Clone, Copy)]
enum Expect {
    /// `== Verified`.
    Verified,
    /// A refutation: `Counterexample`.
    Refuted,
    /// Checked and NOT proved: `Counterexample`, `NotProved` or `Unknown` —
    /// never `Verified`, and never `Error` (an `Error` would mean the goal
    /// stopped being CHECKED, which would pass while testing nothing).
    ///
    /// Used for a liar whose refutation needs a MODEL of a query carrying the
    /// quantified impl-postcondition axiom: ay answers such satisfiable queries
    /// `unknown`, so the engine reports `NotProved { Incompleteness }` — the
    /// verdict the ALIGNED-names liar `p5_liar` (never a hole) gets both before
    /// and after the fix. Every such liar is paired with a `*_neg` pin that
    /// PROVES its negation, so the refutation is still established — by proof
    /// rather than by model.
    NotVerified,
}

enum Target<'a> {
    Function(&'a str),
    Conformance(&'a str),
}

struct Pin<'a> {
    label: &'a str,
    target: Target<'a>,
    expect: Expect,
    /// The verdict measured on the unfixed engine at `ee37bb64`, for the record.
    before: &'a str,
}

fn short(result: &VerifyResult) -> String {
    match result {
        VerifyResult::Verified => "Verified".to_string(),
        VerifyResult::Counterexample {
            obligation_name, ..
        } => format!("Counterexample{{{obligation_name}}}"),
        other => {
            let text = format!("{other:?}");
            text.chars().take(260).collect()
        }
    }
}

fn run_pins(tag: &str, src: &str, pins: &[Pin<'_>]) {
    let path = write_fixture(tag, src);
    let mut failures = Vec::new();
    for pin in pins {
        let result = match pin.target {
            Target::Function(name) => verify_function_from_file(&path, name),
            Target::Conformance(name) => verify_trait_conformance_obligation(&path, name),
        }
        .unwrap_or_else(|e| VerifyResult::Error {
            message: e.to_string(),
        });
        let ok = match pin.expect {
            Expect::Verified => matches!(result, VerifyResult::Verified),
            Expect::Refuted => matches!(result, VerifyResult::Counterexample { .. }),
            Expect::NotVerified => matches!(
                result,
                VerifyResult::Counterexample { .. }
                    | VerifyResult::NotProved { .. }
                    | VerifyResult::Unknown { .. }
            ),
        };
        let line = format!(
            "{tag} {}: expect={:?} got={} (before: {})",
            pin.label,
            pin.expect,
            short(&result),
            pin.before
        );
        println!("PIN {line}");
        if !ok {
            failures.push(line);
        }
    }
    let _ = std::fs::remove_file(&path);
    assert!(
        failures.is_empty(),
        "{} pin(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

fn conformance_names(tag: &str, src: &str) -> Vec<String> {
    let path = write_fixture(tag, src);
    let names = list_trait_conformance_obligations(&path).expect("list conformance obligations");
    let _ = std::fs::remove_file(&path);
    names
}

// ---------------------------------------------------------------------------
// P1 — a swap permutation, no trust hatch.
// ---------------------------------------------------------------------------

const P1_SWAP: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait T {
    fn f(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T for S {
    #[trust_vc::ensures(result == a)]
    fn f(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn p1_liar_recv(s: S) {
    trust_vc::assert!(s.f(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn p1_ctrl_recv(s: S) {
    trust_vc::assert!(s.f(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn p1_neg_recv(s: S) {
    trust_vc::assert!(s.f(1u64, 2u64) != 1u64);
}

#[trust_vc::ensures(true)]
fn p1_liar_ufcs(s: S) {
    let v: u64 = <S as T>::f(&s, 1u64, 2u64);
    trust_vc::assert!(v == 1u64);
}

#[trust_vc::ensures(true)]
fn p1_ctrl_ufcs(s: S) {
    let v: u64 = <S as T>::f(&s, 1u64, 2u64);
    trust_vc::assert!(v == 2u64);
}

#[trust_vc::ensures(result == 1u64)]
fn p1_liar_return(s: S) -> u64 {
    s.f(1u64, 2u64)
}

#[trust_vc::ensures(result == 2u64)]
fn p1_ctrl_return(s: S) -> u64 {
    s.f(1u64, 2u64)
}
"#;

#[test]
fn p1_swapped_impl_params_bind_by_position() {
    run_pins(
        "p1",
        P1_SWAP,
        &[
            Pin {
                label: "p1_liar_recv s.f(1,2)==1",
                target: Target::Function("p1_liar_recv"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "p1_liar_ufcs <S as T>::f(&s,1,2)==1",
                target: Target::Function("p1_liar_ufcs"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "p1_liar_return ensures(result==1)",
                target: Target::Function("p1_liar_return"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "p1_ctrl_recv s.f(1,2)==2",
                target: Target::Function("p1_ctrl_recv"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "p1_neg_recv s.f(1,2)!=1 (the liar, refuted by proof)",
                target: Target::Function("p1_neg_recv"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "p1_ctrl_ufcs <S as T>::f(&s,1,2)==2",
                target: Target::Function("p1_ctrl_ufcs"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "p1_ctrl_return ensures(result==2)",
                target: Target::Function("p1_ctrl_return"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "conformance T::f for S (correct impl)",
                target: Target::Conformance("trait impl conformance T::f for S"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
            Pin {
                label: "direct f (impl names)",
                target: Target::Function("f"),
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
}

/// The hatch-free file lane: the CORRECT program (the P1 impl with only a TRUE
/// caller) must no longer be masked by a conformance obligation that wrongly
/// refutes the correct impl. Before: `trait impl conformance T::f for S` was a
/// Counterexample, so the whole file failed for the wrong reason.
const P1_CORRECT_PROGRAM: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait T {
    fn f(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T for S {
    #[trust_vc::ensures(result == a)]
    fn f(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn p1_ctrl_recv(s: S) {
    trust_vc::assert!(s.f(1u64, 2u64) == 2u64);
}
"#;

#[test]
fn p1_correct_program_every_obligation_verifies() {
    let names = conformance_names("p1_list", P1_CORRECT_PROGRAM);
    assert_eq!(
        names,
        vec!["trait impl conformance T::f for S".to_string()],
        "the non-external impl must still owe exactly its conformance obligation"
    );
    run_pins(
        "p1_file",
        P1_CORRECT_PROGRAM,
        &[
            Pin {
                label: "conformance T::f for S",
                target: Target::Conformance("trait impl conformance T::f for S"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
            Pin {
                label: "direct f",
                target: Target::Function("f"),
                expect: Expect::Verified,
                before: "Verified",
            },
            Pin {
                label: "p1_ctrl_recv s.f(1,2)==2",
                target: Target::Function("p1_ctrl_recv"),
                expect: Expect::Verified,
                before: "NotProved",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P2 — an impl `ensures` FALSE as written (true only under the trait-name
// reading) must be refuted by conformance, not passed.
// ---------------------------------------------------------------------------

const P2_FALSE_AS_WRITTEN: &str = r#"
struct S5;

#[trust_vc::trait_spec]
trait T5 {
    fn f5(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T5 for S5 {
    #[trust_vc::ensures(result == a)]
    fn f5(&self, b: u64, a: u64) -> u64 {
        b
    }
}
"#;

#[test]
fn p2_impl_ensures_false_as_written_is_refuted_by_conformance() {
    run_pins(
        "p2",
        P2_FALSE_AS_WRITTEN,
        &[
            Pin {
                label: "conformance T5::f5 for S5 (ensures false in impl names)",
                target: Target::Conformance("trait impl conformance T5::f5 for S5"),
                expect: Expect::Refuted,
                before: "Verified",
            },
            Pin {
                label: "direct f5",
                target: Target::Function("f5"),
                expect: Expect::Refuted,
                before: "Counterexample",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P3 — one axiom, two scopes: the trait `requires` is in the TRAIT's names, the
// impl `ensures` in the IMPL's. Neither may be read in the other's scope.
// ---------------------------------------------------------------------------

const P3_TWO_SCOPES: &str = r#"
struct W;

#[trust_vc::trait_spec]
trait TW {
    #[trust_vc::requires(b < 10u64)]
    fn w(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TW for W {
    #[trust_vc::ensures(result == a)]
    fn w(&self, b: u64, a: u64) -> u64 {
        a % 10u64
    }
}

#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn p3_liar_ens(p: W, y: u64) {
    trust_vc::assert!(p.w(7u64, y) == 7u64);
}

#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn p3_ctrl(p: W, y: u64) {
    trust_vc::assert!(p.w(7u64, y) == y);
}

#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn p3_neg(p: W, y: u64) {
    trust_vc::assert!(p.w(7u64, y) != 7u64);
}

#[trust_vc::requires(y >= 10u64 && y < 100u64)]
#[trust_vc::ensures(true)]
fn p3_liar_req(p: W, y: u64) {
    trust_vc::assert!(p.w(0u64, y) == y);
}
"#;

#[test]
fn p3_trait_requires_and_impl_ensures_keep_their_own_scopes() {
    run_pins(
        "p3",
        P3_TWO_SCOPES,
        &[
            Pin {
                label: "p3_liar_ens p.w(7,y)==7 (Rust: y)",
                target: Target::Function("p3_liar_ens"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            // Rust: `p.w(0, 15) == 5`. The trait `requires(b < 10)` binds the
            // SECOND argument `y`, which the caller cannot discharge, so no
            // axiom instance applies. A fix that moved the trait requires onto
            // the impl's names (`b` = first arg = 0 < 10) would verify this.
            Pin {
                label: "p3_liar_req p.w(0,y)==y at y in [10,100)",
                target: Target::Function("p3_liar_req"),
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                label: "p3_neg p.w(7,y)!=7 (the liar, refuted by proof)",
                target: Target::Function("p3_neg"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "p3_ctrl p.w(7,y)==y",
                target: Target::Function("p3_ctrl"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "conformance TW::w for W",
                target: Target::Conformance("trait impl conformance TW::w for W"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P4 — a partial shift: impl `(b, c)` against trait `(a, b)`; the impl's `b`
// is the trait's `a`.
// ---------------------------------------------------------------------------

const P4_PARTIAL_SHIFT: &str = r#"
struct Q;

#[trust_vc::trait_spec]
trait TQ {
    fn q(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TQ for Q {
    #[trust_vc::ensures(result == b)]
    fn q(&self, b: u64, c: u64) -> u64 {
        b
    }
}

#[trust_vc::ensures(true)]
fn p4_liar(q: Q) {
    trust_vc::assert!(q.q(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn p4_neg(q: Q) {
    trust_vc::assert!(q.q(1u64, 2u64) != 2u64);
}

#[trust_vc::ensures(true)]
fn p4_ctrl(q: Q) {
    trust_vc::assert!(q.q(1u64, 2u64) == 1u64);
}
"#;

#[test]
fn p4_partially_shifted_impl_params_bind_by_position() {
    run_pins(
        "p4",
        P4_PARTIAL_SHIFT,
        &[
            Pin {
                label: "p4_liar q.q(1,2)==2",
                target: Target::Function("p4_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "p4_neg q.q(1,2)!=2 (the liar, refuted by proof)",
                target: Target::Function("p4_neg"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "p4_ctrl q.q(1,2)==1",
                target: Target::Function("p4_ctrl"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "conformance TQ::q for Q",
                target: Target::Conformance("trait impl conformance TQ::q for Q"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P5 — aligned names: the regression anchor for the ordinary shape.
// ---------------------------------------------------------------------------

const P5_ALIGNED: &str = r#"
struct A;

#[trust_vc::trait_spec]
trait TA {
    fn g(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TA for A {
    #[trust_vc::ensures(result == b)]
    fn g(&self, a: u64, b: u64) -> u64 {
        b
    }
}

#[trust_vc::ensures(true)]
fn p5_ctrl(x: A) {
    trust_vc::assert!(x.g(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn p5_liar(x: A) {
    trust_vc::assert!(x.g(1u64, 2u64) == 1u64);
}
"#;

#[test]
fn p5_aligned_impl_params_are_unchanged() {
    run_pins(
        "p5",
        P5_ALIGNED,
        &[
            Pin {
                label: "p5_ctrl x.g(1,2)==2",
                target: Target::Function("p5_ctrl"),
                expect: Expect::Verified,
                before: "Verified",
            },
            Pin {
                label: "p5_liar x.g(1,2)==1",
                target: Target::Function("p5_liar"),
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                label: "conformance TA::g for A",
                target: Target::Conformance("trait impl conformance TA::g for A"),
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P8 — a three-parameter rotation.
// ---------------------------------------------------------------------------

const P8_ROTATION: &str = r#"
struct R3;

#[trust_vc::trait_spec]
trait T3 {
    fn r(&self, a: u64, b: u64, c: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T3 for R3 {
    #[trust_vc::ensures(result == a)]
    fn r(&self, c: u64, a: u64, b: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn p8_liar_a(x: R3) {
    trust_vc::assert!(x.r(1u64, 2u64, 3u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn p8_neg(x: R3) {
    trust_vc::assert!(x.r(1u64, 2u64, 3u64) != 1u64);
}

#[trust_vc::ensures(true)]
fn p8_ctrl(x: R3) {
    trust_vc::assert!(x.r(1u64, 2u64, 3u64) == 2u64);
}
"#;

#[test]
fn p8_rotated_impl_params_bind_by_position() {
    run_pins(
        "p8",
        P8_ROTATION,
        &[
            Pin {
                label: "p8_liar_a x.r(1,2,3)==1",
                target: Target::Function("p8_liar_a"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "p8_neg x.r(1,2,3)!=1 (the liar, refuted by proof)",
                target: Target::Function("p8_neg"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "p8_ctrl x.r(1,2,3)==2",
                target: Target::Function("p8_ctrl"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "conformance T3::r for R3",
                target: Target::Conformance("trait impl conformance T3::r for R3"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P9 — a TRAIT `ensures` (trait names) and an IMPL `ensures` (impl names) on one
// permuted method, checked in one conformance obligation.
// ---------------------------------------------------------------------------

const P9_BOTH_ENSURES: &str = r#"
struct M;

#[trust_vc::trait_spec]
trait TM {
    #[trust_vc::ensures(result >= b)]
    fn m(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TM for M {
    #[trust_vc::ensures(result == a)]
    fn m(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn p9_liar(x: M) {
    trust_vc::assert!(x.m(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn p9_neg(x: M) {
    trust_vc::assert!(x.m(1u64, 2u64) != 1u64);
}

#[trust_vc::ensures(true)]
fn p9_ctrl(x: M) {
    trust_vc::assert!(x.m(1u64, 2u64) == 2u64);
}
"#;

#[test]
fn p9_trait_and_impl_ensures_on_one_permuted_method() {
    run_pins(
        "p9",
        P9_BOTH_ENSURES,
        &[
            Pin {
                label: "p9_liar x.m(1,2)==1",
                target: Target::Function("p9_liar"),
                expect: Expect::NotVerified,
                before: "Unknown (vacuity: the two scopes' clauses contradicted)",
            },
            Pin {
                label: "p9_neg x.m(1,2)!=1 (the liar, refuted by proof)",
                target: Target::Function("p9_neg"),
                expect: Expect::Verified,
                before: "Unknown (vacuity: the two scopes' clauses contradicted)",
            },
            Pin {
                label: "p9_ctrl x.m(1,2)==2",
                target: Target::Function("p9_ctrl"),
                expect: Expect::Verified,
                before: "Unknown (vacuity: the two scopes' clauses contradicted)",
            },
            Pin {
                label: "conformance TM::m for M",
                target: Target::Conformance("trait impl conformance TM::m for M"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// Trait-scope anchors: a TRAIT `ensures` over a permuted impl was already read
// correctly (trait names, positional UF slots). These must not move.
// ---------------------------------------------------------------------------

const TRAIT_SCOPE_ANCHORS: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait T2 {
    #[trust_vc::ensures(result == b)]
    fn g(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T2 for S {
    fn g(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn anchor_ctrl(s: S) {
    trust_vc::assert!(s.g(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn anchor_liar(s: S) {
    trust_vc::assert!(s.g(1u64, 2u64) == 1u64);
}
"#;

const TRAIT_SCOPE_NONCONFORMING: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait T3 {
    #[trust_vc::ensures(result == b)]
    fn h(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T3 for S {
    fn h(&self, b: u64, a: u64) -> u64 {
        b
    }
}
"#;

#[test]
fn trait_scope_ensures_over_a_permuted_impl_is_unchanged() {
    run_pins(
        "anchor",
        TRAIT_SCOPE_ANCHORS,
        &[
            Pin {
                label: "anchor_ctrl s.g(1,2)==2",
                target: Target::Function("anchor_ctrl"),
                expect: Expect::Verified,
                before: "Verified",
            },
            Pin {
                label: "anchor_liar s.g(1,2)==1",
                target: Target::Function("anchor_liar"),
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                label: "conformance T2::g for S (conforming)",
                target: Target::Conformance("trait impl conformance T2::g for S"),
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
    run_pins(
        "anchor_nc",
        TRAIT_SCOPE_NONCONFORMING,
        &[Pin {
            label: "conformance T3::h for S (non-conforming)",
            target: Target::Conformance("trait impl conformance T3::h for S"),
            expect: Expect::Refuted,
            before: "Counterexample",
        }],
    );
}

// ---------------------------------------------------------------------------
// H5 file-level — the confirmed CLI repro: an EXTERNAL impl whose correct own
// `ensures` was published to callers in the trait's scope with nothing checking
// it.
// ---------------------------------------------------------------------------

const H5_EXTERNAL_IMPL: &str = r#"
struct E;

#[trust_vc::trait_spec]
trait Tx {
    fn g(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
#[trust_vc::external]
impl Tx for E {
    #[trust_vc::ensures(result == a)]
    fn g(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn h5i_external_impl_call_eq1(e: E) {
    trust_vc::assert!(e.g(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn h5i_external_impl_call_eq2(e: E) {
    trust_vc::assert!(e.g(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(result == 1u64)]
fn h5i_external_impl_return(e: E) -> u64 {
    e.g(1u64, 2u64)
}
"#;

#[test]
fn h5_external_impl_publishes_no_impl_ensures_to_callers() {
    assert!(
        conformance_names("h5_list", H5_EXTERNAL_IMPL).is_empty(),
        "the `#[trust_vc::external]` hatch itself is unchanged: an external impl owes \
         no conformance obligation"
    );
    run_pins(
        "h5",
        H5_EXTERNAL_IMPL,
        &[
            Pin {
                label: "h5i_external_impl_return ensures(result==1) (runtime: panics)",
                target: Target::Function("h5i_external_impl_return"),
                expect: Expect::Refuted,
                before: "Verified",
            },
            // The UF is unconstrained now; the engine declines to report a
            // counterexample off an under-constrained empty model and says
            // `Unknown { EmptyModel }` instead. The return form above refutes.
            Pin {
                label: "h5i_external_impl_call_eq1 e.g(1,2)==1 (runtime: panics)",
                target: Target::Function("h5i_external_impl_call_eq1"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            // SCOPE: true in Rust, but an external impl's `ensures` is invisible
            // to callers (Verus parity) — nothing checked it against the body.
            Pin {
                label: "h5i_external_impl_call_eq2 e.g(1,2)==2 (scope: unpublished)",
                target: Target::Function("h5i_external_impl_call_eq2"),
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                label: "direct g (impl names)",
                target: Target::Function("g"),
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P6 — the external gate in isolation: aligned names (so the positional rename
// alone cannot close it), and an impl `ensures` FALSE of its body.
// ---------------------------------------------------------------------------

const P6_EXTERNAL_ALIGNED_FALSE: &str = r#"
struct E;

#[trust_vc::trait_spec]
trait TE {
    fn g(&self) -> u64;
}

#[trust_vc::trait_impl]
#[trust_vc::external]
impl TE for E {
    #[trust_vc::ensures(result == 1u64)]
    fn g(&self) -> u64 {
        2u64
    }
}

#[trust_vc::ensures(true)]
fn p6_liar(e: E) {
    trust_vc::assert!(e.g() == 1u64);
}

#[trust_vc::ensures(result == 1u64)]
fn p6_liar_return(e: E) -> u64 {
    e.g()
}
"#;

#[test]
fn p6_external_impl_ensures_is_not_an_unchecked_axiom() {
    assert!(
        conformance_names("p6_list", P6_EXTERNAL_ALIGNED_FALSE).is_empty(),
        "the external hatch itself is unchanged"
    );
    run_pins(
        "p6",
        P6_EXTERNAL_ALIGNED_FALSE,
        &[
            Pin {
                label: "p6_liar_return ensures(result==1) (body returns 2)",
                target: Target::Function("p6_liar_return"),
                expect: Expect::Refuted,
                before: "Verified",
            },
            Pin {
                label: "p6_liar e.g()==1 (body returns 2)",
                target: Target::Function("p6_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "direct g (its false ensures)",
                target: Target::Function("g"),
                expect: Expect::Refuted,
                before: "Counterexample",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P7 — the decline path: a binder in the impl `ensures` shadows an impl
// parameter name, so no exact positional rewrite exists and registration
// declines the whole method (nothing published, nothing asserted).
// ---------------------------------------------------------------------------

const P7_BINDER_SHADOW: &str = r#"
struct B;

#[trust_vc::trait_spec]
trait TB {
    fn h(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TB for B {
    #[trust_vc::ensures(result == a && forall(|a: u64| a == a))]
    fn h(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn p7_liar(x: B) {
    trust_vc::assert!(x.h(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(result == 1u64)]
fn p7_liar_return(x: B) -> u64 {
    x.h(1u64, 2u64)
}
"#;

#[test]
fn p7_binder_shadowing_an_impl_param_declines_propagation() {
    run_pins(
        "p7",
        P7_BINDER_SHADOW,
        &[
            Pin {
                label: "p7_liar_return ensures(result==1) (Rust: 2)",
                target: Target::Function("p7_liar_return"),
                expect: Expect::Refuted,
                before: "Verified",
            },
            Pin {
                label: "p7_liar x.h(1,2)==1",
                target: Target::Function("p7_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "direct h (impl names)",
                target: Target::Function("h"),
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P10 — an impl parameter named `result` collides with the postcondition's
// return-value binder, so there is no exact reading to publish: decline.
// ---------------------------------------------------------------------------

const P10_PARAM_NAMED_RESULT: &str = r#"
struct Rn;

#[trust_vc::trait_spec]
trait TR {
    fn k(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TR for Rn {
    #[trust_vc::ensures(result == 1u64)]
    fn k(&self, result: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn p10_liar(x: Rn) {
    trust_vc::assert!(x.k(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(result == 1u64)]
fn p10_liar_return(x: Rn) -> u64 {
    x.k(1u64, 2u64)
}
"#;

#[test]
fn p10_impl_param_named_result_declines_propagation() {
    run_pins(
        "p10",
        P10_PARAM_NAMED_RESULT,
        &[
            Pin {
                label: "p10_liar_return ensures(result==1) (Rust: 2)",
                target: Target::Function("p10_liar_return"),
                expect: Expect::Refuted,
                before: "Verified",
            },
            Pin {
                label: "p10_liar x.k(1,2)==1 (Rust: 2)",
                target: Target::Function("p10_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// P11 — a binder in the impl `ensures` named after a TRAIT parameter (not an
// impl one). The impl clause and the trait's names never share a map, so the
// binder is not captured: the clause is exact, published, and checked.
// ---------------------------------------------------------------------------

const P11_BINDER_NAMED_AFTER_TRAIT_PARAM: &str = r#"
struct Bt;

#[trust_vc::trait_spec]
trait TT {
    fn t(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TT for Bt {
    #[trust_vc::ensures(result == y && forall(|a: u64| a == a))]
    fn t(&self, x: u64, y: u64) -> u64 {
        y
    }
}

#[trust_vc::ensures(true)]
fn p11_liar(v: Bt) {
    trust_vc::assert!(v.t(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn p11_neg(v: Bt) {
    trust_vc::assert!(v.t(1u64, 2u64) != 1u64);
}

#[trust_vc::ensures(true)]
fn p11_ctrl(v: Bt) {
    trust_vc::assert!(v.t(1u64, 2u64) == 2u64);
}
"#;

#[test]
fn p11_binder_named_after_a_trait_param_is_not_captured() {
    run_pins(
        "p11",
        P11_BINDER_NAMED_AFTER_TRAIT_PARAM,
        &[
            Pin {
                label: "p11_liar v.t(1,2)==1",
                target: Target::Function("p11_liar"),
                expect: Expect::NotVerified,
                before: "Unknown (EmptyModel: axiom never lowered)",
            },
            Pin {
                label: "p11_neg v.t(1,2)!=1 (the liar, refuted by proof)",
                target: Target::Function("p11_neg"),
                expect: Expect::Verified,
                before: "Unknown (EmptyModel: axiom never lowered)",
            },
            Pin {
                label: "p11_ctrl v.t(1,2)==2",
                target: Target::Function("p11_ctrl"),
                expect: Expect::Verified,
                before: "Unknown (EmptyModel: axiom never lowered)",
            },
            Pin {
                label: "conformance TT::t for Bt",
                target: Target::Conformance("trait impl conformance TT::t for Bt"),
                expect: Expect::Verified,
                before: "Error (unresolved variable `y` under the trait-name map)",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// Method-level trust (`#[trust_vc::external_body]` on the impl method, impl
// NOT external): the impl is still conformance-examined, so the permuted
// `ensures` must bind by position there and at the call site.
// ---------------------------------------------------------------------------

const EXTERNAL_BODY_METHOD: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Tb {
    fn f(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl Tb for S {
    #[trust_vc::external_body]
    #[trust_vc::ensures(result == a)]
    fn f(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn extbody_liar(s: S) {
    trust_vc::assert!(s.f(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn extbody_neg(s: S) {
    trust_vc::assert!(s.f(1u64, 2u64) != 1u64);
}

#[trust_vc::ensures(true)]
fn extbody_ctrl(s: S) {
    trust_vc::assert!(s.f(1u64, 2u64) == 2u64);
}
"#;

#[test]
fn external_body_impl_method_with_permuted_params_is_not_misread() {
    run_pins(
        "extbody",
        EXTERNAL_BODY_METHOD,
        &[
            Pin {
                label: "extbody_liar s.f(1,2)==1 (Rust: 2)",
                target: Target::Function("extbody_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "extbody_neg s.f(1,2)!=1 (the liar, refuted by proof)",
                target: Target::Function("extbody_neg"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "extbody_ctrl s.f(1,2)==2",
                target: Target::Function("extbody_ctrl"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "conformance Tb::f for S",
                target: Target::Conformance("trait impl conformance Tb::f for S"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
        ],
    );
}

// ---------------------------------------------------------------------------
// Review round 2 — the positional binding must hold beside the shapes an
// adversarial reader reaches for first: a clause identifier that does NOT
// resolve to an impl parameter while the CALLER has a local of that very name,
// two impls of one trait that permute differently, a `mut` binding, and a
// three-parameter rotation whose trait `requires` sits on a rotated slot.
// ---------------------------------------------------------------------------

/// The impl parameter is spelled `r#a` and the clause `a`. The rewrite keys on
/// the parameter's spelling, so `a` is not renamed and survives as a free
/// identifier; the positional env holds only `self`, `result` and the
/// placeholders, so the clause cannot lower and NOTHING is published. The
/// callers each hold a local named `a` — the free identifier must not bind it.
/// (The rewrite not unraw-ing `r#a` is an imprecision, not a hole: the direct
/// check and conformance fail closed with `unresolved variable \`a\``.)
const R2_RAW_IDENT_BESIDE_CALLER_LOCALS: &str = r#"
struct R;

#[trust_vc::trait_spec]
trait TR {
    fn f(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TR for R {
    #[trust_vc::ensures(result == a)]
    fn f(&self, b: u64, r#a: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn r2_raw_liar_param_local(r: R, a: u64) {
    trust_vc::assert!(r.f(a, 2u64) == a);
}

#[trust_vc::requires(a == 7u64)]
#[trust_vc::ensures(true)]
fn r2_raw_liar_required_local(r: R, a: u64) {
    trust_vc::assert!(r.f(1u64, 2u64) == a);
}

#[trust_vc::ensures(result == a)]
fn r2_raw_liar_return(r: R, a: u64) -> u64 {
    r.f(a, 3u64)
}
"#;

#[test]
fn r2_unresolved_clause_identifier_never_binds_a_same_named_caller_local() {
    run_pins(
        "r2_raw",
        R2_RAW_IDENT_BESIDE_CALLER_LOCALS,
        &[
            Pin {
                label: "r2_raw_liar_param_local r.f(a,2)==a (Rust: 2)",
                target: Target::Function("r2_raw_liar_param_local"),
                expect: Expect::Refuted,
                before: "Verified (the free `a` read as the TRAIT's first parameter)",
            },
            Pin {
                label: "r2_raw_liar_required_local r.f(1,2)==a at a==7",
                target: Target::Function("r2_raw_liar_required_local"),
                expect: Expect::Refuted,
                before: "NotProved",
            },
            Pin {
                label: "r2_raw_liar_return ensures(result==a) of r.f(a,3) (Rust: 3)",
                target: Target::Function("r2_raw_liar_return"),
                expect: Expect::Refuted,
                before: "Verified",
            },
        ],
    );
}

/// `impl T for S1` swaps, `impl T for S2` does not; both write `result == a`.
/// Each impl's clause binds through ITS OWN positions (the boxed-self guard
/// keeps the two axioms apart), and a generic-bound caller gets neither.
const R2_TWO_IMPLS_TWO_PERMUTATIONS: &str = r#"
struct S1;
struct S2;

#[trust_vc::trait_spec]
trait T {
    fn f(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl T for S1 {
    #[trust_vc::ensures(result == a)]
    fn f(&self, b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::trait_impl]
impl T for S2 {
    #[trust_vc::ensures(result == a)]
    fn f(&self, a: u64, b: u64) -> u64 {
        a
    }
}

#[trust_vc::ensures(true)]
fn r2_s1_liar(s: S1) {
    trust_vc::assert!(s.f(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn r2_s1_ctrl(s: S1) {
    trust_vc::assert!(s.f(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn r2_s2_liar(s: S2) {
    trust_vc::assert!(s.f(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn r2_s2_ctrl(s: S2) {
    trust_vc::assert!(s.f(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn r2_mixed_liar(s1: S1, s2: S2) {
    trust_vc::assert!(s1.f(1u64, 2u64) == s2.f(1u64, 2u64));
}

#[trust_vc::ensures(true)]
fn r2_mixed_neg(s1: S1, s2: S2) {
    trust_vc::assert!(s1.f(1u64, 2u64) != s2.f(1u64, 2u64));
}

#[trust_vc::ensures(true)]
fn r2_generic_liar<X: T>(x: X) {
    trust_vc::assert!(x.f(1u64, 2u64) == 2u64);
}
"#;

#[test]
fn r2_two_impls_with_different_permutations_bind_independently() {
    run_pins(
        "r2_two",
        R2_TWO_IMPLS_TWO_PERMUTATIONS,
        &[
            Pin {
                label: "r2_s1_liar s1.f(1,2)==1 (swapped impl)",
                target: Target::Function("r2_s1_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "r2_s1_ctrl s1.f(1,2)==2",
                target: Target::Function("r2_s1_ctrl"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "r2_s2_liar s2.f(1,2)==2 (aligned impl)",
                target: Target::Function("r2_s2_liar"),
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                label: "r2_s2_ctrl s2.f(1,2)==1",
                target: Target::Function("r2_s2_ctrl"),
                expect: Expect::Verified,
                before: "Verified",
            },
            Pin {
                label: "r2_mixed_liar s1.f(1,2)==s2.f(1,2) (Rust: 2 vs 1)",
                target: Target::Function("r2_mixed_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "r2_mixed_neg s1.f(1,2)!=s2.f(1,2) (the liar, refuted by proof)",
                target: Target::Function("r2_mixed_neg"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "r2_generic_liar x.f(1,2)==2 for any X: T",
                target: Target::Function("r2_generic_liar"),
                expect: Expect::NotVerified,
                before: "NotProved",
            },
            Pin {
                label: "conformance T::f for S1",
                target: Target::Conformance("trait impl conformance T::f for S1"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
            Pin {
                label: "conformance T::f for S2",
                target: Target::Conformance("trait impl conformance T::f for S2"),
                expect: Expect::Verified,
                before: "Verified",
            },
        ],
    );
}

/// A `mut` parameter binding is still a plain ident pattern (same numbering),
/// and on a DATATYPE self a three-parameter rotation keeps the trait `requires`
/// on the TRAIT's third slot while the impl clause (with a `self` field) reads
/// the impl's third slot.
const R2_MUT_AND_ROTATED_REQUIRES: &str = r#"
struct M;
struct K { v: u64 }

#[trust_vc::trait_spec]
trait TM {
    fn f(&self, a: u64, b: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TM for M {
    #[trust_vc::ensures(result == a)]
    fn f(&self, mut b: u64, a: u64) -> u64 {
        a
    }
}

#[trust_vc::trait_spec]
trait TK {
    #[trust_vc::requires(c < 10u64)]
    fn k(&self, a: u64, b: u64, c: u64) -> u64;
}

#[trust_vc::trait_impl]
impl TK for K {
    #[trust_vc::ensures(result == b && self.v == self.v)]
    fn k(&self, c: u64, a: u64, b: u64) -> u64 {
        b
    }
}

#[trust_vc::ensures(true)]
fn r2_mut_liar(m: M) {
    trust_vc::assert!(m.f(1u64, 2u64) == 1u64);
}

#[trust_vc::ensures(true)]
fn r2_mut_ctrl(m: M) {
    trust_vc::assert!(m.f(1u64, 2u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn r2_rot_liar(x: K) {
    trust_vc::assert!(x.k(1u64, 2u64, 3u64) == 2u64);
}

#[trust_vc::ensures(true)]
fn r2_rot_neg(x: K) {
    trust_vc::assert!(x.k(1u64, 2u64, 3u64) != 2u64);
}

#[trust_vc::ensures(true)]
fn r2_rot_ctrl(x: K) {
    trust_vc::assert!(x.k(1u64, 2u64, 3u64) == 3u64);
}
"#;

#[test]
fn r2_mut_binding_and_rotated_trait_requires_bind_by_position() {
    run_pins(
        "r2_mut_rot",
        R2_MUT_AND_ROTATED_REQUIRES,
        &[
            Pin {
                label: "r2_mut_liar m.f(1,2)==1",
                target: Target::Function("r2_mut_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "r2_mut_ctrl m.f(1,2)==2",
                target: Target::Function("r2_mut_ctrl"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "r2_rot_liar x.k(1,2,3)==2",
                target: Target::Function("r2_rot_liar"),
                expect: Expect::NotVerified,
                before: "Verified",
            },
            Pin {
                label: "r2_rot_neg x.k(1,2,3)!=2 (the liar, refuted by proof)",
                target: Target::Function("r2_rot_neg"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "r2_rot_ctrl x.k(1,2,3)==3",
                target: Target::Function("r2_rot_ctrl"),
                expect: Expect::Verified,
                before: "NotProved",
            },
            Pin {
                label: "conformance TM::f for M",
                target: Target::Conformance("trait impl conformance TM::f for M"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
            Pin {
                label: "conformance TK::k for K",
                target: Target::Conformance("trait impl conformance TK::k for K"),
                expect: Expect::Verified,
                before: "Counterexample",
            },
        ],
    );
}
