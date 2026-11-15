// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! H13 — a Rust `union` is not modelled, and a WRITE through one was silently
//! DROPPED instead of refused.
//!
//! `Item::Union` is indexed (`vc_extraction.rs`, the source-type walk records the
//! bare ident so collision resolution can see it) and never lowered. Nothing
//! tracked the active field, so:
//!
//!     union X { a: u32, b: (u8, bool) }
//!     #[trust_vc::ensures(true)]
//!     fn f() { let mut x = X { a: 0 }; x.b.1 = true; }
//!
//! raised NO obligation and NO refusal for the write, and the function came back
//! `Verified` on its (trivially true) `#[ensures]` with the state change simply
//! gone. Ground truth with `trustc -Ztrust-verify=off`: `x.a == 256` afterwards on
//! the natural little-endian layout. Verus REJECTS the write.
//!
//! The 2026-09-14 probe measured that this is NOT a live false verify — every
//! claim that READS union state already fails closed (struct literal for an
//! unknown type, field on type, deref-write refusals, unresolved variable). The
//! defect is the SILENCE: a function can carry an unmodelled state change and
//! still report a verdict, and the next claim that learns to read union state
//! turns that silence into a false Verified.
//!
//! ## The rule these pins hold
//!
//! Where a `union` is declared, a target that names it is REFUSED at extraction
//! — construction, a union-typed binding, parameter or return, a pattern, a
//! builtin over it, and any write whose place root reaches it. A refusal is the
//! correct outcome here; a modelled union is a separate, much larger piece of
//! work.
//!
//! The refusal is keyed to the union IDENT, so the narrowness pins matter as much
//! as the witnesses: an unrelated function in the same file keeps verifying, and
//! the struct twin of the exact repro still tracks its write (verified) and still
//! refutes the negation of it (counterexample). Without those, "refuse unions"
//! degenerates into "refuse the file".
//!
//! ## SCOPE — what these pins do and do not close
//!
//! The taint closure is built from `file.items` plus the target's own block, so
//! the claim is "closed for unions SYNTACTICALLY PRESENT in the file under
//! verification". A union declared in another module FILE yields an empty taint
//! set and its write is still dropped in silence. That was measured identically
//! at the merge base and here, so it is not a regression introduced by the fix —
//! it is single-file extraction, which is broader than unions and older than this
//! work — but nothing may describe H13 as closed without it.
//!
//! `U5` pins the other half of the bill: the conformance lane's refusal is
//! FILE-WIDE, so one union-touching function costs every conformance obligation
//! in the file.

use std::sync::atomic::{AtomicUsize, Ordering};

use trust_vc_core::VerifyResult;

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn verdict(fixture: &str, src: &str, func: &str) -> VerifyResult {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::SeqCst);
    let path = format!(
        "{}/union_write_fail_closed_{}_{fixture}_{seq}.rs",
        env!("CARGO_TARGET_TMPDIR"),
        std::process::id()
    );
    std::fs::write(&path, src).expect("write fixture");
    let result = trust_vc_core::verify_function_from_file(&path, func).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: format!("{err}"),
        }
    });
    let _ = std::fs::remove_file(&path);
    result
}

/// A refusal, and specifically THIS refusal: the message must name the union and
/// say why nothing may be concluded, so an `Error` raised for some unrelated
/// reason cannot pass for the closed hole.
fn assert_union_refusal(fixture: &str, src: &str, func: &str, why: &str) {
    let v = verdict(fixture, src, func);
    let VerifyResult::Error { message } = &v else {
        panic!("SILENT ACCEPTANCE ({fixture}::{func}): {why}. Expected a fail-closed union refusal, got {v:?}");
    };
    assert!(
        message.contains("does not model Rust unions"),
        "({fixture}::{func}) refused, but not as a union boundary — the message must say what \
         was refused and why. Got: {message}"
    );
}

fn assert_verified(fixture: &str, src: &str, func: &str, why: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "CAPABILITY LOST ({fixture}::{func}): {why}. Got {v:?}"
    );
}

fn assert_refuted(fixture: &str, src: &str, func: &str, why: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "({fixture}::{func}): {why}. Expected a Counterexample, got {v:?}"
    );
}

// ===========================================================================
// U1 — the measured repro, its struct twin, and the untouched sibling.
// ===========================================================================

const U1: &str = r#"
union X {
    a: u32,
    b: (u8, bool),
}

struct SB {
    p: u8,
    q: bool,
}

struct SX {
    a: u32,
    b: SB,
}

#[trust_vc::ensures(true)]
fn u1_union_write_is_dropped() {
    let mut x = X { a: 0u32 };
    x.b.1 = true;
}

#[trust_vc::ensures(true)]
fn u1_union_construction() {
    let _x = X { a: 0u32 };
}

#[trust_vc::ensures(true)]
fn u1_union_parameter(x: X) {
    let _ = x;
}

#[trust_vc::ensures(true)]
fn u1_union_return() -> X {
    X { a: 0u32 }
}

#[trust_vc::ensures(true)]
fn u1_struct_write_is_tracked() {
    let mut s = SX { a: 0u32, b: SB { p: 0u8, q: false } };
    s.b.q = true;
    trust_vc::assert!(s.b.q);
}

#[trust_vc::ensures(true)]
fn u1_struct_write_liar() {
    let mut s = SX { a: 0u32, b: SB { p: 0u8, q: false } };
    s.b.q = true;
    trust_vc::assert!(!s.b.q);
}

#[trust_vc::ensures(result)]
fn u1_untouched_sibling() -> bool {
    1u8 + 1u8 == 2u8
}

#[trust_vc::ensures(result)]
fn u1_untouched_sibling_liar() -> bool {
    1u8 + 1u8 == 3u8
}
"#;

/// THE REPRODUCER. Before the fix this was `Verified` with the write gone.
#[test]
fn u1_union_field_write_is_refused_not_dropped() {
    assert_union_refusal(
        "u1",
        U1,
        "u1_union_write_is_dropped",
        "`x.b.1 = true` reinterprets the bytes of `x.a` (really 256 afterwards), and nothing \
         here models that; dropping the write leaves an unmodelled state change behind an \
         apparently discharged obligation",
    );
}

#[test]
fn u1_union_construction_is_refused() {
    assert_union_refusal(
        "u1",
        U1,
        "u1_union_construction",
        "a union value has an ACTIVE FIELD that nothing here represents, so the binding is \
         not modellable even before anything is written through it",
    );
}

#[test]
fn u1_union_parameter_is_refused() {
    assert_union_refusal(
        "u1",
        U1,
        "u1_union_parameter",
        "a union-typed parameter arrives with an active field this engine cannot express",
    );
}

#[test]
fn u1_union_return_is_refused() {
    assert_union_refusal("u1", U1, "u1_union_return", "a union-typed return likewise");
}

/// NARROWNESS. The struct twin of the exact repro: same fields, same write, and
/// the write must still be TRACKED.
#[test]
fn u1_struct_twin_still_tracks_the_write() {
    assert_verified(
        "u1",
        U1,
        "u1_struct_write_is_tracked",
        "`SX` is an ordinary struct with the same nested-field shape (a NAMED inner field, \
         because a tuple-index place in an obligation is a separate pre-existing parse \
         limitation: the same body over `b: (u8, bool)` errors with `expected ,` in a file \
         that declares no union at all); refusing unions must not cost the nested-field \
         write lane",
    );
}

/// The REFUTED liar for the pin above: the same write, the opposite claim. Its
/// counterexample is what proves the verified twin is not vacuous.
#[test]
fn u1_struct_twin_refutes_the_negation() {
    assert_refuted(
        "u1",
        U1,
        "u1_struct_write_liar",
        "`s.b.1` is `true` after the write, so asserting `!s.b.1` must be refuted — this is \
         what shows the verified twin actually observed the write",
    );
}

/// NARROWNESS. Declaring a union in the file must not refuse every function in
/// it; the refusal is keyed to the target that names the union.
#[test]
fn u1_unrelated_sibling_still_verifies() {
    assert_verified(
        "u1",
        U1,
        "u1_untouched_sibling",
        "this function never mentions `X`; a union declared elsewhere in the file is none of \
         its business",
    );
}

/// The REFUTED liar for the pin above — every other verified pin in this suite
/// carries one. Without it, "still verifies" could be a refusal channel that has
/// stopped reading the body at all.
#[test]
fn u1_unrelated_sibling_liar_is_refuted() {
    assert_refuted(
        "u1",
        U1,
        "u1_untouched_sibling_liar",
        "`1 + 1` is 2, so claiming 3 must be refuted in the same union-declaring file",
    );
}

// ===========================================================================
// U2 — the write reaches the union through a deeper place, and through a
// qualified path. Same refusal.
// ===========================================================================

const U2: &str = r#"
pub mod m {
    pub union U {
        pub a: u32,
        pub b: (u8, bool),
    }
}

struct Holder {
    n: u32,
}

#[trust_vc::ensures(true)]
fn u2_qualified_union_path() {
    let mut u = m::U { a: 0u32 };
    u.b.1 = true;
}

#[trust_vc::ensures(true)]
fn u2_union_pattern(u: m::U) {
    let m::U { a } = u;
    let _ = a;
}

#[trust_vc::ensures(result)]
fn u2_unrelated_struct_verifies() -> bool {
    let h = Holder { n: 7u32 };
    h.n == 7u32
}

#[trust_vc::ensures(result)]
fn u2_unrelated_struct_liar() -> bool {
    let h = Holder { n: 7u32 };
    h.n == 8u32
}
"#;

#[test]
fn u2_qualified_union_path_is_refused() {
    assert_union_refusal(
        "u2",
        U2,
        "u2_qualified_union_path",
        "the union is declared in an inline module and reached as `m::U`",
    );
}

#[test]
fn u2_union_pattern_is_refused() {
    assert_union_refusal(
        "u2",
        U2,
        "u2_union_pattern",
        "destructuring a union picks an active field by fiat",
    );
}

#[test]
fn u2_unrelated_struct_still_verifies() {
    assert_verified(
        "u2",
        U2,
        "u2_unrelated_struct_verifies",
        "an ordinary struct in a file that declares a union keeps working",
    );
}

/// The REFUTED liar for the pin above, in the same union-declaring file: the
/// struct lane is really reading the field, not answering vacuously.
#[test]
fn u2_unrelated_struct_liar_is_refuted() {
    assert_refuted(
        "u2",
        U2,
        "u2_unrelated_struct_liar",
        "`h.n` is 7, so claiming 8 must be refuted",
    );
}

// ===========================================================================
// U3 — the IDENT key is not a spelling of "the union". A `type` alias, a
// wrapper struct and a union-producing function each reach the same storage
// without ever writing the union's own name in the target.
//
// Round-1 review measured all three as `Verified` with the overlapping write
// simply GONE — the exact defect U1 pins, one alias away. The refusal is
// therefore keyed to a TAINT CLOSURE over the file's declarations, not to the
// union ident alone.
// ===========================================================================

const U3: &str = r#"
union X {
    a: u32,
    b: (u8, bool),
}

type Al = X;
type Al2 = Al;

struct W {
    u: X,
    n: u32,
}

struct T(X, u32);

struct V {
    w: W,
}

struct Clean {
    n: u32,
}

fn mk() -> X {
    X { a: 0u32 }
}

#[trust_vc::ensures(result == 5u32)]
fn u3_alias_construction_write() -> u32 {
    let mut z = Al { a: 0u32 };
    z.b.1 = true;
    5u32
}

#[trust_vc::ensures(result == 5u32)]
fn u3_alias_of_alias_construction_write() -> u32 {
    let mut z = Al2 { a: 0u32 };
    z.b.1 = true;
    5u32
}

#[trust_vc::ensures(true)]
fn u3_alias_parameter(z: Al) {
    let _ = z;
}

#[trust_vc::ensures(result == 5u32)]
fn u3_named_wrapper_write(w: W) -> u32 {
    let mut q = w;
    q.u.b.1 = true;
    5u32
}

#[trust_vc::ensures(result == 5u32)]
fn u3_tuple_wrapper_write(t: T) -> u32 {
    let mut q = t;
    q.0.b.1 = true;
    5u32
}

#[trust_vc::ensures(result == 5u32)]
fn u3_transitive_wrapper_write(v: V) -> u32 {
    let mut q = v;
    q.w.u.b.1 = true;
    5u32
}

#[trust_vc::ensures(result == 5u32)]
fn u3_union_producing_call_write() -> u32 {
    let mut z = mk();
    z.b.1 = true;
    5u32
}

#[trust_vc::ensures(result == 5u32)]
fn u3_clean_sibling_verifies() -> u32 {
    let mut q = Clean { n: 0u32 };
    q.n = 5u32;
    q.n
}

#[trust_vc::ensures(result == 6u32)]
fn u3_clean_sibling_liar() -> u32 {
    let mut q = Clean { n: 0u32 };
    q.n = 5u32;
    q.n
}
"#;

/// BLOCKER from review round 1: a one-line `type Al = X;` defeated the ident key
/// and the overlapping write came back `Verified` with the write gone.
#[test]
fn u3_alias_to_a_union_is_refused() {
    assert_union_refusal(
        "u3",
        U3,
        "u3_alias_construction_write",
        "`type Al = X;` renames the union without changing anything about its storage; \
         accepting the alias accepts the dropped write",
    );
}

#[test]
fn u3_alias_of_alias_is_refused() {
    assert_union_refusal(
        "u3",
        U3,
        "u3_alias_of_alias_construction_write",
        "alias chains must be followed to a fixpoint, or one more `type` line reopens the hole",
    );
}

#[test]
fn u3_alias_typed_parameter_is_refused() {
    assert_union_refusal(
        "u3",
        U3,
        "u3_alias_parameter",
        "a union-typed parameter spelled through an alias is still union-typed",
    );
}

/// MAJOR from review round 1: the union reached through a struct field. The
/// target never writes the union's ident at all.
#[test]
fn u3_named_field_wrapper_is_refused() {
    assert_union_refusal(
        "u3",
        U3,
        "u3_named_wrapper_write",
        "`W` has a union-typed field, so `q.u.b.1 = true` writes union storage while the \
         target only ever names `W`",
    );
}

#[test]
fn u3_tuple_struct_wrapper_is_refused() {
    assert_union_refusal(
        "u3",
        U3,
        "u3_tuple_wrapper_write",
        "same through a tuple-struct field",
    );
}

#[test]
fn u3_transitive_wrapper_is_refused() {
    assert_union_refusal(
        "u3",
        U3,
        "u3_transitive_wrapper_write",
        "a wrapper of a wrapper is still union storage; the taint has to be a fixpoint",
    );
}

/// The indirect shape. It failed closed before, but for an unrelated reason
/// (`Failed to lower obligation '__body_axiom_mk_sibling_helper'`), which is a
/// diagnostic that tells the author nothing and could evaporate with any change
/// to helper lowering.
#[test]
fn u3_union_producing_call_is_refused_as_a_union() {
    assert_union_refusal(
        "u3",
        U3,
        "u3_union_producing_call_write",
        "`mk()` returns union storage, so the binding is union-typed even though the target \
         names only `mk`",
    );
}

/// NARROWNESS, and the one that keeps the taint closure from becoming "refuse
/// the file": a struct that does not reach the union still tracks its write.
#[test]
fn u3_clean_struct_still_verifies() {
    assert_verified(
        "u3",
        U3,
        "u3_clean_sibling_verifies",
        "`Clean` reaches no union field; a taint closure that swallowed it would be refusing \
         the file rather than the unions in it",
    );
}

/// The REFUTED liar for the pin above.
#[test]
fn u3_clean_struct_liar_is_refuted() {
    assert_refuted(
        "u3",
        U3,
        "u3_clean_sibling_liar",
        "`q.n` is 5 after the write, so claiming 6 must be refuted — the obligation channel is \
         live, the verified twin is not vacuous",
    );
}

// ===========================================================================
// U4 — the TRAIT-CONFORMANCE lane. It reaches extraction with a SYNTHETIC
// target (`fn __probe() {}`) that names nothing at all, so a refusal keyed to
// the target's own tokens can never fire there.
// ===========================================================================

fn conformance_union_verdict(fixture: &str, src: &str) -> VerifyResult {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::SeqCst);
    let path = format!(
        "{}/union_write_fail_closed_conf_{}_{fixture}_{seq}.rs",
        env!("CARGO_TARGET_TMPDIR"),
        std::process::id()
    );
    std::fs::write(&path, src).expect("write fixture");
    let result = match trust_vc_core::list_trait_conformance_obligations(&path) {
        Ok(names) => {
            // The verdict below starts at `Verified` and is only ever moved by a
            // failing obligation, so a fixture that declares NO obligation would
            // make every narrowness pin built on this helper assert nothing at
            // all. The external_body suite's sibling helper has carried this
            // guard from the start; this one did not, and
            // `u4_conformance_lane_still_verifies_without_a_union` was vacuous
            // because of it.
            assert!(
                !names.is_empty(),
                "fixture declares no conformance obligation at all — the guard would be vacuous"
            );
            let mut verdict = VerifyResult::Verified;
            for name in names {
                match trust_vc_core::verify_trait_conformance_obligation(&path, &name) {
                    Ok(result) if result.is_verified() => {}
                    Ok(result) => {
                        verdict = result;
                        break;
                    }
                    Err(err) => {
                        verdict = VerifyResult::Error {
                            message: format!("{err}"),
                        };
                        break;
                    }
                }
            }
            verdict
        }
        Err(err) => VerifyResult::Error {
            message: format!("{err}"),
        },
    };
    let _ = std::fs::remove_file(&path);
    result
}

const U4: &str = r#"
union X {
    a: u32,
    b: (u8, bool),
}

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 5u32)]
    fn d(&self) -> u32 {
        let mut z = X { a: 0u32 };
        z.b.1 = true;
        5u32
    }
}
"#;

/// The NARROWNESS twin of `U4`, re-keyed on review round 2. The shape it used to
/// carry (a plain `trait` plus `impl Tr for S {}`) yields ZERO conformance
/// obligations, and `conformance_union_verdict` starts its verdict at `Verified`
/// and returns it unchanged over an empty list — so the pin asserted nothing. The
/// `#[trust_vc::trait_spec]` + `#[trust_vc::returns(result)]` shape does yield
/// one, and the helper now refuses an empty list outright.
const U4_CLEAN: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 5u32)]
    fn d(&self) -> u32 {
        let mut q = 0u32;
        q = 5u32;
        q
    }
}
"#;

/// The REFUTED liar for `U4_CLEAN`. Same text, one digit changed: the default
/// body returns 4 against an `ensures(result == 5u32)`. A Counterexample here is
/// what shows the verified twin is discharged from the body and is not an
/// obligation channel that has gone quiet — the exact failure mode that made the
/// ROUND-1 shape of this pin vacuous.
const U4_CLEAN_LIAR: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 5u32)]
    fn d(&self) -> u32 {
        let mut q = 0u32;
        q = 4u32;
        q
    }
}
"#;

/// A union DECLARED in the file but reached by nothing: the conformance lane
/// must keep its obligations. This is the narrowness the file-wide refusal
/// actually promises, and the only one it can promise (see `U5`).
const U4_UNTOUCHED_UNION: &str = r#"
union X {
    a: u32,
    b: (u8, bool),
}

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 5u32)]
    fn d(&self) -> u32 {
        let mut q = 0u32;
        q = 5u32;
        q
    }
}
"#;

/// The REFUTED liar for `U4_UNTOUCHED_UNION`: same file, same declared-and-
/// unreached union, the default body returns 4 against `ensures(result == 5u32)`.
const U4_UNTOUCHED_UNION_LIAR: &str = r#"
union X {
    a: u32,
    b: (u8, bool),
}

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 5u32)]
    fn d(&self) -> u32 {
        let mut q = 0u32;
        q = 4u32;
        q
    }
}
"#;

/// THE BLAST RADIUS, measured rather than assumed. The trait default here
/// touches no union; an UNRELATED free function in the same file does. The
/// conformance refusal is file-wide, so this file loses its conformance
/// obligation outright.
const U5_UNRELATED_UNION: &str = r#"
union X {
    a: u32,
    b: (u8, bool),
}

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 5u32)]
    fn d(&self) -> u32 {
        let mut q = 0u32;
        q = 5u32;
        q
    }
}

#[trust_vc::ensures(true)]
fn u5_touches_the_union() {
    let mut x = X { a: 0u32 };
    x.b.1 = true;
}
"#;

#[test]
fn u4_conformance_lane_refuses_a_union_body() {
    let v = conformance_union_verdict("u4", U4);
    let VerifyResult::Error { message } = &v else {
        panic!(
            "SILENT ACCEPTANCE (u4): a trait DEFAULT body constructs a union and writes an \
             overlapping field; the conformance lane drives extraction with a synthetic probe \
             that names nothing, so the target-token refusal cannot fire. Got {v:?}"
        );
    };
    assert!(
        message.contains("does not model Rust unions"),
        "(u4) refused, but not as a union boundary. Got: {message}"
    );
}

/// NARROWNESS for the pin above: the same lane over a union-free file must keep
/// discharging its conformance obligations. Re-keyed on review round 2 — see
/// `U4_CLEAN` for why the previous shape asserted nothing.
#[test]
fn u4_conformance_lane_still_verifies_without_a_union() {
    let v = conformance_union_verdict("u4_clean", U4_CLEAN);
    assert!(
        matches!(v, VerifyResult::Verified),
        "CAPABILITY LOST (u4_clean): the conformance lane must be untouched by the union \
         refusal in a file that declares no union. Got {v:?}"
    );
}

/// NARROWNESS, one step closer in: the union is DECLARED and nothing reaches it.
/// The taint closure is empty of named uses, so the obligation survives.
#[test]
fn u4_declared_but_unreached_union_keeps_its_conformance_obligation() {
    let v = conformance_union_verdict("u4_untouched", U4_UNTOUCHED_UNION);
    assert!(
        matches!(v, VerifyResult::Verified),
        "CAPABILITY LOST (u4_untouched): declaring a union must not by itself refuse a file's \
         conformance obligations — only reaching one does. Got {v:?}"
    );
}

/// The REFUTED liar for `u4_conformance_lane_still_verifies_without_a_union`.
/// Round 3 asked for it: a Verified conformance pin with no Counterexample twin
/// cannot tell "the obligation is discharged" from "the obligation stopped being
/// checked".
#[test]
fn u4_conformance_lane_liar_is_refuted() {
    let v = conformance_union_verdict("u4_clean_liar", U4_CLEAN_LIAR);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "(u4_clean liar) the default body returns 4 against `ensures(result == 5u32)`, so \
         the conformance obligation must be REFUTED. Got {v:?}"
    );
}

/// The REFUTED liar for
/// `u4_declared_but_unreached_union_keeps_its_conformance_obligation`, with the
/// union still declared in the file.
#[test]
fn u4_declared_but_unreached_union_liar_is_refuted() {
    let v = conformance_union_verdict("u4_untouched_liar", U4_UNTOUCHED_UNION_LIAR);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "(u4_untouched liar) a declared-but-unreached union must leave the obligation LIVE, \
         so a body returning 4 against `ensures(result == 5u32)` is still refuted — not \
         quietly dropped. Got {v:?}"
    );
}

// ===========================================================================
// U5 — the COST of the file-wide conformance refusal, pinned honestly.
//
// The conformance lane builds ONE shared context for the whole file from a
// synthetic probe: trait registrations, sibling-helper body axioms, inherent
// method axioms and trait-default bodies all land in it together, and any one of
// them may be the fact an obligation is discharged from. A function that writes
// through a union has that write DROPPED, so a body axiom published from it is
// an outright false premise in that shared context — which is why the refusal is
// keyed to the FILE and not to the obligation.
//
// The bill for that is exact and is charged here: a file whose trait default
// touches no union at all still loses its conformance obligation as soon as any
// other function in the file reaches one. That is over-rejection, and it is
// ACCEPTED rather than narrowed, because the only narrowing available — refusing
// just the obligations whose own default body reaches a union — leaves every
// other obligation discharging against facts derived from a dropped write. If
// per-declaration fact provenance ever lands in this lane, this pin is where to
// revisit it.
// ===========================================================================

#[test]
fn u5_an_unrelated_union_costs_the_whole_files_conformance_obligations() {
    let v = conformance_union_verdict("u5", U5_UNRELATED_UNION);
    let VerifyResult::Error { message } = &v else {
        panic!(
            "(u5) this fixture is the ACCEPTED COST of the file-wide conformance refusal, and \
             the pin exists to keep that cost visible and measured. If it now verifies, the \
             refusal was narrowed — re-derive whether the shared conformance context can \
             still publish a fact from the dropped union write before recording that as a \
             win. Got {v:?}"
        );
    };
    assert!(
        message.contains("does not model Rust unions"),
        "(u5) refused, but not as a union boundary. Got: {message}"
    );
}
