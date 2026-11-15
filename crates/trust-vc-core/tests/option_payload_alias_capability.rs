// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (mut_refs_libs `test_option_insert_and_get_or_insert`,
//! 2026-09-17): the `&mut T` returned by `Option::insert` /
//! `Option::get_or_insert` is an erased alias of the Option's PAYLOAD
//! (`ErasedMutRefTarget::OptionPayload { owner, payload_ty }`).
//!
//! Admission is one straight-line shape, decided by a whole-body syntactic
//! scan (`option_payload_alias_candidates`) plus dynamic checks at the `let`
//! (`option_payload_alias_registration`):
//!
//! * `let r = x.insert(<lit>);` / `let r = x.get_or_insert(<lit>);` as a DIRECT
//!   statement of the function body, `r` a plain immutable identifier, `<lit>`
//!   a suffixed integer or a `bool` of the Option's payload type;
//! * `x` a `let` local of the body whose scoped state at the call is a KNOWN
//!   `Option::<T>::None` or `Some(<suffixed literal>)`, not borrowed or held;
//! * every later use of `r` is a `*r` read under pure operators (in a `let`
//!   initializer, an expression statement or an `assert!` / `assume!`), or a
//!   statement-level `*r = <literal of the payload type>;`, and `x` is not
//!   mentioned at all until `r`'s last use;
//! * the FILE cannot change what `Option` / `Some` / `None` / `insert` /
//!   `get_or_insert` resolve to (no shadowing, no fn named `insert` /
//!   `get_or_insert` anywhere — a by-value trait method of that name was
//!   MEASURED to win resolution over `Option::insert` (f1) — no item macro, no
//!   `mod`, every `use` rooted at std / core / alloc);
//! * every attribute in the FILE is `trust_vc::..`, an inert single-segment
//!   builtin, or a `derive` of builtin traits only, no identifier is raw or
//!   non-ASCII, and every macro path is single-segment or rooted at
//!   `trust_vc` / `std` / `core` / `alloc` with no `#` in its tokens —
//!   `fn r#insert` (f5 / f6), `enum r#Option` (f7), `#[derive(hjd::Hijack)]`
//!   (f8) and `#[hjd::hijack_attr]` (f9) were MEASURED (review 2026-09-17)
//!   to slip past a name-only gate and make the lane verify runtime-false
//!   claims; f11 pins that a builtin-derive file keeps the lane.
//!
//! The model: `insert(v)` (any known state) and `get_or_insert(v)` on `None`
//! bind `r` to `v` and `x` to `Some(v)`; `get_or_insert(v)` on `Some(p)` binds
//! `r` to `p` and leaves `x == Some(p)`; `*r = c;` rebinds `r` to `c` and `x`
//! to `Some(c)`. After `r`'s last use `x` reads exactly and every later
//! operation on it takes the pre-existing machinery.
//!
//! Everything adjacent fails closed through TODAY's path: a refused candidate
//! sets no error of its own (review 2026-09-17: an eager refusal turned
//! runtime-true bodies HEAD verifies into errors — e1-e9 now pin HEAD's
//! Verified verdicts, each with a runtime-false liar). g1-g28, f1-f10 and
//! n1 / n2 pin HEAD's own outcome, each measured byte-identical to a lens
//! built from the untouched tree.
//!
//! Every control has a runtime-false liar; `runtime_twins_execute_std_behavior`
//! executes std twins of every control, liar, gated shape and hijack
//! (the f1 trait, the f5 / f6 raw-identifier traits, the f8 derive expansion)
//! under this test binary's rustc profile (debug: overflow checks on;
//! overflow claims additionally use `checked_add`).
//!
//! NARROWED (review round 2026-09-17, three reachability findings closed —
//! each was MEASURED runtime-false, VERIFIED on the pre-narrowing lane and an
//! Error at HEAD, so the lane introduced it whatever its root cause):
//!
//! * H1a — an `i32` payload is refused WHOLESALE (`OPTION_PAYLOAD_ERR_I32_PAYLOAD`),
//!   the same narrowing the sibling `Option::as_slice` view took: the `let`
//!   annotation is carried only for a BARE primitive-integer binding, so a
//!   genuine `i32` cannot be told apart from a literal defaulted under a
//!   dropped `Option<uN>` annotation (g29 / g30; the old c12 control was
//!   re-keyed and its usize half kept).
//! * H1b — a body holding ANY DEFAULTED numeric literal (an integer with no
//!   primitive-integer suffix, a float with no `f32` / `f64` suffix) takes NO
//!   lane (`OPTION_PAYLOAD_ERR_UNSUFFIXED_LITERAL`): the extractor types such
//!   a literal at the `i32` / `f64` default while Rust infers it from any
//!   later use, and admitting an alias made that PRE-EXISTING hole reachable
//!   in bodies that used to fail closed on the `insert` call (g34-g36,
//!   g37-g46; c21 / l21 / c22 / l22 / c23 / l23 pin that a fully SUFFIXED
//!   body keeps the lane).
//!
//!   WIDENED (review round 3, same day). The first cut keyed on ONE
//!   `syn::Local` — a dropped ascription paired with an unsuffixed literal in
//!   that local's own initializer — and left more than twenty spellings open,
//!   each MEASURED dev-VERIFIED / HEAD-Error with a runtime-false twin: a
//!   later BARE ascription (g37), a free-fn argument (g38), an out-of-range
//!   literal the suffixed-position bound cannot see (g39), a one-hop `Some(k)`
//!   (g40-g42), a DEFERRED-init local (g43), an unsuffixed literal in the
//!   spec assertion alone (g44). Rust integer inference is whole-body, so no
//!   rule anchored on the literal's own `let` can be sound. FLOATS take the
//!   same rule for the same reason and were found by this round's own probing
//!   (g45): `let y = 16777216.0; let _q: f32 = y; y + 1.0 > y` VERIFIED while
//!   the f32 sum rounds back to `y`. g44 also retires the round-2
//!   incompleteness (an Option equality against an unsuffixed literal
//!   returning a Counterexample for a runtime-TRUE claim) — that body now
//!   takes no lane and keeps HEAD's refusal. p1 / p2 pin that the hole itself
//!   is UNCHANGED outside the lane.
//! * H2 — an integer literal that does not FIT the type its own suffix names
//!   is no longer a typed literal, at the single point every arm reads one
//!   (argument, owner payload, write value): `insert(2147483648i32)` was
//!   admitted as an exact payload and `-(*r) == -2147483648i32` VERIFIED while
//!   the program does not compile (g31-g33). `usize` / `isize` take the
//!   32-bit bound because every ported file is dual-width.
//! * H3 — the file gate additionally refuses any `use` leaf that binds a
//!   PRIMITIVE type name and any type-namespace item or generic parameter
//!   that shadows one: `use core::primitive::u8 as u64;` satisfies the
//!   std/core/alloc rooting rule and makes the file's `u64` a `u8` (f12-f14;
//!   f15 pins that the rooting rule itself is unchanged).
//!
//! Each narrowing is a SCAN / FILE-GATE refusal, never an eager error, so a
//! refused shape falls back to HEAD's own verdict byte-for-byte (measured with
//! matched lenses over every probe, 2026-09-17).
//!
//! POINTER WIDTH (closure round 2026-09-17): `option_payload_int_literal_bound`
//! bounds `usize` at `u32::MAX` and `isize` at `i32::MAX`, because every ported
//! file is checked at BOTH widths and a literal that does not fit the narrow
//! one is not a legal Rust literal there. That row had no pin; c24 / l24 pin
//! the boundary value as still modellable and g47 / g48 pin one past it, in the
//! payload and in the write position. Widening either row to 64 bits fails
//! g47 / g48.
//!
//! 143 fixture cases in 117 tests: 25 controls, 24 liars (c1-c24 / l1-l24 plus
//! the re-keyed c30), 9 restored HEAD controls with 9 liars (e1-e9), 47 gated
//! (g1-g48 less the re-keyed g5), 22 file/body-gate pins (f1-f15), 2 non-hijack
//! pins, 1 pre-existing-hole pin (p1; p2 closed and is now a control-shaped
//! refutation pin), 3 helpers; plus the runtime-twins test. Re-counted
//! 2026-09-18 with the width-carry re-key.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// HEAD's lowering refusal for `*r` where `r = x.insert(..)` took today's path.
const LOWER_INSERT: &str =
    "collection operation 'insert' requires a collection receiver, got 'Option<u64>'";
/// HEAD's lowering refusal for `*r` where `r = x.get_or_insert(..)` took today's path.
const LOWER_GET_OR_INSERT: &str = "unsupported method `get_or_insert() on type `Option<u64>`";
const UNRESOLVED_X: &str = "unresolved variable `x`";
const UNRESOLVED_R: &str = "unresolved variable `r`";
/// HEAD's refusal for a statement macro the extractor does not know.
const UNSUPPORTED_MACRO: &str =
    "unsupported macros are rejected to avoid silently dropping proof obligations";

/// The pre-existing generic deref-write refusal (HEAD's text for `*r = ..`).
const DEREF_WRITE_REFUSAL: &str =
    "assignment through a dereferenced reference is unsupported in vc_extraction";

fn verify_src(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_opaa_{}_{}.rs", std::process::id(), tmp_id));
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

fn verify(func: &str) -> VerifyResult {
    verify_src(func, func, SRC)
}

fn assert_verified(func: &str) {
    let result = verify(func);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{func} should verify, got: {result:?}"
    );
}

fn assert_counterexample(func: &str, obligation_needle: &str) {
    let result = verify(func);
    match &result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.contains(obligation_needle),
            "{func} should fail on an obligation containing {obligation_needle:?}, got: {obligation_name}"
        ),
        other => panic!("{func} should be a Counterexample, got: {other:?}"),
    }
}

fn assert_error_message(result: VerifyResult, func: &str, needles: &[&str]) {
    let VerifyResult::Error { message } = &result else {
        panic!("{func} should fail closed with Error, got: {result:?}");
    };
    for needle in needles {
        assert!(
            message.contains(needle),
            "{func} refusal should contain {needle:?}, got: {message}"
        );
    }
}

fn assert_gated(func: &str, needles: &[&str]) {
    assert_error_message(verify(func), func, needles);
}

const SRC: &str = r#"
fn takes(v: &mut u64) {
    *v = 0u64;
}

fn takes_u8(v: u8) -> u8 {
    v
}

// CONTROL c1: insert on a known None; the alias reads the inserted value.
#[trust_vc::ensures(true)]
fn c1_insert_none_read() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

// LIAR l1.
#[trust_vc::ensures(true)]
fn l1_insert_none_read() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 21u64);
}

// CONTROL c2: insert on a known Some overwrites.
#[trust_vc::ensures(true)]
fn c2_insert_some_read() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

// LIAR l2: the old payload is gone.
#[trust_vc::ensures(true)]
fn l2_insert_some_read() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 5u64);
}

// CONTROL c3: get_or_insert on a known None inserts.
#[trust_vc::ensures(true)]
fn c3_get_or_insert_none_read() {
    let mut x = Option::<u64>::None;
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

// LIAR l3.
#[trust_vc::ensures(true)]
fn l3_get_or_insert_none_read() {
    let mut x = Option::<u64>::None;
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r == 5u64);
}

// CONTROL c4: get_or_insert on a known Some keeps the payload.
#[trust_vc::ensures(true)]
fn c4_get_or_insert_some_read() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r == 5u64);
}

// LIAR l4: get_or_insert does NOT overwrite.
#[trust_vc::ensures(true)]
fn l4_get_or_insert_some_read() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

// CONTROL c5: a write through the alias reaches the owner.
#[trust_vc::ensures(true)]
fn c5_insert_none_write_owner() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(21u64));
}

// LIAR l5: the owner must follow the write.
#[trust_vc::ensures(true)]
fn l5_insert_none_write_owner() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(20u64));
}

// CONTROL c6: the same for get_or_insert on Some.
#[trust_vc::ensures(true)]
fn c6_get_or_insert_some_write_owner() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(21u64));
}

// LIAR l6.
#[trust_vc::ensures(true)]
fn l6_get_or_insert_some_write_owner() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(5u64));
}

// CONTROL c7: two sequential writes.
#[trust_vc::ensures(true)]
fn c7_two_writes() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    *r = 22u64;
    trust_vc::assert!(*r == 22u64);
    trust_vc::assert!(x == Some(22u64));
}

// LIAR l7.
#[trust_vc::ensures(true)]
fn l7_two_writes() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    *r = 22u64;
    trust_vc::assert!(*r == 22u64);
    trust_vc::assert!(x == Some(21u64));
}

// CONTROL c8: the owner is readable right after the call when r is unused.
#[trust_vc::ensures(true)]
fn c8_owner_readable_alias_unused() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(x == Some(20u64));
    trust_vc::assert!(x.is_some());
}

// LIAR l8.
#[trust_vc::ensures(true)]
fn l8_owner_readable_alias_unused() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(x.is_none());
}

// CONTROL c9: bool payload.
#[trust_vc::ensures(true)]
fn c9_bool_payload() {
    let mut x = Some(false);
    let r = x.insert(true);
    trust_vc::assert!(*r == true);
    *r = false;
    trust_vc::assert!(x == Some(false));
}

// LIAR l9.
#[trust_vc::ensures(true)]
fn l9_bool_payload() {
    let mut x = Some(false);
    let r = x.insert(true);
    *r = false;
    trust_vc::assert!(x == Some(true));
}

// CONTROL c10: a declared `Option<u8> = None` keeps u8; arithmetic in range.
#[trust_vc::ensures(true)]
fn c10_declared_u8_arith() {
    let mut x: Option<u8> = None;
    let r = x.insert(250u8);
    trust_vc::assert!(*r == 250u8);
    let y = *r + 5u8;
    trust_vc::assert!(y == 255u8);
}

// LIAR l10: `*r + 10u8` overflows u8 (runtime panic).
#[trust_vc::ensures(true)]
fn l10_declared_u8_arith_overflow() {
    let mut x: Option<u8> = None;
    let r = x.insert(250u8);
    let y = *r + 10u8;
    trust_vc::assert!(y > 0u8);
}

// CONTROL c11: arithmetic read into a let.
#[trust_vc::ensures(true)]
fn c11_arith_read() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = *r + 1u64;
    trust_vc::assert!(y == 21u64);
}

// LIAR l11.
#[trust_vc::ensures(true)]
fn l11_arith_read() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = *r + 1u64;
    trust_vc::assert!(y == 20u64);
}

// CONTROL c12: suffixed usize payloads, two owners. RE-KEYED (H1a, review
// 2026-09-17): the `i32` half this control used to carry is now a GATED case
// (g29 / g30) — an `i32` payload is refused wholesale, the same narrowing the
// sibling `Option::as_slice` view took, because a genuine `i32` cannot be told
// apart from a literal defaulted under a dropped `Option<uN>` annotation.
#[trust_vc::ensures(true)]
fn c12_usize_payloads() {
    let mut a = Some(5usize);
    let r = a.insert(7usize);
    trust_vc::assert!(*r == 7usize);
    let mut b = Option::<usize>::None;
    let s = b.get_or_insert(9usize);
    trust_vc::assert!(*s == 9usize);
}

// LIAR l12.
#[trust_vc::ensures(true)]
fn l12_usize_payloads() {
    let mut a = Some(5usize);
    let r = a.insert(7usize);
    trust_vc::assert!(*r == 8usize);
}

// CONTROL c13: the owner re-bound after the alias's last use.
#[trust_vc::ensures(true)]
fn c13_owner_rebound_after_alias() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    x = Option::<u64>::None;
    trust_vc::assert!(x.is_none());
}

// LIAR l13.
#[trust_vc::ensures(true)]
fn l13_owner_rebound_after_alias() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    x = Option::<u64>::None;
    trust_vc::assert!(x == Some(21u64));
}

// CONTROL c14: a second insert after the first alias is dead.
#[trust_vc::ensures(true)]
fn c14_second_insert_after_alias() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
    let s = x.insert(30u64);
    trust_vc::assert!(*s == 30u64);
    trust_vc::assert!(x == Some(30u64));
}

// LIAR l14.
#[trust_vc::ensures(true)]
fn l14_second_insert_after_alias() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
    let s = x.insert(30u64);
    trust_vc::assert!(*s == 30u64);
    trust_vc::assert!(x == Some(20u64));
}

// CONTROL c15: an unrelated conditional region after the write does not
// re-poison or roll back the owner.
#[trust_vc::ensures(true)]
fn c15_region_after_write(b: bool) {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    let mut y = 0u64;
    if b {
        y = 1u64;
    }
    trust_vc::assert!(x == Some(21u64));
    trust_vc::assert!(y <= 1u64);
}

// LIAR l15.
#[trust_vc::ensures(true)]
fn l15_region_after_write(b: bool) {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    let mut y = 0u64;
    if b {
        y = 1u64;
    }
    trust_vc::assert!(x == Some(20u64));
}

// CONTROL c16: u64::MAX payload, arithmetic that cannot overflow.
#[trust_vc::ensures(true)]
fn c16_max_payload() {
    let mut x = Option::<u64>::None;
    let r = x.insert(18446744073709551615u64);
    let y = *r + 0u64;
    trust_vc::assert!(y == *r);
}

// LIAR l16: `*r + 1u64` overflows (runtime panic).
#[trust_vc::ensures(true)]
fn l16_max_payload_overflow() {
    let mut x = Option::<u64>::None;
    let r = x.insert(18446744073709551615u64);
    let y = *r + 1u64;
    trust_vc::assert!(y > 0u64);
}

// CONTROL c17: `&&` in a spec read.
#[trust_vc::ensures(true)]
fn c17_conjunction_read() {
    let x_other = 3u64;
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64 && x_other == 3u64);
}

// LIAR l17: `||` of two false disjuncts.
#[trust_vc::ensures(true)]
fn l17_disjunction_read() {
    let x_other = 3u64;
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 21u64 || x_other == 4u64);
}

// CONTROL c18: the owner returned as the function's tail after a write.
#[trust_vc::ensures(result == Some(2u64))]
fn c18_owner_returned() -> Option<u64> {
    let mut x = Option::<u64>::None;
    let r = x.insert(1u64);
    *r = 2u64;
    x
}

// LIAR l18.
#[trust_vc::ensures(result == Some(1u64))]
fn l18_owner_returned() -> Option<u64> {
    let mut x = Option::<u64>::None;
    let r = x.insert(1u64);
    *r = 2u64;
    x
}

// CONTROL c19: an early return inside the alias window.
#[trust_vc::ensures(result == 8u64 || result == 7u64)]
fn c19_early_return_in_window(b: bool) -> u64 {
    let mut x = Option::<u64>::None;
    let r = x.insert(5u64);
    if b {
        return 7u64;
    }
    *r = 8u64;
    let v = *r;
    v
}

// LIAR l19: the fall-through path returns 8.
#[trust_vc::ensures(result == 7u64)]
fn l19_early_return_in_window(b: bool) -> u64 {
    let mut x = Option::<u64>::None;
    let r = x.insert(5u64);
    if b {
        return 7u64;
    }
    *r = 8u64;
    let v = *r;
    v
}

// CONTROL c20: two owners with interleaved aliases.
#[trust_vc::ensures(true)]
fn c20_two_owners() {
    let mut a = Option::<u64>::None;
    let mut b = Option::<u64>::None;
    let r = a.insert(1u64);
    let s = b.insert(2u64);
    *r = 3u64;
    *s = 4u64;
    trust_vc::assert!(a == Some(3u64));
    trust_vc::assert!(b == Some(4u64));
}

// LIAR l20: the writes do not cross owners.
#[trust_vc::ensures(true)]
fn l20_two_owners() {
    let mut a = Option::<u64>::None;
    let mut b = Option::<u64>::None;
    let r = a.insert(1u64);
    let s = b.insert(2u64);
    *r = 3u64;
    *s = 4u64;
    trust_vc::assert!(a == Some(4u64));
}

// GATED g1: a parameter receiver, even under requires(is_some).
#[trust_vc::requires(x.is_some())]
#[trust_vc::ensures(true)]
fn g1_param_receiver(mut x: Option<u64>) {
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r == 20u64 || *r != 20u64);
}

// GATED g2: an if-joined local.
#[trust_vc::ensures(true)]
fn g2_if_joined_receiver(b: bool) {
    let mut x = Option::<u64>::None;
    if b {
        x = Some(5u64);
    }
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r >= 5u64);
}

// GATED g3: `None::<u64>` renders as a bare `None` (type lost).
#[trust_vc::ensures(true)]
fn g3_turbofish_none_receiver() {
    let mut x = None::<u64>;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

// GATED g4: unsuffixed argument (would default to i32 in the model).
#[trust_vc::ensures(true)]
fn g4_unsuffixed_argument() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20);
    trust_vc::assert!(*r == 20u64);
}

// GATED g5: the dropped-annotation hole: `Some(200)` under `Option<u8>`.
#[trust_vc::ensures(true)]
fn c30_unsuffixed_owner_payload() {
    let mut x: Option<u8> = Some(200);
    let r = x.get_or_insert(5u8);
    trust_vc::assert!(*r == 200u8);
}

// CONTROL c21 (H1b, review 2026-09-17): the dropped-annotation rule is about
// UNSUFFIXED literals only — an `Option<u8>` ascription whose payload IS
// suffixed types the binding exactly and keeps the lane.
#[trust_vc::ensures(true)]
fn c21_suffixed_under_option_annotation() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y: Option<u8> = Some(200u8);
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y == Some(200u8));
}

// LIAR l21.
#[trust_vc::ensures(true)]
fn l21_suffixed_under_option_annotation() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y: Option<u8> = Some(200u8);
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y == Some(201u8));
}

// CONTROL c22 (H1b round 3): the widened rule is about DEFAULTED literals
// only — a body whose every integer literal is suffixed keeps the lane, even
// under the very ascription (`let _q: u8 = y;`) that types a defaulted one.
#[trust_vc::ensures(true)]
fn c22_suffixed_under_later_bare_ascription() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 200u8;
    let _q: u8 = y;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y == 200u8);
}

// LIAR l22.
#[trust_vc::ensures(true)]
fn l22_suffixed_under_later_bare_ascription() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 200u8;
    let _q: u8 = y;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(*r == 21u64);
}

// CONTROL c23 (H1b round 3, floats): a SUFFIXED float is modeled at its own
// width, so it keeps the lane — `16777216.0f32 + 1.0f32 == 16777216.0f32` is
// runtime-TRUE (the sum rounds back) and verifies.
#[trust_vc::ensures(true)]
fn c23_suffixed_f32_payload_neighbour() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 16777216.0f32;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y + 1.0f32 == y);
}

// LIAR l23: the same body claiming the sum GROWS.
#[trust_vc::ensures(true)]
fn l23_suffixed_f32_payload_neighbour() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 16777216.0f32;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y + 1.0f32 > y);
}

// GATED g37 (H1b round 3): the MEASURED minimal liar of the widened rule. The
// first cut of H1b keyed on ONE `syn::Local` and exited early on a BARE
// primitive-integer ascription, so `let y = 200; let _q: u8 = y;` kept the
// lane while rustc infers `y: u8` from that very ascription — `200u8 << 1`
// is 144, so `y << 1 > 200` is runtime-FALSE (no panic, a pure value
// disagreement: the model read i32 and got 400).
#[trust_vc::ensures(true)]
fn g37_later_bare_ascription_shift() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 200;
    let _q: u8 = y;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y << 1 > 200);
}

// GATED g38 (H1b round 3): the type comes from a free-fn ARGUMENT, with no
// ascription anywhere — `y + 100` overflows a u8.
#[trust_vc::ensures(true)]
fn g38_free_fn_argument_overflow() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 200;
    let _q = takes_u8(y);
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y + 100 == 300);
}

// GATED g39 (H2 round 3): an out-of-range literal the SUFFIXED-position bound
// cannot see — rustc rejects `let y = 300;` inferred at `u8` under
// deny-by-default `overflowing_literals`, so the program does not compile.
#[trust_vc::ensures(true)]
fn g39_out_of_range_unsuffixed() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 300;
    let _q: u8 = y;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y == 300);
}

// GATED g40 (H1b round 3): the literal is defaulted in its OWN `let` and typed
// by the `Some(k)` that follows — g34's hole one hop away.
#[trust_vc::ensures(true)]
fn g40_indirect_defaulted_some() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let k = 200;
    let y: Option<u8> = Some(k);
    let z = y.unwrap();
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(z + 100 == 300);
}

// GATED g41: the same through `get_or_insert` on a known `Some`.
#[trust_vc::ensures(true)]
fn g41_indirect_defaulted_get_or_insert() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);
    let k = 200;
    let y: Option<u8> = Some(k);
    let z = y.unwrap();
    trust_vc::assert!(*r == 5u64);
    trust_vc::assert!(z + 100 == 300);
}

// GATED g42: the same in the deref-WRITE arm.
#[trust_vc::ensures(true)]
fn g42_indirect_defaulted_write() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let k = 200;
    let y: Option<u8> = Some(k);
    let z = y.unwrap();
    *r = 21u64;
    trust_vc::assert!(x == Some(21u64));
    trust_vc::assert!(z + 100 == 300);
}

// GATED g43 (H1b round 3): a DEFERRED-init local — the ascription and the
// literal sit in different statements, so no rule reading `local.init` sees
// the pair.
#[trust_vc::ensures(true)]
fn g43_deferred_init_annotation() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y: Option<u8>;
    y = Some(200);
    let z = y.unwrap();
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(z + 100 == 300);
}

// GATED g44: an unsuffixed literal in the SPEC assertion alone. This also
// retires the round-2 incompleteness (an Option equality against an unsuffixed
// literal returned a Counterexample for a runtime-TRUE claim): the body now
// takes no lane at all and keeps HEAD's refusal.
#[trust_vc::ensures(true)]
fn g44_unsuffixed_spec_comparison() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    trust_vc::assert!(*r == 200);
    trust_vc::assert!(x == Some(200));
}

// GATED g45 (H1b round 3, FLOATS — found by this round's own probing, not
// reported): an unsuffixed float is modeled at the `f64` default while
// `let _q: f32 = y;` makes it an `f32`. `16777216.0f32 + 1.0f32` rounds back
// to `16777216.0f32`, so `y + 1.0 > y` is runtime-FALSE.
#[trust_vc::ensures(true)]
fn g45_defaulted_float_sum() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 16777216.0;
    let _q: f32 = y;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y + 1.0 > y);
}

// GATED g46: a recorded COST, not a liar — `y > 1.0` is runtime-true at both
// widths, but a defaulted float is refused whether or not an ascription
// narrows it, because the narrowing use may sit anywhere.
#[trust_vc::ensures(true)]
fn g46_defaulted_float_read() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = 1.5;
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y > 1.0);
}

// CONTROL c24 (POINTER WIDTH, closure round 2026-09-17): `usize` / `isize`
// take the 32-BIT bound in `option_payload_int_literal_bound`, because every
// ported file is checked at BOTH widths and a literal that does not fit the
// narrow width is not a legal Rust literal there. `u32::MAX` is the largest
// `usize` payload the lane may model, and it still verifies — the bound is a
// boundary, not a blanket refusal of `usize` (c12 covers the small end).
#[trust_vc::ensures(true)]
fn c24_boundary_usize_payload() {
    let mut x = Option::<usize>::None;
    let r = x.insert(4294967295usize);
    trust_vc::assert!(*r == 4294967295usize);
}

// LIAR l24.
#[trust_vc::ensures(true)]
fn l24_boundary_usize_payload() {
    let mut x = Option::<usize>::None;
    let r = x.insert(4294967295usize);
    trust_vc::assert!(*r == 4294967294usize);
}

// GATED g47 (POINTER WIDTH): one past c24 — `5000000000usize` compiles on a
// 64-bit host and the read is runtime-true THERE, but the same ported file is
// also checked at 32 bits, where the literal does not compile at all. A
// program rustc refuses to compile is never a true claim, so the payload is
// not a typed literal and the shape falls back to today's path. This pins the
// `usize => u32::MAX` row: widening it to `u64::MAX` reopens the hole.
#[trust_vc::ensures(true)]
fn g47_out_of_range_usize_payload() {
    let mut x = Option::<usize>::None;
    let r = x.insert(5000000000usize);
    trust_vc::assert!(*r == 5000000000usize);
}

// GATED g48 (POINTER WIDTH): the same rule in the WRITE position, on `isize`
// (bound `i32::MAX`). The literal bound is checked at every position the lane
// reads one, so the alias write is refused independently of the payload.
#[trust_vc::ensures(true)]
fn g48_out_of_range_isize_write() {
    let mut x = Option::<isize>::None;
    let r = x.insert(5isize);
    *r = 3000000000isize;
    trust_vc::assert!(*r == 3000000000isize);
}

// PRE-EXISTING p1 / p2: the defaulted-`i32` hole itself, with NO alias in the
// body. Both VERIFIED at HEAD. RE-KEYED 2026-09-18: p2 (the DEFERRED
// ascription) is closed by the `let` annotation width carry; p1 (the literal
// bound to its own un-ascribed `let` first) is the H1b backward-inference class,
// REFUSED since 2026-09-25 (the `let` binds only a value of its ascribed type).
#[trust_vc::ensures(true)]
fn p1_defaulted_hole_no_lane() {
    let k = 200;
    let y: Option<u8> = Some(k);
    let z = y.unwrap();
    trust_vc::assert!(z + 100 == 300);
}

#[trust_vc::ensures(true)]
fn p2_deferred_hole_no_lane() {
    let y: Option<u8>;
    y = Some(200);
    let z = y.unwrap();
    trust_vc::assert!(z + 100 == 300);
}

// GATED g29 (H1a, review 2026-09-17): an `i32` payload is refused wholesale
// — the re-keyed i32 half of the old c12 control.
#[trust_vc::ensures(true)]
fn g29_i32_payload() {
    let mut a = Some(5i32);
    let r = a.insert(7i32);
    trust_vc::assert!(*r == 7i32);
}

// GATED g30 (H1a): the same for a turbofish `Option::<i32>::None` owner.
#[trust_vc::ensures(true)]
fn g30_i32_none_payload() {
    let mut x = Option::<i32>::None;
    let r = x.get_or_insert(20i32);
    trust_vc::assert!(*r == 20i32);
}

// GATED g31 (H2, review 2026-09-17): the MEASURED liar — `2147483648i32` does
// not fit `i32` (rustc's deny-by-default `overflowing_literals`), and the lane
// admitted it as an exact payload, discharging the negation against it:
// `-(*r) == -2147483648i32` VERIFIED on the pre-narrowing lane while the
// program does not compile.
#[trust_vc::ensures(true)]
fn g31_out_of_range_i32_payload() {
    let mut x = Option::<i32>::None;
    let r = x.insert(2147483648i32);
    trust_vc::assert!(-(*r) == -2147483648i32);
}

// GATED g32 (H2): out of range for `u8`, in the argument position — refused
// independently of the `i32` rule.
#[trust_vc::ensures(true)]
fn g32_out_of_range_u8_argument() {
    let mut x = Option::<u8>::None;
    let r = x.insert(300u8);
    trust_vc::assert!(*r == 300u8);
}

// GATED g33 (H2): out of range for `u8`, in the WRITE position.
#[trust_vc::ensures(true)]
fn g33_out_of_range_u8_write() {
    let mut x = Option::<u8>::None;
    let r = x.insert(1u8);
    *r = 300u8;
    trust_vc::assert!(x == Some(300u8));
}

// GATED g34 (H1b, review 2026-09-17): the MEASURED liar — the lane made the
// PRE-EXISTING dropped-annotation hole reachable. `let y: Option<u8> =
// Some(200)` is recorded as `Option<i32>` (only a BARE primitive-integer
// annotation is carried), so `z + 100 == 300` verified at 32 bits while the
// program panics on u8 overflow. HEAD failed closed on the `insert` call.
#[trust_vc::ensures(true)]
fn g34_dropped_option_annotation_overflow() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y: Option<u8> = Some(200);
    let z = y.unwrap();
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(z + 100 == 300);
}

// GATED g35 (H1b): the same hole read through an equality on the owner.
#[trust_vc::ensures(true)]
fn g35_dropped_option_annotation_cmp() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y: Option<u8> = Some(200);
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y == Some(200));
}

// GATED g36 (H1b): a dropped annotation that is not an `Option` — a tuple
// ascription drops the element widths the same way.
#[trust_vc::ensures(true)]
fn g36_dropped_tuple_annotation() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y: (u8, u8) = (200, 1);
    trust_vc::assert!(*r == 20u64);
    trust_vc::assert!(y.0 == 200);
}

// GATED g6: argument type differs from the payload type.
#[trust_vc::ensures(true)]
fn g6_type_mismatch() {
    let mut x = Option::<u8>::None;
    let r = x.insert(5u64);
    trust_vc::assert!(*r == 5u64);
}

// GATED g7: the let inside a block.
#[trust_vc::ensures(true)]
fn g7_let_in_block() {
    let mut x = Option::<u64>::None;
    {
        let r = x.insert(20u64);
        trust_vc::assert!(*r == 20u64);
    }
}

// GATED g8: the let inside an if.
#[trust_vc::ensures(true)]
fn g8_let_in_if(b: bool) {
    let mut x = Option::<u64>::None;
    if b {
        let r = x.insert(20u64);
        trust_vc::assert!(*r == 20u64);
    }
}

// GATED g9: `let mut r`.
#[trust_vc::ensures(true)]
fn g9_mut_alias_binding() {
    let mut x = Option::<u64>::None;
    let mut r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

// GATED g10: the owner re-assigned while the alias is live.
#[trust_vc::ensures(true)]
fn g10_owner_assigned_in_window() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    x = None;
    trust_vc::assert!(*r == 20u64);
}

// GATED g11: a second insert while the first alias is live.
#[trust_vc::ensures(true)]
fn g11_second_insert_in_window() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let s = x.insert(30u64);
    trust_vc::assert!(*r == 20u64);
}

// GATED g12: the owner shadowed while the alias is live.
#[trust_vc::ensures(true)]
fn g12_owner_shadowed_in_window() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let x = 5u64;
    trust_vc::assert!(*r == 20u64);
}

// GATED g13: the alias passed to a call.
#[trust_vc::ensures(true)]
fn g13_alias_call_argument() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    takes(r);
    trust_vc::assert!(*r == 0u64);
}

// GATED g14: a method call on the alias.
#[trust_vc::ensures(true)]
fn g14_alias_method_receiver() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = r.checked_add(1u64);
    trust_vc::assert!(*r == 20u64);
}

// GATED g15: a reborrow of the alias.
#[trust_vc::ensures(true)]
fn g15_alias_reborrow() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let q = &mut *r;
    *q = 9u64;
    trust_vc::assert!(*r == 9u64);
}

// GATED g16: the alias stored in a tuple holder.
#[trust_vc::ensures(true)]
fn g16_alias_in_holder() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let h = (r, 1u64);
    trust_vc::assert!(h.1 == 1u64);
}

// GATED g17: `*r` under an if-let scrutinee.
#[trust_vc::ensures(true)]
fn g17_alias_if_let() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    if let Some(v) = Some(*r) {
        trust_vc::assert!(v == 20u64);
    }
}

// GATED g18: the alias captured by a closure.
#[trust_vc::ensures(true)]
fn g18_alias_closure() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let c = || *r;
    trust_vc::assert!(c() == 20u64);
}

// GATED g19: compound assignment through the alias.
#[trust_vc::ensures(true)]
fn g19_alias_compound_assign() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r += 1u64;
    trust_vc::assert!(*r == 21u64);
}

// GATED g20: a non-literal write right-hand side.
#[trust_vc::ensures(true)]
fn g20_alias_write_non_literal() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = *r + 1u64;
    trust_vc::assert!(*r == 21u64);
}

// GATED g21: an unsuffixed write right-hand side.
#[trust_vc::ensures(true)]
fn g21_alias_write_unsuffixed() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21;
    trust_vc::assert!(*r == 21u64);
}

// GATED g22: a write inside an if.
#[trust_vc::ensures(true)]
fn g22_alias_write_in_if(b: bool) {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    if b {
        *r = 21u64;
    }
    trust_vc::assert!(*r >= 20u64);
}

// GATED g23: a write inside a loop.
#[trust_vc::ensures(true)]
fn g23_alias_write_in_loop() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let mut i = 0u64;
    while i < 3u64 {
        *r = 21u64;
        i = i + 1u64;
    }
    trust_vc::assert!(*r == 21u64);
}

// GATED g24: the alias read as the function's tail value.
#[trust_vc::ensures(true)]
fn g24_alias_tail(b: bool) -> u64 {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r
}

// GATED g25: the alias name bound before the let.
#[trust_vc::ensures(true)]
fn g25_alias_rebound() {
    let r = 1u64;
    let mut x = Option::<u64>::None;
    let r = x.insert(2u64);
    trust_vc::assert!(*r == 2u64);
}

// GATED g26: the owner captured by a closure (after the window).
#[trust_vc::ensures(true)]
fn g26_owner_captured() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
    let mut c = || {
        x = None;
    };
    c();
}

// GATED g27: the owner borrowed by a `&mut` alias before the call.
#[trust_vc::ensures(true)]
fn g27_owner_borrowed() {
    let mut x = Option::<u64>::None;
    let y = &mut x;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

// GATED g28: the let inside a loop body.
#[trust_vc::ensures(true)]
fn g28_let_in_loop() {
    let mut x = Option::<u64>::None;
    let mut i = 0u64;
    while i < 3u64 {
        let r = x.insert(20u64);
        trust_vc::assert!(*r == 20u64);
        i = i + 1u64;
    }
}

// RESTORED e1-e9 (review 2026-09-17): a refused candidate whose claim does
// not depend on the alias takes today's path and keeps HEAD's Verified
// verdict; each `e*l` liar is refuted.
#[trust_vc::ensures(true)]
fn e1_alias_moved(b: bool) {
    let mut x = Some(5u64);
    let r = x.insert(20u64);
    let q = r;
    trust_vc::assert!(b || !b);
}

#[trust_vc::ensures(true)]
fn e1l_alias_moved(b: bool) {
    let mut x = Some(5u64);
    let r = x.insert(20u64);
    let q = r;
    trust_vc::assert!(b && !b);
}

#[trust_vc::ensures(true)]
fn e2_alias_call_argument() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    takes(r);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e2l_alias_call_argument(b: bool) {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    takes(r);
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn e3_alias_closure() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let c = || *r;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e3l_alias_closure(b: bool) {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let c = || *r;
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn e4_alias_method_receiver() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = r.checked_add(1u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e4l_alias_method_receiver(b: bool) {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let y = r.checked_add(1u64);
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn e5_owner_shadowed() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let x = 5u64;
    let k = *r;
    trust_vc::assert!(x == 5u64);
}

#[trust_vc::ensures(true)]
fn e5l_owner_shadowed() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    let x = 5u64;
    let k = *r;
    trust_vc::assert!(x == 6u64);
}

#[trust_vc::ensures(true)]
fn e6_mut_alias_binding() {
    let mut x = Option::<u64>::None;
    let mut r = x.insert(20u64);
    let k = 1u64;
    let _z = &mut r;
    trust_vc::assert!(k == 1u64);
}

#[trust_vc::ensures(true)]
fn e6l_mut_alias_binding() {
    let mut x = Option::<u64>::None;
    let mut r = x.insert(20u64);
    let k = 1u64;
    let _z = &mut r;
    trust_vc::assert!(k == 2u64);
}

#[trust_vc::ensures(true)]
fn e7_let_in_block() {
    let mut x = Option::<u64>::None;
    {
        let r = x.insert(20u64);
        let k = *r;
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e7l_let_in_block(b: bool) {
    let mut x = Option::<u64>::None;
    {
        let r = x.insert(20u64);
        let k = *r;
    }
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn e8_unsuffixed_argument() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20);
    let k = *r;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e8l_unsuffixed_argument(b: bool) {
    let mut x = Option::<u64>::None;
    let r = x.insert(20);
    let k = *r;
    trust_vc::assert!(b);
}

#[trust_vc::ensures(true)]
fn e9_param_receiver(mut x: Option<u64>) {
    let r = x.insert(20u64);
    let k = *r;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e9l_param_receiver(mut x: Option<u64>, b: bool) {
    let r = x.insert(20u64);
    let k = *r;
    trust_vc::assert!(b);
}

// NON-HIJACK n1: a HashSet insert result is untouched by the lane.
#[trust_vc::ensures(true)]
fn n1_hashset_insert() {
    let mut s: std::collections::HashSet<u64> = std::collections::HashSet::new();
    let b = s.insert(3u64);
    trust_vc::assert!(b);
}

// NON-HIJACK n2: a two-argument Vec insert is not a candidate.
#[trust_vc::ensures(true)]
fn n2_vec_insert() {
    let mut v = Vec::<u64>::new();
    v.push(2u64);
    let u = v.insert(0usize, 1u64);
    trust_vc::assert!(v.len() == 2usize);
}
"#;

/// f1: a file-local by-value trait method named `insert` wins method
/// resolution over `Option::insert` (measured: `r == 777`, `x == Some(5)`).
const SRC_F1_TRAIT_HIJACK: &str = r#"
trait Tr {
    fn insert(self, v: u64) -> u64;
}

impl Tr for Option<u64> {
    fn insert(self, v: u64) -> u64 {
        777u64
    }
}

#[trust_vc::ensures(true)]
fn f1_trait_hijack() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);
    trust_vc::assert!(x == Some(20u64));
}
"#;

/// f2: a user tuple struct named `Some`.
const SRC_F2_SOME_SHADOW: &str = r#"
struct Some(u64);

#[trust_vc::ensures(true)]
fn f2_some_shadow() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}
"#;

/// f3: a glob import.
const SRC_F3_GLOB_USE: &str = r#"
use std::collections::*;

#[trust_vc::ensures(true)]
fn f3_glob_use() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(21u64));
}
"#;

/// f4: a function-local `macro_rules!`.
const SRC_F4_LOCAL_MACRO: &str = r#"
#[trust_vc::ensures(true)]
fn f4_local_macro() {
    macro_rules! m {
        () => {};
    }
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(21u64));
}
"#;

/// f5: a by-value trait method spelled `r#insert` (same method name).
const SRC_F5: &str = r#"
trait Tr {
    fn r#insert(self, v: u64) -> &'static mut u64;
}

impl Tr for Option<u64> {
    fn r#insert(self, v: u64) -> &'static mut u64 {
        Box::leak(Box::new(777u64))
    }
}

#[trust_vc::ensures(true)]
fn f5_raw_insert_trait_read() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

#[trust_vc::ensures(true)]
fn f5_raw_insert_trait_owner() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(21u64));
}
"#;

/// f6: a by-value trait method spelled `r#get_or_insert`.
const SRC_F6: &str = r#"
trait TrG {
    fn r#get_or_insert(self, v: u64) -> &'static mut u64;
}

impl TrG for Option<u64> {
    fn r#get_or_insert(self, v: u64) -> &'static mut u64 {
        Box::leak(Box::new(777u64))
    }
}

#[trust_vc::ensures(true)]
fn f6_raw_get_or_insert_trait_read() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r == 5u64);
}
"#;

/// f7: a raw-identifier `enum r#Option` with an inherent `r#insert`.
const SRC_F7: &str = r#"
enum r#Option<T> {
    None,
    Some(T),
}

impl<T> r#Option<T> {
    fn r#insert(&mut self, v: T) -> &'static mut u64 {
        Box::leak(Box::new(777u64))
    }
}

#[trust_vc::ensures(true)]
fn f7_raw_enum_option() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}
"#;

/// f8: a path-qualified derive (a proc macro that can emit an `insert` trait
/// for `Option`; the measured `hjd::Hijack` did).
const SRC_F8: &str = r#"
#[derive(hjd::Hijack)]
struct HjS;

#[trust_vc::ensures(true)]
fn f8_derive_hijack_read() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

#[trust_vc::ensures(true)]
fn f8_derive_hijack_owner() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    *r = 21u64;
    trust_vc::assert!(x == Some(21u64));
}
"#;

/// f9: a path-qualified attribute macro on an unrelated item.
const SRC_F9: &str = r#"
#[hjd::hijack_attr]
fn helper_marked() {}

#[trust_vc::ensures(true)]
fn f9_attr_macro_hijack() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);
    trust_vc::assert!(*r == 5u64);
}
"#;

/// f10: a path-qualified body macro, and an attribute inside std macro tokens.
const SRC_F10: &str = r#"
#[trust_vc::ensures(true)]
fn f10_body_path_macro() {
    hj::hijack!();
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

#[trust_vc::ensures(true)]
fn f10_body_attr_in_macro_tokens() {
    std::thread_local! {
        #[hjd::hijack_attr]
        static T: u8 = 0u8;
    }
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}
"#;

/// f11: builtin single-segment derives keep the lane (control and liar).
const SRC_F11: &str = r#"
#[derive(Clone, Copy, Debug, PartialEq)]
struct Plain(u64);

#[trust_vc::ensures(true)]
fn f11_builtin_derive_file_control() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 20u64);
}

#[trust_vc::ensures(true)]
fn f11_builtin_derive_file_liar() {
    let mut x = Option::<u64>::None;
    let r = x.insert(20u64);
    trust_vc::assert!(*r == 21u64);
}
"#;

/// f12 (H3, review 2026-09-17): the MEASURED liar. `use core::primitive::u8 as
/// u64;` is rooted at `core`, so it satisfies the pre-existing rooting rule —
/// and then the file's `u64` IS a `u8`. `f12_rename_use_liar` verified on the
/// pre-narrowing lane while the program overflows a `u8` (runtime twin:
/// `size_of::<u64>() == 1` and `y.checked_add(z).is_none()`).
const SRC_F12_PRIMITIVE_RENAME: &str = r#"
use core::primitive::u8 as u64;

#[trust_vc::ensures(true)]
fn f12_rename_use_liar() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    let y: u64 = *r as u64;
    let z: u64 = 100;
    trust_vc::assert!(y + z == 300);
}

#[trust_vc::ensures(true)]
fn f12_rename_cast_liar() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    trust_vc::assert!((*r as u64) + 100u64 == 300u64);
}

#[trust_vc::ensures(true)]
fn f12_rename_read_control() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    trust_vc::assert!(*r == 200u8);
}
"#;

/// f13 (H3): a type-namespace ITEM that shadows a primitive type name.
const SRC_F13_PRIMITIVE_TYPE_ALIAS: &str = r#"
type u64 = u8;

#[trust_vc::ensures(true)]
fn f13_type_alias_shadow() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    let y: u64 = *r as u64;
    let z: u64 = 100;
    trust_vc::assert!(y + z == 300);
}
"#;

/// f14 (H3): a generic parameter that shadows a primitive type name.
const SRC_F14_PRIMITIVE_GENERIC: &str = r#"
struct Holder<u64>(u64);

#[trust_vc::ensures(true)]
fn f14_generic_shadow() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    trust_vc::assert!(*r == 200u8);
}
"#;

/// f15 (H3, CONTROL): the rooting rule alone is unchanged — a std `use` that
/// binds no primitive type name keeps the lane.
const SRC_F15_PLAIN_STD_USE: &str = r#"
use core::cmp::Ordering;

#[trust_vc::ensures(true)]
fn f15_plain_std_use_control() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    trust_vc::assert!(*r == 200u8);
}

#[trust_vc::ensures(true)]
fn f15_plain_std_use_liar() {
    let mut x = Option::<u8>::None;
    let r = x.insert(200u8);
    trust_vc::assert!(*r == 201u8);
}
"#;

// ---------------------------------------------------------------- controls

#[test]
fn c1_insert_none_read_verifies() {
    assert_verified("c1_insert_none_read");
}

#[test]
fn l1_insert_none_read_refuted() {
    assert_counterexample("l1_insert_none_read", "assertion_0");
}

#[test]
fn c2_insert_some_read_verifies() {
    assert_verified("c2_insert_some_read");
}

#[test]
fn l2_insert_some_read_refuted() {
    assert_counterexample("l2_insert_some_read", "assertion_0");
}

#[test]
fn c3_get_or_insert_none_read_verifies() {
    assert_verified("c3_get_or_insert_none_read");
}

#[test]
fn l3_get_or_insert_none_read_refuted() {
    assert_counterexample("l3_get_or_insert_none_read", "assertion_0");
}

#[test]
fn c4_get_or_insert_some_read_verifies() {
    assert_verified("c4_get_or_insert_some_read");
}

#[test]
fn l4_get_or_insert_some_read_refuted() {
    assert_counterexample("l4_get_or_insert_some_read", "assertion_0");
}

#[test]
fn c5_insert_none_write_owner_verifies() {
    assert_verified("c5_insert_none_write_owner");
}

#[test]
fn l5_insert_none_write_owner_refuted() {
    assert_counterexample("l5_insert_none_write_owner", "assertion_0");
}

#[test]
fn c6_get_or_insert_some_write_owner_verifies() {
    assert_verified("c6_get_or_insert_some_write_owner");
}

#[test]
fn l6_get_or_insert_some_write_owner_refuted() {
    assert_counterexample("l6_get_or_insert_some_write_owner", "assertion_0");
}

#[test]
fn c7_two_writes_verifies() {
    assert_verified("c7_two_writes");
}

#[test]
fn l7_two_writes_refuted() {
    assert_counterexample("l7_two_writes", "assertion_1");
}

#[test]
fn c8_owner_readable_alias_unused_verifies() {
    assert_verified("c8_owner_readable_alias_unused");
}

#[test]
fn l8_owner_readable_alias_unused_refuted() {
    assert_counterexample("l8_owner_readable_alias_unused", "assertion_0");
}

#[test]
fn c9_bool_payload_verifies() {
    assert_verified("c9_bool_payload");
}

#[test]
fn l9_bool_payload_refuted() {
    assert_counterexample("l9_bool_payload", "assertion_0");
}

#[test]
fn c10_declared_u8_arith_verifies() {
    assert_verified("c10_declared_u8_arith");
}

#[test]
fn l10_declared_u8_arith_overflow_refuted() {
    assert_counterexample("l10_declared_u8_arith_overflow", "overflow_check_");
}

#[test]
fn c11_arith_read_verifies() {
    assert_verified("c11_arith_read");
}

#[test]
fn l11_arith_read_refuted() {
    assert_counterexample("l11_arith_read", "assertion_1");
}

#[test]
fn c12_usize_payloads_verifies() {
    assert_verified("c12_usize_payloads");
}

#[test]
fn l12_usize_payloads_refuted() {
    assert_counterexample("l12_usize_payloads", "assertion_0");
}

#[test]
fn c21_suffixed_under_option_annotation_verifies() {
    assert_verified("c21_suffixed_under_option_annotation");
}

#[test]
fn l21_suffixed_under_option_annotation_refuted() {
    assert_counterexample("l21_suffixed_under_option_annotation", "assertion_1");
}

#[test]
fn c13_owner_rebound_after_alias_verifies() {
    assert_verified("c13_owner_rebound_after_alias");
}

#[test]
fn l13_owner_rebound_after_alias_refuted() {
    assert_counterexample("l13_owner_rebound_after_alias", "assertion_0");
}

#[test]
fn c14_second_insert_after_alias_verifies() {
    assert_verified("c14_second_insert_after_alias");
}

#[test]
fn l14_second_insert_after_alias_refuted() {
    assert_counterexample("l14_second_insert_after_alias", "assertion_2");
}

#[test]
fn c15_region_after_write_verifies() {
    assert_verified("c15_region_after_write");
}

#[test]
fn l15_region_after_write_refuted() {
    assert_counterexample("l15_region_after_write", "assertion_0");
}

#[test]
fn c16_max_payload_verifies() {
    assert_verified("c16_max_payload");
}

#[test]
fn l16_max_payload_overflow_refuted() {
    assert_counterexample("l16_max_payload_overflow", "overflow_check_");
}

#[test]
fn c17_conjunction_read_verifies() {
    assert_verified("c17_conjunction_read");
}

#[test]
fn l17_disjunction_read_refuted() {
    assert_counterexample("l17_disjunction_read", "assertion_0");
}

#[test]
fn c18_owner_returned_verifies() {
    assert_verified("c18_owner_returned");
}

#[test]
fn l18_owner_returned_refuted() {
    assert_counterexample("l18_owner_returned", "postcondition");
}

#[test]
fn c19_early_return_in_window_verifies() {
    assert_verified("c19_early_return_in_window");
}

#[test]
fn l19_early_return_in_window_refuted() {
    assert_counterexample("l19_early_return_in_window", "postcondition");
}

#[test]
fn c20_two_owners_verifies() {
    assert_verified("c20_two_owners");
}

#[test]
fn l20_two_owners_refuted() {
    assert_counterexample("l20_two_owners", "assertion_0");
}

// ------------------------------------------------------------------- gated
//
// Every gated shape takes TODAY's path; each pin below is HEAD's own text
// (measured byte-identical against a lens built from the untouched tree).

#[test]
fn g1_param_receiver_gated() {
    assert_gated("g1_param_receiver", &[LOWER_GET_OR_INSERT]);
}

#[test]
fn g2_if_joined_receiver_gated() {
    assert_gated("g2_if_joined_receiver", &[UNRESOLVED_X]);
}

#[test]
fn g3_turbofish_none_receiver_gated() {
    assert_gated(
        "g3_turbofish_none_receiver",
        &["unresolved variable `None`"],
    );
}

#[test]
fn g4_unsuffixed_argument_gated() {
    assert_gated("g4_unsuffixed_argument", &[LOWER_INSERT]);
}

/// RE-KEYED 2026-09-18 (was GATED g5) by the `let` annotation width carry.
/// HEAD recorded `let mut x: Option<u8> = Some(200)` as `Option<i32>` — the
/// dropped-annotation hole — and BOTH refusals that kept it out (the lowering's
/// `Option<i32>` method refusal and the whole-body defaulted-literal rule) fired
/// on the same body. The ascription now carries `u8` into the payload, so the
/// receiver really is `Option<u8>`, the literal is PLACED and the lane runs.
/// The claim is runtime-true (`Some(200).get_or_insert(5)` keeps 200).
#[test]
fn c30_unsuffixed_owner_payload_verifies() {
    assert_verified("c30_unsuffixed_owner_payload");
}

/// g29 / g30 (H1a): every `i32` payload takes HEAD's path, exactly as the
/// sibling `Option::as_slice` view refuses every `Option<i32>` receiver.
#[test]
fn g29_i32_payload_gated() {
    assert_gated(
        "g29_i32_payload",
        &["collection operation 'insert' requires a collection receiver, got 'Option<i32>'"],
    );
}

#[test]
fn g30_i32_none_payload_gated() {
    assert_gated(
        "g30_i32_none_payload",
        &["unsupported method `get_or_insert() on type `Option<i32>`"],
    );
}

/// g31-g33 (H2): a literal that does not fit the type its suffix names is not
/// a typed literal, so the shape falls back to HEAD's own refusal.
#[test]
fn g31_out_of_range_i32_payload_gated() {
    assert_gated(
        "g31_out_of_range_i32_payload",
        &["collection operation 'insert' requires a collection receiver, got 'Option<i32>'"],
    );
}

#[test]
fn g32_out_of_range_u8_argument_gated() {
    assert_gated(
        "g32_out_of_range_u8_argument",
        &["collection operation 'insert' requires a collection receiver, got 'Option<u8>'"],
    );
}

#[test]
fn g33_out_of_range_u8_write_gated() {
    assert_gated("g33_out_of_range_u8_write", &[DEREF_WRITE_REFUSAL, "`* r`"]);
}

/// g34-g36 (H1b): a `let` whose type ascription the extractor drops, next to
/// an unsuffixed integer literal, turns the lane off for the whole body — the
/// defaulted-`i32` hole it creates is PRE-EXISTING (it verifies at HEAD in a
/// body with no `insert` call) and the lane must not make it reachable.
#[test]
fn g34_dropped_option_annotation_overflow_gated() {
    assert_gated(
        "g34_dropped_option_annotation_overflow",
        &["collection operation 'insert' requires a collection receiver, got 'Option<u64>'"],
    );
}

#[test]
fn g35_dropped_option_annotation_cmp_gated() {
    assert_gated(
        "g35_dropped_option_annotation_cmp",
        &["collection operation 'insert' requires a collection receiver, got 'Option<u64>'"],
    );
}

#[test]
fn g36_dropped_tuple_annotation_gated() {
    assert_gated(
        "g36_dropped_tuple_annotation",
        &["collection operation 'insert' requires a collection receiver, got 'Option<u64>'"],
    );
}

/// c22 / l22 (H1b round 3): the widened rule keys on DEFAULTED literals, not
/// on ascriptions — a fully suffixed body keeps the lane under the same
/// `let _q: u8 = y;` that types a defaulted one.
#[test]
fn c22_suffixed_under_later_bare_ascription_verifies() {
    assert_verified("c22_suffixed_under_later_bare_ascription");
}

#[test]
fn l22_suffixed_under_later_bare_ascription_refuted() {
    assert_counterexample("l22_suffixed_under_later_bare_ascription", "assertion_1");
}

/// c23 / l23: a SUFFIXED float is modeled at its own width, so it keeps the
/// lane and its f32 rounding is decided correctly in BOTH directions.
#[test]
fn c23_suffixed_f32_payload_neighbour_verifies() {
    assert_verified("c23_suffixed_f32_payload_neighbour");
}

#[test]
fn l23_suffixed_f32_payload_neighbour_refuted() {
    assert_counterexample("l23_suffixed_f32_payload_neighbour", "assertion_1");
}

/// g37-g46 (H1b round 3): the first cut of H1b anchored on ONE `syn::Local`
/// and left more than twenty spellings of the same hole reachable, because
/// Rust types a defaulted literal from a use that may sit anywhere in the
/// function. The rule is now whole-body and blunt: any defaulted numeric
/// literal refuses the lane, so each of these falls back to HEAD's own
/// refusal, measured byte-identical with matched lenses (2026-09-17).
#[test]
fn g37_later_bare_ascription_shift_gated() {
    assert_gated("g37_later_bare_ascription_shift", &[LOWER_INSERT]);
}

#[test]
fn g38_free_fn_argument_overflow_gated() {
    assert_gated("g38_free_fn_argument_overflow", &[LOWER_INSERT]);
}

#[test]
fn g39_out_of_range_unsuffixed_gated() {
    assert_gated("g39_out_of_range_unsuffixed", &[LOWER_INSERT]);
}

#[test]
fn g40_indirect_defaulted_some_gated() {
    assert_gated("g40_indirect_defaulted_some", &[LOWER_INSERT]);
}

#[test]
fn g41_indirect_defaulted_get_or_insert_gated() {
    assert_gated(
        "g41_indirect_defaulted_get_or_insert",
        &[LOWER_GET_OR_INSERT],
    );
}

#[test]
fn g42_indirect_defaulted_write_gated() {
    assert_gated(
        "g42_indirect_defaulted_write",
        &[DEREF_WRITE_REFUSAL, "`* r`"],
    );
}

#[test]
fn g43_deferred_init_annotation_gated() {
    assert_gated("g43_deferred_init_annotation", &[LOWER_INSERT]);
}

#[test]
fn g44_unsuffixed_spec_comparison_gated() {
    assert_gated(
        "g44_unsuffixed_spec_comparison",
        &["collection operation 'insert' requires a collection receiver, got 'Option<u8>'"],
    );
}

#[test]
fn g45_defaulted_float_sum_gated() {
    assert_gated("g45_defaulted_float_sum", &[LOWER_INSERT]);
}

#[test]
fn g46_defaulted_float_read_gated() {
    assert_gated("g46_defaulted_float_read", &[LOWER_INSERT]);
}

/// c24 / l24 + g47 / g48 (POINTER WIDTH, closure round 2026-09-17): the
/// `usize => u32::MAX` / `isize => i32::MAX` rows of
/// `option_payload_int_literal_bound`. c24 pins that `u32::MAX` is still a
/// modellable `usize` payload, so the rule is a BOUNDARY; g47 / g48 pin one
/// past it in the payload and in the write position. The needle is
/// width-agnostic on purpose: the refusal is raised by whichever width the
/// dual-width plan lowers first, so it reads `Option<u32>` or `Option<u64>`.
#[test]
fn c24_boundary_usize_payload_verifies() {
    assert_verified("c24_boundary_usize_payload");
}

#[test]
fn l24_boundary_usize_payload_refuted() {
    assert_counterexample("l24_boundary_usize_payload", "assertion_0");
}

#[test]
fn g47_out_of_range_usize_payload_gated() {
    assert_gated(
        "g47_out_of_range_usize_payload",
        &["collection operation 'insert' requires a collection receiver"],
    );
}

#[test]
fn g48_out_of_range_isize_write_gated() {
    assert_gated(
        "g48_out_of_range_isize_write",
        &[DEREF_WRITE_REFUSAL, "* r"],
    );
}

/// p1 / p2 — RE-KEYED 2026-09-18, exactly as this test's own note asked for
/// ("a FAILURE here is good news").
///
/// p2 is CLOSED: `let y: Option<u8>; y = Some(200);` now carries `u8` through
/// the whole-function shape map into the ASSIGNMENT lane, so `z + 100` is
/// discharged at 8 bits and the program's panic is found. It was a false
/// `Verified` at HEAD.
///
/// p1 is DECIDED (re-keyed again, 2026-09-27): `let k = 200; let y:
/// Option<u8> = Some(k);` is the H1b BACKWARD-inference class — the literal has
/// no ascription at its own binding and is narrowed by a later use, which this
/// lane does not model, so `k` is an `i32` and `z + 100 == 300` was a false
/// `Verified` (the program panics). A literal constructor under an ascription
/// now binds each element at the element type (design-trust-proof-backend.md
/// §5b rule 12): the payload `k` — the literal 200 — is bound at `u8`, so
/// `z + 100` is discharged at 8 bits and the panic is found (it was refused at
/// the `let` before: an `Option<i32>` is not an `Option<u8>`).
#[test]
fn p1_p2_pre_existing_defaulted_hole_is_outside_the_lane() {
    // `assertion_1`, not `assertion_0`: `y.unwrap()` gets its own
    // `unwrap_precondition_check_N` obligation from the same index counter, so
    // the `assert!` that carries the overflow refutation is the SECOND
    // obligation. The needle names the assertion, not the (true, `Some`)
    // unwrap check.
    assert_counterexample("p1_defaulted_hole_no_lane", "assertion_1");
    assert_counterexample("p2_deferred_hole_no_lane", "assertion_1");
}

#[test]
fn g6_type_mismatch_gated() {
    assert_gated(
        "g6_type_mismatch",
        &["collection operation 'insert' requires a collection receiver, got 'Option<u8>'"],
    );
}

#[test]
fn g7_let_in_block_gated() {
    assert_gated("g7_let_in_block", &[LOWER_INSERT]);
}

#[test]
fn g8_let_in_if_gated() {
    assert_gated("g8_let_in_if", &[LOWER_INSERT]);
}

#[test]
fn g9_mut_alias_binding_gated() {
    assert_gated("g9_mut_alias_binding", &[LOWER_INSERT]);
}

#[test]
fn g10_owner_assigned_in_window_gated() {
    assert_gated("g10_owner_assigned_in_window", &[LOWER_INSERT]);
}

#[test]
fn g11_second_insert_in_window_gated() {
    assert_gated("g11_second_insert_in_window", &[LOWER_INSERT]);
}

#[test]
fn g12_owner_shadowed_in_window_gated() {
    assert_gated("g12_owner_shadowed_in_window", &[LOWER_INSERT]);
}

#[test]
fn g13_alias_call_argument_gated() {
    assert_gated("g13_alias_call_argument", &[UNRESOLVED_R]);
}

#[test]
fn g14_alias_method_receiver_gated() {
    assert_gated("g14_alias_method_receiver", &[UNRESOLVED_R]);
}

#[test]
fn g15_alias_reborrow_gated() {
    assert_gated("g15_alias_reborrow", &[DEREF_WRITE_REFUSAL, "`* q`"]);
}

#[test]
fn g16_alias_in_holder_gated() {
    assert_gated("g16_alias_in_holder", &[UNRESOLVED_R]);
}

#[test]
fn g17_alias_if_let_gated() {
    assert_gated("g17_alias_if_let", &["unresolved variable `v`"]);
}

#[test]
fn g18_alias_closure_gated() {
    assert_gated(
        "g18_alias_closure",
        &["unknown return type for function 'c'"],
    );
}

#[test]
fn g19_alias_compound_assign_gated() {
    assert_gated("g19_alias_compound_assign", &[DEREF_WRITE_REFUSAL, "`* r`"]);
}

#[test]
fn g20_alias_write_non_literal_gated() {
    assert_gated(
        "g20_alias_write_non_literal",
        &[DEREF_WRITE_REFUSAL, "`* r`"],
    );
}

#[test]
fn g21_alias_write_unsuffixed_gated() {
    assert_gated(
        "g21_alias_write_unsuffixed",
        &[DEREF_WRITE_REFUSAL, "`* r`"],
    );
}

#[test]
fn g22_alias_write_in_if_gated() {
    assert_gated("g22_alias_write_in_if", &[DEREF_WRITE_REFUSAL, "`* r`"]);
}

#[test]
fn g23_alias_write_in_loop_gated() {
    assert_gated("g23_alias_write_in_loop", &[DEREF_WRITE_REFUSAL, "`* r`"]);
}

#[test]
fn g24_alias_tail_gated() {
    assert_gated("g24_alias_tail", &["'return_value'", LOWER_INSERT]);
}

#[test]
fn g25_alias_rebound_gated() {
    assert_gated("g25_alias_rebound", &[LOWER_INSERT]);
}

#[test]
fn g26_owner_captured_gated() {
    assert_gated("g26_owner_captured", &[LOWER_INSERT]);
}

#[test]
fn g27_owner_borrowed_gated() {
    assert_gated("g27_owner_borrowed", &[UNRESOLVED_X]);
}

#[test]
fn g28_let_in_loop_gated() {
    assert_gated("g28_let_in_loop", &[UNRESOLVED_X]);
}

// ------------------------------------------------------ file / body gates

#[test]
fn f1_trait_hijack_file_takes_no_lane() {
    let result = verify_src("f1", "f1_trait_hijack", SRC_F1_TRAIT_HIJACK);
    assert_error_message(result, "f1_trait_hijack", &[UNRESOLVED_X]);
}

#[test]
fn f2_some_shadow_file_takes_no_lane() {
    let result = verify_src("f2", "f2_some_shadow", SRC_F2_SOME_SHADOW);
    assert_error_message(result, "f2_some_shadow", &[]);
}

#[test]
fn f3_glob_use_file_takes_no_lane() {
    let result = verify_src("f3", "f3_glob_use", SRC_F3_GLOB_USE);
    assert_error_message(result, "f3_glob_use", &[DEREF_WRITE_REFUSAL, "* r"]);
}

#[test]
fn f4_local_macro_body_takes_no_lane() {
    let result = verify_src("f4", "f4_local_macro", SRC_F4_LOCAL_MACRO);
    assert_error_message(result, "f4_local_macro", &[DEREF_WRITE_REFUSAL, "* r"]);
}

fn assert_file_gated(tmp_id: &str, func: &str, src: &str, needles: &[&str]) {
    assert_error_message(verify_src(tmp_id, func, src), func, needles);
}

#[test]
fn f5_raw_insert_trait_file_takes_no_lane() {
    assert_file_gated("f5r", "f5_raw_insert_trait_read", SRC_F5, &[LOWER_INSERT]);
    assert_file_gated(
        "f5o",
        "f5_raw_insert_trait_owner",
        SRC_F5,
        &[DEREF_WRITE_REFUSAL, "`* r`"],
    );
}

#[test]
fn f6_raw_get_or_insert_trait_file_takes_no_lane() {
    assert_file_gated(
        "f6",
        "f6_raw_get_or_insert_trait_read",
        SRC_F6,
        &[LOWER_GET_OR_INSERT],
    );
}

#[test]
fn f7_raw_enum_option_file_takes_no_lane() {
    assert_file_gated("f7", "f7_raw_enum_option", SRC_F7, &[LOWER_INSERT]);
}

#[test]
fn f8_path_derive_file_takes_no_lane() {
    assert_file_gated("f8r", "f8_derive_hijack_read", SRC_F8, &[LOWER_INSERT]);
    assert_file_gated(
        "f8o",
        "f8_derive_hijack_owner",
        SRC_F8,
        &[DEREF_WRITE_REFUSAL, "`* r`"],
    );
}

#[test]
fn f9_path_attribute_macro_file_takes_no_lane() {
    assert_file_gated("f9", "f9_attr_macro_hijack", SRC_F9, &[LOWER_GET_OR_INSERT]);
}

#[test]
fn f10_body_macro_hazards_take_no_lane() {
    assert_file_gated(
        "f10p",
        "f10_body_path_macro",
        SRC_F10,
        &["Unsupported hijack!()", UNSUPPORTED_MACRO],
    );
    assert_file_gated(
        "f10t",
        "f10_body_attr_in_macro_tokens",
        SRC_F10,
        &["Unsupported thread_local!()", UNSUPPORTED_MACRO],
    );
}

#[test]
fn f11_builtin_derive_file_keeps_lane() {
    let result = verify_src("f11c", "f11_builtin_derive_file_control", SRC_F11);
    assert!(
        matches!(result, VerifyResult::Verified),
        "f11_builtin_derive_file_control should verify, got: {result:?}"
    );
    match verify_src("f11l", "f11_builtin_derive_file_liar", SRC_F11) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(obligation_name.contains("assertion_0"), "{obligation_name}"),
        other => panic!("f11_builtin_derive_file_liar should be a Counterexample, got: {other:?}"),
    }
}

/// f12-f14 (H3): a file that can make a PRIMITIVE type spelling denote a
/// different type takes no lane. f12 is the measured liar.
#[test]
fn f12_primitive_rename_file_takes_no_lane() {
    // 2026-09-18: `f12_rename_use_liar` now fails closed EARLIER and on a
    // SECOND, independent arm — `use core::primitive::u8 as u64;` makes `u64`
    // an IMPORTED name that spells a width-bearing primitive, so the `let`
    // annotation width carry refuses `let z: u64 = 100;` outright rather than
    // reaching the lowering refusal. The measured liar stays refused; only the
    // arm that catches it moved.
    assert_file_gated(
        "f12u",
        "f12_rename_use_liar",
        SRC_F12_PRIMITIVE_RENAME,
        &[
            "`let` annotation width carry: a `let` type annotation this extraction cannot \
             resolve to a primitive carries an unsuffixed numeric literal",
        ],
    );
    assert_file_gated(
        "f12c",
        "f12_rename_cast_liar",
        SRC_F12_PRIMITIVE_RENAME,
        &["collection operation 'insert' requires a collection receiver, got 'Option<u8>'"],
    );
    assert_file_gated(
        "f12r",
        "f12_rename_read_control",
        SRC_F12_PRIMITIVE_RENAME,
        &["collection operation 'insert' requires a collection receiver, got 'Option<u8>'"],
    );
}

#[test]
fn f13_primitive_type_alias_file_takes_no_lane() {
    assert_file_gated(
        "f13",
        "f13_type_alias_shadow",
        SRC_F13_PRIMITIVE_TYPE_ALIAS,
        &["collection operation 'insert' requires a collection receiver, got 'Option<u8>'"],
    );
}

#[test]
fn f14_primitive_generic_param_file_takes_no_lane() {
    assert_file_gated(
        "f14",
        "f14_generic_shadow",
        SRC_F14_PRIMITIVE_GENERIC,
        &["collection operation 'insert' requires a collection receiver, got 'Option<u8>'"],
    );
}

/// f15 (H3, CONTROL): the std/core/alloc rooting rule is unchanged — a `use`
/// that binds no primitive type name keeps the lane on.
#[test]
fn f15_plain_std_use_file_keeps_lane() {
    let result = verify_src("f15c", "f15_plain_std_use_control", SRC_F15_PLAIN_STD_USE);
    assert!(
        matches!(result, VerifyResult::Verified),
        "f15_plain_std_use_control should verify, got: {result:?}"
    );
    match verify_src("f15l", "f15_plain_std_use_liar", SRC_F15_PLAIN_STD_USE) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(obligation_name.contains("assertion_0"), "{obligation_name}"),
        other => panic!("f15_plain_std_use_liar should be a Counterexample, got: {other:?}"),
    }
}

// ------------------------------------------------- restored HEAD verdicts

/// e1-e9 are runtime-true bodies HEAD verifies although they carry a refused
/// candidate (review 2026-09-17, REGRESSION under the retired eager refusal).
#[test]
fn e_restored_head_controls_verify() {
    for func in [
        "e1_alias_moved",
        "e2_alias_call_argument",
        "e3_alias_closure",
        "e4_alias_method_receiver",
        "e5_owner_shadowed",
        "e6_mut_alias_binding",
        "e7_let_in_block",
        "e8_unsuffixed_argument",
        "e9_param_receiver",
    ] {
        assert_verified(func);
    }
}

#[test]
fn e_restored_head_liars_refuted() {
    for func in [
        "e1l_alias_moved",
        "e2l_alias_call_argument",
        "e3l_alias_closure",
        "e4l_alias_method_receiver",
        "e5l_owner_shadowed",
        "e6l_mut_alias_binding",
        "e7l_let_in_block",
        "e8l_unsuffixed_argument",
        "e9l_param_receiver",
    ] {
        assert_counterexample(func, "assertion_0");
    }
}

// ------------------------------------------------------------- non-hijack

/// n1 / n2 pin HEAD's outcome (measured with a lens built from the untouched
/// tree, 2026-09-17): the HashSet insert result keeps HEAD's encode refusal,
/// the two-argument Vec insert keeps verifying.
#[test]
fn n1_hashset_insert_untouched() {
    let result = verify("n1_hashset_insert");
    assert_error_message(
        result,
        "n1_hashset_insert",
        &["assertion operand must encode to a Bool term"],
    );
}

#[test]
fn n2_vec_insert_untouched() {
    assert_verified("n2_vec_insert");
}

// ---------------------------------------------------------- runtime twins

#[test]
#[allow(
    unused_variables,
    unused_assignments,
    unused_mut,
    dead_code,
    clippy::bool_comparison,
    clippy::nonminimal_bool,
    clippy::overly_complex_bool_expr
)]
#[expect(
    clippy::unnecessary_literal_unwrap,
    reason = "The twin executes the same Option extraction as the verifier regression."
)]
#[expect(
    clippy::needless_late_init,
    reason = "The twin preserves deferred initialization whose type propagation is tested."
)]
#[expect(
    clippy::neg_cmp_op_on_partial_ord,
    reason = "The twin preserves the exact negated float comparison tested by the verifier."
)]
#[expect(
    clippy::unnecessary_cast,
    reason = "The twin tests a primitive alias cast whose written type differs from its resolved type."
)]
#[expect(
    clippy::identity_op,
    reason = "The twin preserves the exact arithmetic expression tested by the verifier."
)]
#[expect(
    clippy::let_and_return,
    reason = "The twin preserves the local binding and return shape tested by the verifier."
)]
#[expect(
    clippy::assign_op_pattern,
    reason = "The twin preserves the direct assignment syntax tested by the verifier."
)]
fn runtime_twins_execute_std_behavior() {
    // c1 / l1
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        assert!(*r == 20u64);
        assert!(!(*r == 21u64));
    }
    // c2 / l2
    {
        let mut x = Some(5u64);
        let r = x.insert(20u64);
        assert!(*r == 20u64);
        assert!(!(*r == 5u64));
    }
    // c3 / l3
    {
        let mut x = Option::<u64>::None;
        let r = x.get_or_insert(20u64);
        assert!(*r == 20u64);
        assert!(!(*r == 5u64));
    }
    // c4 / l4
    {
        let mut x = Some(5u64);
        let r = x.get_or_insert(20u64);
        assert!(*r == 5u64);
        assert!(!(*r == 20u64));
    }
    // c5 / l5
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        *r = 21u64;
        assert!(x == Some(21u64));
        assert!(!(x == Some(20u64)));
    }
    // c6 / l6
    {
        let mut x = Some(5u64);
        let r = x.get_or_insert(20u64);
        *r = 21u64;
        assert!(x == Some(21u64));
        assert!(!(x == Some(5u64)));
    }
    // c7 / l7
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        *r = 21u64;
        *r = 22u64;
        assert!(*r == 22u64);
        assert!(x == Some(22u64));
        assert!(!(x == Some(21u64)));
    }
    // c8 / l8
    {
        let mut x = Option::<u64>::None;
        let _r = x.insert(20u64);
        assert!(x == Some(20u64));
        assert!(x.is_some());
        assert!(!x.is_none());
    }
    // c9 / l9
    {
        let mut x = Some(false);
        let r = x.insert(true);
        assert!(*r == true);
        *r = false;
        assert!(x == Some(false));
        assert!(!(x == Some(true)));
    }
    // c10 / l10 (l10 panics at runtime: 250u8 + 10u8 overflows)
    {
        let mut x: Option<u8> = None;
        let r = x.insert(250u8);
        assert!(*r == 250u8);
        let y = *r + 5u8;
        assert!(y == 255u8);
        assert!(r.checked_add(10u8).is_none());
        let v = *r;
        assert!(std::panic::catch_unwind(move || v + std::hint::black_box(10u8)).is_err());
    }
    // c11 / l11
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        let y = *r + 1u64;
        assert!(y == 21u64);
        assert!(!(y == 20u64));
    }
    // c12 / l12
    {
        let mut a = Some(5usize);
        let r = a.insert(7usize);
        assert!(*r == 7usize);
        assert!(!(*r == 8usize));
        let mut b = Option::<usize>::None;
        let s = b.get_or_insert(9usize);
        assert!(*s == 9usize);
    }
    // g29 (the re-keyed i32 half of the old c12): std behaviour is unchanged,
    // the LANE simply refuses it.
    {
        let mut a = Some(5i32);
        let r = a.insert(7i32);
        assert!(*r == 7i32);
    }
    // h1a / h1b: the dropped-annotation hole the lane used to make reachable.
    // `let y: Option<u8> = Some(200)` is a `u8` at runtime, so `y.unwrap() +
    // 100` OVERFLOWS — the claim `== 300` the lane verified is false.
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        let y: Option<u8> = Some(200);
        let z = y.unwrap();
        assert!(*r == 20u64);
        assert!(z.checked_add(100).is_none());
    }
    // g37 (H1b round 3): a later BARE ascription types the defaulted literal,
    // so the shift is u8 arithmetic — `200u8 << 1 == 144`, and `y << 1 > 200`
    // is FALSE with no panic (the model read i32 and got 400).
    {
        let y = 200;
        let _q: u8 = y;
        assert!(core::mem::size_of_val(&y) == 1usize);
        assert!(y << 1 == 144u8);
        assert!(!(y << 1 > 200u8));
    }
    // g38: the type comes from a free-fn argument alone; `y + 100` overflows.
    {
        fn takes_u8(v: u8) -> u8 {
            v
        }
        let y = 200;
        let _q = takes_u8(y);
        assert!(core::mem::size_of_val(&y) == 1usize);
        assert!(y.checked_add(100).is_none());
    }
    // g40 / g43: the literal is typed one hop away (`Some(k)`, or a deferred
    // `y = Some(200)`), and `z + 100` overflows a u8 either way.
    {
        let k = 200;
        let y: Option<u8> = Some(k);
        let z = y.unwrap();
        assert!(core::mem::size_of_val(&k) == 1usize);
        assert!(z.checked_add(100).is_none());
        let w: Option<u8>;
        w = Some(200);
        let v = w.unwrap();
        assert!(v.checked_add(100).is_none());
    }
    // g45 / c23 / l23 (FLOATS): a defaulted float narrowed to `f32` by a later
    // ascription rounds `y + 1.0` back to `y`, so `y + 1.0 > y` is FALSE while
    // the `f64` the model used would make it true.
    {
        let y = 16777216.0;
        let _q: f32 = y;
        assert!(core::mem::size_of_val(&y) == 4usize);
        assert!(!(y + 1.0 > y));
        assert!(y + 1.0 == y);
        let d: f64 = 16777216.0;
        assert!(d + 1.0 > d);
    }
    // h3: `use core::primitive::u8 as u64;` makes the file's `u64` a `u8`, so
    // `y + z` overflows where a real `u64` would not.
    {
        use core::primitive::u8 as u64;
        let mut x = Option::<u8>::None;
        let r = x.insert(200u8);
        let y: u64 = *r as u64;
        let z: u64 = 100;
        assert!(core::mem::size_of::<u64>() == 1usize);
        assert!(y.checked_add(z).is_none());
    }
    // c13 / l13
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        *r = 21u64;
        x = Option::<u64>::None;
        assert!(x.is_none());
        assert!(!(x == Some(21u64)));
    }
    // c14 / l14
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        assert!(*r == 20u64);
        let s = x.insert(30u64);
        assert!(*s == 30u64);
        assert!(x == Some(30u64));
        assert!(!(x == Some(20u64)));
    }
    // c15 / l15
    for b in [false, true] {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        *r = 21u64;
        let mut y = 0u64;
        if b {
            y = 1u64;
        }
        assert!(x == Some(21u64));
        assert!(y <= 1u64);
        assert!(!(x == Some(20u64)));
    }
    // c16 / l16 (l16 panics at runtime: u64::MAX + 1 overflows)
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(18446744073709551615u64);
        let y = *r + 0u64;
        assert!(y == *r);
        assert!(r.checked_add(1u64).is_none());
        let v = *r;
        assert!(std::panic::catch_unwind(move || v + std::hint::black_box(1u64)).is_err());
    }
    // c17 / l17
    {
        let x_other = 3u64;
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        assert!(*r == 20u64 && x_other == 3u64);
        assert!(!(*r == 21u64 || x_other == 4u64));
    }
    // c18 / l18
    {
        fn owner_returned() -> Option<u64> {
            let mut x = Option::<u64>::None;
            let r = x.insert(1u64);
            *r = 2u64;
            x
        }
        assert!(owner_returned() == Some(2u64));
        assert!(!(owner_returned() == Some(1u64)));
    }
    // c19 / l19
    {
        fn early_return(b: bool) -> u64 {
            let mut x = Option::<u64>::None;
            let r = x.insert(5u64);
            if b {
                return 7u64;
            }
            *r = 8u64;
            let v = *r;
            v
        }
        for b in [false, true] {
            let result = early_return(b);
            assert!(result == 8u64 || result == 7u64);
        }
        assert!(!(early_return(false) == 7u64));
    }
    // c20 / l20
    {
        let mut a = Option::<u64>::None;
        let mut b = Option::<u64>::None;
        let r = a.insert(1u64);
        let s = b.insert(2u64);
        *r = 3u64;
        *s = 4u64;
        assert!(a == Some(3u64));
        assert!(b == Some(4u64));
        assert!(!(a == Some(4u64)));
    }
    // c24 / l24 (POINTER WIDTH): `u32::MAX` is a legal `usize` literal at BOTH
    // widths, so this twin executes on any host. g47 / g48 have no twin here:
    // their literals do not compile at 32-bit `usize` / `isize`, and this
    // binary is built at the host width only.
    {
        let mut x = Option::<usize>::None;
        let r = x.insert(4294967295usize);
        assert!(*r == 4294967295usize);
        assert!(!(*r == 4294967294usize));
    }
    // g1 (both claims are about a requires(is_some) param: `*r` is its payload)
    {
        let mut x = Some(3u64);
        let r = x.get_or_insert(20u64);
        assert!(*r == 3u64);
    }
    // g2 (runtime-true for both branches)
    for b in [false, true] {
        let mut x = Option::<u64>::None;
        if b {
            x = Some(5u64);
        }
        let r = x.get_or_insert(20u64);
        assert!(*r >= 5u64);
    }
    // g3 / g4 / g6 (runtime-true shapes that are refused)
    {
        let mut x = None::<u64>;
        let r = x.insert(20u64);
        assert!(*r == 20u64);
        let mut z = Option::<u64>::None;
        let q = z.insert(20);
        assert!(*q == 20u64);
    }
    // g5: the declared u8 owner payload is 200, not an i32.
    {
        let mut x: Option<u8> = Some(200);
        let r = x.get_or_insert(5u8);
        assert!(*r == 200u8);
        assert!(r.checked_add(100u8).is_none());
    }
    // g7 / g8 / g9 / g28
    {
        let mut x = Option::<u64>::None;
        {
            let r = x.insert(20u64);
            assert!(*r == 20u64);
        }
        let mut i = 0u64;
        while i < 3u64 {
            let mut r = x.insert(20u64);
            assert!(*r == 20u64);
            i += 1u64;
        }
    }
    // g13 / g14 / g15 / g19 / g20 / g21 / g22 / g23 (escapes and writes)
    {
        fn takes(v: &mut u64) {
            *v = 0u64;
        }
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        takes(r);
        assert!(*r == 0u64);
        assert!(r.checked_add(1u64) == Some(1u64));
        let q = &mut *r;
        *q = 9u64;
        assert!(*r == 9u64);
        *r += 1u64;
        assert!(*r == 10u64);
        *r = *r + 1u64;
        assert!(*r == 11u64);
        *r = 21;
        assert!(*r == 21u64);
        for b in [false, true] {
            if b {
                *r = 22u64;
            }
        }
        assert!(*r >= 20u64);
        let mut i = 0u64;
        while i < 3u64 {
            *r = 21u64;
            i += 1u64;
        }
        assert!(*r == 21u64);
        assert!(x == Some(21u64));
    }
    // g16 / g17 / g18 / g24 / g25 / g26 / g27
    {
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        if let Some(v) = Some(*r) {
            assert!(v == 20u64);
        }
        let c = || *r;
        assert!(c() == 20u64);
        let h = (r, 1u64);
        assert!(h.1 == 1u64);
        let r = 1u64;
        assert!(r == 1u64);
        let mut c = || {
            x = None;
        };
        c();
        assert!(x.is_none());
        let y = &mut x;
        let r = y.insert(20u64);
        assert!(*r == 20u64);
    }
    // f1: the file-local by-value trait method wins resolution.
    {
        trait Tr {
            fn insert(self, v: u64) -> u64;
        }
        impl Tr for Option<u64> {
            fn insert(self, _v: u64) -> u64 {
                777u64
            }
        }
        #[allow(unused_mut)]
        let mut x = Some(5u64);
        let r = x.insert(20u64);
        assert!(r == 777u64);
        assert!(x == Some(5u64));
        assert!(!(x == Some(20u64)));
    }
    // f5: the raw-identifier by-value trait method wins resolution too.
    {
        trait Tr {
            fn r#insert(self, v: u64) -> &'static mut u64;
        }
        impl Tr for Option<u64> {
            fn r#insert(self, _v: u64) -> &'static mut u64 {
                Box::leak(Box::new(777u64))
            }
        }
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        assert!(!(*r == 20u64));
        *r = 21u64;
        assert!(x.is_none());
        assert!(!(x == Some(21u64)));
    }
    // f6: raw `r#get_or_insert`.
    {
        trait TrG {
            fn r#get_or_insert(self, v: u64) -> &'static mut u64;
        }
        impl TrG for Option<u64> {
            fn r#get_or_insert(self, _v: u64) -> &'static mut u64 {
                Box::leak(Box::new(777u64))
            }
        }
        let mut x = Some(5u64);
        let r = x.get_or_insert(20u64);
        assert!(!(*r == 5u64));
    }
    // f8: the expansion `#[derive(hjd::Hijack)]` emitted (measured with a
    // real proc-macro crate): a plain-named by-value trait method.
    {
        trait HijackInsertD {
            fn insert(self, v: u64) -> &'static mut u64;
        }
        impl HijackInsertD for Option<u64> {
            fn insert(self, _v: u64) -> &'static mut u64 {
                Box::leak(Box::new(777u64))
            }
        }
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        assert!(!(*r == 20u64));
        *r = 21u64;
        assert!(!(x == Some(21u64)));
    }
    // f11: builtin derives change nothing.
    {
        #[derive(Clone, Copy, Debug, PartialEq)]
        struct Plain(u64);
        let _ = Plain(1u64);
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        assert!(*r == 20u64);
        assert!(!(*r == 21u64));
    }
    // e1-e9 and their liars (runtime-true controls; each liar's claim is
    // false for some input).
    {
        fn takes(v: &mut u64) {
            *v = 0u64;
        }
        for b in [false, true] {
            let mut x = Some(5u64);
            let r = x.insert(20u64);
            let q = r;
            assert!(b || !b);
            assert!(!(b && !b));
        }
        let mut refuted_by_false = 0usize;
        for b in [false, true] {
            // e2 / e2l
            let mut x = Option::<u64>::None;
            let r = x.insert(20u64);
            takes(r);
            // e3 / e3l
            let mut x = Option::<u64>::None;
            let r = x.insert(20u64);
            let c = || *r;
            // e4 / e4l
            let mut x = Option::<u64>::None;
            let r = x.insert(20u64);
            let y = r.checked_add(1u64);
            // e7 / e7l
            let mut x = Option::<u64>::None;
            {
                let r = x.insert(20u64);
                let k = *r;
            }
            // e8 / e8l
            let mut x = Option::<u64>::None;
            let r = x.insert(20);
            let k = *r;
            // e9 / e9l
            let mut p: Option<u64> = if b { Some(1u64) } else { None };
            let r = p.insert(20u64);
            let k = *r;
            if !b {
                refuted_by_false += 1;
            }
        }
        assert!(refuted_by_false == 1usize);
        // e5 / e5l
        let mut x = Option::<u64>::None;
        let r = x.insert(20u64);
        let x = 5u64;
        let k = *r;
        assert!(x == 5u64);
        assert!(!(x == 6u64));
        // e6 / e6l
        let mut x = Option::<u64>::None;
        let mut r = x.insert(20u64);
        let k = 1u64;
        let _z = &mut r;
        assert!(k == 1u64);
        assert!(!(k == 2u64));
    }
}
