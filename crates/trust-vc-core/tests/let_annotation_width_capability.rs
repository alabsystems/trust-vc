// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN + CAPABILITY (`let` ANNOTATION WIDTH CARRY, 2026-09-18).
//!
//! THE HOLE, measured on a HEAD lens built from the untouched tree at
//! `bbb3250b` (ay 0.27.0@`c1dd8ecb`, stock lane). `vc_extraction` recorded a
//! `let` type ascription ONLY for a bare primitive-integer binding, so every
//! COMPOSITE ascription dropped its width: the initializer's literals kept
//! Rust's `i32` default and later element arithmetic was discharged at 32 bits
//! while the program panics at the declared width. THIRTEEN of the twenty
//! shape controls VERIFIED at HEAD and are `Counterexample` here — the ledger's
//! open 2026-09-16 row (`let v: Vec<u8> = vec![200]; v[0usize] + 100u8`) among
//! them — and ELEVEN more moved from a false `Verified` to a PRECISE REFUSAL.
//! (Re-counted 2026-09-18 against a HEAD lens over EVERY one of this file's
//! fixtures, not just `SRC`. The thirteen: c1, c2, c4, c6, c7, c8, c9, c14,
//! c16, c17, c18, c19, c20 — c3, c5, c10, c11, c12, c13 and c15 were already
//! refuted at HEAD. The eleven refusals: g3, g4, g6, g7, g8, g10, g11 in `SRC`,
//! g1 / g2 in `SRC_IMPORTED`, g12 in `SRC_SHADOWED_SOME`, g19 in
//! `SRC_BODY_SCOPE`. Two earlier counts were wrong and are recorded so the
//! mistake is not repeated: "eleven" for the first number omitted c4 and c20,
//! and "seven" for the second was scoped to `SRC` alone while the first number
//! deliberately spanned fixtures. A further ELEVEN correct `Counterexample`s
//! became fail-closed refusals — g9, g13, g14, g15, g16, g17, g18, g20, g21,
//! g22, g23 — and seven more false `Verified`s became `Counterexample`s outside
//! the shape set: l4, c22, c23's overflow sibling, g14n, n9, n10 and
//! `r3_glob_leading_colon_primitive`. 42 functions move in all.)
//!
//! THE MECHANISM IS THE EXISTING CHANNEL. `vec![200u8]` and `Some(200u8)` were
//! ALREADY refuted correctly at HEAD, because a source suffix survives into the
//! rendered obligation text and is re-read by
//! `ir_lowering::atoms::type_from_int_suffix`. So the fix re-spells the broken
//! spellings as the spellings that already work — no IR, encoder or type
//! channel change. See `vc_extraction::declared_width` for the walk, its five
//! refusal arms and the soundness argument.
//!
//! ROUND 5 (2026-09-18) CUT THE ADMISSION BACK TO A CLOSED WORLD, and that is
//! the headline of this file now. Four review rounds had each closed one more
//! way for a type name to be bound where a file-scope scan cannot see it — a
//! nested `mod`, a glob, a body-scope `use`, a captured `core::primitive::`
//! prefix — each by REFUSING that shape. Round 5 found four more, and one
//! measurement ended the method: a `#[derive(..)]` or an attribute proc macro
//! injects `pub type u32 = u64;` into the enclosing module (measured with a
//! dependency-free proc-macro crate: `size_of::<u32>()` is 8), and inertness of
//! an attribute is NOT syntactically decidable — so the escape set cannot be
//! enumerated and a denylist can never be finished.
//!
//! The lane therefore runs ONLY over files built from a fixed MODELLED set of
//! constructs, and any other construct turns it OFF for the whole file (carry
//! nothing, refuse nothing, HEAD's rendering byte-for-byte). The four round-5
//! findings, each measured on an `fv3` lens pair (dev tree vs a pristine
//! `bbb3250b` export, separate target dirs, non-vacuous) with a stock-rustc
//! twin at `-C overflow-checks=on` for truth:
//! * g26 / g27 — an item-position `macro_rules!` INVOCATION rebinds a primitive
//!   file-wide (`elem_bytes=4`); `Verified` on a panicking program, and in the
//!   narrow direction a REFUTED TRUE claim.
//! * g28 / g29 / g30 — `extern crate self as core;` captures the EXTERN
//!   PRELUDE, so `::core::primitive::u64` is captured too (`lead_bytes=4`).
//!   This retires the leading-`::` escape hatch that r3 used to keep.
//! * g31 — a macro-generated `Vec` alias reprojects the element even when the
//!   LEAF is the uncapturable `::core::primitive::u64`, which is why a
//!   leaf-only escape hatch cannot be sound.
//! * g24 / g25 — a FILE-scope alias read for a function written inside an
//!   inline `mod`, which does not see the file's items at all.
//!
//! WHAT THIS FILE PINS — 78 tests: 33 assert a `Counterexample`, 24 a
//! fail-closed refusal with its exact arm needle, 11 a `Verified`, 3 assert
//! several verdicts across one fixture, and 7 assert a shape directly
//! (unchanged rendering, a twin, a census) — of which g16 (a
//! `Counterexample`), g27, g30 and r5 (a `Verified` each) now pin a lane-off
//! refusal instead (§5b rule 12). By role: 23 controls (c1-c23), 4 liars
//! (l1-l4), 12 narrowness (n1-n12), 33 gated/closed-world (g1-g31 plus the
//! g2n / g9n pins), 5 residuals (r1-r5), 1 runtime-twins.
//! * CONTROLS c1-c20: every shape whose width is now carried. Each is written
//!   in BOTH peer spellings where the peer matters (`+ 100u8` AND `+ 100`),
//!   because a suffixed-peer-only probe set reads the hole as half its size.
//! * CONTROLS c21-c23: the RESTORED REGRESSION. The wall first shipped here
//!   fired on `Some(200 + 50)` and seven sibling spellings — TRUE claims HEAD
//!   verified, refused for no soundness gain. Constant integer arithmetic is
//!   decided by the annotation and is carried; c22 and c23's overflowing
//!   sibling pin that the width really does survive the fold.
//! * LIARS l1-l4: claims that must NEVER verify, including the
//!   ENCODER-INTERACTION liar (a body where the peer-coercion heuristic used to
//!   narrow and an explicit suffix now applies) — a suffix can only NARROW the
//!   width an obligation is discharged at, so no verdict may move
//!   `Counterexample` -> `Verified`.
//! * NARROWNESS n1-n12: in-range arithmetic across `Vec`, array, tuple,
//!   `Option`, `usize`, `i32`, `f32`, a user type and a literal-free
//!   initializer, plus the two round-5 pins that keep the CLOSED WORLD from
//!   swallowing ordinary code — a bare primitive under an inline `mod` (n11)
//!   and the nine language-defined derives (n12). None of them may turn into a
//!   refusal; the current `i32` default buys NO completeness on safe code, so a
//!   fix has to protect exactly these.
//! * GATED g1-g23: one per refusal arm, with the exact pinned text, each paired
//!   with the adjacent legal spelling. g3 / g4 / g6 are the wall's REAL domain,
//!   a NON-CONSTANT operand, and the trade they make is measured rather than
//!   argued: `let z = 200; let v: Vec<u8> = vec![z + 50]; v[0usize] + 100u8`
//!   and its `Option` and `if`-payload siblings are HEAD false `Verified`s on
//!   programs that panic, and the wall is what closes them; the cost is that a
//!   TRUE claim with a suffixed peer (`let z = 50u8; Some(z + 50)`) is refused
//!   too, because this file alone cannot show the `+` is the primitive impl.
//!   g14-g31 pin the SCOPE of the name table, and every one of them is a
//!   MEASURED false `Verified` (or a correct `Counterexample` the carry was
//!   about to overturn) before its fix: a nested `mod` rebinding (g14 / g15), a
//!   file-scope glob (g16 — refused, since a glob disarms the file and a
//!   lane-off all-literal composite is bound at no width), a `use`
//!   written inside a function body or a nested block (g17 / g18 / g19 / g20 —
//!   the ordinary multi-file-crate spelling, invisible to a table built from
//!   FILE items), a captured `core::primitive::` PREFIX (g21 / g22 / g23), a
//!   file alias read across an inline `mod` boundary in both directions
//!   (g24 / g25), an item-position macro INVOCATION (g26 / g27), an
//!   `extern crate` capture of the extern prelude (g28 / g29 / g30) and a
//!   macro-generated `Vec` alias (g31). Their narrowness pins are n9, n10, n11
//!   and n12.
//! * RESIDUALS r1-r5: the five scoping limits this increment does NOT close —
//!   no file context, a bare `f32` container, a file-scope glob, a body-scope
//!   glob, and (new in round 5) any file the CLOSED WORLD does not admit, of
//!   which a third-party `#[derive]` is the commonest spelling — recorded as
//!   measured facts rather than claimed closed. In every one of them the lane
//!   declines, it does not worsen, and HEAD's pre-existing false `Verified`
//!   no longer stands in r3, r4 and r5: an all-unsuffixed-literal composite
//!   under a fixed-width ascription in a file that does not decide widths is
//!   REFUSED at the let-binding marker (design-trust-proof-backend.md §5b
//!   rule 12 — its `i32` placeholder reading is no width at all), and so are
//!   g27's and g30's narrow twins (TRUE claims, refused rather than refuted).
//!   In r3 and r4 the file also spells `Vec` where a glob from outside the
//!   file reaches, so the type-name rule (`vc_extraction::type_name_rebinding`)
//!   would refuse a `Verified` answer as well.
//!   The glob residual reaches LESS far than first claimed: 5 of the 167
//!   `evals/verus/ported` files carry any glob, exactly 1 mentions
//!   `vstd::prelude`, and 0 corpus sites hold the shape this lane can reach.
//! * `runtime_twins_execute_std_behavior`: every control's and liar's truth
//!   value executed under stock rustc, with `checked_*` so the pin does not
//!   depend on the debug profile.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify_src(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_letann_{}_{}.rs", std::process::id(), tmp_id));
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

fn verify(func: &str) -> VerifyResult {
    verify_src(func, func, SRC)
}

/// A shape whose declared width the extractor now carries: the obligation is
/// discharged at the DECLARED width, so the overflow the program suffers is
/// found. `Verified` here is the false verify this increment exists to close.
fn assert_counterexample(func: &str) {
    let result = verify(func);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{func} must be refuted at its declared width; got {result:?}"
    );
}

fn assert_counterexample_in(src: &str, func: &str) {
    let result = verify_src(func, func, src);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{func} must be refuted at its declared width; got {result:?}"
    );
}

/// A lane-OFF shape whose element width cannot be known: `vec![3000000000]`
/// renders untyped, so the sequence literal's element type is the `i32`
/// placeholder its first element carries — a type that cannot hold 3000000000.
/// The element is then refused (design-trust-proof-backend.md §5b rules 10-11:
/// a value is bound only at a type that holds it). HEAD refuted these by
/// reading 3000000000 WRAPPED in `i32` — the right verdict for the wrong
/// reason. What must hold is that the panicking program is never `Verified`.
fn assert_refuted_or_refused_in(src: &str, func: &str) {
    let result = verify_src(func, func, src);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. })
            || (!result.is_verified() && (result.is_unknown() || result.is_error())),
        "{func} must be refuted or refused, never verified; got {result:?}"
    );
}

/// A TRUE claim this file cannot give a width to: refused, never refuted.
fn assert_refused_in(src: &str, func: &str) {
    let result = verify_src(func, func, src);
    assert!(
        !result.is_verified() && (result.is_unknown() || result.is_error()),
        "{func} must be refused; got {result:?}"
    );
}

fn assert_verified(func: &str) {
    let result = verify(func);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{func} must keep verifying; got {result:?}"
    );
}

/// The let-binding marker's refusal of a lane-off all-literal composite: its
/// literals reach the marker at the `i32` placeholder, which is no width at
/// all (§5b rule 12). The marker says "cannot hold" for an ascription it
/// resolves and "cannot bind" for one it does not (`Vec<core::primitive::u8>`
/// in a glob file); both name the placeholder-typed value.
const LANE_OFF_LITERAL: &str = "a value of type `Seq<i32>`";

fn assert_gated_in(src: &str, func: &str, needles: &[&str]) {
    let result = verify_src(func, func, src);
    let VerifyResult::Error { message } = &result else {
        panic!("{func} must fail closed with an Error; got {result:?}");
    };
    for needle in needles {
        assert!(
            message.contains(needle),
            "{func} refusal must contain {needle:?}; got {message}"
        );
    }
}

fn assert_gated(func: &str, needles: &[&str]) {
    assert_gated_in(SRC, func, needles);
}

/// The common prefix of every arm, so one needle proves the refusal came from
/// this lane and not from an unrelated fail-closed path.
const PREFIX: &str = "`let` annotation width carry: ";
const ERR_UNDECIDED: &str = "a `let` type annotation this extraction cannot resolve to a primitive carries an unsuffixed numeric literal";
const ERR_WALL: &str = "an unsuffixed numeric literal sits inside an expression the declared-width walk does not model, at a position whose `let` annotation fixes a non-default integer width";
const ERR_RANGE: &str = "an integer literal does not fit the width its `let` annotation declares";
const ERR_ARITY: &str = "the `let` annotation's shape and its initializer's shape disagree while a non-default integer width is in play";
const ERR_SHADOWED_CTOR: &str = "the `let` initializer's constructor is shadowed by a file item, so it need not be the `std` constructor whose payload type the annotation fixes";

// ---------------------------------------------------------------- CONTROLS

/// THE LEDGER'S OPEN 2026-09-16 ROW. `Verified` at HEAD; the program panics.
#[test]
fn c1_vec_u8_suffixed_peer_is_refuted() {
    assert_counterexample("c1_vec_u8_suffixed_peer");
}

/// The same body with a BARE peer — the spelling a suffixed-peer-only probe set
/// would have missed. Also `Verified` at HEAD.
#[test]
fn c2_vec_u8_bare_peer_is_refuted() {
    assert_counterexample("c2_vec_u8_bare_peer");
}

#[test]
fn c3_option_u8_is_refuted() {
    assert_counterexample("c3_option_u8_suffixed_peer");
}

#[test]
fn c4_option_u8_bare_peer_is_refuted() {
    assert_counterexample("c4_option_u8_bare_peer");
}

#[test]
fn c5_nested_option_is_refuted() {
    assert_counterexample("c5_nested_option");
}

#[test]
fn c6_std_vec_path_is_refuted() {
    assert_counterexample("c6_std_vec_path");
}

#[test]
fn c7_vec_of_vec_is_refuted() {
    assert_counterexample("c7_vec_of_vec");
}

#[test]
fn c8_array_literal_is_refuted() {
    assert_counterexample("c8_array_literal");
}

/// The repeat form. Its LENGTH is `usize`-decided by rustc and must never take
/// the element suffix — `[200u8; 3]`, never `[200u8; 3u8]`.
#[test]
fn c9_array_repeat_is_refuted() {
    assert_counterexample("c9_array_repeat");
}

#[test]
fn c10_whole_tuple_is_refuted() {
    assert_counterexample("c10_whole_tuple");
}

#[test]
fn c11_tuple_destructuring_is_refuted() {
    assert_counterexample("c11_tuple_destructuring");
}

#[test]
fn c12_nested_tuple_is_refuted() {
    assert_counterexample("c12_nested_tuple");
}

#[test]
fn c13_shared_reference_is_refuted() {
    assert_counterexample("c13_shared_reference");
}

#[test]
fn c14_slice_reference_is_refuted() {
    assert_counterexample("c14_slice_reference");
}

/// A file-local `type` alias is RESOLVED, not refused.
#[test]
fn c15_scalar_alias_is_refuted() {
    assert_counterexample("c15_scalar_alias");
}

#[test]
fn c16_container_alias_is_refuted() {
    assert_counterexample("c16_container_alias");
}

#[test]
fn c17_vec_of_tuple_is_refuted() {
    assert_counterexample("c17_vec_of_tuple");
}

#[test]
fn c18_u16_array_is_refuted() {
    assert_counterexample("c18_u16_array");
}

/// DEFERRED INITIALISATION: the ascription and the value sit in different
/// statements, so the `let`-initializer funnel never sees the pair and the
/// ASSIGNMENT lane carries the width from the whole-function shape map.
#[test]
fn c19_deferred_vec_is_refuted() {
    assert_counterexample("c19_deferred_vec");
}

/// A file-local `type u64 = u8;` — the name spells a primitive it is NOT.
/// `Verified` at HEAD (the extractor read the SPELLING and rendered `200u64`);
/// the alias now decides it.
#[test]
fn c20_alias_shadowing_a_primitive_name_is_refuted() {
    let result = verify_src(
        "c20",
        "c20_alias_shadows_primitive",
        SRC_ALIAS_SHADOWS_PRIMITIVE,
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "an alias that spells `u64` but means `u8` must be refuted at 8 bits; got {result:?}"
    );
}

/// CONSTANT INTEGER ARITHMETIC IS DECIDED BY THE ANNOTATION — c21-c23.
///
/// A REGRESSION this increment introduced and then restored: the R2(b) wall
/// fired on `Some(200 + 50)`, `vec![100 + 50]`, `[100 + 50, 1]`, `(100 + 50,
/// 1)`, `&(100 + 50)`, `vec![-100 + 50]`, `Some(1 << 3)` and the deferred form
/// — EIGHT spellings that HEAD verified and whose claims are TRUE under stock
/// rustc (`100 + 50 == 150` fits `u8`; nothing overflows). Walling them off
/// traded a capability HEAD had for no soundness gain, so the walk descends
/// into arithmetic whose every leaf is an integer literal: no user `Add` impl
/// can apply there, and rustc's inference has exactly one choice.
#[test]
fn c21_constant_folded_payload_verifies() {
    assert_verified("c21_constant_folded_payload");
}

/// And the width really is carried THROUGH the fold: the same initializer with
/// an overflowing consumer is refuted, which the `i32` default would not be.
#[test]
fn c22_constant_folded_payload_overflow_is_refuted() {
    assert_counterexample("c22_constant_folded_payload_overflow");
}

/// A SHIFT's right operand is typed independently of the result (`1u8 << 3` has
/// an `i32` count), so it must never take the position's suffix — and the LEFT
/// operand must.
#[test]
fn c23_constant_shift_carries_only_the_left_operand() {
    assert_verified("c23_constant_shift_value");
    assert_counterexample("c23_constant_shift_overflow");
}

// ------------------------------------------------------------------- LIARS

#[test]
fn l1_wrong_element_value_never_verifies() {
    assert_counterexample("l1_wrong_element_value");
}

#[test]
fn l2_wrong_payload_bound_never_verifies() {
    assert_counterexample("l2_wrong_payload_bound");
}

#[test]
fn l3_wrong_tuple_element_never_verifies() {
    assert_counterexample("l3_wrong_tuple_element");
}

/// THE ENCODER-INTERACTION LIAR. `coerce_unsuffixed_literal` /
/// `infer_int_width` narrow a bare peer literal to its neighbour's width; where
/// an explicit suffix now applies it is the DECLARED truth, so a heuristic that
/// disagreed was wrong. Carrying more suffixes only REMOVES cases from those
/// heuristics, and no verdict may move `Counterexample` -> `Verified` through
/// the interaction.
#[test]
fn l4_peer_coercion_interaction_never_verifies() {
    assert_counterexample("l4_peer_coercion_interaction");
}

// -------------------------------------------------------------- NARROWNESS

#[test]
fn n1_in_range_vec_still_verifies() {
    assert_verified("n1_in_range_vec");
}

#[test]
fn n2_in_range_option_still_verifies() {
    assert_verified("n2_in_range_option");
}

#[test]
fn n3_usize_container_still_verifies() {
    assert_verified("n3_usize_container");
}

#[test]
fn n4_i32_container_still_verifies() {
    assert_verified("n4_i32_container");
}

#[test]
fn n5_i64_container_still_verifies() {
    assert_verified("n5_i64_container");
}

#[test]
fn n6_user_type_ascription_still_verifies() {
    assert_verified("n6_user_type_ascription");
}

#[test]
fn n7_literal_free_initializer_still_verifies() {
    assert_verified("n7_literal_free_initializer");
}

/// A name bound TWICE is absent from the shape map by construction, so the
/// deferred assignment keeps today's rendering rather than borrowing a shape
/// from a binding it might not denote. It must not silently carry.
#[test]
fn n8_name_bound_twice_does_not_carry() {
    let result = verify("n8_name_bound_twice");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "the twice-bound shape must not verify; got {result:?}"
    );
}

// ------------------------------------------------------------------- GATED

/// R2(a) UNDECIDED ON THE SPINE: an imported name this extraction cannot
/// resolve to a primitive. Refused, never defaulted.
#[test]
fn g1_imported_alias_scalar_gated() {
    assert_gated_in(
        SRC_IMPORTED,
        "g1_imported_alias_scalar",
        &[PREFIX, ERR_UNDECIDED],
    );
}

#[test]
fn g2_imported_alias_element_gated() {
    assert_gated_in(
        SRC_IMPORTED,
        "g2_imported_alias_element",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// Its narrowness pin: the adjacent FILE-LOCAL alias of the same shape resolves
/// and is refuted rather than refused (c15 / c16 above), and a suffixed literal
/// under the imported alias keeps today's handling.
#[test]
fn g2n_suffixed_literal_under_imported_alias_is_not_refused() {
    let result = verify_src("g2n", "g2n_suffixed_under_imported", SRC_IMPORTED);
    assert!(
        !matches!(result, VerifyResult::Error { .. }),
        "a suffixed literal carries its own width and must not be refused; got {result:?}"
    );
}

/// R2(b) WALL AT A WIDTH-BEARING POSITION — a NON-CONSTANT operand, which is
/// the case the wall actually owns. `z`'s type is not decided by this file, so
/// the `50` beside it is not either.
///
/// The wall used to fire on `Some(200 + 50)` too. That was a REGRESSION and is
/// restored at c21-c23: constant integer arithmetic IS decided by the
/// annotation, and eight such spellings are TRUE claims HEAD verified.
#[test]
fn g3_non_constant_operand_gated() {
    assert_gated("g3_non_constant_operand", &[PREFIX, ERR_WALL]);
}

#[test]
fn g4_non_constant_vec_element_gated() {
    assert_gated("g4_non_constant_vec_element", &[PREFIX, ERR_WALL]);
}

#[test]
fn g5_call_argument_element_gated() {
    assert_gated("g5_call_argument_element", &[PREFIX, ERR_WALL]);
}

/// The deferred-assignment half takes the same wall.
#[test]
fn g6_deferred_non_constant_payload_gated() {
    assert_gated("g6_deferred_non_constant_payload", &[PREFIX, ERR_WALL]);
}

/// R2(c) DOES NOT FIT — sign-aware, so `-128i8` passes and `128i8` does not.
#[test]
fn g7_out_of_range_payload_gated() {
    assert_gated("g7_out_of_range_payload", &[PREFIX, ERR_RANGE]);
}

#[test]
fn g8_out_of_range_signed_tuple_gated() {
    assert_gated("g8_out_of_range_signed_tuple", &[PREFIX, ERR_RANGE]);
}

#[test]
fn g9_negative_at_unsigned_leaf_gated() {
    assert_gated("g9_negative_at_unsigned_leaf", &[PREFIX, ERR_RANGE]);
}

/// Its narrowness pin: `-128` AT `i8` is in range and is carried, not refused.
#[test]
fn g9n_signed_minimum_is_carried_not_refused() {
    let result = verify("g9n_signed_minimum");
    assert!(
        !matches!(result, VerifyResult::Error { .. }),
        "`-128` fits `i8` and must be carried; got {result:?}"
    );
}

/// R2(d) SHAPE / ARITY DISAGREEMENT.
#[test]
fn g10_tuple_arity_mismatch_gated() {
    assert_gated("g10_tuple_arity_mismatch", &[PREFIX, ERR_ARITY]);
}

#[test]
fn g11_vec_ascription_array_initializer_gated() {
    assert_gated("g11_vec_ascription_array_initializer", &[PREFIX, ERR_ARITY]);
}

/// R2(e) SHADOWED CONSTRUCTOR: a file-declared `Some` makes the payload the
/// declared function's argument type, not the annotation's.
#[test]
fn g12_shadowed_some_constructor_gated() {
    assert_gated_in(
        SRC_SHADOWED_SOME,
        "g12_shadowed_some",
        &[PREFIX, ERR_SHADOWED_CTOR],
    );
}

/// A file-declared item named `u8` means the ascription does not spell the
/// primitive. HEAD rendered `200u8` against a unit struct; this refuses. A
/// refusal that FIXES a false claim rather than one that costs capability.
#[test]
fn g13_shadowed_primitive_name_gated() {
    assert_gated_in(
        SRC_SHADOWED_PRIMITIVE,
        "g13_shadowed_primitive",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// NESTED-MODULE REBINDING. The name table is built once per FILE and
/// `extract_verification_conditions_with_file_context` is handed no module
/// path, so a function inside `mod inner { type W = i32; }` must NOT be allowed
/// to read the file-scope `type W = i64;`. Resolving it against the file table
/// was a MEASURED false `Verified` on a program that panics at runtime (the
/// twin below); the name is `Undecided` in both directions instead.
#[test]
fn g14_nested_module_rebinding_gated() {
    assert_gated_in(
        SRC_NESTED_MODULE,
        "g14_nested_rebinding",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// The same for the nested-`use`-rename spelling of the rebinding.
#[test]
fn g15_nested_use_rename_gated() {
    assert_gated_in(
        SRC_NESTED_MODULE,
        "g15_nested_use_rename",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// g24 — THE CONVERSE AMBIGUITY, and the measured COST of closing it.
///
/// This case used to be the narrowness pin for g14/g15: `Byte` is rebound by
/// nobody, so the file-scope alias was resolved and the overflow refuted. Round
/// 5 measured the OTHER direction of the same ambiguity and it is a false
/// `Verified`, not a missed refutation: a function written INSIDE an inline
/// module does not see the FILE's items at all, so reading a file-scope alias
/// for it is a guess. `type u32 = ::core::primitive::u64; mod inner { fn f() {
/// let v: Vec<u32> = vec![3000000000]; … } }` carried `u64` while the
/// stock-rustc twin reports `inner elem_bytes=4` and the program panics
/// (`attempt to add with overflow`); the lens VERIFIED it and HEAD refuted it.
///
/// The table is built per FILE and `extract_verification_conditions_with_file_
/// context` is handed no module path, so neither direction can be decided —
/// and the fix is symmetric with g14/g15: once the file holds ANY inline
/// module, every FILE-DECLARED name is `Undecided`. `Byte` is the price, and it
/// is paid fail-closed. A module-path-aware table would buy it back; that is a
/// scoping change, not a name-resolution one.
#[test]
fn g24_file_alias_under_an_inline_module_is_gated() {
    assert_gated_in(
        SRC_NESTED_MODULE,
        "g14n_unrebound_alias",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// The soundness half of g24: the function INSIDE the module, whose annotation
/// the file-scope alias does not govern. `Verified` on a panicking program
/// before the fix.
#[test]
fn g25_nested_fn_reading_a_file_alias_is_gated() {
    assert_gated_in(
        SRC_NESTED_FN_ALIAS,
        "g25_nested_fn_file_alias",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// ... and its narrowness pin: a primitive the file does NOT declare is
/// unaffected in both scopes, so an inline module does not disarm the lane.
#[test]
fn n11_primitive_under_an_inline_module_still_carries() {
    assert_counterexample_in(SRC_NESTED_FN_ALIAS, "n11_nested_fn_bare_primitive");
}

/// A GLOB import can rebind a primitive type name from a module of this very
/// file (`mod shadow { pub type u64 = i32; } use shadow::*;` — measured: the
/// program's `u64` is four bytes wide and it panics). Carrying `u64` there
/// turned HEAD's correct `Counterexample` into a `Verified`.
///
/// It first shipped as a fail-closed REFUSAL (the module's own binding made the
/// name `Undecided`). Under the closed-world admission a glob turns the whole
/// lane OFF instead, so HEAD's rendering — and HEAD's CORRECT refutation —
/// stands. Strictly better than the refusal it replaces: same soundness, one
/// less error.
#[test]
fn g16_glob_shadowed_primitive_keeps_heads_refutation() {
    assert_refuted_or_refused_in(SRC_GLOB_SHADOW, "g16_glob_shadowed_primitive");
}

/// BODY-SCOPE `use`. The name table is built from FILE items, so a `use`
/// written as a STATEMENT inside a function body — the ordinary way a
/// multi-file crate imports a type it uses in one function — was invisible to
/// it, and the carry attached the FILE's meaning of the name.
///
/// Measured as a false `Verified` on a panicking program: the file says
/// `type W = u64;`, the body says `use core::primitive::u32 as W;`, and the
/// stock-rustc twin reports `size_of::<W>() == 4` with
/// `v[0].checked_add(v[0]) == None`. HEAD refuted it (it dropped the width to
/// `i32`, where the same addition also overflows). The name is now `Undecided`
/// file-wide: this table cannot say which half of the body a body `use`
/// governs, so it refuses in both directions.
#[test]
fn g17_body_use_rebinds_alias_gated() {
    assert_gated_in(
        SRC_BODY_SCOPE,
        "g17_body_use_rebinds_alias",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// The same when the rebound name SPELLS a primitive (`use … as u64;`), which
/// needs no file alias at all to reproduce.
#[test]
fn g18_body_use_rebinds_primitive_gated() {
    assert_gated_in(
        SRC_BODY_SCOPE,
        "g18_body_use_rebinds_primitive",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// The BARE SCALAR sibling: `single_typed_bindings` routes its leaf classifier
/// through the same table, so it moved for the same reason and is pinned here.
#[test]
fn g19_body_use_rebinds_alias_scalar_gated() {
    assert_gated_in(
        SRC_BODY_SCOPE,
        "g19_body_use_rebinds_alias_scalar",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// A `use` nested two blocks deep inside the body is found too — the scan is a
/// `syn::visit` walk of the whole body, not a look at its top-level statements.
#[test]
fn g20_nested_block_use_gated() {
    assert_gated_in(
        SRC_BODY_SCOPE,
        "g20_nested_block_use_rebinds_alias",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// Its narrowness pin: a body `use` of an UNRELATED name poisons only that
/// name, so an ordinary carry in the same function still fires.
#[test]
fn n9_body_use_of_an_unrelated_name_still_carries() {
    assert_counterexample_in(SRC_BODY_SCOPE, "n9_body_use_of_an_unrelated_name");
}

/// THE `core::primitive::uN` PREFIX IS NOT PRIVILEGED. It was matched by
/// SPELLING, before any shadowing check, so a crate-root `mod core` redirected
/// the whole path while the lane kept reading it as the primitive — a measured
/// false `Verified` whose twin panics at `elem_size=4`.
#[test]
fn g21_mod_core_prefix_gated() {
    assert_gated_in(
        SRC_SHADOWED_CORE,
        "g21_mod_core_prefix",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// The array spelling of the same capture.
#[test]
fn g22_mod_core_prefix_array_gated() {
    assert_gated_in(
        SRC_SHADOWED_CORE,
        "g22_mod_core_prefix_array",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// And the `use m as core;` spelling, which needs no `mod core` at all.
#[test]
fn g23_use_as_core_prefix_gated() {
    assert_gated_in(
        SRC_RENAMED_CORE,
        "g23_use_as_core_prefix",
        &[PREFIX, ERR_UNDECIDED],
    );
}

/// The narrowness pin for both: with a LEADING `::` the path names the crate
/// `core` and nothing in the file can capture it, so the carry still fires in
/// the very file that shadows the unqualified spelling. rustc agrees —
/// `size_of` is 8 for the shadowed spelling and 1 for the leading-colon one in
/// the same compilation.
#[test]
fn n10_leading_colon_primitive_still_carries() {
    assert_counterexample_in(SRC_SHADOWED_CORE, "n10_leading_colon_primitive");
}

// --------------------------------------------------------------- RESIDUALS

/// RESIDUAL r1 — SCOPING, NOT CLOSED. With no `syn::File` the name table cannot
/// be built, so the whole lane is OFF: no carry and no refusal. Extraction
/// without a file therefore still renders the bare literal, and this pins that
/// the limit is deliberate rather than accidental.
#[test]
fn r1_no_file_context_neither_carries_nor_refuses() {
    let func: syn::ItemFn = syn::parse_quote! {
        fn probe() {
            let v: Vec<u8> = vec![200];
            trust_vc::assert!(v[0usize] + 100u8 > 150u8);
        }
    };
    let vc = trust_vc_core::extract_verification_conditions(&func)
        .expect("no-file extraction must not refuse");
    let rendered: String = vc
        .obligations()
        .iter()
        .map(|o| o.condition().to_string())
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        rendered.contains("vec![200]") || rendered.contains("vec! [200]"),
        "without a file the width must NOT be carried (residual); got {rendered}"
    );
    assert!(
        !rendered.contains("200u8"),
        "without a file the width must NOT be carried (residual); got {rendered}"
    );
}

/// RESIDUAL r2 — CLOSED. The bare-`f32` container `let v: Vec<f32> =
/// vec![16777216.0]; v[0usize] + 1.0 > v[0usize]` (false in `f32`: 2^24 + 1
/// rounds to 2^24) was a recorded open hole that came back `Verified`: float
/// leaves are not carried, so the literal reached the model as the exact
/// real. Since 0ed9ac95 an unsuffixed float literal held by a `vec!` literal
/// is refused (design-trust-proof-backend.md §5b rule 14), so it fails closed;
/// the pin that required it to stay `Verified` failed on origin/main
/// dd3859d2 and now pins the refusal. The suffixed spelling (`NotProved`,
/// not a refutation, on the go/no-go probe) must fail closed too.
#[test]
fn r2_bare_f32_container_is_refused() {
    let bare = verify("r2_bare_f32_container");
    let suffixed = verify("r2_suffixed_f32_container");
    assert!(
        !matches!(bare, VerifyResult::Verified),
        "the bare f32 container asserts a value that is false in f32; got {bare:?}"
    );
    assert!(
        !matches!(suffixed, VerifyResult::Verified),
        "the suffixed f32 spelling must at least fail closed; got {suffixed:?}"
    );
}

/// RESIDUAL r3 — A GLOB IMPORT TURNS THE COMPOSITE CARRY OFF, and that is a
/// CAPABILITY residual, not a closed hole.
///
/// A glob cannot be enumerated from this file's text and it really can rebind a
/// primitive type name (g16). So in a glob-bearing file a width-bearing
/// primitive spelling is `Opaque`: carry nothing, refuse nothing, keep HEAD's
/// rendering byte-for-byte. The consequences, all four pinned here because
/// each one could silently change:
/// * the composite carry is DECLINED — `use …::*;` plus `let v: Vec<u8> =
///   vec![200]` gets no carried width, so its literal reaches the let-binding
///   marker at the `i32` placeholder and is REFUSED there (§5b rule 12: a
///   `Vec<i32>` is not a `Vec<u8>`). A `Verified` answer would be refused by
///   the type-name rule too (`vc_extraction::type_name_rebinding`): the file
///   spells `Vec` where a glob from outside the file reaches, and that glob
///   can bind `Vec`. How FAR that reaches was re-measured 2026-09-18 and is
///   much smaller than the first reading claimed: of the 167
///   `evals/verus/ported` files, **5** carry any glob and exactly **1**
///   mentions `vstd::prelude`, and a scan for the shape this lane can reach
///   (a composite ascription over an integer primitive whose initializer
///   holds a bare literal) finds **0** corpus sites. The earlier "every
///   ported corpus file writes `use vstd::prelude::*;`" was simply false.
/// * the BARE SCALAR recorders are unchanged, so nothing REGRESSES: HEAD
///   refuted `let x: u8 = 200; x + 100u8` under a glob and so does this.
/// * the UNQUALIFIED `core::primitive::u8` is NOT the escape hatch, contrary to
///   what this test asserted when it first shipped. A glob can rebind `core`
///   itself, and rustc agrees: in a file whose glob imports a module named
///   `core`, `core::primitive::u8` measures `size_of == 8` while
///   `::core::primitive::u8` in the same file measures 1. The unqualified
///   spelling therefore DECLINES here, like every other width-bearing spelling
///   in a glob file.
/// * `::core::primitive::u8` — with the LEADING `::` — was the escape hatch,
///   and it is NOT one any more. The leading-`::` spelling is capture-proof
///   against a `mod core`, a `use m as core;` and a glob (all three measured
///   with rustc: eight bytes in a file where the unqualified spelling measures
///   one), which is what had been measured — but `extern crate m as core;` at a
///   crate root rebinds the EXTERN PRELUDE and beats it too (measured:
///   `lead_bytes=4`), and an unenumerable file cannot rule that out. Nor can it
///   show the `vec!` / `Vec` spine is the `std` one: a macro-generated
///   `pub type Vec<T> = ::std::vec::Vec<<T as Proj>::O>;` projects the element
///   to another width, and that was a measured false `Verified` too. So the
///   whole file declines, and `r3_glob_leading_colon_primitive` is read like
///   its siblings: the carry declines and the let-binding marker refuses the
///   placeholder-typed literal.
#[test]
fn r3_glob_import_declines_the_carry() {
    let glob = [LANE_OFF_LITERAL];
    assert_gated_in(SRC_GLOB, "r3_glob_container", &glob);
    assert_counterexample_in(SRC_GLOB, "r3_glob_scalar");
    assert_gated_in(SRC_GLOB, "r3_glob_explicit_primitive", &glob);
    assert_gated_in(SRC_GLOB, "r3_glob_leading_colon_primitive", &glob);
}

// ------------------------------------- THE CLOSED WORLD (round 5, 2026-09-18)

/// g26 — an item-position `macro_rules!` INVOCATION. Four review rounds each
/// closed one more way for a name to be bound invisibly; this one, plus g28's
/// `extern crate` and the `#[derive]` measurement behind r5, is why the
/// admission stopped being a list of escapes and became a CLOSED WORLD: an
/// attribute macro can inject `pub type u32 = u64;` into the enclosing module
/// and no syntax distinguishes it from an inert attribute, so the escape set is
/// not enumerable.
///
/// Unenumerable ⇒ the lane is OFF for the file ⇒ HEAD's rendering, and HEAD's
/// CORRECT refutation, stand. `Verified` on a panicking program before the fix.
#[test]
fn g26_item_macro_invocation_turns_the_lane_off() {
    assert_refuted_or_refused_in(SRC_ITEM_MACRO, "g26_item_macro_widening");
}

/// g27 — the same blindness in the NARROW direction, which is a capability
/// REGRESSION rather than a soundness hole: the element really is eight bytes,
/// `200 + 100 = 300` holds, and the lens refuted a TRUE claim. HEAD's
/// rendering verified it by reading the literal at the `i32` placeholder — a
/// width the file does not give it either — and the all-literal composite is
/// now refused in a file that does not decide widths: never refuted.
#[test]
fn g27_item_macro_narrowing_is_restored() {
    assert_refused_in(SRC_ITEM_MACRO_NARROW, "g27_item_macro_narrowing");
}

/// g28 / g29 — `extern crate self as core;` captures the EXTERN PRELUDE, so the
/// leading-`::` spelling is captured too (`lead_bytes=4`). Both were `Verified`
/// on a panicking program; both are HEAD's correct refutation now.
#[test]
fn g28_extern_crate_bare_prefix_turns_the_lane_off() {
    assert_refuted_or_refused_in(SRC_EXTERN_CRATE, "g28_extern_crate_bare_prefix");
}

#[test]
fn g29_extern_crate_captures_the_leading_colon_spelling() {
    assert_refuted_or_refused_in(SRC_EXTERN_CRATE, "g29_extern_crate_leading_colon");
}

/// g30 — the `extern crate` blindness in the narrow direction. A TRUE claim the
/// lens refuted. HEAD's rendering verified it at the `i32` placeholder; the
/// all-literal composite under a spelled integer type is now refused in a
/// file that does not decide widths (§5b rule 12): never refuted.
#[test]
fn g30_extern_crate_narrowing_is_restored() {
    assert_refused_in(SRC_EXTERN_CRATE, "g30_extern_crate_narrowing");
}

/// g31 — a macro-generated `Vec` ALIAS. The ascription's LEAF is the
/// uncapturable `::core::primitive::u64` and the carry was still wrong, because
/// the constructor SPINE was rebound. This is the probe that rules out a
/// leaf-only escape hatch, and it is why `r3_glob_leading_colon_primitive` was
/// re-keyed as a residual instead of being kept as a control.
#[test]
fn g31_macro_generated_vec_alias_turns_the_lane_off() {
    assert_refuted_or_refused_in(SRC_MACRO_VEC_ALIAS, "g31_macro_vec_alias");
}

/// n12 — the NARROWNESS pin for the whole closed world: the nine built-in
/// derives are language-specified to emit `impl` blocks only, so a file that
/// carries them still carries widths. Without this pin the admission would be
/// free to disarm on any attribute at all.
#[test]
fn n12_builtin_derive_still_carries() {
    assert_counterexample_in(SRC_BUILTIN_DERIVE, "n12_builtin_derive_still_carries");
}

/// RESIDUAL r5 — the COST of the closed world. A third-party `#[derive]` (or
/// any attribute macro, or an item-macro invocation, or an `extern crate`, or
/// a `#[cfg]`) turns the lane off, and HEAD's false `Verified` on `let v:
/// Vec<u8> = vec![200]; v[0] + 100u8 > 150u8` stood in such a file. The
/// all-literal composite is now refused there (§5b rule 12): never `Verified`.
#[test]
fn r5_third_party_attribute_declines_the_carry() {
    assert_refuted_or_refused_in(SRC_THIRD_PARTY_DERIVE, "r5_third_party_derive");
}

/// RESIDUAL r4 — a glob written inside a FUNCTION BODY disarms the carry for
/// the whole file, exactly as a file-scope one does.
///
/// It shipped not doing so, which was a false `Verified`: a body glob really
/// does rebind the name (two-crate stock-rustc twin, `pub type u8 =
/// ::core::primitive::i64;` glob-imported inside the body — `elem_size=8`,
/// `200.checked_add(100) == Some(300)`, so the claim the engine refuted is
/// TRUE). The name table is file-scope and cannot say WHERE the glob applies,
/// so the whole file declines, and the container's placeholder-typed literal
/// is refused at the let-binding marker (§5b rule 12).
#[test]
fn r4_body_scope_glob_declines_the_carry() {
    assert_gated_in(SRC_BODY_GLOB, "r4_body_glob_container", &[LANE_OFF_LITERAL]);
    assert_counterexample_in(SRC_BODY_GLOB, "r4_body_glob_scalar");
}

// ------------------------------------------------------------ RUNTIME TWINS

/// The only truth oracle. Every claim the controls and liars make is executed
/// here under stock rustc; `checked_*` pins the overflow independently of the
/// debug profile, so the file does not depend on `-C debug-assertions=on` being
/// set for this target.
#[allow(clippy::identity_op, unused_variables)]
#[test]
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
fn runtime_twins_execute_std_behavior() {
    // c1 / c2 / l1 — the ledger's row: the program PANICS.
    {
        let v: Vec<u8> = vec![200];
        assert!(v[0usize].checked_add(100u8).is_none());
        assert!(v[0usize] != 201u8);
    }
    // c3 / c4 / l2
    {
        let x: Option<u8> = Some(200);
        assert!(x.unwrap().checked_add(100u8).is_none());
        assert!(!(x.unwrap() < 200u8));
    }
    // c5
    {
        let x: Option<Option<u8>> = Some(Some(200));
        assert!(x.unwrap().unwrap().checked_add(100u8).is_none());
    }
    // c6 / c7 / c17
    {
        let v: std::vec::Vec<u8> = vec![200];
        assert!(v[0usize].checked_add(100u8).is_none());
        let w: Vec<Vec<u8>> = vec![vec![200]];
        assert!(w[0usize][0usize].checked_add(100u8).is_none());
        let t: Vec<(u8, u8)> = vec![(200, 1)];
        assert!(t[0usize].0.checked_add(100u8).is_none());
    }
    // c8 / c9 / c18
    {
        let a: [u8; 2] = [200, 1];
        assert!(a[0usize].checked_add(100u8).is_none());
        let b: [u8; 3] = [200; 3];
        assert!(b[0usize].checked_add(100u8).is_none());
        assert!(b.len() == 3usize);
        let c: [u16; 2] = [65000, 1];
        assert!(c[0usize].checked_add(1000u16).is_none());
    }
    // c10 / c11 / c12 / l3
    {
        let t: (u8, u16) = (200, 2);
        assert!(t.0.checked_add(100u8).is_none());
        assert!(t.1 != 3u16);
        let (a, b): (u8, u8) = (200, 1);
        assert!(a.checked_add(100u8).is_none());
        assert!(b == 1u8);
        let n: (u8, (u8, u8)) = (1, (200, 2));
        assert!(n.1 .0.checked_add(100u8).is_none());
    }
    // c13 / c14
    {
        let r: &u8 = &200;
        assert!((*r).checked_add(100u8).is_none());
        let s: &[u8] = &[200, 1];
        assert!(s[0usize].checked_add(100u8).is_none());
    }
    // c15 / c16 — file-local aliases resolve to the primitives they name.
    {
        type Byte = u8;
        type Bytes = Vec<u8>;
        let x: Byte = 200;
        assert!(x.checked_add(100u8).is_none());
        let v: Bytes = vec![200];
        assert!(v[0usize].checked_add(100u8).is_none());
    }
    // c19 — deferred initialisation.
    {
        let v: Vec<u8>;
        v = vec![200];
        assert!(v[0usize].checked_add(100u8).is_none());
    }
    // c20 — an alias that SPELLS `u64` and MEANS `u8`.
    {
        #[allow(non_camel_case_types)]
        type u64 = u8;
        let x: u64 = 200;
        assert!(x.checked_add(100u8).is_none());
    }
    // l4 — the peer-coercion interaction: true at 32 bits, panics at 8.
    {
        let v: Vec<u8> = vec![200];
        assert!(v[0usize].checked_mul(2u8).is_none());
        assert!((v[0usize] as u32) * 2 == 400u32);
    }
    // n1 / n2 / n3 / n4 / n5 — the safe set the increment must protect.
    {
        let v: Vec<u8> = vec![100];
        assert!(v[0usize] + 100u8 > 150u8);
        let o: Option<u8> = Some(100);
        assert!(o.unwrap() + 100u8 > 150u8);
        let u: Vec<usize> = vec![100];
        assert!(u[0usize] + 100usize > 150usize);
        let i: Vec<i32> = vec![200];
        assert!(i[0usize] + 100 > 150);
        let j: Vec<i64> = vec![200];
        assert!(j[0usize] + 100i64 > 150i64);
    }
    // g9n — `-128` fits `i8`; `128` does not, which is why g8 refuses.
    {
        let t: (i8, i8) = (-128, 1);
        assert!(t.0.checked_sub(t.1).is_none());
        assert!(i8::MIN == -128i8);
    }
    // g3 / g4 / g5 / g6 / g7 — the refused shapes' runtime truth.
    {
        let a: u16 = 200 + 50;
        assert!(a == 250u16);
        assert!(u8::try_from(300u16).is_err());
    }
    // c21 / c22 / c23 — THE RESTORED REGRESSION. Every one of these claims is
    // TRUE: constant integer arithmetic under the annotation fits its declared
    // width, so refusing them cost capability and bought no soundness. c22 and
    // the shift's overflowing sibling show the width is still CARRIED through
    // the fold, which is what makes restoring them safe.
    {
        let x: Option<u8> = Some(200 + 50);
        let v: Vec<u8> = vec![100 + 50];
        let a: [u8; 2] = [100 + 50, 1];
        let t: (u8, u8) = (100 + 50, 1);
        let r: &u8 = &(100 + 50);
        let n: Vec<i8> = vec![-100 + 50];
        assert!(x.unwrap() == 250u8);
        assert!(v[0usize] == 150u8);
        assert!(a[0usize] == 150u8);
        assert!(t.0 == 150u8);
        assert!(*r == 150u8);
        assert!(n[0usize] == -50i8);
        // c22: 250 + 100 overflows `u8` — the carry survives the fold.
        assert!(x.unwrap().checked_add(100u8).is_none());
        // c23: a shift's COUNT is not the value's type. `1u8 << 3` is 8.
        let s: Option<u8> = Some(1 << 3);
        assert!(s.unwrap() == 8u8);
        let w: Vec<u8> = vec![1 << 7];
        assert!(w[0usize] == 128u8);
        assert!(w[0usize].checked_add(200u8).is_none());
    }
    // g14 / g15 / g16 — THE NESTED-SCOPE AND GLOB REBINDINGS. Each of these
    // really is four bytes wide and really does overflow; carrying the
    // file-scope meaning was a false `Verified`.
    {
        mod inner {
            pub type W = i32;
            pub fn widths() -> (usize, bool) {
                let v: Vec<W> = vec![2000000000];
                (
                    core::mem::size_of::<W>(),
                    v[0usize].checked_add(2000000000).is_none(),
                )
            }
        }
        assert_eq!(inner::widths(), (4, true));
        #[allow(non_camel_case_types)]
        mod shadow {
            #[allow(non_camel_case_types)]
            pub type u64 = ::core::primitive::i32;
        }
        #[allow(unused_imports)]
        use shadow::*;
        let v: Vec<u64> = vec![2000000000];
        assert_eq!(core::mem::size_of::<u64>(), 4);
        assert!(v[0usize].checked_add(2000000000).is_none());
        // g14n — an alias nobody rebinds still means what it says.
        type Byte = u8;
        let b: Vec<Byte> = vec![200];
        assert!(b[0usize].checked_add(100u8).is_none());
    }
    // r3 — the glob residual's own truth: `u8` really is `u8` here, so the
    // claim is false. The carry declines; the type-name rule refuses the
    // `Verified` answer.
    {
        let v: Vec<u8> = vec![200];
        assert!(v[0usize].checked_add(100u8).is_none());
    }
    // r2 — the recorded float residual: `16777216.0f32 + 1.0f32` rounds back.
    {
        let v: Vec<f32> = vec![16777216.0];
        assert!(!(v[0usize] + 1.0f32 > v[0usize]));
    }
    // g17 / g19 / g20 — a BODY-scope `use` really does rebind the name for the
    // rest of that body, whatever the file says. The engine read the file's
    // `type W = u64;` and verified; the program's `W` is four bytes wide and
    // the addition overflows.
    {
        #[allow(dead_code)]
        type W = u64;
        assert_eq!(core::mem::size_of::<W>(), 8);
        {
            use core::primitive::u32 as W;
            assert_eq!(core::mem::size_of::<W>(), 4);
            let v: Vec<W> = vec![3000000000];
            assert!(v[0usize].checked_add(v[0usize]).is_none());
            let x: W = 3000000000;
            assert!(x.checked_add(x).is_none());
        }
    }
    // g18 — the same with no file alias: the rebound name SPELLS a primitive.
    {
        use core::primitive::u32 as u64;
        assert_eq!(core::mem::size_of::<u64>(), 4);
        let v: Vec<u64> = vec![3000000000];
        assert!(v[0usize].checked_add(v[0usize]).is_none());
    }
    // n9 — a body `use` of an unrelated name changes nothing about `u8`.
    {
        #[allow(unused_imports)]
        use core::mem::size_of;
        let v: Vec<u8> = vec![200];
        assert!(v[0usize].checked_add(100u8).is_none());
    }
    // g21 / g22 / g23 / n10 — `core::primitive::uN` is matched by SPELLING, and
    // the spelling is capturable: a block-scope `mod core` redirects the whole
    // path, while the LEADING-`::` form in the same scope still names the crate.
    {
        mod core {
            pub mod primitive {
                #[allow(non_camel_case_types)]
                pub type u64 = ::core::primitive::u32;
            }
        }
        assert_eq!(::core::mem::size_of::<core::primitive::u64>(), 4);
        assert_eq!(::core::mem::size_of::<::core::primitive::u64>(), 8);
        let v: Vec<core::primitive::u64> = vec![3000000000];
        assert!(v[0usize].checked_add(v[0usize]).is_none());
        let a: [core::primitive::u64; 2] = [3000000000, 1];
        assert!(a[0usize].checked_add(a[0usize]).is_none());
        // n10 — the leading-colon escape hatch is a real `u8`.
        let w: Vec<::core::primitive::u8> = vec![200];
        assert!(w[0usize].checked_add(100u8).is_none());
    }
}

// ------------------------------------------------------------------ FIXTURE

const SRC: &str = r#"
type Byte = u8;
type Bytes = Vec<u8>;

fn payload(x: u8) -> u8 { x }
fn make() -> Vec<u8> { vec![1u8] }

struct Holder { a: u8 }

// CONTROL c1 — the ledger's open 2026-09-16 row.
#[trust_vc::ensures(true)]
fn c1_vec_u8_suffixed_peer() {
    let v: Vec<u8> = vec![200];
    trust_vc::assert!(v[0usize] + 100u8 > 150u8);
}

// CONTROL c2 — the same with a BARE peer.
#[trust_vc::ensures(true)]
fn c2_vec_u8_bare_peer() {
    let v: Vec<u8> = vec![200];
    trust_vc::assert!(v[0usize] + 100 > 150);
}

// CONTROL c3 / c4 — Option payload, both peer spellings.
#[trust_vc::ensures(true)]
fn c3_option_u8_suffixed_peer() {
    let x: Option<u8> = Some(200);
    trust_vc::assert!(x.unwrap() + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c4_option_u8_bare_peer() {
    let x: Option<u8> = Some(200);
    trust_vc::assert!(x.unwrap() + 100 > 150);
}

#[trust_vc::ensures(true)]
fn c5_nested_option() {
    let x: Option<Option<u8>> = Some(Some(200));
    trust_vc::assert!(x.unwrap().unwrap() + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c6_std_vec_path() {
    let v: std::vec::Vec<u8> = vec![200];
    trust_vc::assert!(v[0usize] + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c7_vec_of_vec() {
    let v: Vec<Vec<u8>> = vec![vec![200]];
    trust_vc::assert!(v[0usize][0usize] + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c8_array_literal() {
    let a: [u8; 2] = [200, 1];
    trust_vc::assert!(a[0usize] + 100u8 > 150u8);
}

// The repeat form: the LENGTH must never take the element suffix.
#[trust_vc::ensures(true)]
fn c9_array_repeat() {
    let a: [u8; 3] = [200; 3];
    trust_vc::assert!(a[0usize] + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c10_whole_tuple() {
    let t: (u8, u16) = (200, 2);
    trust_vc::assert!(t.0 + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c11_tuple_destructuring() {
    let (a, b): (u8, u8) = (200, 1);
    trust_vc::assert!(a + 100u8 > 150u8 && b == 1u8);
}

#[trust_vc::ensures(true)]
fn c12_nested_tuple() {
    let t: (u8, (u8, u8)) = (1, (200, 2));
    trust_vc::assert!(t.1.0 + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c13_shared_reference() {
    let r: &u8 = &200;
    trust_vc::assert!(*r + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c14_slice_reference() {
    let s: &[u8] = &[200, 1];
    trust_vc::assert!(s[0usize] + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c15_scalar_alias() {
    let x: Byte = 200;
    trust_vc::assert!(x + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c16_container_alias() {
    let v: Bytes = vec![200];
    trust_vc::assert!(v[0usize] + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c17_vec_of_tuple() {
    let v: Vec<(u8, u8)> = vec![(200, 1)];
    trust_vc::assert!(v[0usize].0 + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn c18_u16_array() {
    let a: [u16; 2] = [65000, 1];
    trust_vc::assert!(a[0usize] + 1000u16 > 150u16);
}

#[trust_vc::ensures(true)]
fn c19_deferred_vec() {
    let v: Vec<u8>;
    v = vec![200];
    trust_vc::assert!(v[0usize] + 100u8 > 150u8);
}

// LIARS.
#[trust_vc::ensures(true)]
fn l1_wrong_element_value() {
    let v: Vec<u8> = vec![200];
    trust_vc::assert!(v[0usize] == 201u8);
}

#[trust_vc::ensures(true)]
fn l2_wrong_payload_bound() {
    let x: Option<u8> = Some(200);
    trust_vc::assert!(x.unwrap() < 200u8);
}

#[trust_vc::ensures(true)]
fn l3_wrong_tuple_element() {
    let t: (u8, u16) = (200, 2);
    trust_vc::assert!(t.1 == 3u16);
}

// The encoder-interaction liar: `200 * 2` is 400 at 32 bits and panics at 8.
#[trust_vc::ensures(true)]
fn l4_peer_coercion_interaction() {
    let v: Vec<u8> = vec![200];
    trust_vc::assert!(v[0usize] * 2u8 > 100u8);
}

// NARROWNESS: in-range arithmetic that must keep verifying.
#[trust_vc::ensures(true)]
fn n1_in_range_vec() {
    let v: Vec<u8> = vec![100];
    trust_vc::assert!(v[0usize] + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn n2_in_range_option() {
    let x: Option<u8> = Some(100);
    trust_vc::assert!(x.unwrap() + 100u8 > 150u8);
}

#[trust_vc::ensures(true)]
fn n3_usize_container() {
    let v: Vec<usize> = vec![100];
    trust_vc::assert!(v[0usize] + 100usize > 150usize);
}

#[trust_vc::ensures(true)]
fn n4_i32_container() {
    let v: Vec<i32> = vec![200];
    trust_vc::assert!(v[0usize] + 100 > 150);
}

#[trust_vc::ensures(true)]
fn n5_i64_container() {
    let v: Vec<i64> = vec![200];
    trust_vc::assert!(v[0usize] + 100i64 > 150i64);
}

#[trust_vc::ensures(true)]
fn n6_user_type_ascription() {
    let h: Holder = Holder { a: 1 };
    trust_vc::assert!(h.a == 1u8);
}

#[trust_vc::ensures(true)]
fn n7_literal_free_initializer() {
    let v: Vec<u8> = make();
    trust_vc::assert!(v.len() >= 0usize);
}

#[trust_vc::ensures(true)]
fn n8_name_bound_twice() {
    let x: Option<u8>;
    {
        let x = 0i32;
        let _ = x;
    }
    x = Some(200);
    trust_vc::assert!(x.unwrap() + 100u8 > 150u8);
}

// GATED.
#[trust_vc::ensures(true)]
fn g3_non_constant_operand() {
    let z = 50u8;
    let x: Option<u8> = Some(z + 50);
    trust_vc::assert!(x.unwrap() > 0u8);
}

#[trust_vc::ensures(true)]
fn g4_non_constant_vec_element() {
    let z = 50u8;
    let v: Vec<u8> = vec![z + 50];
    trust_vc::assert!(v[0usize] > 0u8);
}

#[trust_vc::ensures(true)]
fn g5_call_argument_element() {
    let v: Vec<u8> = vec![payload(200)];
    trust_vc::assert!(v[0usize] > 150u8);
}

#[trust_vc::ensures(true)]
fn g6_deferred_non_constant_payload() {
    let z = 50u8;
    let x: Option<u8>;
    x = Some(z + 50);
    trust_vc::assert!(x.unwrap() > 0u8);
}

// RESTORED REGRESSIONS: constant integer arithmetic is decided by the
// annotation. Every one of these is a TRUE claim that HEAD verified.
#[trust_vc::ensures(true)]
fn c21_constant_folded_payload() {
    let x: Option<u8> = Some(200 + 50);
    let v: Vec<u8> = vec![100 + 50];
    let a: [u8; 2] = [100 + 50, 1];
    let t: (u8, u8) = (100 + 50, 1);
    let r: &u8 = &(100 + 50);
    let n: Vec<i8> = vec![-100 + 50];
    trust_vc::assert!(x.unwrap() == 250u8);
    trust_vc::assert!(v[0usize] == 150u8);
    trust_vc::assert!(a[0usize] == 150u8);
    trust_vc::assert!(t.0 == 150u8);
    trust_vc::assert!(*r == 150u8);
    trust_vc::assert!(n[0usize] == -50i8);
}

#[trust_vc::ensures(true)]
fn c22_constant_folded_payload_overflow() {
    let x: Option<u8> = Some(200 + 50);
    let s = x.unwrap() + 100u8;
    trust_vc::assert!(s > 150u8);
}

#[trust_vc::ensures(true)]
fn c23_constant_shift_value() {
    let x: Option<u8> = Some(1 << 3);
    trust_vc::assert!(x.unwrap() == 8u8);
}

#[trust_vc::ensures(true)]
fn c23_constant_shift_overflow() {
    let v: Vec<u8> = vec![1 << 7];
    let s = v[0usize] + 200u8;
    trust_vc::assert!(s > 150u8);
}

#[trust_vc::ensures(true)]
fn g7_out_of_range_payload() {
    let x: Option<u8> = Some(300);
    trust_vc::assert!(x.unwrap() > 150u8);
}

#[trust_vc::ensures(true)]
fn g8_out_of_range_signed_tuple() {
    let t: (i8, i8) = (128, 1);
    trust_vc::assert!(t.0 > 0i8);
}

#[trust_vc::ensures(true)]
fn g9_negative_at_unsigned_leaf() {
    let v: Vec<u8> = vec![-1];
    trust_vc::assert!(v[0usize] > 0u8);
}

#[trust_vc::ensures(true)]
fn g9n_signed_minimum() {
    let t: (i8, i8) = (-128, 1);
    trust_vc::assert!(t.0 < t.1);
}

#[trust_vc::ensures(true)]
fn g10_tuple_arity_mismatch() {
    let t: (u8, u16) = (1, 2, 3);
    trust_vc::assert!(t.0 > 0u8);
}

#[trust_vc::ensures(true)]
fn g11_vec_ascription_array_initializer() {
    let v: Vec<u8> = [200, 1];
    trust_vc::assert!(v[0usize] > 150u8);
}

// RESIDUAL r2.
#[trust_vc::ensures(true)]
fn r2_bare_f32_container() {
    let v: Vec<f32> = vec![16777216.0];
    let s = v[0usize] + 1.0;
    trust_vc::assert!(s > v[0usize]);
}

#[trust_vc::ensures(true)]
fn r2_suffixed_f32_container() {
    let v: Vec<f32> = vec![16777216.0f32];
    let s = v[0usize] + 1.0f32;
    trust_vc::assert!(s > v[0usize]);
}
"#;

/// R2(a): the alias is IMPORTED, so this file cannot decide what it denotes.
const SRC_IMPORTED: &str = r#"
use other::Byte;

#[trust_vc::ensures(true)]
fn g1_imported_alias_scalar() {
    let x: Byte = 200;
    trust_vc::assert!(x + 100 > 150);
}

#[trust_vc::ensures(true)]
fn g2_imported_alias_element() {
    let v: Vec<Byte> = vec![200];
    trust_vc::assert!(v[0usize] + 100 > 150);
}

#[trust_vc::ensures(true)]
fn g2n_suffixed_under_imported() {
    let x: Byte = 200u8;
    trust_vc::assert!(x + 100u8 > 150u8);
}
"#;

/// R2(e): a file-declared `Some` need not be the `std` constructor.
const SRC_SHADOWED_SOME: &str = r#"
#[allow(non_snake_case)]
fn Some(x: i64) -> Option<u8> { Option::Some(x as u8) }

#[trust_vc::ensures(true)]
fn g12_shadowed_some() {
    let x: Option<u8> = Some(200);
    trust_vc::assert!(x.unwrap() > 150u8);
}
"#;

/// A file item named `u8`: the ascription does not spell the primitive.
const SRC_SHADOWED_PRIMITIVE: &str = r#"
#[allow(non_camel_case_types)]
struct u8;

#[trust_vc::ensures(true)]
fn g13_shadowed_primitive() {
    let x: u8 = 200;
    trust_vc::assert!(x + 100 > 150);
}
"#;

/// The alias that SPELLS a primitive and MEANS another: `Verified` at HEAD.
const SRC_ALIAS_SHADOWS_PRIMITIVE: &str = r#"
#[allow(non_camel_case_types)]
type u64 = u8;

#[trust_vc::ensures(true)]
fn c20_alias_shadows_primitive() {
    let x: u64 = 200;
    trust_vc::assert!(x + 100u8 > 150u8);
}
"#;

/// A NESTED MODULE rebinds a file-scope name. Inside `mod inner`, `W` is `i32`
/// and `S` is `i32`; the file-scope `W` is `i64`. Resolving either function's
/// annotation against the FILE table gave a false `Verified` on a program that
/// overflows. `Byte` is rebound by nobody and must still carry.
const SRC_NESTED_MODULE: &str = r#"
type W = i64;
type Byte = u8;

mod inner {
    pub type W = i32;
    use core::primitive::i32 as S;

    #[trust_vc::ensures(true)]
    pub fn g14_nested_rebinding() {
        let v: Vec<W> = vec![2000000000];
        let s = v[0usize] + 2000000000;
        trust_vc::assert!(s > 0);
    }

    #[trust_vc::ensures(true)]
    pub fn g15_nested_use_rename() {
        let v: Vec<S> = vec![2000000000];
        let s = v[0usize] + 2000000000;
        trust_vc::assert!(s > 0);
    }
}

#[trust_vc::ensures(true)]
fn g14n_unrebound_alias() {
    let v: Vec<Byte> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}
"#;

/// A GLOB whose source is a module of this very file, rebinding `u64`.
/// `size_of::<u64>()` is 4 here and the program panics; carrying `u64` turned
/// HEAD's correct `Counterexample` into a `Verified`.
const SRC_GLOB_SHADOW: &str = r#"
mod shadow {
    #[allow(non_camel_case_types)]
    pub type u64 = ::core::primitive::i32;
}
use shadow::*;

#[trust_vc::ensures(true)]
fn g16_glob_shadowed_primitive() {
    let v: Vec<u64> = vec![2000000000];
    let s = v[0usize] + 2000000000;
    trust_vc::assert!(s > 0);
}
"#;

/// An ordinary prelude-style glob: nothing in this file rebinds anything, but
/// the file's text cannot PROVE that, so the composite carry is declined.
const SRC_GLOB: &str = r#"
use vstd::prelude::*;

#[trust_vc::ensures(true)]
fn r3_glob_container() {
    let v: Vec<u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}

#[trust_vc::ensures(true)]
fn r3_glob_scalar() {
    let x: u8 = 200;
    let s = x + 100u8;
    trust_vc::assert!(s > 150u8);
}

#[trust_vc::ensures(true)]
fn r3_glob_explicit_primitive() {
    let v: Vec<core::primitive::u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}

#[trust_vc::ensures(true)]
fn r3_glob_leading_colon_primitive() {
    let v: Vec<::core::primitive::u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}
"#;

/// A glob written INSIDE a function body. It disarms the file exactly as a
/// file-scope glob does; before 2026-09-18 it did not, and the composite carry
/// fired on a name the glob may have rebound.
const SRC_BODY_GLOB: &str = r#"
#[trust_vc::ensures(true)]
fn r4_body_glob_container() {
    use vstd::prelude::*;
    let v: Vec<u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}

#[trust_vc::ensures(true)]
fn r4_body_glob_scalar() {
    use vstd::prelude::*;
    let x: u8 = 200;
    let s = x + 100u8;
    trust_vc::assert!(s > 150u8);
}
"#;

/// A `use` written INSIDE a function body rebinds a type name for the rest of
/// that body, and the file-scope name table cannot see it. Measured as a false
/// `Verified` on a panicking program: the file says `type W = u64;`, the body
/// says `use core::primitive::u32 as W;`, and the element really is four bytes
/// wide (`v[0] + v[0]` overflows at 3000000000).
const SRC_BODY_SCOPE: &str = r#"
type W = u64;

#[trust_vc::ensures(true)]
fn g17_body_use_rebinds_alias() {
    use core::primitive::u32 as W;
    let v: Vec<W> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}

#[trust_vc::ensures(true)]
fn g18_body_use_rebinds_primitive() {
    #[allow(non_camel_case_types)]
    use core::primitive::u32 as u64;
    let v: Vec<u64> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}

#[trust_vc::ensures(true)]
fn g19_body_use_rebinds_alias_scalar() {
    use core::primitive::u32 as W;
    let x: W = 3000000000;
    let s = x + x;
    trust_vc::assert!(s > 3000000000);
}

#[trust_vc::ensures(true)]
fn g20_nested_block_use_rebinds_alias() {
    {
        {
            use core::primitive::u32 as W;
            let v: Vec<W> = vec![3000000000];
            let s = v[0usize] + v[0usize];
            trust_vc::assert!(s > 3000000000);
        }
    }
}

#[trust_vc::ensures(true)]
fn n9_body_use_of_an_unrelated_name() {
    use core::mem::size_of;
    let v: Vec<u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}
"#;

/// The `core::primitive::uN` prefix is an ordinary name and can be captured.
/// Both spellings were measured as false `Verified`s whose twins panic
/// (`elem_size=4`); the leading-colon spelling in the same file is the one that
/// really does denote the primitive.
const SRC_SHADOWED_CORE: &str = r#"
mod core {
    pub mod primitive {
        #[allow(non_camel_case_types)]
        pub type u64 = ::core::primitive::u32;
    }
}

#[trust_vc::ensures(true)]
fn g21_mod_core_prefix() {
    let v: Vec<core::primitive::u64> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}

#[trust_vc::ensures(true)]
fn g22_mod_core_prefix_array() {
    let a: [core::primitive::u64; 2] = [3000000000, 1];
    let s = a[0usize] + a[0usize];
    trust_vc::assert!(s > 3000000000);
}

#[trust_vc::ensures(true)]
fn n10_leading_colon_primitive() {
    let v: Vec<::core::primitive::u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}
"#;

/// `use m as core;` captures the prefix the same way an inline `mod core` does.
const SRC_RENAMED_CORE: &str = r#"
mod m {
    pub mod primitive {
        #[allow(non_camel_case_types)]
        pub type u64 = ::core::primitive::u32;
    }
}
use m as core;

#[trust_vc::ensures(true)]
fn g23_use_as_core_prefix() {
    let v: Vec<core::primitive::u64> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}
"#;

/// THE CONVERSE SCOPE AMBIGUITY (g25 / n11). A function written INSIDE an
/// inline module does not see the FILE's items, so a file-scope alias read for
/// it is a guess — measured as a false `Verified` whose stock-rustc twin
/// reports `inner elem_bytes=4` and panics. A primitive the file does NOT
/// declare is unaffected in both scopes, which n11 pins.
const SRC_NESTED_FN_ALIAS: &str = r#"
#[allow(non_camel_case_types)]
pub type u32 = ::core::primitive::u64;

pub mod inner {
    #[trust_vc::ensures(true)]
    pub fn g25_nested_fn_file_alias() {
        let v: Vec<u32> = vec![3000000000];
        let s = v[0usize] + v[0usize];
        trust_vc::assert!(s > 3000000000);
    }

    #[trust_vc::ensures(true)]
    pub fn n11_nested_fn_bare_primitive() {
        let v: Vec<u8> = vec![200];
        let s = v[0usize] + 100u8;
        trust_vc::assert!(s > 150u8);
    }
}
"#;

/// An item-position `macro_rules!` INVOCATION. Its expansion rebinds `u64`
/// file-wide and no scan of this file's text can see it (`elem_bytes=4`; every
/// invocation spelling — `d!();`, `d!{}`, `d![]`, macro-invokes-macro — leaks
/// identically). WIDENING direction: the lens VERIFIED a panicking program.
const SRC_ITEM_MACRO: &str = r#"
macro_rules! widen { () => { #[allow(non_camel_case_types)] pub type u64 = ::core::primitive::u32; } }
widen!();

#[trust_vc::ensures(true)]
fn g26_item_macro_widening() {
    let v: Vec<u64> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}
"#;

/// The same blindness in the NARROW direction: the expansion makes the element
/// eight bytes wide, the claim is TRUE (`elem_bytes=8`, `200 + 100 = 300`), and
/// the lens REFUTED it. A restored capability regression, not a cost.
const SRC_ITEM_MACRO_NARROW: &str = r#"
macro_rules! widen8 { () => { #[allow(non_camel_case_types)] pub type u8 = ::core::primitive::u64; } }
widen8!();

#[trust_vc::ensures(true)]
fn g27_item_macro_narrowing() {
    let v: Vec<u8> = vec![200];
    let s = v[0usize] + 100;
    trust_vc::assert!(s > 150);
}
"#;

/// `extern crate m as core;` at a crate root rebinds the EXTERN PRELUDE, so
/// BOTH `core::primitive::u64` and the LEADING-`::` spelling this file used to
/// call capture-proof denote the file's own `mod primitive`. Measured with
/// rustc: `elem_bytes=4 lead_bytes=4`, while a `mod core`, a `use m as core;`
/// and a glob all leave the leading-`::` spelling at eight.
const SRC_EXTERN_CRATE: &str = r#"
extern crate self as core;

pub mod primitive {
    #[allow(non_camel_case_types)]
    pub type u64 = ::std::primitive::u32;
    #[allow(non_camel_case_types)]
    pub type u8 = ::std::primitive::u64;
}

#[trust_vc::ensures(true)]
fn g28_extern_crate_bare_prefix() {
    let v: Vec<core::primitive::u64> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}

#[trust_vc::ensures(true)]
fn g29_extern_crate_leading_colon() {
    let v: Vec<::core::primitive::u64> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}

#[trust_vc::ensures(true)]
fn g30_extern_crate_narrowing() {
    let v: Vec<core::primitive::u8> = vec![200];
    let s = v[0usize] + 100;
    trust_vc::assert!(s > 150);
}
"#;

/// A macro-generated `Vec` ALIAS that projects its element to another width.
/// The ascription's leaf is the uncapturable `::core::primitive::u64`, so only
/// the CONSTRUCTOR SPINE is wrong — which is why a leaf-only escape hatch
/// cannot be sound.
const SRC_MACRO_VEC_ALIAS: &str = r#"
pub trait WProj { type O; }
impl WProj for ::core::primitive::u64 { type O = ::core::primitive::u32; }
macro_rules! mkv { () => { pub type Vec<T> = ::std::vec::Vec<<T as WProj>::O>; } }
mkv!();

#[trust_vc::ensures(true)]
fn g31_macro_vec_alias() {
    let v: Vec<::core::primitive::u64> = vec![3000000000];
    let s = v[0usize] + v[0usize];
    trust_vc::assert!(s > 3000000000);
}
"#;

/// A THIRD-PARTY derive. MEASURED with a dependency-free proc-macro crate: a
/// `#[derive(Widen)]` really does inject `pub type u32 = u64;` into the
/// enclosing module (`size_of::<u32>()` is 8), and no syntax can tell an inert
/// attribute from a macro. Unknown attribute ⇒ lane off ⇒ HEAD's rendering.
const SRC_THIRD_PARTY_DERIVE: &str = r#"
#[derive(Serialize)]
pub struct S;

#[trust_vc::ensures(true)]
fn r5_third_party_derive() {
    let v: Vec<u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}
"#;

/// The nine BUILT-IN derives are specified by the language to emit `impl`
/// blocks only, so they bind no type name and the lane keeps running.
const SRC_BUILTIN_DERIVE: &str = r#"
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct S;

#[trust_vc::ensures(true)]
fn n12_builtin_derive_still_carries() {
    let v: Vec<u8> = vec![200];
    let s = v[0usize] + 100u8;
    trust_vc::assert!(s > 150u8);
}
"#;
