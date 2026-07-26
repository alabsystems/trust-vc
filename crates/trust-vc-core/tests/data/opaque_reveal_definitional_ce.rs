// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Opaque/reveal definitional-unfolding battery (upstream Verus basic.rs
// `test_spec_fn`, rust_verify_test/tests/basic.rs:84-116, pinned ref
// a40d57c73650cd3648b09386bfdb96ab5c270626).
//
// Upstream shape: `spec fn f1(i, j) -> bool { i <= j }`; `f2` with a let-bound
// body; `#[verifier(opaque)] spec fn f3 { f1(j, i) }`; body `hide(f2);
// assume(f2(a,b)); reveal(f2); assert(f1(a,b)); reveal(f3); assert(f3(b,a));
// assert(f3(a,b))` — expectation `assert_one_fails`: EXACTLY the last assert
// fails with a genuine assertion-failure (model-bearing) verdict.
//
// The file path now supports `hide!` (#2785): `test_spec_fn_full_with_hide`
// carries the EXACT upstream shape including `hide(f2)`. It is verdict-identical
// to `test_spec_fn_full` (no `hide!`) because under trust-vc's query-granular
// reveal model `hide(f2); …; reveal(f2)` nets to revealed AND no checked
// obligation sits in the `[hide(f2), reveal(f2))` window (only an `assume!`),
// so the interleave soundness guard admits it. The guard's fail-closed and
// hide-actually-hides directions are pinned by the `test_hide_*` cases below.
//
// NOT Rust-compiled — only syn-parsed by verify_function_from_file.
#![allow(dead_code, unused_variables)]

use trust_vc_types::int;

// upstream: spec fn f1(i: int, j: int) -> bool { i <= j }
#[trust_vc::spec]
fn f1(i: int, j: int) -> bool {
    i <= j
}

// upstream: spec fn f2(i: int, j: int) -> bool { let x = i; let y = j; x < y }
#[trust_vc::spec]
fn f2(i: int, j: int) -> bool {
    let x = i;
    let y = j;
    x < y
}

// upstream: #[verifier(opaque)] spec fn f3(i: int, j: int) -> bool { f1(j, i) }
#[trust_vc::spec]
#[trust_vc::opaque]
fn f3(i: int, j: int) -> bool {
    f1(j, i)
}

// --- (a) FAITHFUL upstream test_spec_fn (minus the inexpressible hide(f2)) ---
// upstream: assert(f1(a,b)) OK; assert(f3(b,a)) OK; assert(f3(a,b)) FAILS with
// a genuine model-bearing assertion failure (assert_one_fails).
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_spec_fn_full(a: int, b: int) {
    trust_vc::assume!(f2(a, b));
    trust_vc::reveal!(f2);
    trust_vc::assert!(f1(a, b));
    trust_vc::reveal!(f3);
    trust_vc::assert!(f3(b, a));
    trust_vc::assert!(f3(a, b)); // FAILS upstream
}

// --- (b) verified direction only (both good asserts, no CE) ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_spec_fn_verified_only(a: int, b: int) {
    trust_vc::assume!(f2(a, b));
    trust_vc::reveal!(f2);
    trust_vc::assert!(f1(a, b));
    trust_vc::reveal!(f3);
    trust_vc::assert!(f3(b, a));
}

// --- (b) CE with ONLY the revealed opaque fn (two-level definitional chain:
//     f3 -> f1 -> arith; the exact ay quantifier-ematching-exists class) ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_ce_revealed_opaque_only(a: int, b: int) {
    trust_vc::reveal!(f3);
    trust_vc::assert!(f3(a, b)); // unprovable: b <= a not entailed
}

// --- (b) control: CE on a PLAIN (non-opaque) spec fn call ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_ce_plain_spec_fn(a: int, b: int) {
    trust_vc::assert!(f1(a, b)); // unprovable: a <= b not entailed
}

// --- (b) control: CE with the let-body spec fn (f2), non-opaque ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_ce_let_body_spec_fn(a: int, b: int) {
    trust_vc::assert!(f2(a, b)); // unprovable: a < b not entailed
}

// --- (b) nested NON-opaque chain (same two-level class without opacity):
//     g4 -> f1 -> arith. Pins that the definitional-unfolding CE does not
//     depend on the opaque/reveal machinery itself. ---
#[trust_vc::spec]
fn g4(i: int, j: int) -> bool {
    f1(j, i)
}

#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_ce_nested_plain_chain(a: int, b: int) {
    trust_vc::assert!(g4(a, b)); // unprovable: b <= a not entailed
}

// --- (c) SOUNDNESS PIN: unrevealed opaque must NOT verify via its body.
// Provable ONLY by unfolding f3 -> f1(b, a); with no reveal! this must NOT be
// Verified (Verus requires the reveal). This also pins that the demand-inline
// retry catalog excludes unrevealed opaque bodies. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_opaque_no_leak(a: int, b: int) {
    trust_vc::assume!(f1(b, a));
    trust_vc::assert!(f3(a, b)); // must NOT verify without reveal!
}

// --- (c) dual pin: the CE direction must not fire on an unrevealed opaque
// body either — refuting f3(a,b) from the hidden body would also be
// definitional unfolding Verus forbids. Upstream both directions are simply
// "unknown symbol": the assert fails, but never via the hidden definition. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_opaque_no_leak_ce_direction(a: int, b: int) {
    trust_vc::assume!(f1(b, a));
    trust_vc::assert!(!f3(a, b)); // must NOT verify; f3 strictly uninterpreted
}

// --- control: same shape as test_opaque_no_leak WITH reveal must verify ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_opaque_revealed_verifies(a: int, b: int) {
    trust_vc::assume!(f1(b, a));
    trust_vc::reveal!(f3);
    trust_vc::assert!(f3(a, b));
}

// --- (d) reveal scoping: sibling functions in this file reveal!(f3); a
// function WITHOUT its own reveal! must still see f3 as opaque (the file-path
// reveal scan is per-block). Same body as test_opaque_no_leak, kept as a
// separately-named case so the scoping intent is pinned even if the no-leak
// case evolves. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_reveal_does_not_leak_across_fns(a: int, b: int) {
    trust_vc::assume!(f1(b, a));
    trust_vc::assert!(f3(a, b)); // sibling reveals must not apply here
}

// --- (e) KNOWN FIDELITY DIVERGENCE (documented pin, NOT desired behavior):
// trust-vc's reveal! is query-granular (whole-function), Verus's is
// flow-ordered (a statement-positioned fuel assume): upstream, an assert
// placed BEFORE reveal(f3) does NOT see the body and fails; trust-vc verifies
// it. This is a proves-more-than-Verus divergence confined to intra-function
// statement order; it does not change any verdict of the upstream
// test_spec_fn sequence (all its asserts follow their reveals). Pinned here
// so a future statement-ordered reveal implementation flips this case
// CONSCIOUSLY (it should then become NOT-Verified). ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_assert_before_reveal_divergence_pin(a: int, b: int) {
    trust_vc::assume!(f1(b, a));
    trust_vc::assert!(f3(a, b)); // Verus: fails (reveal is below); trust-vc: verifies
    trust_vc::reveal!(f3);
}

// --- (f) #2785: the EXACT upstream test_spec_fn sequence WITH hide(f2). The
// `[hide(f2), reveal(f2))` window contains only `assume!(f2(a,b))` (not a
// checked obligation), so the interleave guard admits it; verdict is the same
// Counterexample as `test_spec_fn_full` (last assert fails, assert_one_fails). ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_spec_fn_full_with_hide(a: int, b: int) {
    trust_vc::hide!(f2);
    trust_vc::assume!(f2(a, b));
    trust_vc::reveal!(f2);
    trust_vc::assert!(f1(a, b));
    trust_vc::reveal!(f3);
    trust_vc::assert!(f3(b, a));
    trust_vc::assert!(f3(a, b)); // FAILS upstream
}

// --- (f) hide-actually-hides: `hide(f1)` with NO reveal re-opaques f1 for the
// whole query. `f1(a, a)` is TRUE via the body (a <= a) but UNPROVABLE with f1
// uninterpreted, so this must NOT verify (Verus hides f1 too → both fail).
// If hide! were a no-op, f1 would stay visible and this would wrongly Verify. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_hide_without_reveal_hides_body(a: int, b: int) {
    trust_vc::hide!(f1);
    trust_vc::assert!(f1(a, a)); // must NOT verify: f1 re-opaqued, no reveal
}

// --- (f) hide-then-reveal restores visibility: nothing checked is bracketed,
// so the guard admits it and f1's body is available at the assert. `f1(a, a)`
// (a <= a) then verifies. Pins that a benign hide/reveal pair does not fail
// closed. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_hide_then_reveal_verifies(a: int, b: int) {
    trust_vc::hide!(f1);
    trust_vc::reveal!(f1);
    trust_vc::assert!(f1(a, a));
}

// --- (f) SOUNDNESS PIN (the cardinal proves-more direction): a CHECKED assert
// bracketed by `hide(f1) … reveal(f1)` must be REJECTED fail-closed. The assert
// is `f1(a, a)` — TRUE via f1's body (a <= a) but UNPROVABLE with f1 re-opaqued.
// Verus checks it with f1 hidden (fuel 0 in this window) → it FAILS; trust-vc's
// query-granular reveal-wins model would otherwise expose f1's body here and
// VERIFY it → proving more than Verus. The exact same assert VERIFIES in
// `test_hide_then_reveal_verifies` where it sits AFTER the reveal, so the only
// difference is body position — precisely what the guard enforces. The guard
// fails the whole query closed (Err), so the result is never Verified. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn test_hide_reveal_brackets_assert_fails_closed(a: int, b: int) {
    trust_vc::hide!(f1);
    trust_vc::assert!(f1(a, a)); // provable ONLY via f1's body; bracketed → fail-closed
    trust_vc::reveal!(f1);
}
