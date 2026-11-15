// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for LANE 1a (Fn-bound n-ary application) — the ARITY-N widening of the
// Fn-bound closure lane (Increments 1 / 2a / 2b, previously UNARY). Verified via
// verify_function_from_file, cache-OFF.
//
// An `F: Fn(A, B, ..) -> R`-bounded value parameter `f: F` is typed as a
// first-class `SpecFn(A, B, .., R)` value (Increment 1, already n-ary), so an
// application `f(a, b, ..)` lowers to the opaque, congruent `spec_fn_apply` UF
// over the N-TUPLE (`dispatch/calls.rs`, widened for Lane 1a). So:
//   * two applications with EQUAL args are one congruent term, but an `Fn`
//     closure can read shared state (an atomic, a borrowed `Cell`), so
//     `f(3,4) == f(3,4)` is false at run time and its `Verified` answer is
//     refused, and
//   * the result is otherwise UNCONSTRAINED — `f(3,4) == 7` and `f(3,4) ==
//     f(3,5)` are NOT provable and COUNTEREXAMPLE.
// The callee-side obligation seam (`emit_fn_bound_param_application_obligations`,
// widened for Lane 1a) PROVES the applied precondition (H6 —
// Verus/vstd call semantics) and emits the SOUND conditional assume over the
// opaque n-ary reflection UFs `call_requires%` / `call_ensures%`:
//   PROVE   call_requires%(f, (a, b))
//   ASSUME  call_requires%(f, (a, b))  ==>  call_ensures%(f, (a, b), f(a, b))
// binding the REAL returned `spec_fn_apply(f, (a, b))` term. The prove-requires
// GATES the assume-ensures (a callee using `f.ensures` without establishing
// `f.requires` fails closed). Pass-site linkage (`emit_closure_pass_site_linkage_facts`,
// already arity-agnostic) bridges a passed n-ary `closure!` literal's OWN concrete
// spec to those opaque UFs. `FnMut`/`FnOnce` stay fail-closed at every arity.
// Every determinism / trap fixture declares the `f.requires(..)` of each tuple it
// applies (before H6 the requires was only an antecedent and requires-free
// determinism verified); each determinism fixture has a requires-free
// `*_no_requires_cx` twin that counterexamples on the call-site requires.

// ===========================================================================
// TYPING / DETERMINISM (arity-2). MUST BE REFUSED. Two applications with EQUAL
// args are one term of the congruent `spec_fn_apply` UF over the 2-tuple, which
// proves them equal; a stateful `Fn` closure does not. The refusal comes only
// from a `Verified` answer, so it is also the witness that the n-ary `SpecFn`
// typing took effect (without it the call fails closed, "Undefined function: f").
// ===========================================================================
#[trust_vc::requires(f.requires((3u64, 4u64)))]
fn nary2_determinism_refused<F: Fn(u64, u64) -> u64>(f: F) {
    let x = f(3u64, 4u64);
    let y = f(3u64, 4u64);
    trust_vc::assert!(x == y);
}

// H6 twin: requires-free arity-2 determinism is refuted on the call-site
// `f.requires((3, 4))`. MUST COUNTEREXAMPLE.
#[trust_vc::ensures(true)]
fn nary2_determinism_no_requires_cx<F: Fn(u64, u64) -> u64>(f: F) {
    let x = f(3u64, 4u64);
    let y = f(3u64, 4u64);
    trust_vc::assert!(x == y);
}

// ===========================================================================
// DETERMINISM via the where-clause spelling (where-predicate recognition path).
// MUST BE REFUSED.
// ===========================================================================
#[trust_vc::requires(f.requires((5u64, 6u64)))]
fn nary2_determinism_where_clause_refused<F>(f: F)
where
    F: Fn(u64, u64) -> u64,
{
    let x = f(5u64, 6u64);
    let y = f(5u64, 6u64);
    trust_vc::assert!(x == y);
}

// H6 twin (where-clause spelling). MUST COUNTEREXAMPLE on the call-site requires.
#[trust_vc::ensures(true)]
fn nary2_determinism_where_clause_no_requires_cx<F>(f: F)
where
    F: Fn(u64, u64) -> u64,
{
    let x = f(5u64, 6u64);
    let y = f(5u64, 6u64);
    trust_vc::assert!(x == y);
}

// ===========================================================================
// DETERMINISM FALSE-VERIFY TRAP (arity-2): DIFFERENT second arg — congruence
// gives nothing, so `f(3,4) == f(3,5)` COUNTEREXAMPLES. A `Verified` = congruence
// leaked across distinct args = UNSOUND.
// ===========================================================================
#[trust_vc::requires(f.requires((3u64, 4u64)) && f.requires((3u64, 5u64)))]
fn nary2_distinct_args_cx<F: Fn(u64, u64) -> u64>(f: F) {
    let x = f(3u64, 4u64);
    let y = f(3u64, 5u64);
    trust_vc::assert!(x == y);
}

// ===========================================================================
// CONCRETE TRAP (arity-2, no ensures): the result is UNCONSTRAINED, so pinning it
// to a concrete value is not provable. MUST COUNTEREXAMPLE (a `Verified` =
// inventing behaviour = UNSOUND). A Counterexample (NOT an "Undefined function"
// error) witnesses the term is modeled but unconstrained.
// ===========================================================================
#[trust_vc::requires(f.requires((3u64, 4u64)))]
fn nary2_concrete_trap_cx<F: Fn(u64, u64) -> u64>(f: F) {
    let r = f(3u64, 4u64);
    trust_vc::assert!(r == 7u64);
}

// ===========================================================================
// OBLIGATION (2a n-ary) POSITIVE — MUST VERIFY. Declares `requires
// f.requires((a, b))` (assumed at entry) + `ensures f.ensures((a, b), result)`,
// body `f(a, b)`. The call-site conditional assume over the 2-tuple, combined with
// the assumed precondition, derives `call_ensures%(f, (a, b), f(a, b))`; the return
// binds `result == f(a, b)`, so the postcondition discharges. Sound for ANY
// `F: Fn(u64, u64) -> u64`.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a, b))),
    ensures(f.ensures((a, b), result)),
    returns(result),
)]
fn nary2_obligation_positive<F: Fn(u64, u64) -> u64>(f: F, a: u64, b: u64) -> u64 {
    f(a, b)
}

// ===========================================================================
// OBLIGATION (2a n-ary) POSITIVE (let form) — MUST VERIFY. Same, application on a
// `let`-RHS (the straight-line `visit_expr_call` seam), returning the local.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a, b))),
    ensures(f.ensures((a, b), result)),
    returns(result),
)]
fn nary2_obligation_positive_let<F: Fn(u64, u64) -> u64>(f: F, a: u64, b: u64) -> u64 {
    let observed = f(a, b);
    observed
}

// ===========================================================================
// OBLIGATION TRAP #1 (opaque, not concrete) — MUST COUNTEREXAMPLE. The
// precondition is declared (so the ensures IS derivable), but `call_ensures%` is
// OPAQUE and pins no concrete value, so `r == 9` is not provable. A `Verified` =
// inventing a concrete result = UNSOUND.
// ===========================================================================
#[trust_vc::requires(f.requires((a, b)))]
fn nary2_obligation_pins_concrete_result_cx<F: Fn(u64, u64) -> u64>(f: F, a: u64, b: u64) {
    let r = f(a, b);
    trust_vc::assert!(r == 9u64);
}

// ===========================================================================
// OBLIGATION TRAP #2 (missing prove-requires) — MUST COUNTEREXAMPLE. USES
// `f.ensures` as the postcondition but declares NO `requires f.requires((a, b))`.
// `call_requires%(f, (a, b))` is unconstrained, so the conditional assume cannot
// fire and the postcondition is underivable. Using the ensures WITHOUT discharging
// the (opaque, non-trivial) requires would be UNSOUND. The load-bearing gate.
// ===========================================================================
#[trust_vc::contract(
    ensures(f.ensures((a, b), result)),
    returns(result),
)]
fn nary2_obligation_missing_requires_cx<F: Fn(u64, u64) -> u64>(f: F, a: u64, b: u64) -> u64 {
    f(a, b)
}

// ===========================================================================
// OBLIGATION ANTI-VACUITY / binds-the-REAL-return — MUST COUNTEREXAMPLE. Declares
// BOTH requires (so `call_ensures%(f, (a, b), f(a, b))` IS derivable) AND ensures,
// but RETURNS a value other than `f(a, b)`. The assume pins the postcondition to
// `f(a, b)`, NOT to `5`, so `f.ensures((a, b), result)` with `result == 5` is not
// derivable. A `Verified` = the ensures is trivially true = UNSOUND.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a, b))),
    ensures(f.ensures((a, b), result)),
    returns(result),
)]
fn nary2_obligation_wrong_return_cx<F: Fn(u64, u64) -> u64>(f: F, a: u64, b: u64) -> u64 {
    let _ = f(a, b);
    5u64
}

// ===========================================================================
// PASS-SITE (2b n-ary) SHARED CALLEE. An `F: Fn(u64, u64) -> u64` value parameter
// used through its own spec. Collected as a sibling helper contract by every
// caller below.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a, b))),
    ensures(f.ensures((a, b), result)),
    returns(result),
)]
fn nary2_apply_callee<F: Fn(u64, u64) -> u64>(f: F, a: u64, b: u64) -> u64 {
    f(a, b)
}

// ===========================================================================
// PASS-SITE (2b n-ary) POSITIVE ROUND-TRIP — MUST VERIFY. The caller passes a
// concrete 2-ary closure `c` (requires `x < 10 && y < 10`, ensures `r == x + y`)
// into the callee at `g(c, 3, 4)`. The pass-site linkage discharges `g`'s
// prove-`requires` from `c`'s `3 < 10 && 4 < 10` (true) and pins `g`'s assumed
// `ensures` to `c`'s `z == 3 + 4`, so `assert!(z == 7)` holds.
// ===========================================================================
#[trust_vc::ensures(true)]
fn nary2_pass_site_positive() {
    let c = trust_vc::closure!(
        |x: u64, y: u64| -> u64
        requires(x < 10u64 && y < 10u64)
        ensures(|r: u64| r == x + y)
        x + y
    );
    let z = nary2_apply_callee(c, 3u64, 4u64);
    trust_vc::assert!(z == 7u64);
}

// ===========================================================================
// PASS-SITE (2b n-ary) REQUIRES-VIOLATION TRAP — MUST COUNTEREXAMPLE. `c` requires
// `x < 10`, but the call passes `50` for the first arg. The linkage pins
// `call_requires%(c, (50, 4)) == (50 < 10 && 4 < 10) == false`, so `g`'s
// prove-`requires` obligation is false. A `Verified` = admitting a call that
// violates the closure's precondition = UNSOUND.
// ===========================================================================
#[trust_vc::ensures(true)]
fn nary2_pass_site_requires_violation_cx() {
    let c = trust_vc::closure!(
        |x: u64, y: u64| -> u64
        requires(x < 10u64 && y < 10u64)
        ensures(|r: u64| r == x + y)
        x + y
    );
    let z = nary2_apply_callee(c, 50u64, 4u64);
    trust_vc::assert!(z == 54u64);
}

// ===========================================================================
// PASS-SITE (2b n-ary) FALSE-ENSURES-USE TRAP — MUST COUNTEREXAMPLE. The call is
// valid (`3 < 10 && 4 < 10`), so the ensures linkage fires and pins `z == 7`, but
// the caller asserts `z == 8`. A `Verified` = the linked ensures did not actually
// constrain the result = UNSOUND.
// ===========================================================================
#[trust_vc::ensures(true)]
fn nary2_pass_site_false_ensures_use_cx() {
    let c = trust_vc::closure!(
        |x: u64, y: u64| -> u64
        requires(x < 10u64 && y < 10u64)
        ensures(|r: u64| r == x + y)
        x + y
    );
    let z = nary2_apply_callee(c, 3u64, 4u64);
    trust_vc::assert!(z == 8u64);
}

// ===========================================================================
// PASS-SITE (2b n-ary) LYING-CLOSURE TRAP — MUST COUNTEREXAMPLE. `c` CLAIMS
// `ensures r == x + y` but its body returns `x + y + 1`. The closure's INDEPENDENT
// def-side obligation (run in an isolated child at `let c = …`) fails and sinks the
// DEFINING function, regardless of the pass site. The 2b linkage (which faithfully
// pins `c`'s WRITTEN ensures) must NOT mask that def-side counterexample.
// ===========================================================================
#[trust_vc::ensures(true)]
fn nary2_pass_site_lying_closure_cx() {
    let c = trust_vc::closure!(
        |x: u64, y: u64| -> u64
        requires(x < 10u64 && y < 10u64)
        ensures(|r: u64| r == x + y)
        x + y + 1u64
    );
    let z = nary2_apply_callee(c, 3u64, 4u64);
    trust_vc::assert!(z == 7u64);
}

// ===========================================================================
// PASS-SITE (2b n-ary) FN-BOUND-PARAM-REPASS TRAP — MUST NOT VERIFY. The wrapper's
// Fn-bound parameter `f` is re-passed to the callee at `g(f, 3, 4)`. `f` is NOT a
// registered closure literal, so NO pass-site ground fact is emitted; `g`'s
// prove-`requires` (`call_requires%(f, (3, 4))`) is the opaque UF with nothing to
// discharge it. A `Verified` = a re-passed param wrongly received a linkage =
// UNSOUND. Fails closed.
// ===========================================================================
#[trust_vc::ensures(true)]
fn nary2_pass_site_param_repass_fail_closed<F: Fn(u64, u64) -> u64>(f: F) {
    let z = nary2_apply_callee(f, 3u64, 4u64);
    trust_vc::assert!(z == 7u64);
}

// ===========================================================================
// REGRESSION: `FnMut(u64, u64) -> u64` stays fail-closed at arity-2 (non-
// deterministic; not typed `SpecFn`, so the application is rejected at extraction
// — "function value"). MUST NOT VERIFY.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnmut2_fail_closed<F: FnMut(u64, u64) -> u64>(mut f: F) {
    let x = f(3u64, 4u64);
    let y = f(3u64, 4u64);
    trust_vc::assert!(x == y);
}

// ===========================================================================
// REGRESSION: `FnOnce(u64, u64) -> u64` stays fail-closed at arity-2. MUST NOT
// VERIFY.
// ===========================================================================
#[trust_vc::ensures(true)]
fn fnonce2_fail_closed<F: FnOnce(u64, u64) -> u64>(f: F) {
    let r = f(3u64, 4u64);
    trust_vc::assert!(r == r);
}

// ===========================================================================
// ARITY-0 SANITY (unit-arg, `Fn() -> u64`): `f() == f()` is one term of the
// congruent UF over the empty tuple, but a nullary `Fn` closure can return a
// counter. MUST BE REFUSED.
// ===========================================================================
#[trust_vc::requires(f.requires(()))]
fn nary0_determinism_refused<F: Fn() -> u64>(f: F) {
    let x = f();
    let y = f();
    trust_vc::assert!(x == y);
}

// H6 twin: requires-free nullary determinism. MUST COUNTEREXAMPLE on the
// call-site `f.requires(())`.
#[trust_vc::ensures(true)]
fn nary0_determinism_no_requires_cx<F: Fn() -> u64>(f: F) {
    let x = f();
    let y = f();
    trust_vc::assert!(x == y);
}

// ===========================================================================
// ARITY-0 SANITY TRAP: the nullary result is UNCONSTRAINED. `f() == 5` is not
// provable. MUST COUNTEREXAMPLE.
// ===========================================================================
#[trust_vc::requires(f.requires(()))]
fn nary0_concrete_trap_cx<F: Fn() -> u64>(f: F) {
    let r = f();
    trust_vc::assert!(r == 5u64);
}

// ===========================================================================
// ARITY-3 SANITY: two applications over the same 3-tuple. MUST BE REFUSED.
// ===========================================================================
#[trust_vc::requires(f.requires((1u64, 2u64, 3u64)))]
fn nary3_determinism_refused<F: Fn(u64, u64, u64) -> u64>(f: F) {
    let x = f(1u64, 2u64, 3u64);
    let y = f(1u64, 2u64, 3u64);
    trust_vc::assert!(x == y);
}

// H6 twin: requires-free arity-3 determinism. MUST COUNTEREXAMPLE on the
// call-site requires.
#[trust_vc::ensures(true)]
fn nary3_determinism_no_requires_cx<F: Fn(u64, u64, u64) -> u64>(f: F) {
    let x = f(1u64, 2u64, 3u64);
    let y = f(1u64, 2u64, 3u64);
    trust_vc::assert!(x == y);
}

// ===========================================================================
// ARITY-3 SANITY TRAP: a differing third arg breaks congruence, so `f(1,2,3) ==
// f(1,2,4)` COUNTEREXAMPLES. MUST COUNTEREXAMPLE.
// ===========================================================================
#[trust_vc::requires(f.requires((1u64, 2u64, 3u64)) && f.requires((1u64, 2u64, 4u64)))]
fn nary3_distinct_args_cx<F: Fn(u64, u64, u64) -> u64>(f: F) {
    let x = f(1u64, 2u64, 3u64);
    let y = f(1u64, 2u64, 4u64);
    trust_vc::assert!(x == y);
}

// ===========================================================================
// ARITY-3 OBLIGATION POSITIVE — MUST VERIFY. Confirms the widened obligation seam
// generalizes past arity-2. Declares requires + ensures over the 3-tuple.
// ===========================================================================
#[trust_vc::contract(
    requires(f.requires((a, b, c))),
    ensures(f.ensures((a, b, c), result)),
    returns(result),
)]
fn nary3_obligation_positive<F: Fn(u64, u64, u64) -> u64>(f: F, a: u64, b: u64, c: u64) -> u64 {
    f(a, b, c)
}
