// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// quality-audit: allow-file allow-rust-size — fixtures read by name by one suite
// Fixtures for the H6 closure-application requires capability suite
// (`closure_application_requires_soundness.rs`). Verified via
// verify_function_from_file, cache-OFF.
//
// THE HOLE (measured before the fix): an application `CALLEE(args)`
// of a closure or other function VALUE proved no precondition in three lanes, and
// the only fail-closed left was a LOWERING error that never fires when the call's
// result is unused (`let _t = f(..)`, a unit statement, a discarded tail, or a
// reflexive `t == t`):
//   (1) a let-bound `closure!` applied at arity != 1 (the extraction seam was
//       unary-only);
//   (2) a `closure!` LITERAL applied directly (unary too) — not a registered
//       callee, so no seam fired;
//   (3) an `F: Fn(..)` parameter applied without `f.requires(..)` — the
//       requires was folded into an assumed implication, never proven;
//   plus every value callee the seams never recognized (FnMut / FnOnce /
//   `impl Fn` / generic params, aliases, block initializers, tuple fields,
//   `if`-selected callees, returned closures, function-item aliases).
// In a non-test build `closure!` expands `requires` to a runtime `assert!`, so
// every liar below PANICS at runtime; the div/overflow liars panic in a test
// build too.
//
// THE RULE: every application either PROVES the callee's precondition at the
// call's shared program point, or fails closed at EXTRACTION time with a
// "function value" diagnostic. Lowering-time failure never counts.

// ===========================================================================
// UNARY CONTROLS (already correct before the fix)
// ===========================================================================
#[trust_vc::ensures(true)]
fn l0a_unary_bad_requires_cx() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f(3u64);
}

#[trust_vc::ensures(true)]
fn l0b_unary_good_requires_verified() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let t = f(0u64);
    trust_vc::assert!(t == 0u64);
}

// ===========================================================================
// R1 LIARS — let-bound n-ary / nullary `closure!`: the requires is PROVEN.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l1a_nary_bad_requires_unused() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f(3u64, 4u64);
}

#[trust_vc::ensures(true)]
fn l1b_nary_param_div(x: u64) {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(b > 0u64)
        ensures(|z: u64| z == a / b)
        a / b
    );
    let _t = f(x, x);
}

#[trust_vc::ensures(true)]
fn l1c_nary_unit_stmt() {
    let f = trust_vc::closure!(|a: u64, b: u64| -> () requires(a == b) ());
    f(3u64, 4u64);
}

#[trust_vc::ensures(true)]
fn l1d_nary3_bad_requires() {
    let f = trust_vc::closure!(
        |a: u64, b: u64, c: u64| -> u64
        requires(a == b && b == c)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f(1u64, 2u64, 3u64);
}

#[trust_vc::ensures(true)]
fn l1e_nullary_requires_false() {
    let f = trust_vc::closure!(
        || -> u64
        requires(false)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let _t = f();
}

#[trust_vc::ensures(true)]
fn l1f_nary_tail_bad_requires() -> u64 {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    f(3u64, 4u64)
}

#[trust_vc::ensures(true)]
fn l1g_nary_in_assert_reflexive() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    trust_vc::assert!(f(3u64, 4u64) == f(3u64, 4u64));
}

#[trust_vc::ensures(true)]
fn l1h_nary_in_loop(n: u64) {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let _t = f(3u64, 4u64);
        i = i + 1u64;
    }
}

#[trust_vc::ensures(true)]
fn l1i_nary_branch_unguarded(c: bool) {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    if c {
        let _t = f(3u64, 4u64);
    }
}

#[trust_vc::ensures(true)]
fn l1u_nary_method_chain() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f(3u64, 4u64).wrapping_add(1u64);
}

#[trust_vc::ensures(true)]
fn l1v_nary_match_scrutinee() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    match f(3u64, 4u64) {
        _ => {}
    }
}

// The body divides by the second argument; applied at 0 it panics in EVERY build.
#[trust_vc::ensures(true)]
fn l1w_nary_div_zero_body() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(b > 0u64)
        ensures(|z: u64| z == a / b)
        a / b
    );
    let _t = f(3u64, 0u64);
}

// The body overflows at (u64::MAX, 1); it panics in EVERY build.
#[trust_vc::ensures(true)]
fn l1x_nary_overflow_body() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a < 100u64 && b < 100u64)
        ensures(|z: u64| z == a + b)
        a + b
    );
    let _t = f(18446744073709551615u64, 1u64);
}

// ===========================================================================
// R1 CONTROLS
// ===========================================================================

// Non-vacuity: the context after a bad n-ary call still refutes `false`.
#[trust_vc::ensures(true)]
fn l1y_nary_false_tail_after_bad_call() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f(3u64, 4u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn l1j_nary_branch_guarded_ok(p: u64, q: u64) {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    if p == q {
        let _t = f(p, q);
    }
    trust_vc::assert!(p == p);
}

#[trust_vc::ensures(true)]
fn l1k_nary_ensures_used_ok() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a < 100u64 && b < 100u64)
        ensures(|z: u64| z == a + b)
        a + b
    );
    let t = f(1u64, 2u64);
    trust_vc::assert!(t == 3u64);
}

#[trust_vc::ensures(true)]
fn l1l_nary_ensures_used_liar() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a < 100u64 && b < 100u64)
        ensures(|z: u64| z == a + b)
        a + b
    );
    let t = f(1u64, 2u64);
    trust_vc::assert!(t == 4u64);
}

// A lying n-ary closure: the def-side check poisons the parent even though the
// call site now assumes the (unchecked-by-the-call) ensures.
#[trust_vc::ensures(true)]
fn l1m_nary_lying_closure() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a < 100u64 && b < 100u64)
        ensures(|z: u64| z == a + b)
        a + b + 1u64
    );
    let t = f(1u64, 2u64);
    trust_vc::assert!(t == 3u64);
}

#[trust_vc::ensures(true)]
fn l1n_nullary_ok() {
    let f = trust_vc::closure!(
        || -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f();
    trust_vc::assert!(t == 7u64);
}

#[trust_vc::ensures(true)]
fn l1o_nullary_liar() {
    let f = trust_vc::closure!(
        || -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f();
    trust_vc::assert!(t == 8u64);
}

#[trust_vc::ensures(true)]
fn l1z_nary_good_requires_verified() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let t = f(3u64, 3u64);
    trust_vc::assert!(t == 3u64);
}

// ===========================================================================
// R1b LIARS — a `closure!` binding that is NOT registered (no `-> T`, a
// non-ident pattern) must still hide every outer binding of the same name and
// must not be applied without a proven requires.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l1p_unregistered_no_ret_ty() {
    let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a);
    let _t = f(3u64);
}

#[trust_vc::ensures(true)]
fn l1q_unregistered_shadows_registered() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    {
        let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
        let t = f(3u64);
        trust_vc::assert!(t == 3u64);
    }
    let _u = f(1u64);
}

#[trust_vc::ensures(true)]
fn l1r_unregistered_shadows_bare() {
    let f = |a: u64| a;
    let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
    let t = f(3u64);
    trust_vc::assert!(t == 3u64);
}

#[trust_vc::ensures(true)]
fn l1s_paren_pattern_binding() {
    let (f) = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f(3u64);
}

// Control: a typed pattern already registers; the requires is proven.
#[trust_vc::ensures(true)]
fn l1t_typed_pattern_binding_cx() {
    let f: fn(u64) -> u64 = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f(3u64);
}

// ===========================================================================
// LANE 2 — a `closure!` LITERAL applied directly is not a modelled callee: it
// fails closed at extraction (unary included).
// ===========================================================================
#[trust_vc::ensures(true)]
fn l2a_literal_unary_bad() {
    let _t = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    )(3u64);
}

#[trust_vc::ensures(true)]
fn l2b_literal_unary_param_div(x: u64) {
    let _t = trust_vc::closure!(
        |b: u64| -> u64
        requires(b > 0u64)
        ensures(|z: u64| z == 100u64 / b)
        100u64 / b
    )(x);
}

#[trust_vc::ensures(true)]
fn l2c_literal_nary_bad() {
    let _t = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    )(3u64, 4u64);
}

#[trust_vc::ensures(true)]
fn l2d_paren_literal(x: u64) {
    let _t = (trust_vc::closure!(
        |b: u64| -> u64
        requires(b > 0u64)
        ensures(|z: u64| z == 100u64 / b)
        100u64 / b
    ))(x);
}

// Documented incompleteness: a TRUE claim over a directly applied literal also
// fails closed (it already failed at lowering with "non-path function call").
#[trust_vc::ensures(true)]
fn l2e_literal_true_claim() {
    let t = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    )(0u64);
    trust_vc::assert!(t == 0u64);
}

// Control: an immediately-invoked BARE closure keeps its body instrumentation.
#[trust_vc::ensures(true)]
fn l2f_ctrl_bare_iife_div0() {
    let _t = (|a: u64, b: u64| a / b)(3u64, 0u64);
}

// ===========================================================================
// R3 LIARS — an `F: Fn(..)` parameter applied without `f.requires(..)`.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l3a_fnbound_unary_no_requires<F: Fn(u64) -> u64>(f: F) {
    let _x = f(0u64);
}

#[trust_vc::ensures(true)]
fn l3b_fnbound_nary_no_requires<F: Fn(u64, u64) -> u64>(f: F) {
    let _x = f(3u64, 0u64);
}

#[trust_vc::ensures(true)]
fn l3c_fnbound_nullary_no_requires<F: Fn() -> u64>(f: F) {
    let _x = f();
}

// Required at 0, applied at 1.
#[trust_vc::requires(f.requires((0u64,)))]
fn l3d_fnbound_requires_other_arg<F: Fn(u64) -> u64>(f: F) {
    let _x = f(1u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l3g_fnbound_determinism_no_requires<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// ===========================================================================
// R3 CONTROLS. The determinism controls call an `Fn` parameter twice with
// the applied requires declared, so the call-site obligations hold; the
// `Verified` answer is then refused by the repeated-callable rule (a stateful
// `Fn` closure returns two values).
// ===========================================================================
#[trust_vc::requires(f.requires((0u64,)))]
fn l3e_fnbound_requires_same_arg_verified<F: Fn(u64) -> u64>(f: F) {
    let _x = f(0u64);
}

#[trust_vc::requires(f.requires((3u64,)))]
fn l3f_fnbound_determinism_refused<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

#[trust_vc::requires(f.requires((3u64, 4u64)))]
fn l3h_fnbound_nary_determinism_refused<F: Fn(u64, u64) -> u64>(f: F) {
    let a = f(3u64, 4u64);
    let b = f(3u64, 4u64);
    trust_vc::assert!(a == b);
}

#[trust_vc::requires(f.requires(()))]
fn l3i_fnbound_nullary_determinism_refused<F: Fn() -> u64>(f: F) {
    let a = f();
    let b = f();
    trust_vc::assert!(a == b);
}

#[trust_vc::requires(f.requires((3u64,)) && f.requires((4u64,)))]
fn l3j_fnbound_distinct_args_cx<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(4u64);
    trust_vc::assert!(a == b);
}

// Whole program: the callee requires what it applies; the caller's pass site
// links the closure's own requires.
#[trust_vc::requires(f.requires((0u64,)))]
fn l3k_apply1u_req<F: Fn(u64) -> u64>(f: F) {
    let _x = f(0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l3l_caller_passes_div_closure() {
    let c = trust_vc::closure!(
        |b: u64| -> u64
        requires(b > 0u64)
        ensures(|z: u64| z == 100u64 / b)
        100u64 / b
    );
    l3k_apply1u_req(c);
}

#[trust_vc::ensures(true)]
fn l3m_caller_passes_good_closure() {
    let c = trust_vc::closure!(
        |b: u64| -> u64
        requires(b < 10u64)
        ensures(|z: u64| z == b)
        b
    );
    l3k_apply1u_req(c);
}

// The H6 whole-program shape: a requires-free callee is itself refuted now.
#[trust_vc::ensures(true)]
fn l3n_apply2u_no_requires<F: Fn(u64, u64) -> u64>(f: F) {
    let _x = f(3u64, 0u64);
    trust_vc::assert!(true);
}

// ===========================================================================
// R4 LIARS — value callees no seam models: fail closed at extraction.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l4a_fnmut_param<F: FnMut(u64) -> u64>(mut f: F) {
    let _x = f(0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4b_fnonce_param<F: FnOnce(u64) -> u64>(f: F) {
    let _x = f(0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4c_impl_fn_param(f: impl Fn(u64) -> u64) {
    let _x = f(0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4d_where_fnmut_param<F>(mut f: F)
where
    F: FnMut(u64) -> u64,
{
    let _x = f(0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4e_generic_fn_param<T, F: Fn(T) -> T>(f: F, t: T) {
    let _x = f(t);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4f_alias_registered() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let g = f;
    let _t = g(3u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4g_block_init() {
    let g = {
        trust_vc::closure!(
            |a: u64| -> u64
            requires(a == 0u64)
            ensures(|z: u64| z == a)
            a
        )
    };
    let _t = g(3u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4h_tuple_field() {
    let p = (
        trust_vc::closure!(
            |a: u64| -> u64
            requires(a == 0u64)
            ensures(|z: u64| z == a)
            a
        ),
        1u64,
    );
    let _t = (p.0)(3u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4i_if_else_callee(b: bool) {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let g = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 1u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = (if b { f } else { g })(3u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4j_alias_bare_div0() {
    let f = |b: u64| 100u64 / b;
    let g = f;
    let _t = g(0u64);
    trust_vc::assert!(true);
}

fn l4k_make_closure() -> impl Fn(u64) -> u64 {
    |b: u64| 100u64 / b
}

#[trust_vc::ensures(true)]
fn l4k_returned_closure() {
    let g = l4k_make_closure();
    let _t = g(0u64);
    trust_vc::assert!(true);
}

#[trust_vc::requires(x == 4u8 || x == 7u8)]
#[trust_vc::ensures(result == (x == 4u8))]
fn l4_llama(x: u8) -> bool {
    x == 4u8
}

#[trust_vc::ensures(true)]
fn l4l_fn_item_alias_bad_requires() {
    let t = l4_llama;
    let _b = t(5u8);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4o_fn_pointer_param(f: fn(u64) -> u64) {
    let _x = f(0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l4p_dyn_fn_param(f: &dyn Fn(u64) -> u64) {
    let _x = f(0u64);
    trust_vc::assert!(true);
}

// ===========================================================================
// R4 CONTROLS — function items and requires-free function-item aliases.
// ===========================================================================
fn l4_plain_one_arg(_i: u8) {}

#[trust_vc::ensures(true)]
fn l4m_plain_fn_item_alias_verified() {
    let x = l4_plain_one_arg;
    x(0u8);
    let y = 1u8;
    trust_vc::assert!(y == 1u8);
}

#[trust_vc::ensures(true)]
fn l4q_direct_contracted_helper_bad_requires_cx() {
    let _b = l4_llama(5u8);
    trust_vc::assert!(true);
}

// ===========================================================================
// R4 LIARS (continued) — pattern-bound, field, reference and qualified callees.
// Measured fail-closed with the R4 classifier (not measured before it).
// ===========================================================================
#[trust_vc::ensures(true)]
fn l4r_match_bound_callee() {
    let f = |b: u64| 100u64 / b;
    match Some(f) {
        Some(g) => {
            let _t = g(0u64);
        }
        None => {}
    }
}

#[trust_vc::ensures(true)]
fn l4s_if_let_bound_callee() {
    let f = |b: u64| 100u64 / b;
    if let Some(g) = Some(f) {
        let _t = g(0u64);
    }
}

#[trust_vc::ensures(true)]
fn l4t_for_bound_callee() {
    let f = |b: u64| 100u64 / b;
    for g in [f] {
        let _t = g(0u64);
    }
}

struct L4Holder<F: Fn(u64) -> u64> {
    g: F,
}

#[trust_vc::ensures(true)]
fn l4u_struct_field_callee() {
    let f = |b: u64| 100u64 / b;
    let h = L4Holder { g: f };
    let _t = (h.g)(0u64);
}

#[trust_vc::ensures(true)]
fn l4v_reference_callee() {
    let f = |b: u64| 100u64 / b;
    let r = &f;
    let _t = r(0u64);
}

mod l4_m {
    pub fn plain(_x: u8) {}

    #[trust_vc::requires(x == 4u8)]
    #[trust_vc::ensures(result == true)]
    pub fn needs_four(x: u8) -> bool {
        x == 4u8
    }
}

#[trust_vc::ensures(true)]
fn l4w_qualified_fn_item_alias_bad_requires() {
    let t = l4_m::needs_four;
    let _b = t(5u8);
}

// Control: a requires-free QUALIFIED function-item alias keeps verifying.
#[trust_vc::ensures(true)]
fn l4x_qualified_plain_fn_item_alias_verified() {
    let t = l4_m::plain;
    t(0u8);
    let y = 1u8;
    trust_vc::assert!(y == 1u8);
}

// ===========================================================================
// R5 LIARS — a STALE closure model after the binding changes. A destructuring
// or valued `let` must hide an outer registered contract of the same name, and
// a `mut` binding ascribed a fn-pointer type (which can later hold other code
// through `=`, a `&mut` write or `mem::replace`) is never modelled. MEASURED
// on this branch with R1-R4 in place and before the R5 rules: every fixture
// except `l5e` returned Verified (each assertion is false / each application
// panics at run time); `l5e` was already fail-closed and is pinned so it stays.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l5a_destructure_shadows_registered() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let g = |a: u64| a + 1u64;
    let (f, _k) = (g, 1u64);
    let t = f(3u64);
    trust_vc::assert!(t == 3u64);
}

#[trust_vc::ensures(true)]
fn l5b_valued_let_shadows_registered() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let g = |a: u64| a + 1u64;
    let f = g;
    let t = f(3u64);
    trust_vc::assert!(t == 3u64);
}

#[trust_vc::ensures(true)]
fn l5c_fn_item_let_shadows_registered() {
    let f = trust_vc::closure!(
        |a: u8| -> bool
        requires(true)
        ensures(|z: bool| z == true)
        true
    );
    let _u = f(1u8);
    let f = l4_llama;
    let t = f(5u8);
    trust_vc::assert!(t == true);
}

#[trust_vc::ensures(true)]
fn l5d_if_value_let_shadows_registered(c: bool) {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let g = |a: u64| a + 1u64;
    let f = if c { g } else { g };
    let t = f(3u64);
    trust_vc::assert!(t == 3u64);
}

#[trust_vc::ensures(true)]
fn l5e_match_arm_shadows_registered() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let g = |a: u64| a + 1u64;
    match g {
        f => {
            let t = f(3u64);
            trust_vc::assert!(t == 3u64);
        }
    }
}

fn l5_div1(a: u64) -> u64 {
    a / 1u64
}

#[trust_vc::ensures(true)]
fn l5f_fn_ptr_closure_reassigned() {
    let mut f: fn(u64) -> u64 = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let _u = f(1u64);
    f = l5_div1;
    let t = f(3u64);
    trust_vc::assert!(t == 7u64);
}

#[trust_vc::ensures(true)]
fn l5g_fn_ptr_closure_deref_written() {
    let mut f: fn(u64) -> u64 = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let _u = f(1u64);
    {
        let r = &mut f;
        *r = l5_div1;
    }
    let t = f(3u64);
    trust_vc::assert!(t == 7u64);
}

#[trust_vc::ensures(true)]
fn l5h_fn_ptr_closure_mem_replaced() {
    let mut f: fn(u64) -> u64 = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let _u = f(1u64);
    let _old = core::mem::replace(&mut f, l5_div1);
    let t = f(3u64);
    trust_vc::assert!(t == 7u64);
}

#[trust_vc::ensures(true)]
fn l5i_fn_ptr_closure_block_assigned() {
    let mut f: fn(u64) -> u64 = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let _u = f(1u64);
    {
        f = l5_div1;
    }
    let t = f(3u64);
    trust_vc::assert!(t == 7u64);
}

#[trust_vc::ensures(true)]
fn l5j_bare_fn_ptr_deref_written_div0() {
    let mut f: fn(u64) -> u64 = |a: u64| a;
    {
        let r = &mut f;
        *r = |b: u64| 100u64 / b;
    }
    let _t = f(0u64);
}

#[trust_vc::ensures(true)]
fn l5k_bare_fn_ptr_mem_replaced_div0() {
    let mut f: fn(u64) -> u64 = |a: u64| a;
    let _old = core::mem::replace(&mut f, |b: u64| 100u64 / b);
    let _t = f(0u64);
}

#[trust_vc::ensures(true)]
fn l5l_bare_fn_ptr_block_assigned_div0() {
    let mut f: fn(u64) -> u64 = |a: u64| a;
    {
        f = |b: u64| 100u64 / b;
    }
    let _t = f(0u64);
}

#[trust_vc::ensures(true)]
fn l5m_bare_fn_ptr_branch_assigned_div0(c: bool) {
    let mut f: fn(u64) -> u64 = |a: u64| a;
    if c {
        f = |b: u64| 100u64 / b;
    }
    let _t = f(0u64);
}

// KNOWN OVER-REJECTION, recorded rather than left implicit (minor): the four
// liars above are all reached through the SAME `mut`-ascribed
// binding, which is why such a binding is never modelled — and a binding that
// is in fact never reassigned pays the same price. Fail-closed, and a total,
// requires-free closure: the refusal is the conservative reassignment rule, not
// a precondition. Deciding it would need a no-reassignment-reaches-this-call
// analysis covering `f = ..`, `*(&mut f) = ..` and `mem::replace`.
#[trust_vc::ensures(true)]
fn l5n_bare_fn_ptr_never_reassigned_refused() {
    let mut f: fn(u64) -> u64 = |a: u64| a;
    let _t = f(3u64);
}

// ===========================================================================
// R5 CONTROLS
// ===========================================================================

// An inner shadow ends with its block; the outer registered closure is back.
#[trust_vc::ensures(true)]
fn l5n_inner_shadow_restores_verified() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    {
        let f = |a: u64| a + 1u64;
        let _v = f(3u64);
    }
    let t = f(3u64);
    trust_vc::assert!(t == 3u64);
}

#[trust_vc::ensures(true)]
fn l5o_inner_shadow_restores_liar() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    {
        let f = |a: u64| a + 1u64;
        let _v = f(3u64);
    }
    let t = f(3u64);
    trust_vc::assert!(t == 4u64);
}

// An unascribed `let mut` closure has the closure's unique type (it cannot hold
// other code), so it stays modelled.
#[trust_vc::ensures(true)]
fn l5p_mut_unascribed_closure_verified() {
    let mut f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f(3u64);
    trust_vc::assert!(t == 7u64);
}

#[trust_vc::ensures(true)]
fn l5q_mut_unascribed_closure_liar() {
    let mut f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f(3u64);
    trust_vc::assert!(t == 8u64);
}

// ===========================================================================
// R6 LIARS — `const` / `static` function values (a fn pointer to a helper
// WITH a requires). MEASURED with R1-R5 in place and before R6: all Verified.
// ===========================================================================
const L6_G: fn(u8) -> bool = l4_llama;
static L6_S: fn(u8) -> bool = l4_llama;

mod l6_m {
    pub const MG: fn(u8) -> bool = super::l4_llama;
}

struct L6W;

impl L6W {
    const WG: fn(u8) -> bool = l4_llama;
}

#[trust_vc::ensures(true)]
fn l6a_const_fn_ptr_callee() {
    let _b = L6_G(5u8);
}

#[trust_vc::ensures(true)]
fn l6b_static_fn_ptr_callee() {
    let _b = L6_S(5u8);
}

#[trust_vc::ensures(true)]
fn l6c_module_const_fn_ptr_callee() {
    let _b = l6_m::MG(5u8);
}

#[trust_vc::ensures(true)]
fn l6d_assoc_const_fn_ptr_callee() {
    let _b = L6W::WG(5u8);
}

// ===========================================================================
// R7 — a `mut` Fn-bound parameter can hold a DIFFERENT closure (`f = g`, a
// branch write, `mem::swap`), so it is not modelled and its application fails
// closed. MEASURED fail-closed at this revision (s1/s4/s6 shapes already by the
// R4/R5 rules; `l7c` is the loop-havoc shape the `mut` rule makes fail-closed,
// which was a solver Unknown on the loop invariant without it).
// ===========================================================================
#[trust_vc::requires(f.requires((3u64,)))]
fn l7a_mut_param_branch_reassigned<F: Fn(u64) -> u64>(mut f: F, g: F, c: bool) {
    if c {
        f = g;
    }
    let _x = f(3u64);
}

#[trust_vc::requires(f.requires((3u64,)))]
fn l7b_mut_param_mem_swapped<F: Fn(u64) -> u64>(mut f: F, mut g: F) {
    core::mem::swap(&mut f, &mut g);
    let _x = f(3u64);
}

#[trust_vc::requires(f.requires((3u64,)))]
fn l7c_mut_param_loop_assigned<F: Fn(u64) -> u64 + Copy>(mut f: F, g: F, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        f = g;
        i = i + 1u64;
    }
    let _x = f(3u64);
}

// R6 (qualified-self spelling). MEASURED before its rule: Verified.
#[trust_vc::ensures(true)]
fn l6e_qself_const_fn_ptr_callee() {
    let _b = <L6W>::WG(5u8);
}

// ===========================================================================
// R8 — blocker 1: an application inside MACRO TOKENS. A call in
// an `assert!` / `assume!` / `invariant!` / `vec!` never reaches the straight-
// line walk, and a callee name hidden by a later binding still lowered against
// the STALE declared `SpecFn` variable of the earlier binding, so the requires
// of the value the name actually holds was never proven. These were Verified
// while the statement-position twins already failed closed.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l8a_unregistered_shadow_in_assert() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
    trust_vc::assert!(f(3u64) == f(3u64));
}

#[trust_vc::ensures(true)]
fn l8b_item_alias_shadow_in_assert() {
    let f = trust_vc::closure!(
        |a: u8| -> bool
        requires(true)
        ensures(|z: bool| z == true)
        true
    );
    let _u = f(1u8);
    let f = l4_llama;
    trust_vc::assert!(f(5u8) == f(5u8));
}

#[trust_vc::requires(f.requires((3u64,)))]
fn l8c_fnbound_shadowed_by_unregistered_in_assert<F: Fn(u64) -> u64>(f: F) {
    let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
    trust_vc::assert!(f(3u64) == f(3u64));
}

#[trust_vc::ensures(true)]
fn l8d_destructure_shadow_in_assert() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let g = |b: u64| 100u64 / b;
    let (f, _k) = (g, 1u64);
    trust_vc::assert!(f(0u64) == f(0u64));
}

#[trust_vc::ensures(true)]
fn l8e_match_arm_shadow_in_assert() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let g = |b: u64| 100u64 / b;
    match g {
        f => {
            trust_vc::assert!(f(0u64) == f(0u64));
        }
    }
}

#[trust_vc::ensures(true)]
fn l8f_inner_block_unregistered_in_assert() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    {
        let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
        trust_vc::assert!(f(3u64) == f(3u64));
    }
    let _u = f(1u64);
}

#[trust_vc::ensures(true)]
fn l8g_unregistered_shadow_in_invariant() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
    let mut i = 0u64;
    while i < 1u64 {
        trust_vc::invariant!(i <= 1u64 && f(3u64) == f(3u64));
        i = i + 1u64;
    }
}

#[trust_vc::requires(f.requires((5u8,)))]
fn l8h_fnbound_shadowed_by_item_in_assert<F: Fn(u8) -> bool>(f: F) {
    let f = l4_llama;
    trust_vc::assert!(f(5u8) == f(5u8));
}

// Whole program: the caller passes `bad` as `g`; the callee's requires covers
// only the ORIGINAL `f`. MEASURED before the fix: callee AND caller Verified; the
// compiled program panics.
#[trust_vc::requires(f.requires((3u64,)))]
fn l8i_fnbound_shadowed_by_alias_in_assert<F: Fn(u64) -> u64, G: Fn(u64) -> u64>(f: F, g: G) {
    let f = g;
    trust_vc::assert!(f(3u64) == f(3u64));
}

#[trust_vc::ensures(true)]
fn l8i_caller() {
    let ok = trust_vc::closure!(
        |b: u64| -> u64
        requires(true)
        ensures(|z: u64| z == b)
        b
    );
    let bad = trust_vc::closure!(
        |b: u64| -> u64
        requires(b > 5u64)
        ensures(|z: u64| z == 100u64 / (b - 5u64))
        100u64 / (b - 5u64)
    );
    l8i_fnbound_shadowed_by_alias_in_assert(ok, bad);
}

#[trust_vc::requires(f.requires((3u64,)))]
fn l8j_fnbound_shadowed_if_let_in_assert<F: Fn(u64) -> u64, G: Fn(u64) -> u64>(f: F, g: G) {
    if let Some(f) = Some(g) {
        trust_vc::assert!(f(3u64) == f(3u64));
    }
}

#[trust_vc::ensures(true)]
fn l8k_unregistered_shadow_in_assert_nonreflexive() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
    trust_vc::assert!(f(3u64) >= 0u64);
}

// Inside a quantifier body of an assert (not rendered through the call path).
// MEASURED before the fix: a lowering Error ("non-path function call"), not a
// false Verified — pinned for the extraction-time refusal that no longer depends
// on the quantifier encoder rejecting the stale application.
#[trust_vc::ensures(true)]
fn l8l_unregistered_shadow_in_assert_forall() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(true)
        ensures(|z: u64| z == a)
        a
    );
    let _u = f(1u64);
    let f = trust_vc::closure!(|a: u64| requires(a == 0u64) a + 1u64);
    trust_vc::assert!(forall|i: u64| f(i) == f(i));
}

// A MODELLED application in a spec-macro condition that proves no call-site
// requires. MEASURED Verified before the fix.
#[trust_vc::ensures(true)]
fn l8m_registered_in_invariant() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let mut i = 0u64;
    while i < 1u64 {
        trust_vc::invariant!(i <= 1u64 && f(3u64) == f(3u64));
        i = i + 1u64;
    }
}

// `vec!` applies its elements at run time. MEASURED Verified before the fix.
#[trust_vc::ensures(true)]
fn l8n_registered_in_vec() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let _v = vec![f(3u64, 4u64)];
}

// Controls in the same context: the modelled assert lane still verifies a true
// claim and refutes its liar; `vec!` over plain items is untouched.
#[trust_vc::ensures(true)]
fn l8o_registered_in_assert_verified() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    trust_vc::assert!(f(0u64) == 0u64);
}

#[trust_vc::ensures(true)]
fn l8p_registered_in_assert_liar() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    trust_vc::assert!(f(0u64) == 1u64);
}

#[trust_vc::requires(f.requires((3u64,)))]
fn l8q_fnbound_in_assert_refused<F: Fn(u64) -> u64>(f: F) {
    trust_vc::assert!(f(3u64) == f(3u64));
}

#[trust_vc::requires(f.requires((3u64,)))]
fn l8r_fnbound_in_assert_liar<F: Fn(u64) -> u64>(f: F) {
    trust_vc::assert!(f(4u64) == f(4u64));
}

fn l8_leaf(x: u64) -> u64 {
    x
}

#[trust_vc::ensures(true)]
fn l8s_vec_plain_items_verified() {
    let _v = vec![l8_leaf(1u64), 2u64];
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn l8s_vec_plain_items_liar() {
    let _v = vec![l8_leaf(1u64), 2u64];
    trust_vc::assert!(false);
}

// Pointer-keyed call-site dedup across TRANSIENT proof-block trees: the second
// block's `f(3)` was allocated at the first block's `f(0)` address and skipped.
// MEASURED Verified before the per-macro dedup snapshot (a single block was
// already CXreq).
#[trust_vc::ensures(true)]
fn l8t_assert_by_blocks_second_application_liar() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    trust_vc::assert_by!(true, {
        let _a = f(0u64);
    });
    trust_vc::assert_by!(true, {
        let _b = f(3u64);
    });
}

#[trust_vc::ensures(true)]
fn l8u_assert_by_blocks_both_applications_verified() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    trust_vc::assert_by!(true, {
        let _a = f(0u64);
    });
    trust_vc::assert_by!(true, {
        let _b = f(0u64);
    });
}

// ===========================================================================
// R9 — blocker 2: a bare closure's parameter named like an
// already-declared program variable (an outer function parameter). The body's
// call-site requires (or assert) was rendered over the bare name, which lowered
// to the OUTER variable. MEASURED Verified before the fix (the n-ary / Fn-bound
// shapes were Error "nothing to prove" on main before the fix; the unary / helper
// shapes Verified there too). Every program below panics at `h(..)`.
// ===========================================================================
#[trust_vc::requires(x == 4u64)]
#[trust_vc::ensures(result == x)]
fn l9_need4(x: u64) -> u64 {
    x
}

#[trust_vc::requires(x == 4u64)]
fn l9a_closure_param_shadows_outer_nary(x: u64) {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let h = |x: u64| f(x, 4u64);
    let _t = h(3u64);
}

#[trust_vc::requires(x == 4u64)]
fn l9b_closure_param_shadows_outer_unary(x: u64) {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 4u64)
        ensures(|z: u64| z == a)
        a
    );
    let h = |x: u64| f(x);
    let _t = h(3u64);
}

#[trust_vc::requires(f.requires((x,)))]
fn l9c_fnbound_closure_param_shadow<F: Fn(u64) -> u64>(f: F, x: u64) {
    let h = |x: u64| f(x);
    let _t = h(0u64);
}

#[trust_vc::requires(f.requires((x,)))]
fn l9d_fnbound_in_map_closure<F: Fn(u64) -> u64>(f: F, x: u64) {
    let _o = Some(0u64).map(|x| f(x));
}

#[trust_vc::requires(x == 4u64)]
fn l9e_registered_in_map_closure(x: u64) {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let _o = Some(3u64).map(|x| f(x, 4u64));
}

#[trust_vc::requires(x == 4u64)]
fn l9f_helper_closure_param_shadow(x: u64) {
    let h = |x: u64| l9_need4(x);
    let _t = h(3u64);
}

#[trust_vc::requires(f.requires((x,)))]
fn l9g_fnbound_callee<F: Fn(u64) -> u64>(f: F, x: u64) {
    let h = |x: u64| f(x);
    let _t = h(0u64);
}

#[trust_vc::ensures(true)]
fn l9g_caller() {
    let c = trust_vc::closure!(
        |b: u64| -> u64
        requires(b > 0u64)
        ensures(|z: u64| z == 100u64 / b)
        100u64 / b
    );
    l9g_fnbound_callee(c, 5u64);
}

#[trust_vc::requires(x < 10u64)]
fn l9h_closure_body_assert_param_collision(x: u64) {
    let h = |x: u64| {
        trust_vc::assert!(x < 10u64);
    };
    h(100u64);
}

// Parity: the same shape with NOTHING to collide with is refused identically
// (the closure parameter is an unresolved variable at lowering).
#[trust_vc::requires(y == 4u64)]
fn l9i_helper_closure_param_no_collision(y: u64) {
    let h = |x: u64| l9_need4(x);
    let _t = h(3u64);
}

// Controls: a colliding parameter the body does not read changes nothing.
#[trust_vc::requires(b == 1u64)]
fn l9j_closure_param_collision_unused_verified(b: u64) {
    let h = |b: u64| l9_need4(4u64);
    let _t = h(0u64);
}

#[trust_vc::requires(b == 1u64)]
fn l9k_closure_param_collision_unused_liar(b: u64) {
    let h = |b: u64| l9_need4(5u64);
    let _t = h(0u64);
}

// ===========================================================================
// R10 — major (pre-existing on main): a `closure!`
// whose ENSURES result binder is named like a PARAMETER. The requires was
// substituted from the same map as the ensures, so the parameter was replaced
// by the (narrower) call-result term and the requires became trivially true.
// MEASURED Verified before the fix; `f(1000)` underflows in every
// build.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l10a_result_named_like_param_unary() {
    let f = trust_vc::closure!(
        |a: u64| -> u8
        requires(a < 256u64)
        ensures(|a: u8| true)
        7u8
    );
    let _t = f(1000u64);
}

#[trust_vc::ensures(true)]
fn l10b_result_named_like_param_nary() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u8
        requires(a < 256u64)
        ensures(|a: u8| true)
        7u8
    );
    let _t = f(1000u64, 0u64);
}

#[trust_vc::ensures(true)]
fn l10c_result_named_like_param_underflow() {
    let f = trust_vc::closure!(
        |a: u64| -> u8
        requires(a <= 255u64)
        ensures(|a: u8| true)
        (255u64 - a) as u8
    );
    let _t = f(1000u64);
}

#[trust_vc::ensures(true)]
fn l10d_result_named_like_param_underflow_nary() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u8
        requires(a <= 255u64)
        ensures(|a: u8| true)
        (255u64 - a) as u8
    );
    let _t = f(1000u64, 1u64);
}

// Controls: inside the ENSURES the result binder still wins.
#[trust_vc::ensures(true)]
fn l10e_result_named_like_param_verified() {
    let f = trust_vc::closure!(
        |a: u64| -> u8
        requires(a < 256u64)
        ensures(|a: u8| a == 7u8)
        7u8
    );
    let t = f(3u64);
    trust_vc::assert!(t == 7u8);
}

#[trust_vc::ensures(true)]
fn l10f_result_named_like_param_liar() {
    let f = trust_vc::closure!(
        |a: u64| -> u8
        requires(a < 256u64)
        ensures(|a: u8| a == 7u8)
        7u8
    );
    let t = f(3u64);
    trust_vc::assert!(t == 8u8);
}

// ===========================================================================
// R11 — a PATTERN binding named like an already-declared program variable
// (the review-round-1 blocker-2 class, generalised): `while let` (whose pattern
// was bound to nothing), and an `if let` / `match` arm over a scrutinee that is
// not a resolvable datatype (an identity shadow). Every body obligation over
// the bound name — a helper's requires, a registered `closure!`'s requires, an
// `assert!` — rendered the bare name and lowered to the OUTER variable.
// MEASURED Verified before the fix; every program below panics (or
// asserts falsely) for a `v` holding a value other than 4.
// ===========================================================================
#[trust_vc::requires(x == 4u64)]
fn l11a_while_let_shadow_helper(x: u64, v: Vec<u64>) {
    let mut it = v.into_iter();
    while let Some(x) = it.next() {
        let _t = l9_need4(x);
    }
}

#[trust_vc::requires(x == 4u64)]
fn l11b_while_let_shadow_closure_app(x: u64, v: Vec<u64>) {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 4u64)
        ensures(|z: u64| z == a)
        a
    );
    let mut it = v.into_iter();
    while let Some(x) = it.next() {
        let _t = f(x);
    }
}

#[trust_vc::requires(x == 4u64)]
fn l11c_while_let_shadow_assert(x: u64, v: Vec<u64>) {
    let mut it = v.into_iter();
    while let Some(x) = it.next() {
        trust_vc::assert!(x == 4u64);
    }
}

#[trust_vc::requires(x == 4u64)]
fn l11d_if_let_opaque_scrutinee_shadow(x: u64, v: Vec<u64>) {
    let mut it = v.into_iter();
    if let Some(x) = it.next() {
        let _t = l9_need4(x);
    }
}

#[trust_vc::requires(x == 4u64)]
fn l11e_match_opaque_scrutinee_shadow(x: u64, v: Vec<u64>) {
    let mut it = v.into_iter();
    match it.next() {
        Some(x) => {
            let _t = l9_need4(x);
        }
        None => {}
    }
}

#[trust_vc::requires(x == 4u64)]
fn l11f_while_let_tuple_shadow(x: u64, v: Vec<(u64, u64)>) {
    let mut it = v.into_iter();
    while let Some((x, _y)) = it.next() {
        let _t = l9_need4(x);
    }
}

// Parity: the same shape with NOTHING to collide with is refused identically.
#[trust_vc::requires(y == 4u64)]
fn l11g_while_let_no_collision(y: u64, v: Vec<u64>) {
    let mut it = v.into_iter();
    while let Some(x) = it.next() {
        let _t = l9_need4(x);
    }
}

// Controls: a colliding binding the body does not read changes nothing, and a
// resolvable-datatype `if let` still binds the projection (refuted, not
// refused).
#[trust_vc::requires(x == 4u64)]
fn l11h_while_let_collision_unused_verified(x: u64, v: Vec<u64>) {
    let mut it = v.into_iter();
    while let Some(x) = it.next() {
        let _t = l9_need4(4u64);
    }
}

#[trust_vc::requires(x == 4u64)]
fn l11i_while_let_collision_unused_liar(x: u64, v: Vec<u64>) {
    let mut it = v.into_iter();
    while let Some(x) = it.next() {
        let _t = l9_need4(5u64);
    }
}

#[trust_vc::requires(x == 4u64)]
fn l11j_if_let_datatype_shadow_cx(x: u64, o: Option<u64>) {
    if let Some(x) = o {
        let _t = l9_need4(x);
    }
}

// ===========================================================================
// R12 — the `Fn` / `FnMut` / `FnOnce` ABI SPELLING of an application (blocker).
// `f.call((a, b))` IS the application `f(a, b)` —
// `dispatch/methods.rs` lowers the unary form to the very same `spec_fn_apply`
// UF — but every seam was keyed on `syn::ExprCall`, so an `ExprMethodCall`
// reached none of them. With the RESULT UNUSED nothing is ever lowered either,
// so the whole fragment the branch was built to close leaked back out through
// this one spelling. MEASURED Verified before the fix: every liar below. `l12b`
// is the ORIGINAL H6 repro
// `h6_nary_bad_requires_via_call_method` verbatim, which the hole record's own
// confirmation also lists as Verified at main. Each program panics on the
// violated `requires` (or divides by zero). `Fn::call` needs unstable
// `fn_traits`, so these are nightly-only programs — they are still
// applications trust-vc must not verify.
// ===========================================================================
#[trust_vc::ensures(true)]
fn l12a_call_unary_bad_requires() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f.call((3u64,));
}

// The ORIGINAL H6 hole repro, verbatim.
#[trust_vc::ensures(true)]
fn l12b_call_nary_bad_requires() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f.call((3u64, 4u64));
}

// Runtime-grade witness: the program divides by zero.
#[trust_vc::ensures(true)]
fn l12c_call_unary_div_zero() {
    let f = trust_vc::closure!(
        |b: u64| -> u64
        requires(b > 0u64)
        ensures(|z: u64| z <= 100u64)
        100u64 / b
    );
    let _t = f.call((0u64,));
}

#[trust_vc::ensures(true)]
fn l12d_call_once_bad_requires() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f.call_once((3u64,));
}

#[trust_vc::ensures(true)]
fn l12e_call_mut_bad_requires() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f.call_mut((3u64,));
}

#[trust_vc::ensures(true)]
fn l12f_call_ufcs_bad_requires() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = Fn::call(&f, (3u64,));
}

#[trust_vc::ensures(true)]
fn l12g_call_ufcs_once_bad_requires() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = FnOnce::call_once(f, (3u64,));
}

// The R3 (`F: Fn` parameter) lane through the same spelling.
#[trust_vc::ensures(true)]
fn l12h_call_fnbound_unary<F: Fn(u64) -> u64>(f: F) {
    let _t = f.call((0u64,));
}

#[trust_vc::ensures(true)]
fn l12i_call_fnbound_nary<F: Fn(u64, u64) -> u64>(f: F) {
    let _t = f.call((3u64, 4u64));
}

// The bare exec-closure lane: the body's divide-by-zero is pinned at the
// application exactly as for `f(0u64)`.
#[trust_vc::ensures(true)]
fn l12j_call_bare_closure_div_zero() {
    let f = |b: u64| 100u64 / b;
    let _t = f.call((0u64,));
}

// Inside an `assert!`'s tokens (the R8 surface) through the same spelling.
#[trust_vc::ensures(true)]
fn l12k_call_in_assert() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    trust_vc::assert!(f.call((3u64,)) == f.call((3u64,)));
}

// A CONTRACTED SIBLING function item is a function value too, and its name sits
// in RECEIVER position — so `referenced_helper_calls` did not even collect its
// contract.
#[trust_vc::ensures(true)]
fn l12l_call_helper_item() {
    let _t = l9_need4.call((5u64,));
}

#[trust_vc::ensures(true)]
fn l12m_call_helper_item_ufcs() {
    let _t = Fn::call(&l9_need4, (5u64,));
}

// Unmodelled value callees through the spelling: an `FnMut` parameter and an
// ALIAS of a registered closure both fail closed, as for `f(3u64)`.
#[trust_vc::ensures(true)]
fn l12n_call_mut_fnmut_param<F: FnMut(u64) -> u64>(mut f: F) {
    let _t = f.call_mut((3u64,));
}

#[trust_vc::ensures(true)]
fn l12o_call_alias_of_closure() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let g = f;
    let _t = g.call((3u64,));
}

// A DEREF receiver is not peeled: `g` is the reference, not the value, so the
// classifier sees a non-path callee and fails closed — the same treatment
// `(*g)(x)` gets.
#[trust_vc::ensures(true)]
fn l12p_call_through_deref<F: Fn(u64) -> u64>(g: &F) {
    let _t = (*g).call((3u64,));
}

// --- CONTROLS: the same spelling, satisfied precondition — must VERIFY ------
#[trust_vc::ensures(true)]
fn l12q_call_nary_good_requires_verified() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == a)
        a
    );
    let _t = f.call((3u64, 3u64));
}

#[trust_vc::ensures(true)]
fn l12r_call_ufcs_good_requires_verified() {
    let f = trust_vc::closure!(
        |a: u64| -> u64
        requires(a == 0u64)
        ensures(|z: u64| z == a)
        a
    );
    let _t = Fn::call(&f, (0u64,));
}

#[trust_vc::requires(f.requires((3u64,)))]
#[trust_vc::ensures(true)]
fn l12s_call_fnbound_good_requires_verified<F: Fn(u64) -> u64>(f: F) {
    let _t = f.call((3u64,));
}

#[trust_vc::ensures(true)]
fn l12t_call_helper_item_good_verified() {
    let _t = l9_need4.call((4u64,));
}

// A GHOST `SpecFn::call(x)` — a BARE (non-tuple) argument — is the spec
// surface, not the `Fn` ABI, and is untouched by the desugaring: the reflexive
// claim still VERIFIES and its liar twin still COUNTEREXAMPLES.
#[trust_vc::ensures(true)]
fn l12u_spec_fn_call_surface_verified(f: SpecFn<int, int>, n: int) {
    trust_vc::assert!(f.call(n) == f.call(n));
}

#[trust_vc::ensures(true)]
fn l12v_spec_fn_call_surface_liar(f: SpecFn<int, int>, n: int) {
    trust_vc::assert!(f.call(n) == f.call(n + 1));
}
