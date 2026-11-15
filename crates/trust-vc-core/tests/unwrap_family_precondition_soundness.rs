// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PIN (H3, 2026-09-14): every EVALUATION of `Option::{unwrap,
//! expect}` or `Result::{unwrap, expect, unwrap_err, expect_err}` in an exec
//! body carries its vstd precondition — `option is Some` / `result is Ok` /
//! `result is Err` (vstd `std_specs/option.rs:157-159`,
//! `std_specs/result.rs:174-178` at the pinned Verus `a40d57c7`) — as a PROVED
//! assert at that program point, WHETHER OR NOT the result is used.
//!
//! Before the fix the only unwrap semantics lived in IR lowering
//! (`known_some_value_or_selector`), which runs only when some obligation
//! mentions the call. A USED unwrap therefore failed closed, but an unwrap
//! whose value was dropped — `let _v = o.unwrap();`, `None::<u64>.unwrap();`,
//! an unwrap in a tuple element, a call argument, an assignment RHS, a loop
//! body, a UFCS `Option::unwrap(o)` — emitted NO obligation and the function
//! came back `Verified` with a guaranteed runtime panic (the H3 probe and
//! design measured the L1–L16 liars `Verified` at `ee37bb64`; the H3 judges
//! compiled the minimal shapes with `trustc -Ztrust-verify=off` and ran them to
//! a panic).
//!
//! The obligation is the TESTER form `G ==> R is Some|Ok|Err` (named
//! `unwrap_precondition_check_N`), never a reflexive `R.unwrap() == R.unwrap()`:
//! the reflexive form fails closed under a `requires(o.is_some())` context and
//! would regress the true controls below. It is emitted BEFORE the statement
//! is visited (the visit havocs an unresolved receiver and pushes the
//! assumptions of calls evaluated after the unwrap); a site preceded in
//! evaluation order by a side effect in the same expression fails closed.
//!
//! Mutation discriminators (measured when this file landed, by disabling one
//! arm and re-running this file): disabling the emitter flipped 57 of the 104
//! pins then present — every `RefutedByPrecondition` liar and most fail-closed
//! ones — to `Verified`; disabling the loop-modified-receiver arm flips
//! `l11b_while_reassign_none_no_invariant` to `Verified`; disabling the
//! after-effect arm flips `o1_block_write_before_site` and
//! `o2_take_before_site` to `Verified`; restoring the old user-method
//! exemption for a same-named trait method on `Option` flips
//! `o19_trait_named_unwrap_on_option` (and, because the registry is
//! file-wide, every other liar in that fixture) to `Verified`. Before the
//! `move`-closure arm, `o4_move_closure_capture` was `Verified`.
//!
//! Secondary (latent) item: an integer-to-`char` cast from anything but `u8`
//! (rustc E0604) was accepted with no Unicode-scalar validity guard, so
//! `(0xD800u32 as char) as u32 == 0xD800u32` verified. It now fails closed.
//!
//! Review round 1 (same day) found five false verifies introduced by the first
//! fix (`c08cb668`), each measured `Verified` there and compiled to a runtime
//! panic. Each now has pins in a `review_round1_*` table:
//!
//! 1. An unwrap-family UFCS path whose owner is a type alias or a `use … as`
//!    rename (`Opt::unwrap(o)`, `<Opt>::unwrap`, `Maybe::unwrap`, and the
//!    fn-item forms) emitted nothing. An owner that is neither literally
//!    `Option` / `Result` nor a type declared in the file with that method now
//!    fails closed.
//! 2. The evaluation-order effect model treated every method NAMED `is_some` /
//!    `unwrap` / … as effect-free, whatever the receiver type. Now only a call
//!    whose receiver type resolves scope-exactly to std `Option` / `Result`
//!    counts as effect-free.
//! 3. The user-method exemption resolved a `let`-shadowed name to the shadowed
//!    PARAMETER's type.
//! 4. The std receiver-keep had the same stale lookup. Both 3 and 4 now use a
//!    scope-exact lookup.
//! 5. The invoked-closure instrumentation resolved captured names at the CALL.
//!    Each tracked closure now records its captures' definition-time bindings,
//!    and the call fails closed on any difference. This also closes the
//!    arithmetic twin and a reassigned `move` capture.
//!
//! Discriminator: with the engine sources reverted to `c08cb668` and this file
//! unchanged, exactly 32 of the 49 round-1 pins flip to `Verified`:
//!
//! - all nine `alias_ufcs` fail-closed pins (`a11` included);
//! - the seven `user_named_effects` fail-closed pins;
//! - the five shadowed `m*` refutations and `k5` / `k5b`;
//! - eight `closure_captures` fail-closed pins (all but `c9` / `c11`, which
//!   already failed closed there);
//! - `ch5`.
//!
//! The other 17 held already at `c08cb668`: the `Verified` controls, `c9` /
//! `c11`, and the non-vacuity refutations `a8`, `u4`, `uc2`, `k5d`, `cl1`–`cl3`.
//!
//! Review round 2 (2026-09-15/16) measured 19 more programs `Verified` that
//! panic at every run, all of them the SAME defect wearing different syntax:
//! the new obligation IS emitted, but its receiver renders against a binding a
//! JOIN restored, so it asserts `is Some` of the PRE-join value. Two framing
//! losses fed it, neither introduced by the H3 obligation — both are closed
//! here because the obligation is only as sound as the receiver it names:
//!
//! B. A `let`-local or typed-local `Option` / `Result` receiver was in NEITHER
//!    receiver classification the modified-set collector consults, so `o.take()`
//!    was recorded as a modification at NO join — block, `if`, `match` arm,
//!    `while` / `for` / `loop`, or capture-mutating closure. Such a binding is
//!    now an `untyped_receivers` entry and a method on it is recorded unless it
//!    is PROVABLY non-mutating (`review_round2_untyped_receiver_framing`,
//!    `review_round2_closure_capture_havoc`).
//! A. A BARE `{ .. }` / `unsafe { .. }` block dropped a registered `&mut self`
//!    user method's effect even on a PARAMETER receiver: the block is visited
//!    under a snapshot that is restored, and the post-block
//!    `invalidate_scoped_names` drops a scoped rewrite only — a DECLARED
//!    binding fell back to its entry symbol, still pinned by `requires`. The
//!    block join now havocs every assigned declared binding, as the `if` and
//!    loop joins already did (`review_round2_block_join_framing`).
//!
//! Minor, same round: a trait-qualified `<T as Trait>::unwrap(..)` classified
//! as no unwrap site at all, on the unchecked assumption that no such trait
//! exists. The owner now comes from the trait path and an undeclared trait
//! fails closed (`review_round2_trait_qualified_ufcs`).
//!
//! KNOWN RESIDUAL (latent, measured): the integer-to-`char` guard lives in IR
//! lowering, so it covers every cast that reaches an obligation — every USED
//! spelling is rejected (`int_to_char_casts`) — while a cast whose value no
//! obligation mentions (`let c = 0xD800u32 as char;`, itself rustc E0604) is
//! admitted with no diagnostic. Such a value cannot reach a verdict without
//! going through lowering, so no `Verified` depends on it.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn verify(func: &str, src: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut p = std::env::temp_dir();
    p.push(format!(
        "tvc_unwrap_pre_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&p, src).expect("write fixture");
    // A VC-cache hit written by a pre-fix binary would replay its stale
    // `Verified`; this pin never trusts the cache.
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(p.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// A panicking program refuted by the NEW precondition obligation.
    RefutedByPrecondition,
    /// A program that must be refuted by some counterexample (not the new
    /// obligation — a satisfiability witness for a liar's context).
    Counterexample,
    /// Out of the exact model: must fail closed (an extraction or lowering
    /// refusal), never `Verified`.
    FailClosed,
    /// Either refuted by the new obligation or failed closed — never
    /// `Verified`. Used where the design admits both.
    RefutedOrFailClosed,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(160).collect::<String>())
        }
        Ok(other) => format!("{:.160}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(160).collect::<String>()),
    }
}

fn matches_expect(r: &Result<VerifyResult, String>, expect: Expect) -> bool {
    let refuted_by_precondition = matches!(
        r,
        Ok(VerifyResult::Counterexample { obligation_name, .. })
            if obligation_name.starts_with("unwrap_precondition_check_")
    );
    let failed_closed = matches!(r, Ok(VerifyResult::Error { .. }) | Err(_));
    match expect {
        Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
        Expect::RefutedByPrecondition => refuted_by_precondition,
        Expect::Counterexample => matches!(r, Ok(VerifyResult::Counterexample { .. })),
        Expect::FailClosed => failed_closed,
        Expect::RefutedOrFailClosed => refuted_by_precondition || failed_closed,
    }
}

fn check_table(group: &str, src: &str, table: &[(&str, Expect)]) {
    let mut failures = Vec::new();
    for (func, expect) in table {
        let r = verify(func, src);
        let ok = matches_expect(&r, *expect);
        println!(
            "{group} {func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{group}: {} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{Counterexample, FailClosed, RefutedByPrecondition, RefutedOrFailClosed, Verified};

// ---------------------------------------------------------------------------
// Straight-line statement and let positions
// ---------------------------------------------------------------------------

const STRAIGHT: &str = r#"
#![allow(dead_code, unused)]

// LIAR L1 — the minimal repro: panics on every call.
#[trust_vc::ensures(true)]
fn l1_none_local_let_unused() {
    let o: Option<u64> = None;
    let _v = o.unwrap();
}

// LIAR L2 — statement position over a literal None. (`None::<u64>` renders
// without its turbofish — a pre-existing lowering gap, `assert!(None::<u64>
// .is_none())` is the same Error — so this one may fail closed.)
#[trust_vc::ensures(true)]
fn l2_none_literal_stmt() {
    None::<u64>.unwrap();
}

// LIAR L2d — statement position over a declared None local.
#[trust_vc::ensures(true)]
fn l2d_none_local_stmt() {
    let o: Option<u64> = None;
    o.unwrap();
}

// LIAR L3 — parameter receiver, `expect`.
#[trust_vc::ensures(true)]
fn l3_param_option_expect(o: Option<u64>) {
    let _v = o.expect("x");
}

// LIAR L3b — `let _ =` still evaluates the call.
#[trust_vc::ensures(true)]
fn l3b_param_option_let_underscore(o: Option<u64>) {
    let _ = o.unwrap();
}

// LIAR L4 — Result parameter, `unwrap`.
#[trust_vc::ensures(true)]
fn l4_param_result_unwrap(r: Result<u64, u8>) {
    let _v = r.unwrap();
}

// LIAR L4b — Result parameter, statement `expect`.
#[trust_vc::ensures(true)]
fn l4b_param_result_expect_stmt(r: Result<u64, u8>) {
    r.expect("x");
}

// LIAR L5 — `expect_err` on a Result parameter.
#[trust_vc::ensures(true)]
fn l5_param_result_expect_err(r: Result<u64, u8>) {
    let _e = r.expect_err("x");
}

// LIAR L5b — `unwrap_err` on a local Ok.
#[trust_vc::ensures(true)]
fn l5b_ok_local_unwrap_err() {
    let r: Result<u64, u8> = Ok(1u64);
    let _e = r.unwrap_err();
}

// LIAR L6 — satisfiable context that forces the panic.
#[trust_vc::requires(o.is_none())]
#[trust_vc::ensures(true)]
fn l6_requires_none_stmt(o: Option<u64>) {
    o.unwrap();
}

// CONTROL for L6 — the same context is satisfiable (the body is analysed).
#[trust_vc::requires(o.is_none())]
#[trust_vc::ensures(true)]
fn l6_ctrl_requires_none_assert_false(o: Option<u64>) {
    trust_vc::assert!(false);
}

// LIAR L7 — under an unrelated branch.
#[trust_vc::ensures(true)]
fn l7_branch_unwrap(o: Option<u64>, b: bool) {
    if b {
        let _v = o.unwrap();
    }
}

// LIAR L7b — under the branch that proves the panic.
#[trust_vc::ensures(true)]
fn l7b_is_none_branch_unwrap(o: Option<u64>) {
    if o.is_none() {
        let _v = o.unwrap();
    }
}

// LIAR L7c — a true postcondition after the dropped unwrap.
#[trust_vc::ensures(result == 7u64)]
fn l7c_ret_after_unwrap(o: Option<u64>) -> u64 {
    let _v = o.unwrap();
    7u64
}

// LIAR L2b — Result statement on a literal Err. (A let-local `Err(..)`
// initializer has no registered type — the pre-existing lowering gap that
// also makes `assert!(r.is_err())` an Error — so this may fail closed.)
#[trust_vc::ensures(true)]
fn l2b_err_local_unwrap_stmt() {
    let r: Result<u64, u8> = Err(1u8);
    r.unwrap();
}

// LIAR — tail expression of a unit function.
#[trust_vc::ensures(true)]
fn l2c_tail_unwrap(o: Option<u64>) {
    o.unwrap()
}

// CONTROL C1 — a known-Some local.
#[trust_vc::ensures(true)]
fn c1_some_local_unwrap() {
    let o = Some(3u64);
    let _v = o.unwrap();
}

// CONTROL C1b — a Some literal receiver.
#[trust_vc::ensures(true)]
fn c1b_some_literal_unwrap() {
    let _x = Some(3u64).unwrap();
}

// CONTROL C2 — the precondition is the requires (forbids the reflexive design).
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn c2_requires_some_let(o: Option<u64>) {
    let _v = o.unwrap();
}

// CONTROL C2b — Result twin.
#[trust_vc::requires(r.is_ok())]
#[trust_vc::ensures(true)]
fn c2b_requires_ok_expect(r: Result<u64, u8>) {
    let _v = r.expect("x");
}

// CONTROL — `unwrap_err` under `requires(r.is_err())`.
#[trust_vc::requires(r.is_err())]
#[trust_vc::ensures(true)]
fn c2c_requires_err_unwrap_err(r: Result<u64, u8>) {
    let _e = r.unwrap_err();
}

// KNOWN COMPLETENESS GAP (true program, pre-existing lowering limit): a
// let-local `Err(..)` initializer has no registered type, so the precondition
// — like `assert!(r.is_err())` on the same local — fails closed.
#[trust_vc::ensures(true)]
fn c2d_err_local_expect_err() {
    let r: Result<u64, u8> = Err(1u8);
    let _e = r.expect_err("x");
}

// CONTROL — the receiver survives the `unwrap` (a by-value `self` on a `Copy`
// `Option` cannot change the caller's binding), so a later read of it still
// resolves to the same value.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(result)]
fn c2e_receiver_survives_unwrap(o: Option<u64>) -> bool {
    let _v = o.unwrap();
    let _w = o.unwrap();
    o.is_some()
}

// CONTROL C5 — a user type's own `unwrap` is its own contract's business.
struct DW {
    v: u64,
}
impl DW {
    fn unwrap(&self) -> u64 {
        self.v
    }
}

#[trust_vc::ensures(true)]
fn c5_user_struct_unwrap(w: DW) {
    let _x = w.unwrap();
}

// CONTROL C6 — the non-panicking family is untouched.
#[trust_vc::ensures(true)]
fn c6_unwrap_or(o: Option<u64>) {
    let _x = o.unwrap_or(0u64);
}

// CONTROL C9 — a helper's `ensures(result.is_some())`.
#[trust_vc::requires(x > 0u64)]
#[trust_vc::ensures(result.is_some())]
fn d_some_helper(x: u64) -> Option<u64> {
    Some(x)
}

#[trust_vc::ensures(true)]
fn c9_helper_some_let() {
    let h = d_some_helper(1u64);
    let _x = h.unwrap();
}

// UNCHANGED — a USED unwrap of an unconstrained parameter stays fail-closed.
#[trust_vc::ensures(true)]
fn u1_used_unwrap_param(o: Option<u64>) -> u64 {
    o.unwrap()
}
"#;

#[test]
fn straight_line_positions() {
    check_table(
        "straight",
        STRAIGHT,
        &[
            ("l1_none_local_let_unused", RefutedByPrecondition),
            ("l2_none_literal_stmt", RefutedOrFailClosed),
            ("l2d_none_local_stmt", RefutedByPrecondition),
            ("l2b_err_local_unwrap_stmt", RefutedOrFailClosed),
            ("l2c_tail_unwrap", RefutedByPrecondition),
            ("l3_param_option_expect", RefutedByPrecondition),
            ("l3b_param_option_let_underscore", RefutedByPrecondition),
            ("l4_param_result_unwrap", RefutedByPrecondition),
            ("l4b_param_result_expect_stmt", RefutedByPrecondition),
            ("l5_param_result_expect_err", RefutedByPrecondition),
            ("l5b_ok_local_unwrap_err", RefutedOrFailClosed),
            ("l6_requires_none_stmt", RefutedByPrecondition),
            ("l6_ctrl_requires_none_assert_false", Counterexample),
            ("l7_branch_unwrap", RefutedByPrecondition),
            ("l7b_is_none_branch_unwrap", RefutedByPrecondition),
            ("l7c_ret_after_unwrap", RefutedByPrecondition),
            ("c1_some_local_unwrap", Verified),
            ("c1b_some_literal_unwrap", Verified),
            ("c2_requires_some_let", Verified),
            ("c2b_requires_ok_expect", Verified),
            ("c2c_requires_err_unwrap_err", Verified),
            ("c2d_err_local_expect_err", FailClosed),
            ("c2e_receiver_survives_unwrap", Verified),
            ("c5_user_struct_unwrap", Verified),
            ("c6_unwrap_or", Verified),
            ("c9_helper_some_let", Verified),
            ("u1_used_unwrap_param", FailClosed),
        ],
    );
}

// ---------------------------------------------------------------------------
// Value positions nested in a statement, and place writes
// ---------------------------------------------------------------------------

const NESTED: &str = r#"
#![allow(dead_code, unused)]

fn d_nocontract(x: u64) -> u64 {
    x
}

struct EV {
    x: u64,
}

struct EW {
    o: Option<u64>,
}

#[trust_vc::ensures(true)]
fn l8a_tuple_elem(o: Option<u64>) {
    let _t = (o.unwrap(), 0u64);
}

#[trust_vc::ensures(true)]
fn l8b_nocontract_arg(o: Option<u64>) {
    let _x = d_nocontract(o.unwrap());
}

#[trust_vc::ensures(true)]
fn l8c_push_arg(o: Option<u64>) {
    let mut v: Vec<u64> = Vec::new();
    v.push(o.unwrap());
}

#[trust_vc::ensures(true)]
fn l8d_struct_literal(o: Option<u64>) {
    let _s = EV { x: o.unwrap() };
}

#[trust_vc::ensures(true)]
fn l8e_nested_unwrap_chain(o: Option<Option<u64>>) {
    let _x = o.unwrap().unwrap();
}

#[trust_vc::ensures(true)]
fn l8f_field_expect(w: EW) {
    let _x = w.o.expect("x");
}

#[trust_vc::ensures(true)]
fn l8g_match_scrutinee(o: Option<u64>) {
    match o.unwrap() {
        _ => {}
    }
}

#[trust_vc::ensures(true)]
fn l8h_if_cond(o: Option<u64>) {
    if o.unwrap() > 0u64 {}
}

#[trust_vc::ensures(true)]
fn l8i_if_expr_branch(o: Option<u64>, b: bool) {
    let _x = if b { o.unwrap() } else { 0u64 };
}

#[trust_vc::ensures(true)]
fn l9a_assign_rhs(o: Option<u64>) {
    let mut x: u64 = 0u64;
    x = o.unwrap();
}

#[trust_vc::ensures(true)]
fn l9b_index_write_rhs(o: Option<u64>) {
    let mut a: [u64; 2] = [0u64, 0u64];
    a[0usize] = o.unwrap();
}

#[trust_vc::ensures(true)]
fn l9c_deref_write_rhs(r: &mut u64, o: Option<u64>) {
    *r = o.unwrap();
}

#[trust_vc::ensures(true)]
fn l9d_compound_rhs(o: Option<u64>) {
    let mut x: u64 = 0u64;
    x += o.unwrap();
}

#[trust_vc::ensures(true)]
fn l10a_short_circuit_liar(o: Option<u64>) {
    let _b = o.is_none() && o.unwrap() > 0u64;
}

#[trust_vc::ensures(true)]
fn l10b_match_none_arm(o: Option<u64>) {
    match o {
        Some(_) => {}
        None => {
            o.unwrap();
        }
    }
}

#[trust_vc::ensures(true)]
fn l10c_short_circuit_or_liar(o: Option<u64>) {
    let _b = o.is_some() || o.unwrap() > 0u64;
}

#[trust_vc::ensures(true)]
fn l12a_ufcs_option_unwrap(o: Option<u64>) {
    let _x = Option::unwrap(o);
}

#[trust_vc::ensures(true)]
fn l12b_ufcs_result_expect(r: Result<u64, u8>) {
    let _x = Result::expect(r, "x");
}

#[trust_vc::ensures(true)]
fn l12c_qself_option_unwrap(o: Option<u64>) {
    let _x = <Option<u64>>::unwrap(o);
}

#[trust_vc::ensures(true)]
fn l13a_generic_option<T>(o: Option<T>) {
    o.unwrap();
}

#[trust_vc::ensures(true)]
fn l13b_as_ref_unwrap(o: Option<u64>) {
    let _x = o.as_ref().unwrap();
}

#[trust_vc::ensures(true)]
fn l13c_map_unwrap(o: Option<u64>) {
    let _x = o.map(|y| y).unwrap();
}

#[trust_vc::ensures(true)]
fn l15a_from_u32_surrogate_unwrap() {
    let _c = char::from_u32(0xD800u32).unwrap();
}

#[trust_vc::ensures(true)]
fn l15b_from_digit_unwrap(d: u32) {
    let _ = char::from_digit(d, 10u32).unwrap();
}

#[trust_vc::ensures(true)]
fn l15c_parse_unwrap() {
    let _ = "abc".parse::<u32>().unwrap();
}

#[trust_vc::ensures(true)]
fn l16_ordering_write_after_site() {
    let mut p: Option<u64> = None;
    let _t = (p.unwrap(), {
        p = Some(1u64);
        0u64
    });
}

// CONTROL C3 — guarded by the branch / arm / pattern.
#[trust_vc::ensures(true)]
fn c3a_if_is_some(o: Option<u64>) {
    if o.is_some() {
        let _v = o.unwrap();
    }
}

#[trust_vc::ensures(true)]
fn c3b_match_some_arm(o: Option<u64>) {
    match o {
        Some(_) => {
            o.unwrap();
        }
        None => {}
    }
}

#[trust_vc::ensures(true)]
fn c3c_if_let_some(o: Option<u64>) {
    if let Some(_x) = o {
        o.unwrap();
    }
}

#[trust_vc::ensures(true)]
fn c3d_if_is_err_unwrap_err(r: Result<u64, u8>) {
    if r.is_err() {
        let _e = r.unwrap_err();
    }
}

// CONTROL C4 — short-circuit guard.
#[trust_vc::ensures(true)]
fn c4_short_circuit_guard(o: Option<u64>) {
    let _b = o.is_some() && o.unwrap() > 0u64;
}

#[trust_vc::ensures(true)]
fn c4b_short_circuit_or_guard(o: Option<u64>) {
    let _b = o.is_none() || o.unwrap() > 0u64;
}

#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn c8b_tuple_elem_requires(o: Option<u64>) {
    let _t = (o.unwrap(), 0u64);
}

#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn c8c_assign_rhs_requires(o: Option<u64>) {
    let mut x: u64 = 0u64;
    x = o.unwrap();
}
"#;

#[test]
fn nested_value_positions_and_writes() {
    check_table(
        "nested",
        NESTED,
        &[
            ("l8a_tuple_elem", RefutedByPrecondition),
            ("l8b_nocontract_arg", RefutedByPrecondition),
            ("l8c_push_arg", RefutedOrFailClosed),
            ("l8d_struct_literal", RefutedByPrecondition),
            ("l8e_nested_unwrap_chain", RefutedOrFailClosed),
            ("l8f_field_expect", RefutedByPrecondition),
            ("l8g_match_scrutinee", RefutedByPrecondition),
            ("l8h_if_cond", RefutedByPrecondition),
            ("l8i_if_expr_branch", RefutedByPrecondition),
            ("l9a_assign_rhs", RefutedByPrecondition),
            ("l9b_index_write_rhs", RefutedByPrecondition),
            ("l9c_deref_write_rhs", RefutedByPrecondition),
            ("l9d_compound_rhs", RefutedOrFailClosed),
            ("l10a_short_circuit_liar", RefutedByPrecondition),
            ("l10b_match_none_arm", RefutedByPrecondition),
            ("l10c_short_circuit_or_liar", RefutedByPrecondition),
            ("l12a_ufcs_option_unwrap", RefutedByPrecondition),
            ("l12b_ufcs_result_expect", RefutedByPrecondition),
            ("l12c_qself_option_unwrap", RefutedByPrecondition),
            ("l13a_generic_option", RefutedByPrecondition),
            ("l13b_as_ref_unwrap", RefutedOrFailClosed),
            ("l13c_map_unwrap", RefutedOrFailClosed),
            ("l15a_from_u32_surrogate_unwrap", FailClosed),
            ("l15b_from_digit_unwrap", FailClosed),
            ("l15c_parse_unwrap", FailClosed),
            ("l16_ordering_write_after_site", RefutedOrFailClosed),
            ("c3a_if_is_some", Verified),
            ("c3b_match_some_arm", Verified),
            ("c3c_if_let_some", Verified),
            ("c3d_if_is_err_unwrap_err", Verified),
            ("c4_short_circuit_guard", Verified),
            ("c4b_short_circuit_or_guard", Verified),
            ("c8b_tuple_elem_requires", Verified),
            ("c8c_assign_rhs_requires", Verified),
        ],
    );
}

// ---------------------------------------------------------------------------
// Loops and closures
// ---------------------------------------------------------------------------

const LOOPS_CLOSURES: &str = r#"
#![allow(dead_code, unused)]

// LIAR L11 — the receiver is reassigned to None in the body: the second
// iteration panics.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn l11a_while_reassign_none(mut o: Option<u64>) {
    let mut i: u64 = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64);
        let _v = o.unwrap();
        o = None;
        i = i + 1u64;
    }
}

// LIAR L11b — same, no invariant.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn l11b_while_reassign_none_no_invariant(mut o: Option<u64>, n: u64) {
    let mut i: u64 = 0u64;
    while i < n {
        let _v = o.unwrap();
        o = None;
        i = i + 1u64;
    }
}

// LIAR L11c — an unconstrained receiver in a for body.
#[trust_vc::ensures(true)]
fn l11c_for_body_unwrap(o: Option<u64>) {
    for _i in 0u64..3u64 {
        let _x = o.unwrap();
    }
}

// LIAR — an unconstrained receiver in a while body.
#[trust_vc::ensures(true)]
fn l11d_while_body_unwrap(o: Option<u64>) {
    let mut i: u64 = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64);
        let _x = o.unwrap();
        i = i + 1u64;
    }
}

// LIAR — unwrap in the while condition.
#[trust_vc::ensures(true)]
fn l11e_while_cond_unwrap(o: Option<u64>) {
    let mut i: u64 = 0u64;
    while i < o.unwrap() {
        trust_vc::invariant!(true);
        i = i + 1u64;
    }
}

// LIAR L14 — an invoked capture-only closure.
#[trust_vc::ensures(true)]
fn l14a_invoked_closure(o: Option<u64>) {
    let g = || o.unwrap();
    let _ = g();
}

// LIAR L14b — a fn-item path handed to a library HOF.
#[trust_vc::ensures(true)]
fn l14b_map_fn_item(v: Vec<Option<u64>>) {
    let _w: Vec<u64> = v.into_iter().map(Option::unwrap).collect();
}

// LIAR L14c — a closure literal handed to a library HOF.
#[trust_vc::ensures(true)]
fn l14c_map_closure(v: Vec<Option<u64>>) {
    let _w: Vec<u64> = v.into_iter().map(|x| x.unwrap()).collect();
}

// LIAR — an invoked closure with a parameter.
#[trust_vc::ensures(true)]
fn l14d_invoked_closure_param() {
    let g = |p: Option<u64>| p.unwrap();
    let _ = g(None);
}

// LIAR — an invoked closure inside a loop body.
#[trust_vc::ensures(true)]
fn l14e_invoked_closure_in_loop(o: Option<u64>) {
    let g = || o.unwrap();
    let mut i: u64 = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64);
        let _ = g();
        i = i + 1u64;
    }
}

// CONTROL C7 — a receiver the loop never modifies, guarded before the loop.
#[trust_vc::ensures(true)]
fn c7_stable_receiver_in_loop(o: Option<u64>) {
    let mut i: u64 = 0u64;
    if o.is_some() {
        while i < 3u64 {
            trust_vc::invariant!(i <= 3u64);
            let _x = o.unwrap();
            i = i + 1u64;
        }
    }
}

// CONTROL — a requires-guarded receiver in a for body.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn c7b_for_body_requires(o: Option<u64>) {
    for _i in 0u64..3u64 {
        let _x = o.unwrap();
    }
}

// CONTROL C8 — a closure that is never invoked evaluates nothing.
#[trust_vc::ensures(true)]
fn c8_closure_never_invoked(o: Option<u64>) {
    let _g = || o.unwrap();
}

// CONTROL C8b — an invoked closure under the precondition.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn c8b_invoked_closure_requires(o: Option<u64>) {
    let g = || o.unwrap();
    let _ = g();
}
"#;

#[test]
fn loops_and_closures() {
    check_table(
        "loops",
        LOOPS_CLOSURES,
        &[
            ("l11a_while_reassign_none", RefutedOrFailClosed),
            // The no-invariant loop head rebinds `o` to an arbitrary value, so
            // the precondition is refuted there; the loop-modified-receiver arm
            // fails it closed where no head rebinding applies.
            ("l11b_while_reassign_none_no_invariant", RefutedOrFailClosed),
            ("l11c_for_body_unwrap", RefutedOrFailClosed),
            ("l11d_while_body_unwrap", RefutedByPrecondition),
            ("l11e_while_cond_unwrap", RefutedOrFailClosed),
            ("l14a_invoked_closure", RefutedByPrecondition),
            ("l14b_map_fn_item", FailClosed),
            ("l14c_map_closure", FailClosed),
            ("l14d_invoked_closure_param", RefutedOrFailClosed),
            ("l14e_invoked_closure_in_loop", RefutedOrFailClosed),
            ("c7_stable_receiver_in_loop", Verified),
            ("c7b_for_body_requires", Verified),
            ("c8_closure_never_invoked", Verified),
            ("c8b_invoked_closure_requires", Verified),
        ],
    );
}

// ---------------------------------------------------------------------------
// Evaluation order, effects, move closures, and more true controls
// ---------------------------------------------------------------------------

const ORDERING: &str = r#"
#![allow(dead_code, unused)]

struct EW {
    o: Option<u64>,
}

// LIAR — a nested block writes the receiver BEFORE the unwrap is evaluated:
// panics, although the pre-statement state satisfies the precondition.
#[trust_vc::requires(p.is_some())]
#[trust_vc::ensures(true)]
fn o1_block_write_before_site(mut p: Option<u64>) {
    let _t = ({
        p = None;
        0u64
    }, p.unwrap());
}

// LIAR — a `&mut self` method empties the receiver before the unwrap.
#[trust_vc::requires(p.is_some())]
#[trust_vc::ensures(true)]
fn o2_take_before_site(mut p: Option<u64>) {
    let _t = (p.take(), p.unwrap());
}

// CONTROL — the write happens AFTER the unwrap, which sees the requires.
#[trust_vc::requires(p.is_some())]
#[trust_vc::ensures(true)]
fn o3_site_before_block_write_ctrl(mut p: Option<u64>) {
    let _t = (p.unwrap(), {
        p = None;
        0u64
    });
}

// LIAR — a `move` closure captures `None` at its definition; the later write
// does not reach the capture, so the call panics.
#[trust_vc::ensures(true)]
fn o4_move_closure_capture() {
    let mut o: Option<u64> = None;
    let g = move || o.unwrap();
    o = Some(1u64);
    let _ = g();
}

// LIAR — an expression match-arm body.
#[trust_vc::ensures(true)]
fn o5_match_arm_expr(o: Option<u64>, b: bool) {
    let _x = match b {
        true => o.unwrap(),
        false => 0u64,
    };
}

// CONTROL — the same arm under the precondition.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn o6_match_arm_expr_ctrl(o: Option<u64>, b: bool) {
    let _x = match b {
        true => o.unwrap(),
        false => 0u64,
    };
}

// LIAR — the second of two sites in one aggregate.
#[trust_vc::requires(a.is_some())]
#[trust_vc::ensures(true)]
fn o7_second_site_liar(a: Option<u64>, b: Option<u64>) {
    let _t = (a.unwrap(), b.unwrap());
}

// CONTROL — both sites under the precondition.
#[trust_vc::requires(a.is_some() && b.is_some())]
#[trust_vc::ensures(true)]
fn o8_two_sites_ctrl(a: Option<u64>, b: Option<u64>) {
    let _t = (a.unwrap(), b.unwrap());
}

// CONTROL — a `Vec::push` argument.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn o9_push_arg_ctrl(o: Option<u64>) {
    let mut v: Vec<u64> = Vec::new();
    v.push(o.unwrap());
}

// CONTROL — UFCS under the precondition.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn o10_ufcs_ctrl(o: Option<u64>) {
    let _x = Option::unwrap(o);
}

// CONTROL — a field receiver under the precondition.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn o11_field_ctrl(w: EW) {
    let _x = w.o.expect("x");
}

// CONTROL — an `if let` scrutinee under the precondition.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn o12_if_let_scrutinee_ctrl(o: Option<u64>) {
    if let Some(_y) = Some(o.unwrap()) {}
}

// CONTROL — statement `expect_err` under `requires(r.is_err())`.
#[trust_vc::requires(r.is_err())]
#[trust_vc::ensures(true)]
fn o13_expect_err_stmt_ctrl(r: Result<u64, u8>) {
    r.expect_err("x");
}

// LIAR — the while guard is re-evaluated after the body empties the receiver.
#[trust_vc::ensures(true)]
fn o14_while_cond_reevaluated(mut o: Option<u64>) {
    let mut i: u64 = 0u64;
    o = Some(3u64);
    while o.unwrap() > i {
        trust_vc::invariant!(true);
        o = None;
        i = i + 1u64;
    }
}

// LIAR — a bare `loop` empties the receiver after the first iteration.
#[trust_vc::ensures(true)]
fn o15_bare_loop_modified() {
    let mut o: Option<u64> = Some(1u64);
    let mut i: u64 = 0u64;
    loop {
        if i >= 2u64 {
            break;
        }
        let _v = o.unwrap();
        o = None;
        i = i + 1u64;
    }
}

// LIAR — a `for` body empties a parameter receiver after the first iteration.
#[trust_vc::requires(p.is_some())]
#[trust_vc::ensures(true)]
fn o16_for_modified_param(mut p: Option<u64>) {
    for _k in 0u64..3u64 {
        let _v = p.unwrap();
        p = None;
    }
}

// LIAR — the receiver is a let-local copy of a loop-modified parameter.
#[trust_vc::requires(p.is_some())]
#[trust_vc::ensures(true)]
fn o17_loop_let_local_alias(mut p: Option<u64>, n: u64) {
    let mut i: u64 = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let q = p;
        let _v = q.unwrap();
        p = None;
        i = i + 1u64;
    }
}

// LIAR — an unwrap-family call nested in a macro argument.
#[trust_vc::ensures(true)]
fn o18_macro_arg(o: Option<u64>) {
    let _v = vec![o.unwrap()];
}

// LIAR — a `closure!` literal's body is discharged DEF-SIDE; an unwrap of its
// parameter there fails closed in lowering (the token scan skips `closure!`
// because of exactly this), bound to a name ...
#[trust_vc::ensures(true)]
fn o20_closure_macro_let_body_unwrap() {
    let f = trust_vc::closure!(|x: Option<u32>| -> u32 requires(true) ensures(|r: u32| true) x.unwrap());
}

// ... and passed straight to a combinator.
#[trust_vc::ensures(true)]
fn o21_closure_macro_arg_body_unwrap(o: Option<u32>) {
    let _r = o.map(trust_vc::closure!(|x: u32| -> u32 requires(true) ensures(|r: u32| true) Option::<u32>::None.unwrap()));
}
"#;

#[test]
fn evaluation_order_effects_and_controls() {
    check_table(
        "ordering",
        ORDERING,
        &[
            ("o1_block_write_before_site", FailClosed),
            ("o2_take_before_site", FailClosed),
            ("o3_site_before_block_write_ctrl", Verified),
            ("o4_move_closure_capture", FailClosed),
            ("o5_match_arm_expr", RefutedByPrecondition),
            ("o6_match_arm_expr_ctrl", Verified),
            ("o7_second_site_liar", RefutedByPrecondition),
            ("o8_two_sites_ctrl", Verified),
            ("o9_push_arg_ctrl", Verified),
            ("o10_ufcs_ctrl", Verified),
            ("o11_field_ctrl", Verified),
            ("o12_if_let_scrutinee_ctrl", Verified),
            ("o13_expect_err_stmt_ctrl", Verified),
            ("o14_while_cond_reevaluated", FailClosed),
            ("o15_bare_loop_modified", FailClosed),
            ("o16_for_modified_param", FailClosed),
            ("o17_loop_let_local_alias", FailClosed),
            ("o18_macro_arg", FailClosed),
            ("o20_closure_macro_let_body_unwrap", FailClosed),
            ("o21_closure_macro_arg_body_unwrap", FailClosed),
        ],
    );
}

// A file trait with a method named `unwrap` makes every `.unwrap()` call of
// its file one the method-call rule (`vc_extraction::trait_method_resolution`)
// refuses to verify, so it has a file of its own here; the controls above
// would be refused beside it.
const TRAIT_NAMED_UNWRAP: &str = r#"
#![allow(dead_code, unused)]

// LIAR — a file-local TRAIT method named `unwrap` implemented for `Option`
// does not own `o.unwrap()`: Rust picks the inherent by-value
// `Option::unwrap` first, which panics on `None`.
trait MyUnwrap {
    fn unwrap(&self) -> u64;
}

impl MyUnwrap for Option<u64> {
    fn unwrap(&self) -> u64 {
        0u64
    }
}

#[trust_vc::ensures(true)]
fn o19_trait_named_unwrap_on_option(o: Option<u64>) {
    let _x = o.unwrap();
}
"#;

#[test]
fn a_trait_named_unwrap_does_not_own_the_inherent_unwrap() {
    check_table(
        "trait named unwrap",
        TRAIT_NAMED_UNWRAP,
        &[("o19_trait_named_unwrap_on_option", RefutedByPrecondition)],
    );
}

// ---------------------------------------------------------------------------
// Secondary: integer-to-char casts (rustc accepts only `u8 as char`)
// ---------------------------------------------------------------------------

const CHAR_CASTS: &str = r#"
#![allow(dead_code, unused)]

#[trust_vc::spec]
fn ch_spec_cast(x: u32) -> char {
    x as char
}

// LIAR (rustc E0604) — a surrogate reinterpreted as a char.
#[trust_vc::ensures(true)]
fn ch1_u32_as_char_surrogate_value() {
    let c = 0xD800u32 as char;
    trust_vc::assert!((c as u32) == 0xD800u32);
}

// LIAR (rustc E0604) — an arbitrary u32 returned as a char.
#[trust_vc::ensures(true)]
fn ch2_u32_as_char_return(x: u32) -> char {
    x as char
}

// LIAR (rustc E0604) — the same cast in a spec fn.
#[trust_vc::ensures(true)]
fn ch3_spec_cast_surrogate() {
    trust_vc::assert!((ch_spec_cast(0xD800u32) as u32) == 0xD800u32);
}

// LIAR (rustc E0604) — i32 source.
#[trust_vc::ensures(true)]
fn ch4_i32_as_char(x: i32) {
    let c = x as char;
    trust_vc::assert!((c as u32) <= 0x10FFFFu32);
}

// CONTROL — char parameters carry validity.
#[trust_vc::ensures(true)]
fn chc1_param_char_le_max(c: char) {
    trust_vc::assert!((c as u32) <= 0x10FFFFu32);
}

#[trust_vc::ensures(true)]
fn chc2_param_char_not_surrogate(c: char) {
    trust_vc::assert!((c as u32) != 0xD800u32);
}

#[trust_vc::ensures(true)]
fn chc3_param_char_eq_surrogate_liar(c: char) {
    trust_vc::assert!((c as u32) == 0xD800u32);
}

// CONTROL — `u8 as char` round-trips and is bounded at 255.
#[trust_vc::ensures(true)]
fn chc4_u8_as_char_le255(x: u8) {
    let c = x as char;
    trust_vc::assert!((c as u32) <= 255u32);
}

#[trust_vc::ensures(true)]
fn chc5_u8_as_char_lt255_liar(x: u8) {
    let c = x as char;
    trust_vc::assert!((c as u32) < 255u32);
}

#[trust_vc::ensures(true)]
fn chc6_u32_as_u8_as_char(x: u32) {
    let c = (x as u8) as char;
    trust_vc::assert!((c as u32) <= 255u32);
}

// CONTROL — `char as char` is the identity.
#[trust_vc::ensures(true)]
fn chc7_char_as_char(c: char) {
    let d = c as char;
    trust_vc::assert!(d == c);
}

// LIAR (rustc E0604) — an `i32`-SUFFIXED literal shares the unsuffixed
// literal's placeholder type, but is not `u8` (review round 1).
#[trust_vc::ensures(true)]
fn ch5_i32_suffixed_literal_as_char() {
    let c = 97i32 as char;
    trust_vc::assert!((c as u32) == 97u32);
}

// CONTROL — an UNSUFFIXED literal <= 255 is inferred `u8`.
#[trust_vc::ensures(true)]
fn chc8_unsuffixed_literal_as_char() {
    let c = 97 as char;
    trust_vc::assert!((c as u32) == 97u32);
}
"#;

#[test]
fn int_to_char_casts() {
    check_table(
        "char",
        CHAR_CASTS,
        &[
            ("ch1_u32_as_char_surrogate_value", FailClosed),
            ("ch2_u32_as_char_return", FailClosed),
            ("ch3_spec_cast_surrogate", FailClosed),
            ("ch4_i32_as_char", FailClosed),
            ("chc1_param_char_le_max", Verified),
            ("chc2_param_char_not_surrogate", Verified),
            ("chc3_param_char_eq_surrogate_liar", Counterexample),
            ("chc4_u8_as_char_le255", Verified),
            ("chc5_u8_as_char_lt255_liar", Counterexample),
            ("chc6_u32_as_u8_as_char", Verified),
            ("chc7_char_as_char", Verified),
            ("ch5_i32_suffixed_literal_as_char", FailClosed),
            ("chc8_unsuffixed_literal_as_char", Verified),
        ],
    );
}

// ---------------------------------------------------------------------------
// Review round 1 (2026-09-14): five branch-attributable false verifies of the
// first H3 fix, each measured `Verified` at c08cb668 by the reviewer and
// compiled with `trustc -Ztrust-verify=off` to a runtime panic.
// ---------------------------------------------------------------------------

// (1) An unwrap-family UFCS path whose owner is a type alias, a `use … as`
// rename or anything else that is not literally `Option` / `Result` (and not a
// file-declared type declaring that method) used to emit nothing.
const REVIEW_ALIAS_UFCS: &str = r#"
#![allow(dead_code, unused)]
use std::option::Option as Maybe;
type Opt = Option<u64>;
type Res = Result<u64, u8>;

struct DW {
    v: u64,
}
impl DW {
    fn unwrap(&self) -> u64 {
        self.v
    }
}

#[trust_vc::ensures(true)]
fn a1_alias_ufcs_let(o: Option<u64>) {
    let _x = Opt::unwrap(o);
}

#[trust_vc::ensures(true)]
fn a2_alias_ufcs_stmt(o: Option<u64>) {
    Opt::unwrap(o);
}

#[trust_vc::ensures(true)]
fn a3_alias_qself(o: Option<u64>) {
    let _x = <Opt>::unwrap(o);
}

#[trust_vc::ensures(true)]
fn a4_alias_result_expect(r: Result<u64, u8>) {
    let _x = Res::expect(r, "x");
}

#[trust_vc::ensures(true)]
fn a5_alias_fn_item_local(o: Option<u64>) {
    let f = Opt::unwrap;
    let _x = f(o);
}

#[trust_vc::ensures(true)]
fn a6_alias_result_unwrap_err(r: Result<u64, u8>) {
    let _x = Res::unwrap_err(r);
}

#[trust_vc::ensures(true)]
fn a9_use_rename_ufcs(o: Option<u64>) {
    let _x = Maybe::unwrap(o);
}

#[trust_vc::ensures(true)]
fn a10_alias_fn_item_hof(v: Vec<Option<u64>>) {
    let _w: Vec<u64> = v.into_iter().map(Opt::unwrap).collect();
}

// LIAR — the METHOD spelling on an alias-typed parameter resolves in lowering.
#[trust_vc::ensures(true)]
fn a8_alias_param_method(o: Opt) {
    o.unwrap();
}

// COMPLETENESS COST — a true alias UFCS program fails closed too: the owner is
// not resolved through the alias.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn a11_alias_ufcs_requires_some(o: Option<u64>) {
    let _x = Opt::unwrap(o);
}

// CONTROL — UFCS on a file-declared type that declares `unwrap` is that type's
// own method, not an `Option` one.
#[trust_vc::ensures(true)]
fn a12_user_type_ufcs_ctrl(w: DW) {
    let _x = DW::unwrap(&w);
}
"#;

#[test]
fn review_round1_alias_and_rename_ufcs() {
    check_table(
        "alias_ufcs",
        REVIEW_ALIAS_UFCS,
        &[
            ("a1_alias_ufcs_let", FailClosed),
            ("a2_alias_ufcs_stmt", FailClosed),
            ("a3_alias_qself", FailClosed),
            ("a4_alias_result_expect", FailClosed),
            ("a5_alias_fn_item_local", FailClosed),
            ("a6_alias_result_unwrap_err", FailClosed),
            ("a9_use_rename_ufcs", FailClosed),
            ("a10_alias_fn_item_hof", FailClosed),
            ("a8_alias_param_method", RefutedByPrecondition),
            ("a11_alias_ufcs_requires_some", FailClosed),
            ("a12_user_type_ufcs_ctrl", Verified),
        ],
    );
}

// (2) The evaluation-order effect model treated every method NAMED like a std
// tester or unwrap-family method as effect-free, whatever the receiver type, so
// a user `&mut self` method of that name emptying the receiver earlier in the
// same expression was invisible to a later site.
const REVIEW_USER_NAMED_EFFECTS: &str = r#"
#![allow(dead_code, unused)]
struct W {
    o: Option<u64>,
}
impl W {
    fn is_some(&mut self) -> bool {
        self.o = None;
        true
    }
}
struct V {
    o: Option<u64>,
}
impl V {
    fn unwrap(&mut self) -> u64 {
        self.o = None;
        0u64
    }
}
struct X {
    o: Option<u64>,
}
impl X {
    #[trust_vc::ensures(self.o.is_none())]
    fn is_ok(&mut self) -> bool {
        self.o = None;
        true
    }
}
struct E {
    o: Option<u64>,
}
impl E {
    fn expect(&mut self, _m: &str) -> u64 {
        self.o = None;
        0u64
    }
    fn is_none(&mut self) -> bool {
        self.o = None;
        false
    }
}
trait Tst {
    fn is_err(&mut self) -> bool;
}
struct T2 {
    r: Result<u64, u8>,
}
impl Tst for T2 {
    fn is_err(&mut self) -> bool {
        self.r = Err(0u8);
        false
    }
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn u1_user_is_some_mut_before_site(mut w: W) {
    let _t = (w.is_some(), w.o.unwrap());
}

#[trust_vc::requires(v.o.is_some())]
#[trust_vc::ensures(true)]
fn u2_user_unwrap_mut_before_site(mut v: V) {
    let _t = (v.unwrap(), v.o.unwrap());
}

#[trust_vc::requires(x.o.is_some())]
#[trust_vc::ensures(true)]
fn u3_user_is_ok_contract_before_site(mut x: X) {
    let _t = (x.is_ok(), x.o.unwrap());
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn u5_user_is_some_and_guard(mut w: W) {
    let _b = w.is_some() && w.o.unwrap() > 0u64;
}

#[trust_vc::requires(e.o.is_some())]
#[trust_vc::ensures(true)]
fn u7_user_expect_mut(mut e: E) {
    let _t = (e.expect("m"), e.o.unwrap());
}

#[trust_vc::requires(e.o.is_some())]
#[trust_vc::ensures(true)]
fn u8_user_is_none_mut_or(mut e: E) {
    let _b = e.is_none() || e.o.unwrap() > 0u64;
}

#[trust_vc::requires(t.r.is_ok())]
#[trust_vc::ensures(true)]
fn u9_user_trait_is_err_mut(mut t: T2) {
    let _t = (t.is_err(), t.r.unwrap());
}

// LIAR — the two-statement form: the user method's havoc is seen.
#[trust_vc::requires(v.o.is_some())]
#[trust_vc::ensures(true)]
fn u4_user_unwrap_mut_then_stmt(mut v: V) {
    let _a = v.unwrap();
    let _b = v.o.unwrap();
}

// CONTROL — the std tester on a parameter IS effect-free ...
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn uc1_param_tester_guard_ctrl(o: Option<u64>) {
    let _b = o.is_some() && o.unwrap() > 0u64;
}

// ... and its guard is not vacuous.
#[trust_vc::ensures(true)]
fn uc2_param_tester_guard_liar(o: Option<u64>) {
    let _b = o.is_none() && o.unwrap() > 0u64;
}

// CONTROL — a std tester on a field of a parameter.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn uc3_field_tester_then_unwrap_ctrl(w: W) {
    let _t = (w.o.is_some(), w.o.unwrap());
}
"#;

#[test]
fn review_round1_user_methods_named_like_std() {
    check_table(
        "user_named_effects",
        REVIEW_USER_NAMED_EFFECTS,
        &[
            ("u1_user_is_some_mut_before_site", FailClosed),
            ("u2_user_unwrap_mut_before_site", FailClosed),
            ("u3_user_is_ok_contract_before_site", FailClosed),
            ("u5_user_is_some_and_guard", FailClosed),
            ("u7_user_expect_mut", FailClosed),
            ("u8_user_is_none_mut_or", FailClosed),
            ("u9_user_trait_is_err_mut", FailClosed),
            ("u4_user_unwrap_mut_then_stmt", RefutedByPrecondition),
            ("uc1_param_tester_guard_ctrl", Verified),
            ("uc2_param_tester_guard_liar", RefutedByPrecondition),
            ("uc3_field_tester_then_unwrap_ctrl", Verified),
        ],
    );
}

// (3) + (4) The user-method exemption and the std receiver-keep resolved a
// receiver's type through a lookup that falls back to a shadowed PARAMETER's
// type when a `let` re-binds the name.
const REVIEW_SHADOWED_RECEIVER_TYPE: &str = r#"
#![allow(dead_code, unused)]
struct DW {
    v: u64,
}
impl DW {
    fn unwrap(&self) -> u64 {
        self.v
    }
}
struct EX {
    v: u64,
}
impl EX {
    fn expect(&self, _m: &str) -> u64 {
        self.v
    }
    fn unwrap_err(&self) -> u64 {
        self.v
    }
}
struct W {
    o: Option<u64>,
}
impl W {
    fn is_some(&mut self) -> bool {
        self.o = None;
        true
    }
}

// LIAR — an `Option` let shadows a user-struct parameter declaring `unwrap`.
#[trust_vc::ensures(true)]
fn m1_shadow_user_struct_by_option(w: DW) {
    let w: Option<u64> = None;
    let _x = w.unwrap();
}

#[trust_vc::ensures(true)]
fn m1b_shadow_user_struct_by_option_param(w: DW, o: Option<u64>) {
    let w = o;
    w.unwrap();
}

#[trust_vc::ensures(true)]
fn m1c_shadow_inner_block(w: DW, o: Option<u64>) {
    {
        let w = o;
        w.unwrap();
    }
}

#[trust_vc::ensures(true)]
fn m21_shadow_unwrap_err_owner(w: EX, r: Result<u64, u8>) {
    let w = r;
    let _x = w.unwrap_err();
}

#[trust_vc::ensures(true)]
fn m23_shadow_let_none_literal_type(w: EX) {
    let w: Option<u64> = None;
    w.expect("m");
}

// CONTROL — the exemption still covers the unshadowed user parameter.
#[trust_vc::ensures(true)]
fn m24_user_ctrl(w: EX) {
    let _x = w.expect("m");
}

// LIAR — a user struct shadows an `Option` parameter; its `&mut self` `is_some`
// empties `v.o`, so the assertion panics. Must not keep the receiver.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k5_param_option_shadowed_by_user_mut_is_some(v: Option<u64>, w: W) {
    let mut v = w;
    v.is_some();
    assert!(v.o.is_some());
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k5b_same_trust_assert(v: Option<u64>, w: W) {
    let mut v = w;
    v.is_some();
    trust_vc::assert!(v.o.is_some());
}

// LIAR — the unshadowed form is havocked and refuted.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn k5d_param_direct_ctrl(mut w: W) {
    w.is_some();
    trust_vc::assert!(w.o.is_some());
}

// CONTROL — a std `Option` parameter's receiver is still kept.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn k9_keep_then_later_read_ctrl(o: Option<u64>) {
    let _a = o.is_some();
    let _b = o.unwrap();
    trust_vc::assert!(o.is_some());
}
"#;

#[test]
fn review_round1_shadowed_receiver_types() {
    check_table(
        "shadowed_receiver",
        REVIEW_SHADOWED_RECEIVER_TYPE,
        &[
            ("m1_shadow_user_struct_by_option", RefutedByPrecondition),
            (
                "m1b_shadow_user_struct_by_option_param",
                RefutedByPrecondition,
            ),
            ("m1c_shadow_inner_block", RefutedByPrecondition),
            ("m21_shadow_unwrap_err_owner", RefutedByPrecondition),
            ("m23_shadow_let_none_literal_type", RefutedByPrecondition),
            ("m24_user_ctrl", Verified),
            ("k5_param_option_shadowed_by_user_mut_is_some", FailClosed),
            ("k5b_same_trust_assert", FailClosed),
            ("k5d_param_direct_ctrl", Counterexample),
            ("k9_keep_then_later_read_ctrl", Verified),
        ],
    );
}

// (5) The invoked-closure instrumentation renders the body at the CALL and
// resolved captured names in the call-time scope, so a shadowing binding
// between definition and call retargeted them. The arithmetic twin (and a
// reassigned `move` capture) had the same root cause.
const REVIEW_CLOSURE_CAPTURES: &str = r#"
#![allow(dead_code, unused)]
#[trust_vc::ensures(result.is_none())]
fn mk_none() -> Option<u64> {
    None
}
#[trust_vc::ensures(result.is_some())]
fn mk_some() -> Option<u64> {
    Some(1u64)
}

#[trust_vc::ensures(true)]
fn c1_shadow_capture_after_def() {
    let o: Option<u64> = None;
    let g = || o.unwrap();
    let o: Option<u64> = Some(1u64);
    let _ = g();
}

#[trust_vc::ensures(true)]
fn c1b_shadow_capture_param(o: Option<u64>) {
    let g = || o.unwrap();
    let o: Option<u64> = Some(1u64);
    let _ = g();
}

#[trust_vc::ensures(true)]
fn c1c_shadow_capture_inner_block() {
    let o: Option<u64> = None;
    let g = || o.unwrap();
    {
        let o: Option<u64> = Some(1u64);
        let _ = g();
    }
}

#[trust_vc::ensures(true)]
fn c9_capture_shadowed_by_if_let() {
    let o: Option<u64> = None;
    let g = || o.unwrap();
    if let Some(o) = Some(Some(1u64)) {
        let _ = g();
    }
}

#[trust_vc::ensures(true)]
fn c11_result_capture_shadow() {
    let r: Result<u64, u8> = Err(1u8);
    let g = || r.unwrap();
    let r: Result<u64, u8> = Ok(1u64);
    let _ = g();
}

#[trust_vc::requires(p.is_some())]
#[trust_vc::ensures(true)]
fn c12_capture_shadow_by_param_copy(o: Option<u64>, p: Option<u64>) {
    let g = || o.unwrap();
    let o = p;
    let _ = g();
}

// An identity shadow (a call result) whose scoped value reads the same.
#[trust_vc::ensures(true)]
fn c14_capture_identity_shadow_by_call() {
    let o = mk_none();
    let g = || o.unwrap();
    let o = mk_some();
    let _ = g();
}

// The shadow is seen when a second closure invokes the first.
#[trust_vc::ensures(true)]
fn c15_shadow_then_closure_calling_closure() {
    let o: Option<u64> = None;
    let g = || o.unwrap();
    let o: Option<u64> = Some(1u64);
    let h = || g();
    h();
}

// Arithmetic twin: a shadowed divisor capture.
#[trust_vc::ensures(true)]
fn c1d_arith_twin_shadow() {
    let y: u64 = 0u64;
    let g = || 10u64 / y;
    let y: u64 = 1u64;
    let _ = g();
}

// Arithmetic twin: a `move` capture reassigned after the definition.
#[trust_vc::ensures(true)]
fn x6_move_closure_arith_reassigned() {
    let mut y: u64 = 0u64;
    let g = move || 10u64 / y;
    y = 1u64;
    let _ = g();
}

// LIAR — the capture is unchanged and refuted at the call ...
#[trust_vc::ensures(true)]
fn cl1_capture_none_invoked() {
    let o: Option<u64> = None;
    let g = || o.unwrap();
    let _ = g();
}

// ... also when the shadow lives only in a branch that has ended.
#[trust_vc::ensures(true)]
fn cl2_branch_shadow_ended(b: bool) {
    let o: Option<u64> = None;
    let g = || o.unwrap();
    if b {
        let o: Option<u64> = Some(1u64);
    }
    let _ = g();
}

// CONTROL — an unchanged capture verifies.
#[trust_vc::ensures(true)]
fn cc1_capture_some_invoked_ctrl() {
    let o: Option<u64> = Some(1u64);
    let g = || o.unwrap();
    let _ = g();
}

// CONTROL / LIAR — an unchanged arithmetic capture is still instrumented.
#[trust_vc::requires(y > 0u64)]
#[trust_vc::ensures(true)]
fn cc2_arith_capture_div_ctrl(y: u64) {
    let g = || 10u64 / y;
    let _ = g();
}

#[trust_vc::ensures(true)]
fn cl3_arith_capture_div_liar(y: u64) {
    let g = || 10u64 / y;
    let _ = g();
}
"#;

#[test]
fn review_round1_closure_capture_rebinding() {
    check_table(
        "closure_captures",
        REVIEW_CLOSURE_CAPTURES,
        &[
            ("c1_shadow_capture_after_def", FailClosed),
            ("c1b_shadow_capture_param", FailClosed),
            ("c1c_shadow_capture_inner_block", FailClosed),
            ("c9_capture_shadowed_by_if_let", FailClosed),
            ("c11_result_capture_shadow", FailClosed),
            ("c12_capture_shadow_by_param_copy", FailClosed),
            ("c14_capture_identity_shadow_by_call", FailClosed),
            ("c15_shadow_then_closure_calling_closure", FailClosed),
            ("c1d_arith_twin_shadow", FailClosed),
            ("x6_move_closure_arith_reassigned", FailClosed),
            ("cl1_capture_none_invoked", RefutedByPrecondition),
            ("cl2_branch_shadow_ended", RefutedByPrecondition),
            ("cc1_capture_some_invoked_ctrl", Verified),
            ("cc2_arith_capture_div_ctrl", Verified),
            ("cl3_arith_capture_div_liar", Counterexample),
        ],
    );
}

// ---------------------------------------------------------------------------
// Review round 2 (2026-09-14): the precondition is only as sound as the state
// it reads. Two state-model gaps let a correct `o is Some` obligation verify
// over STALE state, each measured `Verified` at `2d8a5174`:
//
// (a) The modified-set collector (loop frame, `if` / `match` / block join,
//     closure capture-mutation havoc) classified a receiver ONLY through the
//     declared-variable map or a scoped struct-type record. A `let`-local bound
//     to a parameter (`let mut p = w;`, `let mut o = o;`), a typed `Option`
//     local, or a call result records neither, so `p.bump()` / `o.take()` in a
//     loop body or branch was recorded by NO arm: the frame pinned `p ↦ w` and a
//     post-loop `p.o.unwrap()` verified a guaranteed panic. Such a binding is
//     now classified by the declared variable its scoped value names, and a
//     binding with no type at all records any non-pure method conservatively.
//
// (b) The closure capture-mutation "havoc" was an `invalidate_scoped`, which
//     for a declared binding (a `mut o` parameter, or a `let mut o = o;` shadow
//     of one) fell back to the ENTRY symbol still pinned by `requires`, so
//     `let mut f = || { o = None; }; f(); o.unwrap();` verified. The binding is
//     now rebound to a fresh unconstrained symbol (the `&mut`-call-arg model).
//
// Discriminator: with the engine reverted to `2d8a5174` the liars marked (!)
// below come back `Verified`.
// ---------------------------------------------------------------------------

const REVIEW2_USER_TESTER_LOOP: &str = r#"
#![allow(dead_code, unused)]
struct W { o: Option<u64> }
impl W { fn is_some(&mut self) -> bool { self.o = None; true } }

// LIAR (!) — a user `&mut self fn is_some` on a let-local that shadows an
// `Option` parameter, inside a loop: the loop frame kept `v ↦ w`.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_u1_loop_shadow_user_tester_unwrap(v: Option<u64>, w: W) {
    let mut v = w;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        v.is_some();
        i = i + 1u64;
    }
    v.o.unwrap();
}

// LIAR (!) — the assertion twin.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_u2_loop_shadow_user_tester_assert(v: Option<u64>, w: W) {
    let mut v = w;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        v.is_some();
        i = i + 1u64;
    }
    trust_vc::assert!(v.o.is_some());
}

// A loop writing `let mut v = w` (a `W`) that shadows `v: Option<u64>` is
// refused: the loop would model it as the parameter, at the parameter's type.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_u3_loop_shadow_user_tester_assert_false(v: Option<u64>, w: W) {
    let mut v = w;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        v.is_some();
        i = i + 1u64;
    }
    trust_vc::assert!(false);
}
"#;

const REVIEW2_LOOP_JOIN_RECEIVERS: &str = r#"
#![allow(dead_code, unused)]
struct W { o: Option<u64> }
impl W { fn bump(&mut self) { self.o = None; } fn peek(&self) -> bool { self.o.is_some() } }
struct A { x: u64 }
impl A { fn get(&self) -> u64 { self.x } fn zero(&mut self) { self.x = 0u64; } }
trait Tr { fn probe(&self) -> u64; }
impl Tr for A { fn probe(&self) -> u64 { self.x } }
fn mk() -> Option<u64> { Some(1u64) }

// LIAR (!) — `&mut self` user method on a let-local copy of a struct param.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l1_loop_local_user_bump_unwrap(w: W) {
    let mut p = w;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        p.bump();
        i = i + 1u64;
    }
    p.o.unwrap();
}

// LIAR (!) — `Option::take` on a shadowing let-local.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l2_loop_shadow_take_unwrap(o: Option<u64>) {
    let mut o = o;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        o.take();
        i = i + 1u64;
    }
    o.unwrap();
}

// LIAR (!) — the assertion twin of r2_l2.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l3_loop_shadow_take_assert(o: Option<u64>) {
    let mut o = o;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        o.take();
        i = i + 1u64;
    }
    trust_vc::assert!(o.is_some());
}

// LIAR (!) — `Option::take` on a non-shadowing let-local copy.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l4_loop_local_take_unwrap(o: Option<u64>) {
    let mut p = o;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        p.take();
        i = i + 1u64;
    }
    p.unwrap();
}

// LIAR (!) — a typed `Option` local with a literal initializer.
#[trust_vc::ensures(true)]
fn r2_l5_loop_typed_local_take_unwrap() {
    let mut o: Option<u64> = Some(1u64);
    let mut i: u64 = 0u64;
    while i < 2u64 {
        o.take();
        i = i + 1u64;
    }
    o.unwrap();
}

// LIAR (!) — `for` loop.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l6_for_local_take_unwrap(o: Option<u64>) {
    let mut p = o;
    for _i in 0..2u64 {
        p.take();
    }
    p.unwrap();
}

// LIAR (!) — a local bound to a call result.
#[trust_vc::ensures(true)]
fn r2_l7_loop_call_result_take_unwrap() {
    let mut o = mk();
    let mut i: u64 = 0u64;
    while i < 2u64 {
        o.take();
        i = i + 1u64;
    }
    o.unwrap();
}

// LIAR (!) — `if` join.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l8_if_join_local_bump_unwrap(w: W, b: bool) {
    let mut p = w;
    if b {
        p.bump();
    }
    p.o.unwrap();
}

// LIAR (!) — `if` join, `take`.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l9_if_join_local_take_unwrap(o: Option<u64>) {
    let mut p = o;
    if p.is_some() {
        p.take();
    }
    p.unwrap();
}

// LIAR (!) — `match` join.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l10_match_join_local_take_unwrap(o: Option<u64>, k: u64) {
    let mut p = o;
    match k {
        0u64 => {
            p.take();
        }
        _ => {}
    }
    p.unwrap();
}

// LIAR (!) — plain block join.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l11_block_join_local_take_unwrap(o: Option<u64>) {
    let mut p = o;
    {
        p.take();
    }
    p.unwrap();
}

// LIAR (!) — a copy of a copy.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l12_loop_alias_of_alias_unwrap(w: W) {
    let mut p = w;
    let mut q = p;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        q.bump();
        i = i + 1u64;
    }
    q.o.unwrap();
}

// LIAR (!) — a scalar-field struct, assertion form.
#[trust_vc::requires(a.x == 5u64)]
#[trust_vc::ensures(true)]
fn r2_l13_loop_local_struct_zero_assert(a: A) {
    let mut p = a;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        p.zero();
        i = i + 1u64;
    }
    trust_vc::assert!(p.x == 5u64);
}

// CONTROL — the parameter forms were already refuted.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l14_loop_param_take_unwrap_ctrl(mut o: Option<u64>) {
    let mut i: u64 = 0u64;
    while i < 2u64 {
        o.take();
        i = i + 1u64;
    }
    o.unwrap();
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_l15_loop_param_user_bump_assert_ctrl(mut w: W) {
    let mut i: u64 = 0u64;
    while i < 2u64 {
        w.bump();
        i = i + 1u64;
    }
    trust_vc::assert!(w.o.is_some());
}

// CONTROLS — true programs that must keep verifying: a `&self` reader on a
// let-local copy stays framed (no over-rejection).
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_t1_loop_local_peek_ctrl(w: W) {
    let p = w;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        let _b = p.peek();
        i = i + 1u64;
    }
    p.o.unwrap();
}

#[trust_vc::requires(a.x == 5u64)]
#[trust_vc::ensures(true)]
fn r2_t2_loop_local_get_ctrl(a: A) {
    let p = a;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        let _g = p.get();
        i = i + 1u64;
    }
    trust_vc::assert!(p.x == 5u64);
}

#[trust_vc::requires(a.x == 5u64)]
#[trust_vc::ensures(true)]
fn r2_t3_loop_local_trait_probe_ctrl(a: A) {
    let p = a;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        let _g = p.probe();
        i = i + 1u64;
    }
    trust_vc::assert!(p.x == 5u64);
}

// A std tester / consumer on a typed `Option` local (no type record at all)
// is not a modification when the file registers no `&mut self` method of
// that name.
#[trust_vc::ensures(true)]
fn r2_t4_loop_typed_local_tester_ctrl() {
    let o: Option<u64> = Some(1u64);
    let mut i: u64 = 0u64;
    while i < 2u64 {
        if o.is_some() {}
        i = i + 1u64;
    }
    o.unwrap();
}

#[trust_vc::ensures(true)]
fn r2_t5_loop_typed_local_unwrap_or_ctrl() {
    let o: Option<u64> = Some(1u64);
    let mut i: u64 = 0u64;
    while i < 2u64 {
        let _v = o.unwrap_or(0u64);
        i = i + 1u64;
    }
    o.unwrap();
}

#[trust_vc::ensures(true)]
fn r2_t6_loop_typed_local_clone_ctrl() {
    let o: Option<u64> = Some(1u64);
    let mut i: u64 = 0u64;
    while i < 2u64 {
        let _c = o.clone();
        i = i + 1u64;
    }
    o.unwrap();
}

// A by-value method on a `Copy` scalar local never modifies it.
#[trust_vc::ensures(true)]
fn r2_t7_loop_scalar_method_ctrl() {
    let x: u64 = 5u64;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        let _m = x.max(1u64);
        i = i + 1u64;
    }
    trust_vc::assert!(x == 5u64);
}

#[trust_vc::ensures(true)]
fn r2_t8_loop_scalar_unsuffixed_ctrl() {
    let x = 5;
    let mut i = 0;
    while i < 2 {
        let _m = x.max(1);
        i = i + 1;
    }
    trust_vc::assert!(x == 5);
}

#[trust_vc::ensures(true)]
fn r2_t9_loop_bool_local_method_ctrl() {
    let b: bool = true;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        let _t = b.then_some(1u64);
        i = i + 1u64;
    }
    trust_vc::assert!(b);
}

// A let-local copy of an `Option` parameter now resolves scope-exactly to
// `Option<u64>`, so the std tester keeps the binding across an `if`.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_t10_if_join_local_tester_ctrl(o: Option<u64>) {
    let p = o;
    if p.is_none() {}
    p.unwrap();
}

// HONEST COMPLETENESS COST — `replace` makes the receiver `Some`, but the
// mutation is modelled as arbitrary, so this true program fails closed
// (before the fix it verified for the WRONG reason: `p` was never havocked).
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_t11_loop_local_replace_cost(o: Option<u64>) {
    let mut p = o;
    let mut i: u64 = 0u64;
    while i < 2u64 {
        p.replace(1u64);
        i = i + 1u64;
    }
    p.unwrap();
}
"#;

#[test]
fn review_round2_untyped_receiver_framing() {
    check_table(
        "user_tester_loop",
        REVIEW2_USER_TESTER_LOOP,
        &[
            ("r2_u1_loop_shadow_user_tester_unwrap", FailClosed),
            ("r2_u2_loop_shadow_user_tester_assert", FailClosed),
            ("r2_u3_loop_shadow_user_tester_assert_false", FailClosed),
        ],
    );
    check_table(
        "loop_join_receivers",
        REVIEW2_LOOP_JOIN_RECEIVERS,
        &[
            ("r2_l1_loop_local_user_bump_unwrap", FailClosed),
            ("r2_l2_loop_shadow_take_unwrap", RefutedByPrecondition),
            ("r2_l3_loop_shadow_take_assert", Counterexample),
            ("r2_l4_loop_local_take_unwrap", FailClosed),
            ("r2_l5_loop_typed_local_take_unwrap", FailClosed),
            ("r2_l6_for_local_take_unwrap", FailClosed),
            ("r2_l7_loop_call_result_take_unwrap", FailClosed),
            ("r2_l8_if_join_local_bump_unwrap", FailClosed),
            ("r2_l9_if_join_local_take_unwrap", FailClosed),
            ("r2_l10_match_join_local_take_unwrap", FailClosed),
            ("r2_l11_block_join_local_take_unwrap", FailClosed),
            ("r2_l12_loop_alias_of_alias_unwrap", FailClosed),
            ("r2_l13_loop_local_struct_zero_assert", FailClosed),
            ("r2_l14_loop_param_take_unwrap_ctrl", RefutedByPrecondition),
            ("r2_l15_loop_param_user_bump_assert_ctrl", Counterexample),
            ("r2_t1_loop_local_peek_ctrl", Verified),
            ("r2_t2_loop_local_get_ctrl", Verified),
            ("r2_t3_loop_local_trait_probe_ctrl", Verified),
            ("r2_t4_loop_typed_local_tester_ctrl", Verified),
            ("r2_t5_loop_typed_local_unwrap_or_ctrl", Verified),
            ("r2_t6_loop_typed_local_clone_ctrl", Verified),
            ("r2_t7_loop_scalar_method_ctrl", Verified),
            ("r2_t8_loop_scalar_unsuffixed_ctrl", Verified),
            ("r2_t9_loop_bool_local_method_ctrl", Verified),
            ("r2_t10_if_join_local_tester_ctrl", Verified),
            ("r2_t11_loop_local_replace_cost", FailClosed),
        ],
    );
}

const REVIEW2_CLOSURE_CAPTURE_MUTATION: &str = r#"
#![allow(dead_code, unused)]
struct W { o: Option<u64> }
impl W { fn bump(&mut self) { self.o = None; } fn peek(&self) -> bool { self.o.is_some() } }

// LIAR (!) — a shadowing let-local written by an invoked closure.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c1_closure_shadow_write_unwrap(o: Option<u64>) {
    let mut o = o;
    let mut f = || {
        o = None;
    };
    f();
    o.unwrap();
}

// LIAR (!) — a `mut` parameter written by an invoked closure.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c2_closure_param_write_unwrap(mut o: Option<u64>) {
    let mut f = || {
        o = None;
    };
    f();
    o.unwrap();
}

// LIAR — a typed local (no declared symbol: fails closed as unresolved).
#[trust_vc::ensures(true)]
fn r2_c3_closure_typed_local_write_unwrap() {
    let mut o: Option<u64> = Some(1u64);
    let mut f = || {
        o = None;
    };
    f();
    o.unwrap();
}

// LIAR (!) — a field write through the closure, shadow and parameter forms.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c4_closure_shadow_field_write_unwrap(w: W) {
    let mut w = w;
    let mut f = || {
        w.o = None;
    };
    f();
    w.o.unwrap();
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c5_closure_param_field_write_unwrap(mut w: W) {
    let mut f = || {
        w.o = None;
    };
    f();
    w.o.unwrap();
}

// LIAR (!) — a `&mut self` std method on a shadow inside the closure.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c6_closure_shadow_take_unwrap(o: Option<u64>) {
    let mut o = o;
    let mut f = || {
        o.take();
    };
    f();
    o.unwrap();
}

// LIAR (!) — a `&mut self` user method on a let-local copy.
#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c7_closure_local_bump_unwrap(w: W) {
    let mut p = w;
    let mut f = || {
        p.bump();
    };
    f();
    p.o.unwrap();
}

// LIAR (!) — `take` on a typed local inside the closure.
#[trust_vc::ensures(true)]
fn r2_c8_closure_typed_local_take_unwrap() {
    let mut o: Option<u64> = Some(1u64);
    let mut f = || {
        o.take();
    };
    f();
    o.unwrap();
}

// LIARS (!) — the assertion and arithmetic twins (a stale `requires` fact).
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c9_closure_shadow_write_assert(o: Option<u64>) {
    let mut o = o;
    let mut f = || {
        o = None;
    };
    f();
    trust_vc::assert!(o.is_some());
}

#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c10_closure_param_write_assert(mut o: Option<u64>) {
    let mut f = || {
        o = None;
    };
    f();
    trust_vc::assert!(o.is_some());
}

#[trust_vc::requires(x == 1u64)]
#[trust_vc::ensures(true)]
fn r2_c11_closure_scalar_shadow_div(x: u64) {
    let mut x = x;
    let mut f = || {
        x = 0u64;
    };
    f();
    let _q = 10u64 / x;
}

#[trust_vc::requires(x == 1u64)]
#[trust_vc::ensures(true)]
fn r2_c12_closure_scalar_param_div(mut x: u64) {
    let mut f = || {
        x = 0u64;
    };
    f();
    let _q = 10u64 / x;
}

// LIAR — a scoped-only scalar local is freshened (refuted, not unresolved).
#[trust_vc::ensures(true)]
fn r2_c13_closure_scalar_local_div() {
    let mut x: u64 = 1u64;
    let mut f = || {
        x = 0u64;
    };
    f();
    let _q = 10u64 / x;
}

// LIAR — a non-shadowing `Option` local keeps the fail-closed model.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_c14_closure_local_write_unwrap(o: Option<u64>) {
    let mut p = o;
    let mut f = || {
        p = None;
    };
    f();
    p.unwrap();
}

// CONTROLS — a closure that only READS a let-local copy leaves it framed.
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_ct1_closure_reads_local_ctrl(o: Option<u64>) {
    let p = o;
    let g = || p.is_some();
    let _b = g();
    p.unwrap();
}

#[trust_vc::requires(w.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_ct2_closure_reads_local_peek_ctrl(w: W) {
    let p = w;
    let g = || p.peek();
    let _b = g();
    p.o.unwrap();
}
"#;

#[test]
fn review_round2_closure_capture_havoc() {
    check_table(
        "closure_capture_mutation",
        REVIEW2_CLOSURE_CAPTURE_MUTATION,
        &[
            ("r2_c1_closure_shadow_write_unwrap", RefutedByPrecondition),
            ("r2_c2_closure_param_write_unwrap", RefutedByPrecondition),
            ("r2_c3_closure_typed_local_write_unwrap", FailClosed),
            (
                "r2_c4_closure_shadow_field_write_unwrap",
                RefutedByPrecondition,
            ),
            (
                "r2_c5_closure_param_field_write_unwrap",
                RefutedByPrecondition,
            ),
            ("r2_c6_closure_shadow_take_unwrap", RefutedByPrecondition),
            ("r2_c7_closure_local_bump_unwrap", FailClosed),
            ("r2_c8_closure_typed_local_take_unwrap", FailClosed),
            ("r2_c9_closure_shadow_write_assert", Counterexample),
            ("r2_c10_closure_param_write_assert", Counterexample),
            ("r2_c11_closure_scalar_shadow_div", Counterexample),
            ("r2_c12_closure_scalar_param_div", Counterexample),
            ("r2_c13_closure_scalar_local_div", Counterexample),
            ("r2_c14_closure_local_write_unwrap", FailClosed),
            ("r2_ct1_closure_reads_local_ctrl", Verified),
            ("r2_ct2_closure_reads_local_peek_ctrl", Verified),
        ],
    );
}

// ---------------------------------------------------------------------------
// Review round 2, finding A — the BARE BLOCK / `unsafe` block join
//
// A `{ .. }` / `unsafe { .. }` block is visited under a scope snapshot that is
// RESTORED afterwards, and the only post-block step was
// `invalidate_scoped_names`. That drops a SCOPED REWRITE only: an undeclared
// local then reads as an unresolved name (fail closed — sound), but a DECLARED
// binding fell back to its ENTRY symbol, still pinned by `requires`. So a
// registered `&mut self` user method called inside a bare block left the
// receiver at its entry value and `{ h.sink(); } h.o.unwrap()` verified a
// guaranteed panic, while the straight-line, `if` and `while` twins of the same
// program are refuted. The block join now havocs every assigned DECLARED
// binding, exactly as the `if` join (`havoc_unmerged_assigned_at_join`) and the
// loop join (`havoc_modified_var_at_loop_join`) do.
// ---------------------------------------------------------------------------

const REVIEW2_BLOCK_JOIN_FRAMING: &str = r#"
#![allow(dead_code, unused)]

struct H { o: Option<u64> }
impl H { fn sink(&mut self) { self.o = None; } }

struct Q { o: Option<u64>, v: u64 }
impl Q {
    fn drain(&mut self) -> u64 { self.o = None; self.v = 0u64; 0u64 }
    fn peek(&self) -> u64 { self.v }
}

struct S { x: u64 }
impl S { fn zero(&mut self) { self.x = 0u64; } }

// LIAR — the finding-A repro: a bare block drops a registered `&mut self`
// method's effect on a PARAMETER receiver, so the unwrap read the pre-block
// `Some`. Panics on every call.
#[trust_vc::requires(h.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_b1_block_user_sink_unwrap(mut h: H) {
    {
        h.sink();
    }
    h.o.unwrap();
}

// LIAR — same through a `&mut self` method that also RETURNS a value.
#[trust_vc::requires(q.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_b2_block_user_drain_unwrap(mut q: Q) {
    {
        q.drain();
    }
    q.o.unwrap();
}

// LIAR — `unsafe { .. }` executes inline with identical scoping.
#[trust_vc::requires(h.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_b3_unsafe_block_user_sink_unwrap(mut h: H) {
    unsafe {
        h.sink();
    }
    h.o.unwrap();
}

// LIAR — nested bare blocks.
#[trust_vc::requires(h.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_b4_nested_block_user_sink_unwrap(mut h: H) {
    {
        {
            h.sink();
        }
    }
    h.o.unwrap();
}

// LIAR — the ASSERT form of the same framing loss (no unwrap obligation
// involved): the block sets `q.v` to 0, the assert claims the entry value.
#[trust_vc::requires(q.v == 5u64)]
#[trust_vc::ensures(true)]
fn r2_b5_block_user_drain_assert(mut q: Q) {
    {
        q.drain();
    }
    trust_vc::assert!(q.v == 5u64);
}

// LIAR — a `let`-local copy of a struct parameter: the block's `&mut self`
// call is recorded, and an undeclared local fails closed.
#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::ensures(true)]
fn r2_b6_block_local_struct_zero_assert(s: S) {
    let mut t = s;
    {
        t.zero();
    }
    trust_vc::assert!(t.x == 5u64);
}

// LIAR — a typed `Option` local mutated by `take()` inside a bare block.
#[trust_vc::ensures(true)]
fn r2_b7_block_local_option_take_unwrap() {
    let mut o: Option<u64> = Some(1u64);
    {
        o.take();
    }
    o.unwrap();
}

// LIAR — the assert twin of b7: the engine must not still believe `o` is
// `Some(1)` after the block.
#[trust_vc::ensures(true)]
fn r2_b8_block_local_option_take_assert_some() {
    let mut o: Option<u64> = Some(1u64);
    {
        o.take();
    }
    trust_vc::assert!(o.is_some());
}

// NON-VACUITY — the block fixture's context is satisfiable, so the refutations
// above are real and not an infeasible path.
#[trust_vc::requires(h.o.is_some())]
#[trust_vc::ensures(true)]
fn r2_b9_block_sink_assert_false(mut h: H) {
    {
        h.sink();
    }
    trust_vc::assert!(false);
}

// CONTROL — a resolved `&self` reader in the block leaves the receiver framed.
#[trust_vc::requires(q.v == 5u64)]
#[trust_vc::ensures(true)]
fn r2_bt1_block_readonly_ctrl(q: Q) {
    {
        let _r = q.peek();
    }
    trust_vc::assert!(q.v == 5u64);
}

// CONTROL — a block that touches only its own locals.
#[trust_vc::requires(q.v == 5u64)]
#[trust_vc::ensures(true)]
fn r2_bt2_block_local_only_ctrl(q: Q) {
    {
        let mut u: u64 = 0u64;
        u = u + 1u64;
    }
    trust_vc::assert!(q.v == 5u64);
}

// CONTROL — a std `Option` tester in the block is pure, so the TRUE unwrap
// after it still verifies (no over-rejection).
#[trust_vc::requires(o.is_some())]
#[trust_vc::ensures(true)]
fn r2_bt3_block_pure_tester_ctrl(o: Option<u64>) {
    {
        let _b = o.is_some();
    }
    o.unwrap();
}

// CONTROL — a read-only `unsafe` block.
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn r2_bt4_unsafe_block_readonly_ctrl(x: u64) {
    unsafe {
        let _y = x;
    }
    trust_vc::assert!(x == 5u64);
}

// The remaining round-2 liar SPELLINGS, all of them the same defect: a typed
// `Option` local mutated by `take()` under a join that restored the binding.
// Each was `Verified` at `2d8a5174` and panics at every run; each now fails
// closed (the receiver is an unresolved name after the join).

// LIAR — `unsafe { .. }` around the local mutation.
#[trust_vc::ensures(true)]
fn r2_b10_unsafe_block_local_take() {
    let mut o: Option<u64> = Some(1u64);
    unsafe {
        o.take();
    }
    o.unwrap();
}

// LIAR — a `loop { .. break; }` body.
#[trust_vc::ensures(true)]
fn r2_b11_loop_break_local_take() {
    let mut o: Option<u64> = Some(1u64);
    loop {
        o.take();
        break;
    }
    o.unwrap();
}

// LIAR — nested bare blocks.
#[trust_vc::ensures(true)]
fn r2_b12_nested_block_local_take() {
    let mut o: Option<u64> = Some(1u64);
    {
        {
            o.take();
        }
    }
    o.unwrap();
}

// LIAR — the mutation on the `else` arm only.
#[trust_vc::ensures(true)]
fn r2_b13_else_arm_local_take(b: bool) {
    let mut o: Option<u64> = Some(1u64);
    if b {
    } else {
        o.take();
    }
    o.unwrap();
}

// LIAR — a constant-true guard.
#[trust_vc::ensures(true)]
fn r2_b14_if_true_local_take() {
    let mut o: Option<u64> = Some(1u64);
    if true {
        o.take();
    }
    o.unwrap();
}

// LIAR — a bare block nested inside a `while` body.
#[trust_vc::ensures(true)]
fn r2_b15_while_inner_block_local_take() {
    let mut o: Option<u64> = Some(1u64);
    let mut i: u64 = 0u64;
    while i < 2u64 {
        {
            o.take();
        }
        i = i + 1u64;
    }
    o.unwrap();
}

// LIAR — both arms mutate.
#[trust_vc::ensures(true)]
fn r2_b16_both_arms_local_take(b: bool) {
    let mut o: Option<u64> = Some(1u64);
    if b {
        o.take();
    } else {
        o.take();
    }
    o.unwrap();
}

// RECORDED PRECISION COST — these two are TRUE programs (`replace` leaves the
// option `Some`; a `while false` body never runs) that the conservative
// modified-set over-approximation now fails closed on. Pinned so a later
// precision gain is a deliberate, measured change and not a silent drift.
#[trust_vc::ensures(true)]
fn r2_bc1_block_replace_true_cost() {
    let mut o: Option<u64> = Some(1u64);
    {
        o.replace(2u64);
    }
    o.unwrap();
}

#[trust_vc::ensures(true)]
fn r2_bc2_while_false_true_cost() {
    let mut o: Option<u64> = Some(1u64);
    while false {
        o.take();
    }
    o.unwrap();
}

// CONTROL — the same local read-only in a block still verifies.
#[trust_vc::ensures(true)]
fn r2_bt5_local_readonly_block_ctrl() {
    let o: Option<u64> = Some(1u64);
    {
        let _b = o.is_some();
    }
    o.unwrap();
}
"#;

#[test]
fn review_round2_block_join_framing() {
    check_table(
        "block_join_framing",
        REVIEW2_BLOCK_JOIN_FRAMING,
        &[
            ("r2_b1_block_user_sink_unwrap", RefutedByPrecondition),
            ("r2_b2_block_user_drain_unwrap", RefutedByPrecondition),
            ("r2_b3_unsafe_block_user_sink_unwrap", RefutedByPrecondition),
            ("r2_b4_nested_block_user_sink_unwrap", RefutedByPrecondition),
            ("r2_b5_block_user_drain_assert", Counterexample),
            ("r2_b6_block_local_struct_zero_assert", FailClosed),
            ("r2_b7_block_local_option_take_unwrap", FailClosed),
            ("r2_b8_block_local_option_take_assert_some", FailClosed),
            ("r2_b9_block_sink_assert_false", Counterexample),
            ("r2_bt1_block_readonly_ctrl", Verified),
            ("r2_bt2_block_local_only_ctrl", Verified),
            ("r2_bt3_block_pure_tester_ctrl", Verified),
            ("r2_bt4_unsafe_block_readonly_ctrl", Verified),
            ("r2_b10_unsafe_block_local_take", FailClosed),
            ("r2_b11_loop_break_local_take", FailClosed),
            ("r2_b12_nested_block_local_take", FailClosed),
            ("r2_b13_else_arm_local_take", FailClosed),
            ("r2_b14_if_true_local_take", FailClosed),
            ("r2_b15_while_inner_block_local_take", FailClosed),
            ("r2_b16_both_arms_local_take", FailClosed),
            ("r2_bc1_block_replace_true_cost", FailClosed),
            ("r2_bc2_while_false_true_cost", FailClosed),
            ("r2_bt5_local_readonly_block_ctrl", Verified),
        ],
    );
}

// ---------------------------------------------------------------------------
// Review round 2, minor 2 — the TRAIT-QUALIFIED UFCS path
//
// `<T as Trait>::unwrap(..)` used to classify as "not an unwrap site at all",
// justified by the unchecked standing assumption that no std trait declares an
// unwrap-family method. The owner is now taken from the TRAIT path: a trait the
// file declares keeps owning its own call (control below), anything else fails
// closed.
// ---------------------------------------------------------------------------

const REVIEW2_TRAIT_QUALIFIED_UFCS: &str = r#"
#![allow(dead_code, unused)]

struct U { o: Option<u64> }
trait Tr { fn unwrap(&self) -> u64; }
impl Tr for U { fn unwrap(&self) -> u64 { 7u64 } }

// LIAR — the fully-qualified std spellings still carry the precondition.
#[trust_vc::ensures(true)]
fn r2_n1_std_option_path(o: Option<u64>) {
    std::option::Option::unwrap(o);
}

#[trust_vc::ensures(true)]
fn r2_n2_core_option_path(o: Option<u64>) {
    core::option::Option::unwrap(o);
}

#[trust_vc::ensures(true)]
fn r2_n3_qself_option(o: Option<u64>) {
    <Option<u64>>::unwrap(o);
}

// UNRESOLVED — a trait qualification the file does not declare. Not compilable
// Rust today (E0576), but the model must not assume that: it fails closed.
#[trust_vc::ensures(true)]
fn r2_n4_trait_qualified_unknown_trait(o: Option<u64>) {
    <Option<u64> as Sized>::unwrap(o);
}

// CONTROL — a user trait's own `unwrap` is owned by that trait's contract path,
// so it is not an unwrap-family site and the true program still verifies.
#[trust_vc::ensures(true)]
fn r2_n5_user_trait_ufcs_ctrl(u: U) {
    let _r = <U as Tr>::unwrap(&u);
}
"#;

#[test]
fn review_round2_trait_qualified_ufcs() {
    check_table(
        "trait_qualified_ufcs",
        REVIEW2_TRAIT_QUALIFIED_UFCS,
        &[
            ("r2_n1_std_option_path", RefutedByPrecondition),
            ("r2_n2_core_option_path", RefutedByPrecondition),
            ("r2_n3_qself_option", RefutedByPrecondition),
            ("r2_n4_trait_qualified_unknown_trait", FailClosed),
            ("r2_n5_user_trait_ufcs_ctrl", Verified),
        ],
    );
}
