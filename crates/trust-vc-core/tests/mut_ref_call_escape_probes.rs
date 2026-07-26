// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Mutable-borrow call-escape probes — the slice-D adversarial suite,
//! committed as a permanent battery (all 28 adversarial must-never-verify
//! shapes + the remediation-added p20b match-assignment sibling + 2
//! completeness pins).
//!
//! Every `mnv_*` case has a REAL execution that violates its `assert!` (or a
//! callee `requires`), so `Verified` there is a catastrophic false positive.
//! On the pre-remediation tree TEN of these shapes VERIFIED:
//!
//! * p8/p8b (short-circuit `&&`/`||` RHS call): the call sits in the if
//!   CONDITION where the path-condition stack is empty and `&&`/`||`
//!   short-circuit conditionality is unmodeled, so the callee `ensures` was
//!   assumed unconditionally over the havoc'd fresh symbol — post-`if` code
//!   gained ensures knowledge for a call that may never execute. CLOSED by
//!   `short_circuit_rhs_depth`: the `__call_ensures_*` assume (and bare
//!   `assume!` / post-loop exit facts) are DROPPED inside a short-circuit RHS;
//!   the `requires` obligations and the arg havoc stay (fail-closed / sound).
//! * p7b/p20 (nested-block / match-arm call-arg havoc rollback): the
//!   `&mut`-call-arg havoc ran inside a region whose snapshot-restore reverted
//!   it, and the root was never recorded into the deref-write region set, so
//!   the region exit did not re-havoc and the `requires`-pinned PRE value
//!   resurfaced. CLOSED by recording the root in
//!   `havoc_mut_ref_call_arg_referents` (the slice-C region mechanism); the
//!   match join additionally havocs every arm-assigned declared binding
//!   (`havoc_unmerged_assigned_at_join`, previously struct-only).
//! * p1/p23 (reborrow `&mut *(&mut p)` / `&mut &mut p`), p4 (method arg
//!   `s.mwr(&mut p)`), p19 (UFCS arg `SPair::wr(&mut p)`), p44 (fn-pointer
//!   call `g(&mut p)`), p2 (alias borrow-escape `let r = &mut p;`): base-era
//!   holes — these shapes bypass the owned call-arg havoc, and the general
//!   borrow-escape model was `invalidate_scoped` alone, so a DECLARED
//!   `requires`-pinned param fell back to its ENTRY symbol (a stale read,
//!   NOT fail-closed — the earlier "honest scope-outs are all fail-closed"
//!   claim was WRONG for exactly these shapes). CLOSED by
//!   `havoc_mut_borrow_escaped_binding`: a mutable borrow of a DECLARED
//!   binding escaping through any unowned shape havocs it to a fresh
//!   unconstrained symbol (undeclared locals keep the fail-closed
//!   invalidate), and records the root into any active rollback region.
//!
//! The remaining `mnv_*` shapes were already fail-closed (loop-context Error,
//! branch-join CE, requires-discharge CE, directionality CE) and are pinned
//! here so they stay that way. The two `ok_*` cases pin completeness: the
//! swap relation and the mixed `&mut`+by-value `old()` requires form must
//! keep verifying (no over-rejection).
//!
//! Pin discipline: `assert_never_verifies` — Error / Counterexample / Unknown
//! are all acceptable, `Verified` is the one catastrophic outcome. Exact
//! verdicts (CE vs Error) are deliberately not pinned: several shapes sit on
//! fail-closed error paths whose message/verdict may legitimately improve.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- callees ----------

#[trust_vc::requires(*old(a) < 10u64)]
#[trust_vc::ensures(*a == *old(a) + 1u64)]
fn add1(a: &mut u64) {
    *a = *a + 1u64;
}

#[trust_vc::requires(a < 10u64)]
#[trust_vc::ensures(a == 7u64)]
fn set7(a: &mut u64) {
    *a = 7u64;
}

#[trust_vc::ensures(*a == *old(a) + 1u64)]
fn add1b(a: &mut u64) -> bool {
    *a = *a + 1u64;
    true
}

#[trust_vc::ensures(*a == *old(a) + 1u64)]
fn lt10inc(a: &mut u64) -> bool {
    *a = *a + 1u64;
    *a < 10u64
}

fn nocontract(a: &mut u64) {
    *a = 99u64;
}

fn nc2(a: &mut &mut u64) {
    **a = 99u64;
}

fn genw<T>(a: &mut u64) {
    *a = 99u64;
}

#[trust_vc::ensures(*a == *old(b) && *b == *old(a))]
fn swp(a: &mut u64, b: &mut u64) {
    let t = *a;
    *a = *b;
    *b = t;
}

#[trust_vc::requires(*old(a) + k < 10u64)]
#[trust_vc::ensures(*a == *old(a) + k)]
fn addk(a: &mut u64, k: u64) {
    *a = *a + k;
}

struct SPair {
    x: u64,
    y: u64,
}

impl SPair {
    fn wr(a: &mut u64) {
        *a = 99u64;
    }
    fn mwr(&self, a: &mut u64) {
        *a = 99u64;
    }
}

#[trust_vc::requires(a == 5u64)]
#[trust_vc::ensures(a == 20u64)]
fn set20(a: &mut u64) {
    *a = 20u64;
}

// P50: chain requires — call 2's requires must be discharged against call 1's
// POST (20), not the original pre (5). Real execution violates add1's
// requires (*old(a) = 20, not < 10) — must NOT verify.
#[trust_vc::ensures(true)]
fn mnv_p50_chain_requires_stale_pre() {
    let mut v = 5u64;
    set20(&mut v);
    add1(&mut v);
}

// ---------- probes ----------

// P1: reborrow arg shape — real: p = 99, assert fails
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p1_reborrow(mut p: u64) {
    nocontract(&mut *(&mut p));
    trust_vc::assert!(p == 5u64);
}

// P2: alias-local forwarding from a DECLARED param — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p2_alias_param_nocontract(mut p: u64) {
    let r = &mut p;
    nocontract(r);
    trust_vc::assert!(p == 5u64);
}

// P2b: alias-local forwarding, contracted callee — real: p = 6
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p2b_alias_param_contracted(mut p: u64) {
    let r = &mut p;
    add1(r);
    trust_vc::assert!(p == 5u64);
}

// P3: multi-segment path call — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p3_selfpath(mut p: u64) {
    self::nocontract(&mut p);
    trust_vc::assert!(p == 5u64);
}

// P4: method-call &mut arg — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p4_method_arg(mut p: u64) {
    let s = SPair { x: 1u64, y: 2u64 };
    s.mwr(&mut p);
    trust_vc::assert!(p == 5u64);
}

// P19: UFCS associated-fn &mut arg — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p19_ufcs_assoc(mut p: u64) {
    SPair::wr(&mut p);
    trust_vc::assert!(p == 5u64);
}

// P23: &mut &mut p (write reaches p through inner &mut) — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p23_mutmut(mut p: u64) {
    nc2(&mut &mut p);
    trust_vc::assert!(p == 5u64);
}

// P18: paren-wrapped referent — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p18_paren(mut p: u64) {
    nocontract(&mut (p));
    trust_vc::assert!(p == 5u64);
}

// P44: call through a fn-pointer binding — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p44_fnptr(mut p: u64) {
    let g = nocontract;
    g(&mut p);
    trust_vc::assert!(p == 5u64);
}

// P45: generic callee — real: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p45_generic(mut p: u64) {
    genw::<u64>(&mut p);
    trust_vc::assert!(p == 5u64);
}

// P5: call in loop body, contract-less — real (3 iterations): v = 99
#[trust_vc::ensures(true)]
fn mnv_p5_loop_nocontract() {
    let mut v = 5u64;
    let mut i = 0u64;
    while i < 3u64 {
        nocontract(&mut v);
        i = i + 1u64;
    }
    trust_vc::assert!(v == 5u64);
}

// P5b: call in loop body, contracted — real: v = 8
#[trust_vc::ensures(true)]
fn mnv_p5b_loop_contracted() {
    let mut v = 5u64;
    let mut i = 0u64;
    while i < 3u64 {
        add1(&mut v);
        i = i + 1u64;
    }
    trust_vc::assert!(v == 5u64);
}

// P6: branch call on a DECLARED param, contract-less — real c=true: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p6_branch_param_nocontract(mut p: u64, c: bool) {
    if c {
        nocontract(&mut p);
    }
    trust_vc::assert!(p == 5u64);
}

// P6b: branch call on a DECLARED param, contracted — real c=true: p = 6
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p6b_branch_param_contracted(mut p: u64, c: bool) {
    if c {
        add1(&mut p);
    }
    trust_vc::assert!(p == 5u64);
}

// P6c: both arms call — real: p = 6 either way
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p6c_both_arms_param(mut p: u64, c: bool) {
    if c {
        add1(&mut p);
    } else {
        add1(&mut p);
    }
    trust_vc::assert!(p == 5u64);
}

// P7: call inside a plain nested block — real: v = 6
#[trust_vc::ensures(true)]
fn mnv_p7_nested_block() {
    let mut v = 5u64;
    {
        add1(&mut v);
    }
    trust_vc::assert!(v == 5u64);
}

// P7b: nested block, param + contract-less — real: p = 99
// (was FALSE VERIFIED: the in-block call-arg havoc was rolled back by the
// region snapshot-restore and never re-havocked at exit)
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p7b_nested_block_param(mut p: u64) {
    {
        nocontract(&mut p);
    }
    trust_vc::assert!(p == 5u64);
}

// P8: short-circuit && RHS call — real c=false: v stays 5, assert v==6 fails
// (was FALSE VERIFIED: the ensures was assumed unconditionally)
#[trust_vc::ensures(true)]
fn mnv_p8_shortcircuit_and(c: bool) {
    let mut v = 5u64;
    if c && add1b(&mut v) {
        let _ = v;
    }
    trust_vc::assert!(v == 6u64);
}

// P8b: short-circuit || RHS call — real c=true: v stays 5, assert v==6 fails
// (was FALSE VERIFIED, sibling of P8)
#[trust_vc::ensures(true)]
fn mnv_p8b_shortcircuit_or(c: bool) {
    let mut v = 5u64;
    if c || add1b(&mut v) {
        let _ = v;
    }
    trust_vc::assert!(v == 6u64);
}

// P13: pre-call write then call — real: v = 8, assert v==6 fails
// (catches old() binding the stale INIT value 5 instead of the latest 7)
#[trust_vc::ensures(true)]
fn mnv_p13_precall_write() {
    let mut v = 5u64;
    v = 7u64;
    add1(&mut v);
    trust_vc::assert!(v == 6u64);
}

// P33: requires must be discharged against PRE (20), not the ensures-pinned
// post (7): set7 requires a < 10 — real execution violates the precondition
#[trust_vc::ensures(true)]
fn mnv_p33_requires_against_post() {
    let mut v = 20u64;
    set7(&mut v);
}

// P15: cross-param old — real: x = 2 after swap, assert x==1 fails
#[trust_vc::ensures(true)]
fn mnv_p15_cross_param_swap(mut q: u64) {
    let mut x = 1u64;
    let mut y = 2u64;
    swp(&mut x, &mut y);
    trust_vc::assert!(x == 1u64);
}

// P15b (completeness, expect Verified): swap relates both directions
#[trust_vc::ensures(true)]
fn ok_p15b_cross_param_swap_verified() {
    let mut x = 1u64;
    let mut y = 2u64;
    swp(&mut x, &mut y);
    trust_vc::assert!(x == 2u64);
    trust_vc::assert!(y == 1u64);
}

// P42: mixed &mut + by-value param in old-form requires — real: 5+20 >= 10
#[trust_vc::ensures(true)]
fn mnv_p42_addk_requires_violated() {
    let mut v = 5u64;
    addk(&mut v, 20u64);
}

// P42b (completeness, expect Verified)
#[trust_vc::ensures(true)]
fn ok_p42b_addk_verified() {
    let mut v = 5u64;
    addk(&mut v, 2u64);
    trust_vc::assert!(v == 7u64);
}

// P20: match arm call on a DECLARED param — real c=true: p = 99
// (was FALSE VERIFIED: rollback sibling of P7b, plus the match join only
// havocked struct receivers — declared scalars reverted to the entry pin)
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p20_match_arm(mut p: u64, c: bool) {
    match c {
        true => {
            nocontract(&mut p);
        }
        false => {}
    }
    trust_vc::assert!(p == 5u64);
}

// P20b (remediation-added sibling of P20): match arm PLAIN ASSIGNMENT on a
// DECLARED param — real c=true: p = 9. Probed firsthand on base ff9ea638:
// Verified (the match join only havocked struct receivers, so the declared
// scalar reverted to the requires-pinned entry symbol). Closed by the match
// join's `havoc_unmerged_assigned_at_join` upgrade.
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p20b_match_arm_assign(mut p: u64, c: bool) {
    match c {
        true => {
            p = 9u64;
        }
        false => {}
    }
    trust_vc::assert!(p == 5u64);
}

// P38: call in a while CONDITION — real: exits at w = 10, assert w==6 fails
#[trust_vc::requires(w == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p38_while_cond(mut w: u64) {
    while lt10inc(&mut w) {
        let _ = w;
    }
    trust_vc::assert!(w == 6u64);
}

// P39: early-return guard then call — real c=false: p = 99
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn mnv_p39_early_return(mut p: u64, c: bool) {
    if c {
        return;
    }
    nocontract(&mut p);
    trust_vc::assert!(p == 5u64);
}

// P35: nested expression-position call — real: v = 6, assert v==5 fails
#[trust_vc::ensures(true)]
fn mnv_p35_nested_expr_call() {
    let mut v = 5u64;
    let _w = add1b(&mut v);
    trust_vc::assert!(v == 5u64);
}

// ---------- bare-loop family (recheck q-series, fixed by frame_loop_modified_vars) ----------
// visit_expr_loop used invalidate_scoped_names (scoped locals only) — a
// requires-pinned DECLARED param written in a loop body fell back to its
// ENTRY symbol post-loop (three base-era holes + one landing-chain
// regression). Now framed like for-loops: declared vars havoc unless a loop
// invariant constrains them.

// real: p = 8
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn q1_loop_body_call_param(mut p: u64) {
    loop {
        add1(&mut p);
        break;
    }
    trust_vc::assert!(p == 5u64);
}

// real: p = 9
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn q3_loop_body_assign_param(mut p: u64) {
    loop {
        p = 9u64;
        break;
    }
    trust_vc::assert!(p == 5u64);
}

// real: p = 8 (second call shape)
#[trust_vc::requires(p == 5u64)]
#[trust_vc::ensures(true)]
fn q4_loop_body_nocontract_param(mut p: u64) {
    loop {
        add1(&mut p);
        break;
    }
    trust_vc::assert!(p == 5u64);
}

"####;

fn run(func: &str) -> VerifyResult {
    // The on-disk VC-result cache stores only `verified` verdicts and replays
    // them without re-encoding — it MUST be disabled for true verdicts.
    // Serialized behind the process-wide env lock and restored on scope exit
    // (guards drop before the lock releases) via the workspace env choke point.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::env::temp_dir().join("trust_vc_mut_ref_call_escape_probes");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(SRC.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

/// The one catastrophic outcome for an `mnv_*` case is `Verified` — every one
/// of these programs has a real execution violating its assert or a callee
/// requires. Error / Counterexample / Unknown are all fail-closed.
fn assert_never_verifies(func: &str) {
    let r = run(func);
    assert!(
        !r.is_verified(),
        "{func} must NEVER verify (a real execution violates it), got: {r:?}"
    );
}

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (no over-rejection), got: {r:?}"
    );
}

#[test]
fn probe_p1_reborrow_never_verifies() {
    assert_never_verifies("mnv_p1_reborrow");
}

#[test]
fn probe_p2_alias_param_nocontract_never_verifies() {
    assert_never_verifies("mnv_p2_alias_param_nocontract");
}

#[test]
fn probe_p2b_alias_param_contracted_never_verifies() {
    assert_never_verifies("mnv_p2b_alias_param_contracted");
}

#[test]
fn probe_p3_selfpath_never_verifies() {
    assert_never_verifies("mnv_p3_selfpath");
}

#[test]
fn probe_p4_method_arg_never_verifies() {
    assert_never_verifies("mnv_p4_method_arg");
}

#[test]
fn probe_p19_ufcs_assoc_never_verifies() {
    assert_never_verifies("mnv_p19_ufcs_assoc");
}

#[test]
fn probe_p23_mutmut_never_verifies() {
    assert_never_verifies("mnv_p23_mutmut");
}

#[test]
fn probe_p18_paren_never_verifies() {
    assert_never_verifies("mnv_p18_paren");
}

#[test]
fn probe_p44_fnptr_never_verifies() {
    assert_never_verifies("mnv_p44_fnptr");
}

#[test]
fn probe_p45_generic_never_verifies() {
    assert_never_verifies("mnv_p45_generic");
}

#[test]
fn probe_p5_loop_nocontract_never_verifies() {
    assert_never_verifies("mnv_p5_loop_nocontract");
}

#[test]
fn probe_p5b_loop_contracted_never_verifies() {
    assert_never_verifies("mnv_p5b_loop_contracted");
}

#[test]
fn probe_p6_branch_param_nocontract_never_verifies() {
    assert_never_verifies("mnv_p6_branch_param_nocontract");
}

#[test]
fn probe_p6b_branch_param_contracted_never_verifies() {
    assert_never_verifies("mnv_p6b_branch_param_contracted");
}

#[test]
fn probe_p6c_both_arms_param_never_verifies() {
    assert_never_verifies("mnv_p6c_both_arms_param");
}

#[test]
fn probe_p7_nested_block_never_verifies() {
    assert_never_verifies("mnv_p7_nested_block");
}

#[test]
fn probe_p7b_nested_block_param_never_verifies() {
    assert_never_verifies("mnv_p7b_nested_block_param");
}

#[test]
fn probe_p8_shortcircuit_and_never_verifies() {
    assert_never_verifies("mnv_p8_shortcircuit_and");
}

#[test]
fn probe_p8b_shortcircuit_or_never_verifies() {
    assert_never_verifies("mnv_p8b_shortcircuit_or");
}

#[test]
fn probe_p13_precall_write_never_verifies() {
    assert_never_verifies("mnv_p13_precall_write");
}

#[test]
fn probe_p33_requires_against_post_never_verifies() {
    assert_never_verifies("mnv_p33_requires_against_post");
}

#[test]
fn probe_p15_cross_param_swap_never_verifies() {
    assert_never_verifies("mnv_p15_cross_param_swap");
}

#[test]
fn probe_p42_addk_requires_violated_never_verifies() {
    assert_never_verifies("mnv_p42_addk_requires_violated");
}

#[test]
fn probe_p20_match_arm_never_verifies() {
    assert_never_verifies("mnv_p20_match_arm");
}

#[test]
fn probe_p20b_match_arm_assign_never_verifies() {
    assert_never_verifies("mnv_p20b_match_arm_assign");
}

#[test]
fn probe_p38_while_cond_never_verifies() {
    assert_never_verifies("mnv_p38_while_cond");
}

#[test]
fn probe_p39_early_return_never_verifies() {
    assert_never_verifies("mnv_p39_early_return");
}

#[test]
fn probe_p35_nested_expr_call_never_verifies() {
    assert_never_verifies("mnv_p35_nested_expr_call");
}

#[test]
fn probe_p50_chain_requires_stale_pre_never_verifies() {
    assert_never_verifies("mnv_p50_chain_requires_stale_pre");
}

// ---- completeness pins (no over-rejection) ----

#[test]
fn probe_ok_p15b_cross_param_swap_verified() {
    assert_verified("ok_p15b_cross_param_swap_verified");
}

#[test]
fn probe_ok_p42b_addk_verified() {
    assert_verified("ok_p42b_addk_verified");
}

#[test]
fn bare_loop_family_never_false_verifies() {
    // The q-series recheck holes: post-loop stale reads of a loop-written
    // declared param must never verify.
    assert_never_verifies("q1_loop_body_call_param");
    assert_never_verifies("q3_loop_body_assign_param");
    assert_never_verifies("q4_loop_body_nocontract_param");
}
