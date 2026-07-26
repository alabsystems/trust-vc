// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice-C REMEDIATION battery: control-flow deref-write region havoc + loop
//! gate + alias-shadow nearest-resolution filter.
//!
//! BLOCKER 1 (control-flow deref-write drop). Deref writes are EXCLUDED from
//! `ExternalAssignmentCollector::external_assignments` (the deliberate #83
//! deref-aliasing skip), so a write through a dereference inside an
//! `if`/`match` arm, a loop body, a closure body, or a nested `{ .. }` block
//! was silently ROLLED BACK by the region's snapshot-restore and never
//! join-havocked — a post-join assert then read the PRE-region value and
//! proved wrong facts (six distinct false-`Verified` constructions, three
//! false on EVERY execution path). The same drop was ALREADY reachable on
//! base 2fdd181 with a SINGLE first write (branch, explicit-RMW branch,
//! unconditional block, and called-closure constructions all probed firsthand
//! as false-`Verified` ON BASE), so this remediation is a strict soundness
//! improvement over base, not just a rollback of slice C's exposure.
//!
//! REMEDIATION SHIPPED (two mechanisms):
//! 1. REGION HAVOC for `if`/`else`, `match` (one region per whole arm
//!    sweep), nested blocks, value-path block evaluation, and closure
//!    bodies: in-region writes keep EXACT SSA semantics (a write + assert
//!    inside one branch is modeled precisely — the manifest-pinned
//!    mut_refs.rs control-flow ports stay `verified`), and at region exit
//!    every deref-written ROOT is havocked to a fresh unconstrained symbol
//!    (its aliases invalidated), so no post-region read can see the reverted
//!    state. Havoc is one-directional: it can only LOSE provability, never
//!    prove wrong facts — post-region reads become genuine counterexamples.
//! 2. FAIL-CLOSED GATE for loop bodies/conditions (every form) and
//!    calc!/assert-by proof blocks, with the VERBATIM pre-existing rejection
//!    ("assignment through a dereferenced reference is unsupported"): the
//!    loop SSA rebind would prove first-iteration facts for every iteration
//!    (deref roots are excluded from the loop havoc maps), so no sound
//!    model exists short of full loop-havoc integration.
//!
//! BLOCKER 2 (alias shadow retarget, adversarial p8). The slice-C repin loop
//! collected alias NAMES across ALL frames (`erased_mut_ref_aliases_targeting`)
//! and updated/repinned at each name's NEAREST value-binding frame — so a
//! write to `*x` forcibly retargeted an inner SHADOW alias of the same name
//! that pointed at a DIFFERENT root: `let r = &mut *x; { let r = &mut *y;
//! *x = 7; *r = 9; assert!(*x == 9); }` compiled clean, PANICKED at runtime
//! (actual x == 7), and slice C said `Verified` — inverting base's correct
//! CE / V / V verdicts. REMEDIATION: the nearest-resolution filter
//! (`erased_mut_ref_targets_aliases`) — only names whose nearest resolution
//! actually targets the written root are updated/repinned; shadowed names
//! keep their own meaning. The p8 family below pins the BASE verdicts
//! restored exactly: false assert => Counterexample, both truths => Verified.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---------- adversarial construction 1: compound in a branch ----------
#[trust_vc::requires(x == 5u64)]
fn c1_if_compound_false(x: &mut u64, c: bool) {
    if c {
        *x += 1u64;
    }
    trust_vc::assert!(*x == 5u64);
}

// c-dependent fact (false for c == false): genuinely a counterexample.
#[trust_vc::requires(x == 5u64)]
fn c1_if_compound_true_twin(x: &mut u64, c: bool) {
    if c {
        *x += 1u64;
    }
    trust_vc::assert!(*x == 6u64);
}

// ---------- construction 2: sequential write, second in a branch ----------
fn c2_seq_then_branch_write(x: &mut u64, c: bool) {
    *x = 10u64;
    if c {
        *x = 11u64;
    }
    trust_vc::assert!(*x == 10u64);
}

// ---------- construction 3: compound in BOTH arms (false on every path) ----------
#[trust_vc::requires(x == 5u64)]
fn c3_if_else_both_arms(x: &mut u64, c: bool) {
    if c {
        *x += 1u64;
    } else {
        *x += 1u64;
    }
    trust_vc::assert!(*x == 5u64);
}

// ---------- construction 4: match arms (false on every path) ----------
#[trust_vc::requires(x == 5u64)]
fn c4_match_arms(x: &mut u64, c: bool) {
    match c {
        true => {
            *x += 1u64;
        }
        false => {
            *x += 1u64;
        }
    }
    trust_vc::assert!(*x == 5u64);
}

// A bare-expression match arm (no braces) must be covered the same way.
#[trust_vc::requires(x == 5u64)]
fn c4_match_bare_arm(x: &mut u64, c: bool) {
    match c {
        true => *x += 1u64,
        false => (),
    }
    trust_vc::assert!(*x == 5u64);
}

// ---------- construction 5: COMPOUND in a loop body (GATED — fail-closed) ----------
// The compound desugar's SSA read inside a loop would be the previous
// VISIT's value, not the previous ITERATION's — kept at the verbatim
// pre-existing rejection (base behavior).
#[trust_vc::requires(x == 0u64)]
fn c5_while_loop(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x += 1u64;
        i += 1u64;
    }
    trust_vc::assert!(*x == 0u64);
}

// for-loop form of the same gate.
#[trust_vc::requires(x == 0u64)]
fn c5_for_loop(x: &mut u64) {
    for _i in 0..3u64 {
        *x += 1u64;
    }
    trust_vc::assert!(*x == 0u64);
}

// Sequential (second) deref write in a loop body: the slice-C repin stays
// off in loops, so the emergent once-only shadow rejects it (base parity).
#[trust_vc::requires(x == 0u64)]
fn c5_sequential_in_loop(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 1u64;
        *x = 2u64;
        i += 1u64;
    }
    trust_vc::assert!(*x == 0u64);
}

// PLAIN single deref write in a loop body + post-loop stale read: base
// accepted the write and dropped it at the join (false-Verified for n > 0);
// the loop-exit havoc closes it — both directions non-Verified.
#[trust_vc::requires(x == 5u64)]
fn c5_plain_write_post_loop_stale(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 7u64;
        i += 1u64;
    }
    trust_vc::assert!(*x == 5u64);
}

#[trust_vc::requires(x == 5u64)]
fn c5_plain_write_post_loop_written(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 7u64;
        i += 1u64;
    }
    trust_vc::assert!(*x == 7u64);
}

// PLAIN single write + assert INSIDE the loop body: base parity (the ported
// mut_refs_loops control_flow_loops shape) — per-iteration value-numbering
// is exact for a single write, so this stays Verified.
#[trust_vc::requires(x == 5u64)]
fn c5_plain_write_in_loop_assert(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 20u64;
        trust_vc::assert!(*x == 20u64);
        i += 1u64;
    }
}

#[trust_vc::requires(x == 5u64)]
fn c5_plain_write_in_loop_assert_wrong(x: &mut u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        *x = 20u64;
        trust_vc::assert!(*x == 21u64);
        i += 1u64;
    }
}

// ---------- construction 6: unconditional nested block (false on every path) ----------
fn c6_nested_block_false(x: &mut u64) {
    *x = 10u64;
    {
        *x += 1u64;
    }
    trust_vc::assert!(*x == 10u64);
}

// TRUE twin: `*x == 11` holds on every execution, but the region-exit havoc
// forgets the value — a Counterexample, the documented sound incompleteness
// (never a false `Verified`; base gave CE here too, from the dropped write).
fn c6_nested_block_true_twin(x: &mut u64) {
    *x = 10u64;
    {
        *x += 1u64;
    }
    trust_vc::assert!(*x == 11u64);
}

// ---------- nested-region propagation (the outer restore reverts the inner havoc) ----------

// The inner `if`'s exit havoc happens INSIDE the outer then-branch and is
// itself reverted by the OUTER join's snapshot-restore — the roots must
// propagate so the outer exit re-havocs, or this would false-Verify.
#[trust_vc::requires(x == 5u64)]
fn nested_if_in_if(x: &mut u64, a: bool, b: bool) {
    if a {
        if b {
            *x = 1u64;
        }
    }
    trust_vc::assert!(*x == 5u64);
}

// `else if` is a RECURSIVE `visit_expr_if` inside the outer else arm — same
// propagation channel.
#[trust_vc::requires(x == 5u64)]
fn else_if_write(x: &mut u64, a: bool, b: bool) {
    if a {
    } else if b {
        *x = 1u64;
    }
    trust_vc::assert!(*x == 5u64);
}

// Nested block inside a branch (block region propagates into the if region).
#[trust_vc::requires(x == 5u64)]
fn block_in_branch(x: &mut u64, a: bool) {
    if a {
        {
            *x = 1u64;
        }
    }
    trust_vc::assert!(*x == 5u64);
}

// ---------- PRE-EXISTING BASE HOLES (probed firsthand as false-Verified on 2fdd181) ----------

// Single FIRST write in a branch, post-join stale read: base accepted the
// write, dropped it at the join, and false-`Verified` this for c == true.
#[trust_vc::requires(x == 5u64)]
fn base_hole_single_branch_write(x: &mut u64, c: bool) {
    if c {
        *x = 7u64;
    }
    trust_vc::assert!(*x == 5u64);
}

// Explicit-spelling sibling of construction 1 (also false-Verified on base).
#[trust_vc::requires(x == 5u64)]
fn base_hole_explicit_branch_rmw(x: &mut u64, c: bool) {
    if c {
        *x = *x + 1u64;
    }
    trust_vc::assert!(*x == 5u64);
}

// Single first write inside an unconditional nested block + post-block stale
// read: false on EVERY execution (x == 7 at the assert), Verified on base.
#[trust_vc::requires(x == 5u64)]
fn base_hole_block_single_write(x: &mut u64) {
    {
        *x = 7u64;
    }
    trust_vc::assert!(*x == 5u64);
}

// Closure-body deref write, closure CALLED, post-call stale read: false at
// runtime (x == 7), Verified on base — the #83 skip also excluded the deref
// root from the capture-mutation havoc.
#[trust_vc::requires(x == 5u64)]
fn base_hole_closure_write(x: &mut u64) {
    let mut f = || {
        *x = 7u64;
    };
    f();
    trust_vc::assert!(*x == 5u64);
}

// ---------- post-region observation channels (all must fail closed) ----------

// Read through an ALIAS after a branch write to the root: the alias's scoped
// value is a stale in-region snapshot — it is invalidated at the region exit,
// so this must never verify against entry (5) NOR against the branch value.
#[trust_vc::requires(x == 5u64)]
fn post_join_alias_read_stale(x: &mut u64, c: bool) {
    let r = &mut *x;
    if c {
        *x = 7u64;
    }
    trust_vc::assert!(*r == 5u64);
}

// Contract-side channel: the callee-side ensures resolver must not see a
// clean final after a branch write (the final is the havoc symbol,
// unconstrained — the false relation can never prove).
#[trust_vc::requires(*old(x) == 5u64)]
#[trust_vc::ensures(*x == *old(x))]
fn post_join_ensures_stale(x: &mut u64, c: bool) {
    if c {
        *x = 7u64;
    }
}

// ---------- in-region semantics stay EXACT (the manifest-pinned capability) ----------

// The ported mut_refs.rs control-flow shape: write + assert inside each
// branch, nothing observed after the join — stays Verified.
#[trust_vc::requires(x == 5u64)]
fn in_branch_write_and_assert_verified(x: &mut u64, c: bool) {
    if c {
        *x = 20u64;
        trust_vc::assert!(*x == 20u64);
    } else {
        *x = 30u64;
        trust_vc::assert!(*x == 30u64);
    }
}

// Its wrong-value tripwire: the in-branch SSA must be exact, not havocked.
#[trust_vc::requires(x == 5u64)]
fn in_branch_write_wrong_value_counterexample(x: &mut u64, c: bool) {
    if c {
        *x = 20u64;
        trust_vc::assert!(*x == 21u64);
    }
}

// Straight-line write AFTER a branch write re-establishes exact tracking
// (the root's fresh havoc symbol is simply rebound by the next write).
#[trust_vc::requires(x == 5u64)]
fn post_join_rewrite_recovers(x: &mut u64, c: bool) {
    if c {
        *x = 7u64;
    }
    *x = 3u64;
    trust_vc::assert!(*x == 3u64);
}

#[trust_vc::requires(x == 5u64)]
fn post_join_rewrite_recovers_wrong(x: &mut u64, c: bool) {
    if c {
        *x = 7u64;
    }
    *x = 3u64;
    trust_vc::assert!(*x == 5u64);
}

// ---------- adversarial p8 family: alias shadow retarget ----------
// Compiles clean; at runtime x == 7 and y == 9, and the false variant
// PANICS. Slice C said Verified / CE / CE (inverted); the nearest-resolution
// filter restores the BASE verdicts: CE / Verified / Verified.
fn p8_false_assert(x: &mut u64, y: &mut u64) {
    let r = &mut *x;
    {
        let r = &mut *y;
        *x = 7u64;
        *r = 9u64;
        trust_vc::assert!(*x == 9u64);
    }
    let _ = r;
}

fn p8_truth_x(x: &mut u64, y: &mut u64) {
    let r = &mut *x;
    {
        let r = &mut *y;
        *x = 7u64;
        *r = 9u64;
        trust_vc::assert!(*x == 7u64);
    }
    let _ = r;
}

fn p8_truth_y(x: &mut u64, y: &mut u64) {
    let r = &mut *x;
    {
        let r = &mut *y;
        *x = 7u64;
        *r = 9u64;
        trust_vc::assert!(*y == 9u64);
    }
    let _ = r;
}

// Compound spelling through the shadow: `*r += 2` adds to Y (the shadow's
// root), so `*x == 9` is false (x == 7) — must never verify. (Base rejected
// the compound spelling outright; correct modeling is strictly better.)
fn p8_compound_shadow(x: &mut u64, y: &mut u64) {
    let r = &mut *x;
    {
        let r = &mut *y;
        *x = 7u64;
        *r += 2u64;
        trust_vc::assert!(*x == 9u64);
    }
    let _ = r;
}

// ---------- straight-line capability preserved ----------
#[trust_vc::requires(x == 5u64)]
fn straight_line_chain_ok(x: &mut u64) {
    *x = 10u64;
    *x += 1u64;
    trust_vc::assert!(*x == 11u64);
}

#[trust_vc::requires(x == 5u64)]
fn straight_line_chain_stale(x: &mut u64) {
    *x = 10u64;
    *x += 1u64;
    trust_vc::assert!(*x == 6u64);
}

// Same-frame re-let of an alias name (no cross-frame shadow): the second
// `let r` overwrites the first in the SAME frame; writes through `r` go to
// `y` and `x` keeps its own value.
#[trust_vc::requires(x == 1u64)]
#[trust_vc::requires(y == 2u64)]
fn straight_line_same_frame_relet(x: &mut u64, y: &mut u64) {
    let r = &mut *x;
    *r = 5u64;
    let r = &mut *y;
    *r = 6u64;
    trust_vc::assert!(*x == 5u64);
    trust_vc::assert!(*y == 6u64);
}

#[trust_vc::requires(x == 1u64)]
#[trust_vc::requires(y == 2u64)]
fn straight_line_same_frame_relet_wrong(x: &mut u64, y: &mut u64) {
    let r = &mut *x;
    *r = 5u64;
    let r = &mut *y;
    *r = 6u64;
    trust_vc::assert!(*x == 6u64);
}
// ---------- unsafe/async block channels (recheck u1/u8) ----------
// ExprUnsafe had no visitor override: a first deref write inside `unsafe {}`
// was silently dropped (false-VERIFIED stale post-read). Unsafe executes
// inline -> exact ExprBlock treatment (region + exit havoc; post-block reads
// havoc both directions, the documented nested-block incompleteness).
// Async/try/const blocks have non-inline execution -> deref writes inside
// them fail closed.

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn u1_unsafe_write_stale_read(x: &mut u64) {
    unsafe {
        *x = 7u64;
    }
    trust_vc::assert!(*x == 5u64);
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn u1_unsafe_write_true_twin(x: &mut u64) {
    unsafe {
        *x = 7u64;
    }
    trust_vc::assert!(*x == 7u64);
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn u8_unsafe_alias_write_stale_read(x: &mut u64) {
    let r = &mut *x;
    unsafe {
        *r = 7u64;
    }
    trust_vc::assert!(*x == 5u64);
}

#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn u9_async_block_deref_write(x: &mut u64) {
    let _fut = async {
        *x = 7u64;
    };
    trust_vc::assert!(*x == 5u64);
}


"####;

fn run(func: &str) -> VerifyResult {
    // The on-disk VC-result cache stores only `verified` verdicts and replays
    // them without re-encoding — it MUST be disabled for true verdicts.
    // Serialized behind the process-wide env lock and restored on scope exit
    // (guards drop before the lock releases) via the workspace env choke point.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir = std::env::temp_dir().join("trust_vc_mut_ref_control_flow_gate");
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

// The pre-existing deref-write rejection, kept VERBATIM by the loop gate.
const DEREF_HARD_ERROR: &str = "assignment through a dereferenced reference is unsupported";

fn assert_verified(func: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must verify (in-region/straight-line capability preserved), got: {r:?}"
    );
}

fn assert_counterexample(func: &str) {
    let r = run(func);
    assert!(
        r.is_counterexample(),
        "{func} must be a Counterexample (NEVER Verified), got: {r:?}"
    );
}

fn assert_gated(func: &str) {
    let r = run(func);
    let VerifyResult::Error { message } = &r else {
        panic!("{func} must fail closed with the loop deref-write gate Error, got: {r:?}");
    };
    assert!(
        message.contains(DEREF_HARD_ERROR),
        "{func} error must be the verbatim pre-existing deref rejection, got: {message}"
    );
}

/// Any non-`Verified` outcome is acceptable; `Verified` is the catastrophic
/// false positive this battery exists to prevent.
fn assert_never_verifies(func: &str) {
    let r = run(func);
    assert!(
        !r.is_verified(),
        "{func} must NEVER verify (post-region observation of a reverted write), got: {r:?}"
    );
}

// ---- the six adversarial false-VERIFIED constructions ----

#[test]
fn c1_if_compound_both_directions() {
    // post-join read of a branch-written root: havocked — both directions
    // are genuine counterexamples (the fact is c-dependent either way).
    assert_counterexample("c1_if_compound_false");
    assert_counterexample("c1_if_compound_true_twin");
}

#[test]
fn c2_sequential_then_branch_write() {
    assert_counterexample("c2_seq_then_branch_write");
}

#[test]
fn c3_if_else_both_arms() {
    assert_counterexample("c3_if_else_both_arms");
}

#[test]
fn c4_match_arms() {
    assert_counterexample("c4_match_arms");
    assert_counterexample("c4_match_bare_arm");
}

#[test]
fn c5_loops_compound_gated() {
    assert_gated("c5_while_loop");
    assert_gated("c5_for_loop");
}

#[test]
fn c5_loops_sequential_gated() {
    assert_gated("c5_sequential_in_loop");
}

#[test]
fn c5_loops_plain_write_post_loop_havocked() {
    // The base stale-post-loop-read hole, closed by the loop-exit havoc.
    assert_never_verifies("c5_plain_write_post_loop_stale");
    // The written-value fact is also forgotten (havoc) — sound
    // incompleteness, never a false Verified.
    assert_never_verifies("c5_plain_write_post_loop_written");
}

#[test]
fn c5_loops_plain_write_in_loop_base_parity() {
    // The manifest-pinned loops capability: single write + assert inside the
    // body stays exact (both directions).
    assert_verified("c5_plain_write_in_loop_assert");
    assert_counterexample("c5_plain_write_in_loop_assert_wrong");
}

#[test]
fn c6_nested_block_both_directions() {
    assert_counterexample("c6_nested_block_false");
    // Sound incompleteness: the true fact is forgotten by the exit havoc —
    // CE, never a false Verified (base also gave CE here).
    assert_counterexample("c6_nested_block_true_twin");
}

// ---- nested-region propagation tripwires ----

#[test]
fn nested_regions_propagate_havoc() {
    assert_never_verifies("nested_if_in_if");
    assert_never_verifies("else_if_write");
    assert_never_verifies("block_in_branch");
}

// ---- pre-existing base holes, now closed (strict improvement over base) ----

#[test]
fn base_hole_single_branch_write_closed() {
    assert_counterexample("base_hole_single_branch_write");
}

#[test]
fn base_hole_explicit_branch_rmw_closed() {
    assert_counterexample("base_hole_explicit_branch_rmw");
}

#[test]
fn base_hole_block_single_write_closed() {
    assert_counterexample("base_hole_block_single_write");
}

#[test]
fn base_hole_closure_write_closed() {
    assert_never_verifies("base_hole_closure_write");
}

// ---- post-region observation channels ----

#[test]
fn post_join_alias_read_never_stale() {
    assert_never_verifies("post_join_alias_read_stale");
}

#[test]
fn post_join_ensures_never_stale() {
    assert_never_verifies("post_join_ensures_stale");
}

// ---- in-region semantics stay exact (manifest-pinned capability) ----

#[test]
fn in_branch_write_and_assert_still_verifies() {
    assert_verified("in_branch_write_and_assert_verified");
    assert_counterexample("in_branch_write_wrong_value_counterexample");
}

#[test]
fn post_join_rewrite_recovers_exact_tracking() {
    assert_verified("post_join_rewrite_recovers");
    assert_counterexample("post_join_rewrite_recovers_wrong");
}

// ---- adversarial p8 family: base verdicts restored exactly ----

#[test]
fn p8_family_matches_base() {
    assert_counterexample("p8_false_assert");
    assert_verified("p8_truth_x");
    assert_verified("p8_truth_y");
    assert_never_verifies("p8_compound_shadow");
}

// ---- straight-line capability preserved ----

#[test]
fn straight_line_still_works() {
    assert_verified("straight_line_chain_ok");
    assert_counterexample("straight_line_chain_stale");
}

#[test]
fn straight_line_same_frame_relet_still_works() {
    assert_verified("straight_line_same_frame_relet");
    assert_counterexample("straight_line_same_frame_relet_wrong");
}

#[test]
fn unsafe_block_write_channels_closed() {
    // Stale post-unsafe read must never verify (was false-VERIFIED before the
    // ExprUnsafe override); both directions havoc — never a false verify.
    assert_counterexample("u1_unsafe_write_stale_read");
    assert_never_verifies("u1_unsafe_write_true_twin");
    assert_never_verifies("u8_unsafe_alias_write_stale_read");
}

#[test]
fn async_block_deref_write_fails_closed() {
    assert_gated("u9_async_block_deref_write");
}
