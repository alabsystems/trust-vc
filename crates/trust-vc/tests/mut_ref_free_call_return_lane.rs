// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A `&mut` ARGUMENT passed to a FREE FUNCTION must not be a no-op in the
//! RETURN-VALUE lane.
//!
//! `4ee6d1d4` closed the return lane for a call through a mutable RECEIVER
//! (`t.bump()`). The identical mutation ONE HOP AWAY — through a free function
//! taking `&mut` — was still dropped:
//!
//!     pub struct C { pub n: u64 }
//!     pub fn bump(c: &mut C) { c.n = c.n + 1; }
//!     #[requires(t.n == 0)] #[ensures(result == 0)]
//!     pub fn g(t: &mut C) -> u64 { bump(t); t.n }        // reported `verified`
//!
//! It is FALSE — `bump` increments, so `g` returns 1 — and the very same body
//! written with the read as an `assert!` was already refuted:
//!
//!     #[requires(t.n == 0)] pub fn g(t: &mut C) { bump(t); assert!(t.n == 0); }
//!
//! That asymmetry is the discriminator, and it is pinned below (`*_control_*`).
//! No trait, no generic, no `impl Trait` is involved in the smallest witness.
//!
//! MECHANISM — the SAME root shape as `4ee6d1d4`, one field further on. The
//! return-value render runs on its own `AssertionCollector` over a throwaway
//! `VerificationContext`. `4ee6d1d4` seeded that CONTEXT (declared variables,
//! receiver-kind registries, function context, trait decls) and left the
//! COLLECTOR at `AssertionCollector::new(..)` defaults — so `mut_ref_call_args`,
//! the callee-signature map that is the SOLE enable of
//! `havoc_mut_ref_call_arg_referents` (it opens with
//! `if self.mut_ref_call_args.is_empty() { return }`), stayed empty and the
//! free-call havoc never fired in the return lane. The in-body lane had it; the
//! return lane did not; the two lanes decided one program differently.
//!
//! The fix is not another ad-hoc seed. Both lanes now install ONE
//! `body_extract::CollectorLaneSeed`, constructed by exhaustive struct literal
//! and consumed by exhaustive destructures in `apply_lane_seed` and
//! `return_lane_view`, so a future seeded field is a COMPILE ERROR until someone
//! decides in writing which lanes get it. There is exactly ONE deliberate
//! difference between the lanes (`supported_mut_ref_param_targets`, withheld
//! from the return lane because it changes deref ERASURE rather than framing,
//! and because granting it cost a fail-closed rejection —
//! `mut_refs_old_rs_snapshot_boundaries_fail_closed_from_file`), and it is
//! written down there rather than left implicit at a call site. That type's doc
//! comment carries the per-field audit of everything `AssertionCollector::new`
//! still leaves defaulted and why the return lane does not need it (in short:
//! the three contract maps only ever ADD facts, so their absence is an
//! over-rejection; the index/solver-mode fields name obligations this throwaway
//! lane discards; everything else is per-visit working state whose correct
//! initial value IS the default).
//!
//! AXES. A shape is not an axis. The false verify keys on (a) the callee being a
//! FREE function rather than a method, (b) the `&mut` position coming from the
//! callee SIGNATURE, and (c) the mutated binding being READ BY THE RETURNED
//! VALUE. Each test below varies one of those independently: argument position
//! (first / second / both), a module-qualified callee, a callee that only
//! mutates via a further hop, a mutation inside a loop body, a free call mixed
//! with a method call, and a multi-path (`if`/`else`) return where only one
//! branch is reached after the mutation.
//!
//! NARROWNESS PINS — the fix must not be bought with blanket rejection:
//!
//! * `shared_ref_argument_*` — a `&`-only parameter is spelled IDENTICALLY at
//!   the call site (`f(t)`), and must NOT havoc. This is the whole reason the
//!   havoc is keyed on the callee signature rather than on syntax; without these
//!   pins the "fix" would be `havoc everything passed to anything`.
//! * `mutation_of_an_unread_binding_costs_nothing` — mutating a binding the
//!   returned value does not read must stay free.
//! * `*_still_verifies` — a TRUE claim over post-mutation state must still be
//!   provable. The render models the post-call binding as ARBITRARY, not as
//!   unmodelable, so a fact that holds of EVERY post-state (here: a trait
//!   `ensures`) survives the havoc. `4ee6d1d4`'s author rejected a first draft
//!   that DECLINED instead; do not regress that.
//! * `a_pure_sibling_helper_keeps_its_body_axiom` /
//!   `a_pure_inherent_method_keeps_its_body_axiom` /
//!   `a_declared_mut_self_method_costs_nothing_to_a_helper_that_never_calls_it`
//!   — the two body-axiom publisher gates are keyed on the body's own CALL
//!   SITES, not on the file. A body that only reads keeps its axiom, and merely
//!   DECLARING a mutator somewhere in the file costs a non-calling body nothing.
//!   All three fail for the blunt "drop every body axiom" implementation, which
//!   would otherwise pass every cardinal probe in this file.

use trust_vc_core::{verify_function_from_file, VerifyResult};

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_mutref_freecall_{label}_{}_{}.rs",
        std::process::id(),
        FIXTURE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).expect("write mut-ref free-call fixture");
    path
}

fn verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result =
        verify_function_from_file(path_str, "g").unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

/// A claim that does NOT follow must be REFUTED, and refuted for a reason that
/// means the pipeline actually ran. `Counterexample` (a model), `NotProved` and
/// `Unknown` all count. `Verified` is the cardinal failure. A bare `Error` is
/// excluded on purpose: a fixture that never reached the solver would otherwise
/// satisfy every pin in this file vacuously.
fn assert_rejected(label: &str, source: &str) {
    let result = verdict(label, source);
    match result {
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE VERIFY — a `&mut` argument to a free function \
             was treated as a no-op on the caller's binding in the RETURN lane"
        ),
        other => panic!(
            "{label}: expected a refutation, got {other:?}. An `Error` here means the \
             fixture never reached the solver, so the pin proves nothing."
        ),
    }
}

fn assert_verified(label: &str, source: &str) {
    let result = verdict(label, source);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label}: a TRUE claim must still verify — this is the narrowness pin \
         keeping the fix from being a blanket rejection; got: {result:?}"
    );
}

/// A concrete struct and a contract-less free mutator. Every real execution of
/// `bump` increments, so any claim that the caller's binding is unchanged is
/// false. NOTHING here is generic and no trait exists in the file — this is not
/// a trait-lane defect.
const C_AND_BUMP: &str = "
pub struct C { pub n: u64 }
pub fn bump(c: &mut C) { c.n = c.n + 1; }
";

// ---------------------------------------------------------------------------
// The cardinal witness and its discriminator.
// ---------------------------------------------------------------------------

#[test]
fn free_fn_mut_ref_argument_mutation_reaches_the_return_value() {
    assert_rejected(
        "free_fn_basic",
        &format!(
            "{C_AND_BUMP}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 {{ bump(t); t.n }}
"
        ),
    );
}

/// The SAME body with the post-mutation read written as an `assert!`. Already
/// correct before the fix — this is what identifies the return lane, and not the
/// free-call framing as a whole, as the leak.
#[test]
fn free_fn_mut_ref_argument_control_via_assert() {
    assert_rejected(
        "free_fn_control_assert",
        &format!(
            "{C_AND_BUMP}
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) {{ bump(t); assert!(t.n == 0); }}
"
        ),
    );
}

// ---------------------------------------------------------------------------
// AXIS: which argument position carries the `&mut`. The havoc is driven by the
// callee signature positionally, so a `&mut` in a NON-FIRST slot — next to a
// `&`-shared slot that must be left alone — is a genuinely different code path
// from the one-argument case.
// ---------------------------------------------------------------------------

#[test]
fn mut_ref_in_the_second_argument_position_reaches_the_return_value() {
    assert_rejected(
        "second_position",
        "
pub struct C { pub n: u64 }
pub fn bump_snd(a: &C, b: &mut C) { b.n = b.n + a.n + 1; }
#[trust_vc::requires(t.n == 0)]
#[trust_vc::requires(u.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C, u: &mut C) -> u64 { bump_snd(t, u); u.n }
",
    );
}

#[test]
fn two_mut_ref_arguments_both_reach_the_return_value() {
    assert_rejected(
        "two_mut_args",
        "
pub struct C { pub n: u64 }
pub fn bump2(a: &mut C, b: &mut C) { a.n = a.n + 1; b.n = b.n + 1; }
#[trust_vc::requires(t.n == 0)]
#[trust_vc::requires(u.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C, u: &mut C) -> u64 { bump2(t, u); t.n + u.n }
",
    );
}

// ---------------------------------------------------------------------------
// AXIS: how the callee is SPELLED and where it lives. The seed is keyed by
// `call_function_symbol`, so a module-qualified path is a different key than a
// bare ident.
// ---------------------------------------------------------------------------

#[test]
fn module_qualified_free_fn_mut_ref_argument_reaches_the_return_value() {
    assert_rejected(
        "module_qualified",
        "
pub struct C { pub n: u64 }
pub mod m { pub fn bump(c: &mut crate::C) { c.n = c.n + 1; } }
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 { m::bump(t); t.n }
",
    );
}

/// The mutation is TWO HOPS from `g`: the called function does not write the
/// field itself, it forwards the `&mut` on. `g` sees only `outer`'s signature,
/// which is exactly the information the fix keys on.
#[test]
fn mutation_two_hops_deep_reaches_the_return_value() {
    assert_rejected(
        "two_hops",
        "
pub struct C { pub n: u64 }
pub fn inner(c: &mut C) { c.n = c.n + 1; }
pub fn outer(c: &mut C) { inner(c); }
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 { outer(t); t.n }
",
    );
}

/// UFCS spelling of an inherent `&mut self` method — a `Call`, not a
/// `MethodCall`, so it travels the free-call path rather than the receiver path
/// that `4ee6d1d4` fixed.
#[test]
fn ufcs_inherent_mut_self_call_reaches_the_return_value() {
    assert_rejected(
        "ufcs_inherent",
        "
pub struct C { pub n: u64 }
impl C { pub fn bump(&mut self) { self.n = self.n + 1; } }
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 { C::bump(t); t.n }
",
    );
}

// ---------------------------------------------------------------------------
// AXIS: where the call SITS. Straight line, inside a loop body, and alongside a
// receiver-form mutation of a different binding.
// ---------------------------------------------------------------------------

#[test]
fn mut_ref_argument_in_a_loop_body_reaches_the_return_value() {
    assert_rejected(
        "in_loop",
        &format!(
            "{C_AND_BUMP}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 {{
    let mut i = 0u64;
    while i < 3u64 {{ bump(t); i = i + 1u64; }}
    t.n
}}
"
        ),
    );
}

/// A free `&mut` call and a `&mut self` METHOD call in one body, on two
/// different bindings. `4ee6d1d4` framed the method; this pins that framing the
/// method does not accidentally stand in for framing the free call.
#[test]
fn free_call_alongside_a_mut_receiver_method_call() {
    assert_rejected(
        "alongside_method",
        "
pub struct C { pub n: u64 }
impl C { pub fn tick(&mut self) { self.n = self.n + 1; } }
pub fn bump(c: &mut C) { c.n = c.n + 1; }
#[trust_vc::requires(t.n == 0)]
#[trust_vc::requires(u.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C, u: &mut C) -> u64 { u.tick(); bump(t); t.n }
",
    );
}

/// A MULTI-PATH return. Each branch renders on its own throwaway collector, so
/// each one has to be seeded; a fix that seeded only the single-return arm would
/// pass every test above and fail here.
#[test]
fn multi_path_return_after_a_mut_ref_call_is_framed_on_every_branch() {
    assert_rejected(
        "multi_path_return",
        &format!(
            "{C_AND_BUMP}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C, k: bool) -> u64 {{
    bump(t);
    if k {{ return t.n; }}
    t.n
}}
"
        ),
    );
}

/// The mutation happens through a FIELD projection argument (`&mut o.c`) rather
/// than a bare binding, and the returned value reads back through the same
/// projection. Only the ROOT is havoced, which is what has to be enough here.
#[test]
fn field_projection_mut_ref_argument_reaches_the_return_value() {
    assert_rejected(
        "field_projection",
        "
pub struct C { pub n: u64 }
pub struct O { pub c: C }
pub fn bump(c: &mut C) { c.n = c.n + 1; }
#[trust_vc::requires(o.c.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(o: &mut O) -> u64 { bump(&mut o.c); o.c.n }
",
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS. A `&`-shared argument is spelled identically at the call site and
// must NOT be havoced — the callee signature is the only thing that tells the
// two apart, and these are the pins that keep it that way.
// ---------------------------------------------------------------------------

#[test]
fn shared_ref_argument_does_not_havoc_the_return_value() {
    assert_verified(
        "shared_ref_arg",
        "
pub struct C { pub n: u64 }
pub fn read(c: &C) -> u64 { c.n }
#[trust_vc::requires(t.n == 3)]
#[trust_vc::ensures(result == 3)]
pub fn g(t: &mut C) -> u64 { let _r = read(t); t.n }
",
    );
}

/// Two reads bracketing a `&`-only call must still collapse to one term, so a
/// difference of `0` remains provable. This is the strictly stronger form of the
/// pin above: it fails for any implementation that havocs on call syntax.
#[test]
fn reads_bracketing_a_shared_ref_call_still_collapse() {
    assert_verified(
        "shared_ref_bracketing",
        "
pub struct C { pub n: u64 }
pub fn read(c: &C) -> u64 { c.n }
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 { let a = t.n; let _z = read(t); let b = t.n; b - a }
",
    );
}

#[test]
fn a_call_with_no_reference_parameters_at_all_still_verifies() {
    assert_verified(
        "by_value_call",
        "
pub struct C { pub n: u64 }
pub fn twice(c: &C) -> u64 { c.n + c.n }
#[trust_vc::requires(t.n == 2)]
#[trust_vc::ensures(result == 4)]
pub fn g(t: &C) -> u64 { twice(t) }
",
    );
}

#[test]
fn mutation_of_an_unread_binding_costs_nothing() {
    assert_verified(
        "unread_binding",
        &format!(
            "{C_AND_BUMP}
#[trust_vc::requires(k == 7)]
#[trust_vc::ensures(result == 7)]
pub fn g(t: &mut C, k: u64) -> u64 {{ bump(t); k }}
"
        ),
    );
}

/// THE anti-blanket-rejection pin. After the free `&mut` call the receiver's
/// state is ARBITRARY — not unmodelable — so a fact that holds of EVERY state a
/// `Ctr` can be in (the trait's own `ensures`) must still discharge through the
/// havoc'd binding. An implementation that DECLINED the render instead of
/// reporting fresh symbols fails exactly here, and the `_liar` sibling below is
/// what stops this pin from being satisfied by simply not framing at all.
#[test]
fn a_true_claim_over_post_mutation_state_still_verifies() {
    assert_verified(
        "post_mutation_true",
        "
#[trust_vc::trait_spec]
pub trait Ctr {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}
pub fn touch<T: Ctr>(t: &mut T) { let _ = t; }
#[trust_vc::ensures(result >= 2)]
pub fn g(t: &mut impl Ctr) -> int { touch(t); t.a() }
",
    );
}

#[test]
fn the_liar_over_post_mutation_state_is_refuted() {
    assert_rejected(
        "post_mutation_liar",
        "
#[trust_vc::trait_spec]
pub trait Ctr {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}
pub fn touch<T: Ctr>(t: &mut T) { let _ = t; }
#[trust_vc::ensures(result == 2)]
pub fn g(t: &mut impl Ctr) -> int { touch(t); t.a() }
",
    );
}

// ---------------------------------------------------------------------------
// SIBLING-HELPER BODY AXIOM. The definitional-axiom lane publishes
// `name(args) == BODY` for a helper, and it renders BODY through the SAME return
// lane — but over the TARGET's context, in which the helper's own parameters are
// not declared. The free-call havoc only rebinds a root it can see as a tracked
// binding, so seeding that render does nothing here and the axiom was published
// against the ENTRY value. Unlike the caller lane there is no fresh symbol to
// fall back on (a definitional axiom's binders are fixed by the signature), so
// the axiom is DROPPED instead.
//
// Both were live cardinal false verifies, found by probing the claim that
// `CollectorLaneSeed::EMPTY` was safe here — it was not.
// ---------------------------------------------------------------------------

#[test]
fn sibling_helper_body_axiom_is_dropped_when_the_body_passes_a_mut_ref_argument() {
    assert_rejected(
        "sibling_body_axiom_free_call",
        "
pub struct C { pub n: u64 }
pub fn bump(c: &mut C) { c.n = c.n + 1; }
pub fn via(mut c: C) -> u64 { bump(&mut c); c.n }
#[trust_vc::ensures(result == 0u64)]
pub fn g() -> u64 { let c = C { n: 0 }; via(c) }
",
    );
}

/// The receiver-form sibling of the same hole: `4ee6d1d4` seeded the return
/// render's receiver-kind registries, but that machinery resolves a receiver
/// through its DECLARED type and a helper's parameters are declared nowhere this
/// render can see, so a `&mut self` call in a helper body was still a no-op.
#[test]
fn sibling_helper_body_axiom_is_dropped_when_the_body_calls_a_mut_self_method() {
    assert_rejected(
        "sibling_body_axiom_mut_self",
        "
pub struct C { pub n: u64 }
impl C { pub fn tick(&mut self) { self.n = self.n + 1; } }
pub fn via(mut c: C) -> u64 { c.tick(); c.n }
#[trust_vc::ensures(result == 0u64)]
pub fn g() -> u64 { let c = C { n: 0 }; via(c) }
",
    );
}

/// NARROWNESS for both gates above: a helper whose body only READS keeps its
/// body axiom, so a true claim about its value is still provable. Without this
/// the two gates could have been "drop every helper's axiom", which passes every
/// cardinal probe and is a capability disaster.
#[test]
fn a_pure_sibling_helper_keeps_its_body_axiom() {
    assert_verified(
        "sibling_pure_axiom",
        "
pub struct C { pub n: u64 }
pub fn read(c: &C) -> u64 { c.n }
pub fn via(c: C) -> u64 { read(&c) + 1u64 }
#[trust_vc::ensures(result == 1u64)]
pub fn g() -> u64 { let c = C { n: 0 }; via(c) }
",
    );
}

/// The INHERENT-METHOD body-axiom publisher has the identical hole:
/// `impl C { fn via(mut self) -> u64 { bump(&mut self); self.n } }` published
/// `C__via(self) == self.n` against the ENTRY `self`.
#[test]
fn inherent_method_body_axiom_is_dropped_when_the_body_passes_a_mut_ref_argument() {
    assert_rejected(
        "inherent_body_axiom_free_call",
        "
pub struct C { pub n: u64 }
pub fn bump(c: &mut C) { c.n = c.n + 1; }
impl C {
    pub fn via(mut self) -> u64 { bump(&mut self); self.n }
}
#[trust_vc::ensures(result == 0u64)]
pub fn g() -> u64 { let c = C { n: 0 }; c.via() }
",
    );
}

#[test]
fn inherent_method_body_axiom_is_dropped_when_the_body_calls_a_mut_self_method() {
    assert_rejected(
        "inherent_body_axiom_mut_self",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn tick(&mut self) { self.n = self.n + 1; }
    pub fn via(mut self) -> u64 { self.tick(); self.n }
}
#[trust_vc::ensures(result == 0u64)]
pub fn g() -> u64 { let c = C { n: 0 }; c.via() }
",
    );
}

/// NARROWNESS for the inherent gate: a method that only reads keeps its body
/// axiom, so a true claim about its value is still provable.
#[test]
fn a_pure_inherent_method_keeps_its_body_axiom() {
    assert_verified(
        "inherent_pure_axiom",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn via(self) -> u64 { self.n + 1u64 }
}
#[trust_vc::ensures(result == 1u64)]
pub fn g() -> u64 { let c = C { n: 0 }; c.via() }
",
    );
}

/// The receiver gate is keyed on the helper's own CALL SITES, not on the file.
/// A file that declares `&mut self` methods must not cost an axiom to a helper
/// that never calls one — otherwise the gate degrades into "any file with a
/// mutator loses every body axiom", which passes every cardinal probe above and
/// is exactly the capability disaster the narrowness pins exist to catch.
#[test]
fn a_declared_mut_self_method_costs_nothing_to_a_helper_that_never_calls_it() {
    assert_verified(
        "sibling_axiom_unrelated_mutator",
        "
pub struct C { pub n: u64 }
impl C {
    pub fn tick(&mut self) { self.n = self.n + 1; }
    pub fn bump(&mut self) { self.n = self.n + 2; }
}
pub fn read(c: &C) -> u64 { c.n }
pub fn via(c: C) -> u64 { read(&c) + 1u64 }
#[trust_vc::ensures(result == 1u64)]
pub fn g() -> u64 { let c = C { n: 0 }; via(c) }
",
    );
}
