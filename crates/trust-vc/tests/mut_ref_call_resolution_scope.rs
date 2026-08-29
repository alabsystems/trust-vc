// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A resolver that consults ONE syntactic scope, and a fallback that answers for
//! a render which declined.
//!
//! `7781306a` closed the free-call `&mut`-argument havoc for a bare or
//! `::`-qualified free fn called in STATEMENT POSITION at the top level of the
//! body. Seven live cardinal false verifies survived it, on legal single-file
//! Rust needing no trait bound, no generic and no `impl Trait`. They fall into
//! three groups, and every one of them is the SAME defect class: **a resolver or
//! a fallback that consults one place, finds nothing, and silently returns a
//! default that reads as "nothing to do here".**
//!
//! GROUP 1 — THE CALLEE SPELLING THE RESOLVER NEVER SAW.
//! `collect_referenced_sibling_mut_ref_call_args` took its aliases from
//! `block_use_function_aliases(&target_func.block)` — the TARGET FUNCTION'S OWN
//! BLOCK. A FILE-LEVEL `use m::bump2;` was invisible, so `bump2(t)` resolved to
//! nothing, no entry reached `mut_ref_call_args`, and the mutation was a no-op.
//! `SourceFunctionRegistry` holds free `ItemFn`s only, so `H::zap(t)` (an
//! inherent associated fn with a `&mut` parameter) was invisible too. And the
//! havoc itself is reached only from `visit_expr_call`, so `h.hit(t)` — a
//! `&mut` NON-SELF argument of an inherent or trait method — was framed by
//! nothing at all. Controls that already worked the whole time: `m::bump(t)`,
//! and an IN-BLOCK `use m::bump2 as loc; loc(t)`. The hole was purely "which
//! scope did the resolver look in".
//!
//! The fix is not three more lookups. Alias resolution now runs over
//! `CalleeAliasScopes` — function block + file top level + the enclosing inline
//! module chain — a struct built by exhaustive literal and consumed by an
//! exhaustive destructure, so a future scope is a compile error rather than a
//! silent miss. And where a spelling STILL cannot be resolved (an out-of-line
//! `mod m;`, a glob, another crate, a fn pointer, a conflicting alias), the
//! resolver reports UNKNOWN rather than an empty flag vector: an unknown callee
//! falls back to the ARGUMENT's own type, and a binding of type `&mut T` passed
//! bare is REBORROWED into the call, so whoever the callee turns out to be may
//! write through it. Presence in the map now means "resolved", which is why a
//! resolved pure reader records an all-`false` vector instead of being omitted.
//!
//! GROUP 2 — THE CONTAINER THE RETURNED EXPRESSION SAT IN. `expr_to_scoped_string`
//! falls back to re-emitting the expression VERBATIM when no arm models it, and
//! `vc_extraction::scoped_return_expression` did the same thing one level up
//! (`render.rendered.unwrap_or_else(|| extract_expr_string(return_expr))`),
//! throwing away every fail-closed decision the render had just made. For a
//! container whose nested blocks carry statement-position mutations that raw
//! rendering loses them entirely — the encoder has no statement semantics, so it
//! reads each block's tail against the ENTRY state. `if f { bump(t); t.n } else
//! { bump(t); t.n }`, `let x = { bump(t); t.n }; x` and the `match`-arm twin all
//! proved `result == 0` while every execution returns 1. Note the root itself
//! WAS havoced (`assert!(t.n == 0)` after the same `let` was correctly refuted),
//! so this was never a missing havoc — it was a value carried out of a container
//! and rendered against a state the container had already left.
//!
//! GROUP 3 — MUTATION WITHOUT A CALL. The two definitional-body-axiom publisher
//! gates added by `7781306a` have three clauses and all three are CALL-SITE
//! shaped. A bare field assignment calls nothing, so `pub fn via(mut c: C) ->
//! u64 { c.n = c.n + 1; c.n }` still published `via(c) == c.n` over the ENTRY
//! `c` — a FALSE PREMISE, which proves arbitrary goals — and the `impl C { fn
//! via(mut self) }` twin with it. The discriminator that this is an entry-pinned
//! axiom and not merely a weak one: the TRUE claim `result == 1` was REFUTED
//! while the false `result == 0` verified.
//!
//! NARROWNESS. Every fix here must fail for a blunter implementation, and the
//! `*_still_verifies` half of this file is what enforces that:
//!
//! * `shared_ref_argument_*` / `*_shared_non_self_argument_*` — a `&`-shared
//!   parameter is spelled IDENTICALLY at the call site (`f(t)`, `h.peek(t)`), so
//!   the ONLY thing separating it from a mutator is the resolved signature. Any
//!   "havoc anything passed anywhere" fix fails here. This is also why the
//!   argument-type fallback is reached only for an UNRESOLVED callee.
//! * `*_statement_prefix_that_does_not_mutate_*` — the raw-fallback rejection
//!   examines only the statements a raw rendering DROPS, and only a MUTATION
//!   counts. `if c { let y = t.n; y } else { … }` and every statement-free
//!   container keep the existing rendering. "Decline every unmodelled container"
//!   passes every cardinal probe in this file and fails these.
//! * `a_field_write_to_a_body_local_keeps_its_body_axiom` (+ its liar) and
//!   `a_bare_scalar_assignment_to_a_parameter_keeps_its_body_axiom` — publisher
//!   clause 4 is gated on the write being rooted at a PARAMETER and being a
//!   PROJECTION. A field write to a local the body itself created is modeled
//!   correctly today, so "any field write drops the axiom" would retire a
//!   working capability.

use trust_vc_core::{verify_function_from_file, VerifyResult};

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_mutref_scope_{label}_{}_{}.rs",
        std::process::id(),
        FIXTURE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).expect("write mut-ref resolution-scope fixture");
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

/// A false claim must not be `Verified`. Both fail-closed shapes count here:
/// a solver REFUTATION, and a rejection (`Error`) from one of the new
/// fail-closed gates — the container group deliberately DECLINES the model
/// rather than approximating it, because there is no sound raw rendering of a
/// dropped statement mutation.
///
/// `Error` is admitted only in this file's cardinal pins, and every one of them
/// is paired with a `*_still_verifies` narrowness pin over a near-identical
/// program, so "reject everything" cannot satisfy the file.
fn assert_not_verified(label: &str, source: &str) {
    let result = verdict(label, source);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{label}: CARDINAL FALSE VERIFY — a mutation of the caller's binding was \
         treated as a no-op. Got {result:?}"
    );
}

/// The stronger form: the claim must be refuted by the SOLVER, proving the
/// fixture reached it. Used wherever the fix models the post-state as arbitrary
/// rather than declining.
fn assert_refuted(label: &str, source: &str) {
    let result = verdict(label, source);
    match result {
        VerifyResult::Counterexample { .. }
        | VerifyResult::NotProved { .. }
        | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE VERIFY — a mutation of the caller's binding was \
             treated as a no-op"
        ),
        other => panic!(
            "{label}: expected a solver refutation, got {other:?}. An `Error` here means \
             the fixture never reached the solver, so the pin proves nothing."
        ),
    }
}

fn assert_verified(label: &str, source: &str) {
    let result = verdict(label, source);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label}: a TRUE claim must still verify — this is the narrowness pin keeping \
         the fix from being a blanket rejection; got: {result:?}"
    );
}

/// A concrete struct, a contract-less free mutator, the same mutator behind an
/// inline module, and an inherent-impl carrier for the associated-fn and
/// non-self-argument spellings. Nothing here is generic and no trait is
/// involved; `C_AND_TRAIT` below adds one only for the trait-method spelling.
const CARRIERS: &str = "
pub struct C { pub n: u64 }
pub fn bump(c: &mut C) { c.n = c.n + 1; }
pub fn read(c: &C) -> u64 { c.n }
pub mod m {
    pub fn bump2(c: &mut super::C) { c.n = c.n + 1; }
    pub fn read2(c: &super::C) -> u64 { c.n }
}
pub struct H;
impl H {
    pub fn zap(c: &mut C) { c.n = c.n + 1; }
    pub fn hit(&self, c: &mut C) { c.n = c.n + 1; }
    pub fn peek(&self, c: &C) -> u64 { c.n }
}
";

// ---------------------------------------------------------------------------
// GROUP 1 — CALLEE SPELLING. Each of these resolves to a `&mut` parameter that
// the old one-scope resolver could not see, so `mut_ref_call_args` had no entry
// and the havoc was a no-op. The controls the old code DID get right
// (`m::bump(t)`, in-block `use … as loc`) are pinned in
// `mut_ref_free_call_return_lane.rs` and stay green.
// ---------------------------------------------------------------------------

#[test]
fn file_level_use_alias_callee_reaches_the_return_value() {
    assert_refuted(
        "file_use_return",
        &format!(
            "{CARRIERS}
use m::bump2;
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 {{ bump2(t); t.n }}
"
        ),
    );
}

/// The in-body `assert!` twin. `7781306a` reported that the assert lane was
/// already correct and used that asymmetry as its discriminator; for THIS
/// spelling the assert lane was wrong too, because the defect is upstream of
/// both lanes in the resolver.
#[test]
fn file_level_use_alias_callee_reaches_an_in_body_assert() {
    assert_refuted(
        "file_use_assert",
        &format!(
            "{CARRIERS}
use m::bump2;
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) {{ bump2(t); assert!(t.n == 0); }}
"
        ),
    );
}

/// An `use` written in the ENCLOSING INLINE MODULE rather than at file top
/// level or in the function's own block — the third scope.
#[test]
fn enclosing_module_use_alias_callee_reaches_the_return_value() {
    assert_refuted(
        "mod_use_return",
        "
pub struct C { pub n: u64 }
pub mod m { pub fn bump2(c: &mut super::C) { c.n = c.n + 1; } }
pub mod q {
    use crate::m::bump2;
    #[trust_vc::requires(t.n == 0)]
    #[trust_vc::ensures(result == 0)]
    pub fn g(t: &mut super::C) -> u64 { bump2(t); t.n }
}
",
    );
}

/// An inherent-impl ASSOCIATED FN. `SourceFunctionRegistry` enumerates free
/// `ItemFn`s only, so `H::zap` resolved to nothing.
#[test]
fn inherent_associated_fn_mut_ref_argument_reaches_the_return_value() {
    assert_refuted(
        "assoc_fn_return",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 {{ H::zap(t); t.n }}
"
        ),
    );
}

#[test]
fn inherent_associated_fn_mut_ref_argument_reaches_an_in_body_assert() {
    assert_refuted(
        "assoc_fn_assert",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) {{ H::zap(t); assert!(t.n == 0); }}
"
        ),
    );
}

/// A `&mut` NON-SELF argument of an inherent METHOD. The free-call havoc is
/// reached only from `visit_expr_call`; nothing framed a method's arguments.
/// The RECEIVER lane (`4ee6d1d4`) is a different hole and is pinned elsewhere.
#[test]
fn inherent_method_mut_ref_non_self_argument_reaches_the_return_value() {
    assert_refuted(
        "method_arg_return",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 {{ let h = H; h.hit(t); t.n }}
"
        ),
    );
}

#[test]
fn inherent_method_mut_ref_non_self_argument_reaches_an_in_body_assert() {
    assert_refuted(
        "method_arg_assert",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) {{ let h = H; h.hit(t); assert!(t.n == 0); }}
"
        ),
    );
}

/// The TRAIT-impl form of the same spelling.
#[test]
fn trait_method_mut_ref_non_self_argument_reaches_an_in_body_assert() {
    assert_refuted(
        "trait_method_arg",
        "
pub struct C { pub n: u64 }
pub struct H;
pub trait B { fn bump(&self, c: &mut C); }
impl B for H { fn bump(&self, c: &mut C) { c.n = c.n + 1; } }
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) { let h = H; h.bump(t); assert!(t.n == 0); }
",
    );
}

/// A callee this file genuinely CANNOT resolve — an indirect call through a
/// function-pointer local. There is no signature to consult, so the answer comes
/// from the ARGUMENT's own type: `t: &mut C` passed bare is reborrowed into the
/// call, and the callee may write through it. This is the pin that says the
/// resolver reports UNKNOWN instead of "no mutable arguments".
#[test]
fn an_unresolvable_indirect_callee_still_frames_a_reborrowed_mut_ref_argument() {
    assert_refuted(
        "fn_pointer_callee",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) {{ let f: fn(&mut C) = bump; f(t); assert!(t.n == 0); }}
"
        ),
    );
}

// ---------------------------------------------------------------------------
// GROUP 2 — CONTAINER OF THE RETURNED EXPRESSION. The root IS havoced in every
// one of these; what was wrong is the value carried OUT of the container.
// ---------------------------------------------------------------------------

#[test]
fn a_mut_ref_call_inside_both_if_branches_reaches_the_return_value() {
    assert_not_verified(
        "if_branch_container",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(f: bool, t: &mut C) -> u64 {{ if f {{ bump(t); t.n }} else {{ bump(t); t.n }} }}
"
        ),
    );
}

#[test]
fn a_mut_ref_call_inside_both_match_arms_reaches_the_return_value() {
    assert_not_verified(
        "match_arm_container",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(k: bool, t: &mut C) -> u64 {{
    match k {{ true => {{ bump(t); t.n }} false => {{ bump(t); t.n }} }}
}}
"
        ),
    );
}

#[test]
fn a_mut_ref_call_inside_a_let_initializer_block_reaches_the_return_value() {
    assert_not_verified(
        "block_initializer_container",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 {{ let x = {{ bump(t); t.n }}; x }}
"
        ),
    );
}

/// The in-body `assert!` twin of the block container: the value BOUND OUT of the
/// nested scope was rendered against the entry state even though a direct
/// `assert!(t.n == 0)` in the same body was correctly refuted.
#[test]
fn a_value_bound_out_of_a_mutating_block_reaches_an_in_body_assert() {
    assert_not_verified(
        "block_initializer_assert",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) {{ let x = {{ bump(t); t.n }}; assert!(x == 0); }}
"
        ),
    );
}

#[test]
fn a_mut_ref_call_inside_an_if_initializer_reaches_an_in_body_assert() {
    assert_not_verified(
        "if_initializer_assert",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 0)]
pub fn g(t: &mut C) {{ let x = if true {{ bump(t); t.n }} else {{ 0 }}; assert!(x == 0); }}
"
        ),
    );
}

// ---------------------------------------------------------------------------
// GROUP 3 — MUTATION WITHOUT A CALL, in the two definitional-body-axiom
// publishers. Clauses 1-3 of `body_has_unframeable_mutation` are all call-site
// shaped; a bare field assignment matches none of them.
// ---------------------------------------------------------------------------

#[test]
fn sibling_helper_body_axiom_is_dropped_on_a_direct_field_write_to_a_parameter() {
    assert_refuted(
        "helper_direct_field_write",
        "
pub struct C { pub n: u64 }
pub fn via(mut c: C) -> u64 { c.n = c.n + 1; c.n }
#[trust_vc::ensures(result == 0u64)]
pub fn g() -> u64 { let c = C { n: 0 }; via(c) }
",
    );
}

#[test]
fn inherent_method_body_axiom_is_dropped_on_a_direct_field_write_to_self() {
    assert_refuted(
        "method_direct_field_write",
        "
pub struct C { pub n: u64 }
impl C { pub fn via(mut self) -> u64 { self.n = self.n + 1; self.n } }
#[trust_vc::ensures(result == 0u64)]
pub fn g() -> u64 { let c = C { n: 0 }; c.via() }
",
    );
}

/// The DISCRIMINATOR for the two above: the axiom was pinned to the ENTRY state,
/// so the TRUE claim was refuted while the false one verified. Both directions
/// must now be non-`Verified` for the false claim and this one shows the axiom is
/// genuinely gone rather than merely re-pointed.
#[test]
fn the_true_claim_over_a_dropped_body_axiom_is_not_verified_either() {
    assert_not_verified(
        "helper_direct_field_write_true_claim",
        "
pub struct C { pub n: u64 }
pub fn via(mut c: C) -> u64 { c.n = c.n + 1; c.n }
#[trust_vc::ensures(result == 1u64)]
pub fn g() -> u64 { let c = C { n: 0 }; via(c) }
",
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS. Every one of these passed BEFORE the fix and must still pass, so
// they pin rather than flip — which is what makes them a real check.
// ---------------------------------------------------------------------------

#[test]
fn shared_ref_argument_through_a_file_level_use_alias_does_not_havoc() {
    assert_verified(
        "file_use_shared",
        &format!(
            "{CARRIERS}
use m::read2;
#[trust_vc::requires(t.n == 3)]
#[trust_vc::ensures(result == 3)]
pub fn g(t: &mut C) -> u64 {{ let _r = read2(t); t.n }}
"
        ),
    );
}

/// THE pin for the argument-type fallback's scope. `t` IS a `&mut` binding, and
/// the fallback would havoc it — but `read2` RESOLVES, and a resolved signature
/// is authoritative and says `&`-shared. Two reads bracketing the call must
/// still collapse to one term, so a difference of `0` stays provable. This fails
/// for any implementation that havocs on the argument type alone.
#[test]
fn reads_bracketing_a_file_level_use_shared_call_still_collapse() {
    assert_verified(
        "file_use_shared_bracketing",
        &format!(
            "{CARRIERS}
use m::read2;
#[trust_vc::ensures(result == 0)]
pub fn g(t: &mut C) -> u64 {{ let a = t.n; let _z = read2(t); let b = t.n; b - a }}
"
        ),
    );
}

#[test]
fn method_shared_non_self_argument_does_not_havoc() {
    assert_verified(
        "method_shared_arg",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 3)]
#[trust_vc::ensures(result == 3)]
pub fn g(t: &mut C) -> u64 {{ let h = H; let _r = h.peek(t); t.n }}
"
        ),
    );
}

#[test]
fn an_if_container_with_a_non_mutating_statement_prefix_still_renders() {
    assert_verified(
        "if_container_pure_prefix",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 3)]
#[trust_vc::ensures(result == 3)]
pub fn g(f: bool, t: &mut C) -> u64 {{ if f {{ let y = t.n; y }} else {{ let z = t.n; z }} }}
"
        ),
    );
}

#[test]
fn a_block_initializer_with_a_non_mutating_statement_prefix_still_renders() {
    assert_verified(
        "block_container_pure_prefix",
        &format!(
            "{CARRIERS}
#[trust_vc::requires(t.n == 3)]
#[trust_vc::ensures(result == 3)]
pub fn g(t: &mut C) -> u64 {{ let x = {{ let y = t.n; y }}; x }}
"
        ),
    );
}

#[test]
fn a_statement_free_if_container_still_renders() {
    assert_verified(
        "if_container_no_statements",
        "
#[trust_vc::ensures(result == 1 || result == 2)]
pub fn g(f: bool) -> u64 { if f { 1 } else { 2 } }
",
    );
}

/// Publisher clause 4 is gated on the write being rooted at a PARAMETER: a field
/// write to a local the body itself created is modeled correctly, so the axiom
/// must survive. "Drop the axiom on any field write" fails here.
#[test]
fn a_field_write_to_a_body_local_keeps_its_body_axiom() {
    assert_verified(
        "local_field_write_axiom",
        "
pub struct C { pub n: u64 }
pub fn via(x: u64) -> u64 { let mut c = C { n: x }; c.n = 5; c.n }
#[trust_vc::ensures(result == 5u64)]
pub fn g() -> u64 { via(1) }
",
    );
}

/// …and its liar, so the pin above cannot be satisfied by an axiom that says
/// nothing.
#[test]
fn the_liar_over_a_body_local_field_write_axiom_is_refuted() {
    assert_refuted(
        "local_field_write_axiom_liar",
        "
pub struct C { pub n: u64 }
pub fn via(x: u64) -> u64 { let mut c = C { n: x }; c.n = 5; c.n }
#[trust_vc::ensures(result == 1u64)]
pub fn g() -> u64 { via(1) }
",
    );
}

/// Publisher clause 4 also requires a PROJECTION: a whole-binding rebind of a
/// parameter is modeled correctly and keeps its axiom.
#[test]
fn a_bare_scalar_assignment_to_a_parameter_keeps_its_body_axiom() {
    assert_verified(
        "param_scalar_assign_axiom",
        "
pub fn via(mut v: u64) -> u64 { v = v + 1; v }
#[trust_vc::ensures(result == 1u64)]
pub fn g() -> u64 { via(0) }
",
    );
}

/// The caller lane models a direct field write to a `&mut` / by-value parameter
/// correctly — it is only the definitional-axiom lane that could not. Pinned so
/// the new publisher clause is not mistaken for a general rejection of field
/// writes on parameters.
#[test]
fn a_direct_field_write_to_a_parameter_still_verifies_in_the_caller_lane() {
    assert_verified(
        "caller_lane_param_field_write",
        "
pub struct C { pub n: u64 }
#[trust_vc::requires(t.n == 0)]
#[trust_vc::ensures(result == 1u64)]
pub fn g(t: &mut C) -> u64 { t.n = t.n + 1; t.n }
",
    );
}

/// Merely DECLARING mutators in the file costs a body that calls none of them
/// nothing — the group-1 maps are consulted at CALL SITES, not used to poison
/// the file.
#[test]
fn a_file_full_of_mutators_costs_a_pure_body_nothing() {
    assert_verified(
        "declared_mutators_cost_nothing",
        &format!(
            "{CARRIERS}
use m::bump2;
#[trust_vc::requires(t.n == 3)]
#[trust_vc::ensures(result == 3)]
pub fn g(t: &mut C) -> u64 {{ let _r = read(t); t.n }}
"
        ),
    );
}
