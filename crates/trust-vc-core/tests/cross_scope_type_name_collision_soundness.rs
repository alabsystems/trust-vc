// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard for a CARDINAL false verify: an INHERENT method on `inner::S`
//! answered the call sites of a DIFFERENT, top-level `S` whose `v` comes from a
//! trait.
//!
//! ## The defect
//!
//! All method metadata is keyed by the receiver type's BARE ident:
//! `ctx.inherent_methods` is a `HashMap<(self_type, method_name), _>` whose
//! `self_type` carries no module path, and
//! `register_trait_impl_methods_for_concrete_types` keys the same way. That
//! pass runs LAST and is deliberately fail-safe — it "never overrides an
//! existing binding", justified by "an inherent method shadows a trait method,
//! as in Rust".
//!
//! That justification is true within ONE type. With the module path erased it
//! also lets an inherent method on `inner::S` outrank the trait method of an
//! unrelated top-level `S`. `register_method_metadata` does guard a same-key
//! conflict, but only between two entries that BOTH reach it; the inherent and
//! the concrete-trait-impl entries arrive through different passes, so the
//! collision was never seen.
//!
//! ## Ground truth
//!
//! Compiled AND RUN under stock `rustc --edition 2021`:
//!
//! ```text
//! mod inner { pub struct S; impl S { pub fn v(&self) -> u8 { 1 } } }
//! pub struct S;
//! trait Tr { fn v(&self) -> u8; }
//! impl Tr for S { fn v(&self) -> u8 { 2 } }
//!
//! top-level S::v() == 2      inner::S::v() == 1
//! ```
//!
//! Measured through the production CLI, cache off, BEFORE the fix:
//!
//! ```text
//! assert!(s.v() == 2)  (TRUE)   -> counterexample
//! assert!(s.v() == 1)  (FALSE)  -> VERIFIED
//! ```
//!
//! The false claim proved and the true claim refuted, simultaneously — the
//! confident-wrong-value signature of this whole defect class.
//!
//! ## The fix these tests pin
//!
//! `TraitScopeIndex::reject_duplicate_type_names` refuses the file. Dropping the
//! colliding entry is NOT the remedy: with competing declarations present,
//! dropping the one the program named PROMOTES the one it did not (20e12591 /
//! 63e3bcf3 are that mistake). The ambiguity is made unrepresentable instead,
//! order-independently — the strike depends on the SET of declarations, not on
//! which one the file writes first.
//!
//! The `..._still_...` tests are the NARROWNESS pins: the gate must not become
//! a blanket rejection of modules, and the legitimate inherent-shadows-trait
//! rule WITHIN one type must keep working.
//!
//! ## Amendment: the refusal became a RESOLUTION
//!
//! Refusing the whole file cost every legal program that merely CONTAINS a
//! same-named pair, including functions that never mention it — measured as 8
//! red narrowness pins in `module_type_shadow_resolution` /
//! `module_type_shadow_soundness`. `resolve_duplicate_type_names_or_reject` now
//! decides such a file instead: the duplicate-ident check is only the DETECTOR,
//! and the collision is resolved against the scopes that hold code, exactly as
//! `rustc` resolves it. The four rejections above are unchanged — they are the
//! cases resolution genuinely cannot settle — and the three tests at the bottom
//! of this file pin the two NEW checks that keep the narrower gate sound.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// The cardinal reproducer. `inner::S::v` is inherent (1); the top-level `S`
/// gets `v` from a trait (2). Two scopes, one bare key `S.v`.
const CROSS_SCOPE_COLLISION: &str = r#"
mod inner {
    pub struct S;
    impl S { #[trust_vc::returns(1u8)] pub fn v(&self) -> u8 { 1 } }
}

pub struct S;

#[trust_vc::trait_spec]
trait Tr { #[trust_vc::returns(2u8)] fn v(&self) -> u8; }

#[trust_vc::trait_impl]
impl Tr for S { fn v(&self) -> u8 { 2 } }

#[trust_vc::ensures(true)]
pub fn outer_true(s: S) { let r = s.v(); trust_vc::assert!(r == 2); }

#[trust_vc::ensures(true)]
pub fn outer_liar(s: S) { let r = s.v(); trust_vc::assert!(r == 1); }

#[trust_vc::ensures(true)]
pub fn inner_true(s: inner::S) { let r = s.v(); trust_vc::assert!(r == 1); }

#[trust_vc::ensures(true)]
pub fn inner_liar(s: inner::S) { let r = s.v(); trust_vc::assert!(r == 2); }
"#;

/// Same shape with the collision written in the REVERSE textual order, so the
/// gate cannot be passing by declaration order.
const CROSS_SCOPE_COLLISION_REVERSED: &str = r#"
pub struct S;

#[trust_vc::trait_spec]
trait Tr { #[trust_vc::returns(2u8)] fn v(&self) -> u8; }

#[trust_vc::trait_impl]
impl Tr for S { fn v(&self) -> u8 { 2 } }

mod inner {
    pub struct S;
    impl S { #[trust_vc::returns(1u8)] pub fn v(&self) -> u8 { 1 } }
}

#[trust_vc::ensures(true)]
pub fn outer_liar(s: S) { let r = s.v(); trust_vc::assert!(r == 1); }
"#;

/// NARROWNESS: identical but for the top-level type's NAME. Nothing collides,
/// so every claim must still be decided correctly in both directions.
const NO_COLLISION_CONTROL: &str = r#"
mod inner {
    pub struct S;
    impl S { #[trust_vc::returns(1u8)] pub fn v(&self) -> u8 { 1 } }
}

pub struct Other;
impl Other { #[trust_vc::returns(2u8)] pub fn v(&self) -> u8 { 2 } }

#[trust_vc::ensures(true)]
pub fn outer_true(s: Other) { let r = s.v(); trust_vc::assert!(r == 2); }

#[trust_vc::ensures(true)]
pub fn outer_liar(s: Other) { let r = s.v(); trust_vc::assert!(r == 1); }

#[trust_vc::ensures(true)]
pub fn inner_true(s: inner::S) { let r = s.v(); trust_vc::assert!(r == 1); }

#[trust_vc::ensures(true)]
pub fn inner_liar(s: inner::S) { let r = s.v(); trust_vc::assert!(r == 2); }
"#;

/// NARROWNESS: the LEGITIMATE Rust rule — an inherent method shadows a trait
/// method of the same name on the SAME type — must keep working. The gate must
/// not fire here; there is exactly one type named `S`.
const INHERENT_SHADOWS_TRAIT_ONE_TYPE: &str = r#"
pub struct S;

#[trust_vc::trait_spec]
trait Tr { #[trust_vc::returns(2u8)] fn v(&self) -> u8; }

#[trust_vc::trait_impl]
impl Tr for S { fn v(&self) -> u8 { 2 } }

impl S { #[trust_vc::returns(1u8)] pub fn v(&self) -> u8 { 1 } }

#[trust_vc::ensures(true)]
pub fn inherent_true(s: S) { let r = s.v(); trust_vc::assert!(r == 1); }

#[trust_vc::ensures(true)]
pub fn inherent_liar(s: S) { let r = s.v(); trust_vc::assert!(r == 2); }
"#;

/// NARROWNESS: two sibling functions may each declare their own function-local
/// `S`. The corpus does exactly this (`evals/verus/ported/recursive_types.rs`),
/// and body extraction already rejects nested items, so such a declaration can
/// never reach the bare-name method registry.
const FUNCTION_LOCAL_TYPES: &str = r#"
pub struct Holder;
impl Holder { #[trust_vc::returns(7u8)] pub fn v(&self) -> u8 { 7 } }

#[trust_vc::ensures(true)]
pub fn only_target(h: Holder) { let r = h.v(); trust_vc::assert!(r == 7); }
"#;

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_xscope_{}_{}.rs", std::process::id(), tmp_id));
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

/// The collision has no faithful bare-name representation, so the only sound
/// outcome is a refusal that NAMES the collision. A bare `!Verified` would also
/// be satisfied by an unrelated failure, which would hollow the guard out.
fn assert_rejected_for_collision(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Error { ref message }
            if message.contains("both named `S`") && message.contains("bare name") => {}
        other => panic!("{label} expected a named type-collision rejection. Got: {other:?}"),
    }
}

fn assert_verified(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Verified { .. } => {}
        other => panic!("{label} Got: {other:?}"),
    }
}

/// Stricter than `!Verified`: an `Error` would mean the obligation stopped
/// being CHECKED, so the guard would "pass" while testing nothing.
fn assert_refuted(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{label} Got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// CARDINAL — the false claim must never verify.
// ---------------------------------------------------------------------------

/// THE false verify: `s.v() == 1` is `inner::S`'s fact and the top-level `S`
/// cannot reach it. This VERIFIED before the fix.
#[test]
fn cross_scope_collision_does_not_verify_the_other_types_value() {
    assert_rejected_for_collision(
        "top-level S must not take inner::S's inherent value:",
        verify("outer_liar", "outer_liar", CROSS_SCOPE_COLLISION),
    );
}

/// The other half of the inverted pair: the TRUE claim was refuted. It must not
/// silently stay refuted — the file is now rejected outright.
#[test]
fn cross_scope_collision_no_longer_refutes_the_true_claim() {
    assert_rejected_for_collision(
        "top-level S's true trait value must not be refuted:",
        verify("outer_true", "outer_true", CROSS_SCOPE_COLLISION),
    );
}

/// The collision poisons resolution in BOTH directions, so the inner type's
/// call sites are refused too rather than answered from a coin flip.
#[test]
fn cross_scope_collision_rejects_the_inner_type_as_well() {
    assert_rejected_for_collision(
        "inner::S true claim:",
        verify("inner_true", "inner_true", CROSS_SCOPE_COLLISION),
    );
    assert_rejected_for_collision(
        "inner::S false claim:",
        verify("inner_liar", "inner_liar", CROSS_SCOPE_COLLISION),
    );
}

/// Order-independence. Resolving by declaration order is the bug; a gate that
/// only fires in one textual order would just relocate it.
#[test]
fn cross_scope_collision_rejection_is_order_independent() {
    assert_rejected_for_collision(
        "reversed declaration order:",
        verify("rev_liar", "outer_liar", CROSS_SCOPE_COLLISION_REVERSED),
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS — the gate must not swallow legal programs.
// ---------------------------------------------------------------------------

/// The control that proves the rejections above are caused by the COLLISION and
/// not by "methods in a `mod` are unsupported". Rename the top-level type and
/// all four claims are decided correctly again.
#[test]
fn distinct_type_names_still_resolve_in_both_directions() {
    assert_verified(
        "Other::v true:",
        verify("ctl_ot", "outer_true", NO_COLLISION_CONTROL),
    );
    assert_refuted(
        "Other::v false:",
        verify("ctl_ol", "outer_liar", NO_COLLISION_CONTROL),
    );
    assert_verified(
        "inner::S::v true:",
        verify("ctl_it", "inner_true", NO_COLLISION_CONTROL),
    );
    assert_refuted(
        "inner::S::v false:",
        verify("ctl_il", "inner_liar", NO_COLLISION_CONTROL),
    );
}

/// The legitimate Rust shadowing rule, within ONE type, is untouched.
#[test]
fn inherent_still_shadows_a_trait_method_on_the_same_type() {
    assert_verified(
        "inherent wins, true:",
        verify("one_t", "inherent_true", INHERENT_SHADOWS_TRAIT_ONE_TYPE),
    );
    assert_refuted(
        "trait value must not leak:",
        verify("one_l", "inherent_liar", INHERENT_SHADOWS_TRAIT_ONE_TYPE),
    );
}

/// An ordinary single-type file is unaffected by the new gate.
#[test]
fn an_ordinary_file_is_unaffected() {
    assert_verified(
        "ordinary single-type file:",
        verify("plain", "only_target", FUNCTION_LOCAL_TYPES),
    );
}

// ---------------------------------------------------------------------------
// The refusal is a RESOLUTION: what it now admits, and the two checks that
// keep admitting it sound.
// ---------------------------------------------------------------------------

/// The collision above minus the SECOND scope's code: `mod inner` declares the
/// twin but holds nothing that can be lowered, so every code-bearing scope in
/// the file (just the root) resolves the bare `S` to the top-level declaration,
/// and the impl on it is the only method metadata under the key `("S", "v")`.
///
/// Legal Rust — `rustc --edition 2021` compiles and runs it — and the previous
/// cut failed the whole file on it.
const CODE_FREE_TWIN: &str = r#"
mod inner {
    pub struct S;
}

pub struct S;
impl S { #[trust_vc::returns(2u8)] pub fn v(&self) -> u8 { 2 } }

#[trust_vc::ensures(true)]
pub fn outer_true(s: S) { let r = s.v(); trust_vc::assert!(r == 2); }

#[trust_vc::ensures(true)]
pub fn outer_liar(s: S) { let r = s.v(); trust_vc::assert!(r == 1); }
"#;

/// THE cardinal shape, moved out of reach of the agreement check: the inherent
/// impl on `inner::S` is written at the ROOT with an explicit qualifier, so
/// `mod inner` holds no code and every code-bearing scope agrees that bare `S`
/// is the top-level one. Nothing in steps 1–2 sees a problem.
///
/// It is still the false verify, because `impl_self_type_base_name` — the key
/// every method registry uses — is the path's LAST SEGMENT: `impl inner::S` and
/// `impl Tr for S` land on the same `("S", "v")`. `assert!(r == 1)` is FALSE for
/// the top-level `S`, whose `v` is the trait's `2`.
const QUALIFIED_IMPL_HEADER: &str = r#"
mod inner {
    pub struct S;
}

impl inner::S { #[trust_vc::returns(1u8)] pub fn v(&self) -> u8 { 1 } }

pub struct S;

#[trust_vc::trait_spec]
trait Tr { #[trust_vc::returns(2u8)] fn v(&self) -> u8; }

#[trust_vc::trait_impl]
impl Tr for S { fn v(&self) -> u8 { 2 } }

#[trust_vc::ensures(true)]
pub fn outer_liar(s: S) { let r = s.v(); trust_vc::assert!(r == 1); }
"#;

/// The winner of the collision is a declaration this engine cannot model (an
/// `enum` with a lifetime parameter), while the LOSER can be modeled. The
/// bare-keyed shape maps are filled only from modelable declarations, so
/// without the second check they would carry `inner::E`'s shape while every use
/// site in the file's code means the top-level `E`.
const UNMODELABLE_WINNER: &str = r#"
pub enum E<'a> { A(&'a u8) }

mod inner {
    pub enum E { A }
}

pub struct Holder;
impl Holder { #[trust_vc::returns(3u8)] pub fn v(&self) -> u8 { 3 } }

#[trust_vc::ensures(true)]
pub fn only_target(h: Holder) { let r = h.v(); trust_vc::assert!(r == 3); }
"#;

/// An unexpanded item-macro invocation can declare a type the scope walk never
/// sees, so the declaration it would shadow cannot be resolved against. Here the
/// macro is inert, which is the point: the rejection is on the SHAPE of what the
/// walk can see, not on what this particular expansion happens to do.
const ITEM_MACRO_BESIDE_A_COLLISION: &str = r#"
macro_rules! nothing { () => {}; }

nothing!();

mod inner {
    pub struct S;
}

pub struct S;
impl S { #[trust_vc::returns(2u8)] pub fn v(&self) -> u8 { 2 } }

#[trust_vc::ensures(true)]
pub fn outer_true(s: S) { let r = s.v(); trust_vc::assert!(r == 2); }
"#;

fn assert_rejected_naming(label: &str, ident: &str, result: VerifyResult) {
    let expected = format!("both named `{ident}`");
    match result {
        VerifyResult::Error { ref message }
            if message.contains(&expected) && message.contains("bare name") => {}
        other => panic!("{label} expected a named type-collision rejection. Got: {other:?}"),
    }
}

/// CAPABILITY: a same-named type in a module that holds no code must not cost
/// the file its methods. Both directions are pinned, so "green" cannot mean
/// "the obligation stopped being checked".
#[test]
fn a_code_free_twin_resolves_instead_of_failing_the_file() {
    assert_verified(
        "code-free twin, true claim:",
        verify("cft_t", "outer_true", CODE_FREE_TWIN),
    );
    assert_refuted(
        "code-free twin, false claim:",
        verify("cft_l", "outer_liar", CODE_FREE_TWIN),
    );
}

/// SOUNDNESS: a qualified `impl inner::S` on a duplicated bare name is refused.
/// Neuter that check and `outer_liar` — a FALSE claim — verifies.
#[test]
fn a_qualified_impl_header_on_a_duplicated_name_is_rejected() {
    assert_rejected_naming(
        "qualified impl header:",
        "S",
        verify("qih", "outer_liar", QUALIFIED_IMPL_HEADER),
    );
}

/// SOUNDNESS: when the declaration the file's code names has no model, the bare
/// carrier must not silently fall back to the other declaration's shape.
#[test]
fn an_unmodelable_winning_declaration_is_rejected() {
    assert_rejected_naming(
        "unmodelable winner:",
        "E",
        verify("umw", "only_target", UNMODELABLE_WINNER),
    );
}

/// SOUNDNESS: resolution is only as good as what the walk can SEE. An item
/// macro can declare a type, so a collision beside one is not resolved.
/// `CODE_FREE_TWIN` is this file minus the macro and it VERIFIES, which is the
/// control proving the macro is what causes the refusal.
#[test]
fn an_item_macro_beside_a_collision_is_rejected() {
    assert_rejected_naming(
        "item macro beside a collision:",
        "S",
        verify("imc", "outer_true", ITEM_MACRO_BESIDE_A_COLLISION),
    );
}

// ---------------------------------------------------------------------------
// The refusal is scoped to the KEY, not the file: what the registries' own
// collision guards already make unreadable needs no refusal at all.
// ---------------------------------------------------------------------------

/// CAPABILITY, and the case whose absence cost 14 soundness pins: BOTH scopes
/// declare an inherent `grab` on their own `LeafClash`, so the inherent
/// registry's same-key guard drops BOTH registrations and the bare key answers
/// nothing. Resolution still cannot pick a declaration — there is simply nothing
/// left to read, so the file is DECIDED instead of failed, and
/// `a2_generic_soundness`'s cross-contamination pins can reach their assertions
/// again.
///
/// The two declarations are token-identical here on purpose: the shape maps do
/// NOT strike the name, so the method guard is the only thing standing between
/// the two bodies. Both liars are pinned, so a leak in either direction shows up.
///
/// Legal Rust — compiled AND RUN under stock `rustc --edition 2021`, printing
/// `root LeafClash::grab = 7  shadow::LeafClash::grab = 9`.
const GUARD_STRUCK_TWIN: &str = r#"
mod shadow {
    pub struct LeafClash { pub a: u64, pub b: u64 }
    impl LeafClash {
        #[trust_vc::ensures(result == self.b)]
        pub fn grab(self: LeafClash) -> u64 { self.b }
    }

    #[trust_vc::requires(a != b)]
    #[trust_vc::ensures(true)]
    pub fn shadow_liar(a: u64, b: u64) {
        let w = LeafClash { a, b };
        trust_vc::assert!(w.grab() == a);
    }
}

pub struct LeafClash { pub a: u64, pub b: u64 }
impl LeafClash {
    #[trust_vc::ensures(result == self.a)]
    pub fn grab(self: LeafClash) -> u64 { self.a }
}

#[trust_vc::requires(a != b)]
#[trust_vc::ensures(true)]
pub fn root_liar(a: u64, b: u64) {
    let w = LeafClash { a, b };
    trust_vc::assert!(w.grab() == b);
}

#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(result == n + 1u64)]
pub fn untouched(n: u64) -> u64 { n + 1 }
"#;

/// NARROWNESS: an inherent method declared exactly ONCE on the duplicated leaf
/// is NOT a collision to any guard — that single registration answers the call
/// sites of both declarations — so it is still refused. The declarations are
/// token-identical, so the shape maps do not strike the name either; the
/// refusal is the only thing keeping the key honest.
const SINGLE_INHERENT_ON_A_DUPLICATE: &str = r#"
mod inner {
    pub struct S { pub x: u64 }
    impl S {
        #[trust_vc::ensures(result == 1u64)]
        pub fn v(self: S) -> u64 { 1 }
    }

    #[trust_vc::ensures(true)]
    pub fn inner_side(x: u64) {
        let s = S { x };
        trust_vc::assert!(s.v() == 1u64);
    }
}

pub struct S { pub x: u64 }

#[trust_vc::ensures(true)]
pub fn root_side(s: S) { trust_vc::assert!(s.x == s.x); }
"#;

/// NARROWNESS: two declarations that do NOT collapse onto ONE registry key are
/// still refused. A generic `impl<A> W<A>` registers under the bare leaf and is
/// dropped by the file-wide leaf count; a concrete `impl W<u64>` registers under
/// `W<u64>` and survives alone — case 2 again by another route. `inner_liar`
/// asserts the ROOT impl's value (`0`), false for `inner`'s own `get`, so a
/// `Verified` here would be the cardinal cross-contamination.
const MIXED_GENERIC_AND_CONCRETE: &str = r#"
mod inner {
    pub struct W<A> { pub v: A }
    impl<A> W<A> {
        #[trust_vc::ensures(result == self.v)]
        pub fn get(self: W<A>) -> A { self.v }
    }

    #[trust_vc::requires(n > 0u64)]
    #[trust_vc::ensures(true)]
    pub fn inner_liar(n: u64) {
        let w = W::<u64> { v: n };
        trust_vc::assert!(w.get() == 0u64);
    }
}

pub struct W<A> { pub v: A }
impl W<u64> {
    #[trust_vc::ensures(result == 0u64)]
    pub fn get(self: W<u64>) -> u64 { 0 }
}

#[trust_vc::ensures(true)]
pub fn root_side(n: u64) {
    let w = W::<u64> { v: n };
    trust_vc::assert!(w.get() == 0u64);
}
"#;

/// CAPABILITY: the file is decided, not failed. An obligation that never touches
/// the colliding name verifies — the whole point of scoping the refusal to the
/// key. This is the assertion HEAD could not reach at all.
#[test]
fn a_guard_struck_collision_still_decides_the_rest_of_the_file() {
    assert_verified(
        "obligation that never mentions the collision:",
        verify("gst_u", "untouched", GUARD_STRUCK_TWIN),
    );
}

/// CARDINAL: neither declaration may read the other's body. Both directions, so
/// a leak cannot hide on one side.
///
/// The failure must be the METHOD failing closed — the guard struck both
/// `("LeafClash", "grab")` registrations, so the call has no body axiom — and
/// NOT the collision refusal. Asserting on the message is what stops this pin
/// from being satisfied by the whole-file rejection it exists to replace: it
/// distinguishes "the file was decided and this one call declined" from "the
/// file was refused".
#[test]
fn a_guard_struck_collision_cannot_cross_contaminate_either_way() {
    for (id, func) in [("gst_r", "root_liar"), ("gst_s", "shadow_liar")] {
        match verify(id, func, GUARD_STRUCK_TWIN) {
            VerifyResult::Verified { .. } => {
                panic!("FALSE-VERIFY: `{func}` read the other `LeafClash`'s `grab` body")
            }
            VerifyResult::Error { ref message } if message.contains("both named") => {
                panic!("`{func}` was refused as a collision, not decided: {message}")
            }
            VerifyResult::Error { ref message } => assert!(
                message.contains("unsupported method `grab()"),
                "`{func}` must fail closed on the struck method key, got: {message}"
            ),
            _ => {}
        }
    }
}

/// NARROWNESS: a single inherent registration on a duplicated leaf is still a
/// whole-file refusal. Neuter it and that one registration answers both types.
#[test]
fn a_single_inherent_method_on_a_duplicated_leaf_is_still_rejected() {
    assert_rejected_naming(
        "one inherent registration, two declarations:",
        "S",
        verify("sio", "root_side", SINGLE_INHERENT_ON_A_DUPLICATE),
    );
}

/// NARROWNESS: declarations that land on DIFFERENT registry keys are not
/// collapsed by any guard, so they are still refused.
#[test]
fn a_generic_beside_a_concrete_impl_on_a_duplicated_leaf_is_still_rejected() {
    assert_rejected_naming(
        "generic impl beside a concrete one:",
        "W",
        verify("mgc", "inner_liar", MIXED_GENERIC_AND_CONCRETE),
    );
}
