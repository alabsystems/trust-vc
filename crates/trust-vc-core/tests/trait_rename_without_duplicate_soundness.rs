// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guards for FOUR measured false verifies — three of them CARDINAL — that a
//! `use ... as Alias` rename opens with **no duplicate declaration ident
//! anywhere in the file**.
//!
//! ## Why the existing gates do not cover this
//!
//! `trait_path_resolution` already closed the same-named-declaration axis:
//! `reject_duplicate_trait_names` fails a file whose traits share a bare ident,
//! and `prune_shadowed_duplicate_traits` elects a survivor when every naming
//! site — impl headers *and*, since the trait-BOUND fix, bounds and supertraits
//! — agrees. Both engage **only when an ident is duplicated**. Its module header
//! then argues that the remaining bare-name-keyed lanes are "correct by
//! construction, because the surviving last segment is faithful".
//!
//! That argument silently assumes a duplicate triggered the election. Every
//! fixture below has **all-distinct declaration idents**, so neither gate ever
//! runs, and the last segment is simply not the declaration's name.
//!
//! Each cardinal was measured through the production CLI with
//! `TRUST_VC_DISABLE_VC_CACHE=1`, against a byte-identical control written
//! without the rename, and each legal reproducer compiles AND RUNS under stock
//! `rustc --edition 2021`.
//!
//! ### 1. Impl header → `trait_method_declares_requires` (precondition DROP)
//!
//! ```text
//! mod origin { #[trait_spec] trait Orig { #[requires(false)] fn make() -> u64; } }
//! use origin::Orig as Alias;
//! #[trait_impl] impl Alias for S { fn make() -> u64 { 1u64 } }
//! fn probe() { assert!(S::make() == 1u64); }
//! ```
//!
//! The scan looked for a trait named `"Alias"`, found none, reported "declares
//! no requires", and the method's definitional body axiom published
//! UNCONDITIONALLY — so a call that cannot satisfy `requires(false)` **verified**.
//! `impl origin::Orig for S` correctly errored. The same rename defeats it
//! through a `pub use` chain, a grouped `use {A as a, B as b}` and a
//! `self::`-rooted path.
//!
//! ### 2. Trait bound → `append_trait_bounds` (WRONG TRAIT, cardinal)
//!
//! ```text
//! mod origin { #[trait_spec] trait Counter { #[ensures(result == 7)] fn peek(&self) -> u64; } }
//! mod other  { #[trait_spec] trait Peek    { #[ensures(result == 9)] fn peek(&self) -> u64; } }
//! use origin::Counter as Peek;
//! fn probe<T: Peek>(x: T) { assert!(x.peek() == 9u64); }
//! ```
//!
//! `TraitBound::trait_name` recorded the SPELLING `"Peek"`, which answered with
//! `other::Peek`. The FALSE claim **verified** and its TRUE twin (`== 7u64`) was
//! refuted — simultaneously, this class's signature. `rustc` prints
//! `probe(S) = 7`. The plain rename (`T: Alias`, naming nothing) was the
//! fail-closed half of the same defect and cost the entire generic-dispatch
//! capability, including the `&mut self` mutation framing.
//!
//! ### 3. Supertrait → `parse_trait_decl` (WRONG TRAIT, cardinal)
//!
//! `trait Derived: Peek` with the same rename in scope: `TraitDecl::supertraits`
//! recorded `"Peek"`, `supertrait_closure_methods` walked to `other::Peek`, and
//! the same inversion followed through the derived bound.
//!
//! ### 4. `impl PartialEq` detection → `collect_manual_partial_eq_impls`
//!
//! ```text
//! use core::cmp::PartialEq as Eq2;
//! impl Eq2 for P { fn eq(&self, _o: &P) -> bool { false } }
//! fn probe(x: P) { assert!(x == x); }
//! ```
//!
//! This is a FAIL-CLOSED gate, so failing to recognise the header opens the hole
//! it exists to close: the impl went uncollected, `==` lowered STRUCTURALLY, and
//! `x == x` **verified** against an `eq` that always returns `false` (`rustc`
//! prints `x == x is false`). `impl PartialEq for P` correctly errored.
//!
//! ## The fix these tests pin
//!
//! Every one of those keys is now produced by resolving the written path against
//! the file's `use` bindings and module structure — the DECLARATION decides. The
//! impl-header and bound/supertrait lanes go through `TraitScopeIndex`; the
//! `PartialEq` lane, which must recognise a FOREIGN trait that resolves to no
//! in-file declaration, goes through `TraitScopeIndex::expanded_path_segments`.
//!
//! ## The narrowness pins matter as much
//!
//! A fix that rejected every renamed impl or bound would be a capability
//! disaster, and an inert-on-undecidable bound must not disturb a sibling site
//! that names its declaration exactly. Both directions are pinned below, and
//! resolution RESTORED capability that the pre-fix engine did not have: a
//! renamed bound and a renamed supertrait now dispatch instead of erroring.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tag: &str, func: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_rename_nodup_{}_{}_{}.rs",
        std::process::id(),
        tag,
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result = verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    result
}

fn is_verified(result: &VerifyResult) -> bool {
    matches!(result, VerifyResult::Verified)
}

// ---------------------------------------------------------------------------
// 1. Impl header: the requires-bearing body axiom.
// ---------------------------------------------------------------------------

/// The renamed impl header must NOT let a `requires(false)` method's body axiom
/// publish. Every rename spelling the resolver handles is exercised, because the
/// defect is in the KEY, not in any one import form.
#[test]
fn renamed_impl_header_does_not_drop_the_traits_requires() {
    const SPELLINGS: &[(&str, &str)] = &[
        ("plain", "use origin::Orig as Alias;"),
        ("selfrooted", "use self::origin::Orig as Alias;"),
        ("grouped", "use origin::{Orig as Alias};"),
    ];
    for (tag, import) in SPELLINGS {
        let src = format!(
            r#"
mod origin {{
    #[trust_vc::trait_spec]
    pub trait Orig {{ #[trust_vc::requires(false)] fn make() -> u64; }}
}}
{import}
pub struct S;
#[trust_vc::trait_impl]
impl Alias for S {{ fn make() -> u64 {{ 1u64 }} }}

#[trust_vc::ensures(true)]
pub fn probe() -> u64 {{ trust_vc::assert!(S::make() == 1u64); 0u64 }}
"#
        );
        let result = verify(tag, "probe", &src);
        assert!(
            !is_verified(&result),
            "renamed impl header ({tag}) dropped the trait's `requires`: {result:?}"
        );
    }
}

/// The same through a `pub use` RE-EXPORT chain, which the pre-fix scan also
/// failed to follow.
#[test]
fn reexported_then_renamed_impl_header_does_not_drop_the_requires() {
    const SRC: &str = r#"
mod deep {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::requires(false)] fn make() -> u64; }
}
mod mid { pub use crate::deep::Orig; }
use mid::Orig as Alias;
pub struct S;
#[trust_vc::trait_impl]
impl Alias for S { fn make() -> u64 { 1u64 } }

#[trust_vc::ensures(true)]
pub fn probe() -> u64 { trust_vc::assert!(S::make() == 1u64); 0u64 }
"#;
    let result = verify("reexport", "probe", SRC);
    assert!(
        !is_verified(&result),
        "re-exported rename dropped the trait's `requires`: {result:?}"
    );
}

/// The WRONG-TRAIT flavour: the rename's target NAME is borne by a different
/// declaration, which has no `requires` at all. Still no duplicate ident.
#[test]
fn renamed_impl_header_is_not_answered_by_a_same_named_other_trait() {
    const SRC: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Orig  { #[trust_vc::requires(false)] fn make() -> u64; } }
mod other  { #[trust_vc::trait_spec] pub trait Decoy { fn make() -> u64; } }
use origin::Orig as Decoy;
pub struct S;
#[trust_vc::trait_impl]
impl Decoy for S { fn make() -> u64 { 1u64 } }

#[trust_vc::ensures(true)]
pub fn probe() -> u64 { trust_vc::assert!(S::make() == 1u64); 0u64 }
"#;
    let result = verify("wrongtrait", "probe", SRC);
    assert!(
        !is_verified(&result),
        "the rename was answered by `other::Decoy`, dropping `origin::Orig`'s \
         `requires`: {result:?}"
    );
}

/// NARROWNESS. A renamed impl of a requires-FREE trait method must still
/// publish its body axiom and verify — a fix that rejects every renamed impl is
/// a capability disaster, and this is the exact shape it would cost.
#[test]
fn renamed_impl_header_without_requires_still_verifies() {
    const SRC: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Orig { fn make() -> u64; } }
use origin::Orig as Alias;
pub struct S;
#[trust_vc::trait_impl]
impl Alias for S { fn make() -> u64 { 1u64 } }

#[trust_vc::ensures(true)]
pub fn honest() -> u64 { trust_vc::assert!(S::make() == 1u64); 0u64 }
#[trust_vc::ensures(true)]
pub fn liar() -> u64 { trust_vc::assert!(S::make() == 2u64); 0u64 }
"#;
    assert!(
        is_verified(&verify("cap", "honest", SRC)),
        "a renamed requires-free impl lost its body axiom"
    );
    assert!(
        !is_verified(&verify("cap", "liar", SRC)),
        "the body axiom proved a FALSE claim"
    );
}

/// CONTROL. The qualified spelling of the cardinal fixture is unchanged: it was
/// fail-closed before the fix and must stay so.
#[test]
fn qualified_impl_header_control_is_unchanged() {
    const SRC: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Orig { #[trust_vc::requires(false)] fn make() -> u64; } }
pub struct S;
#[trust_vc::trait_impl]
impl origin::Orig for S { fn make() -> u64 { 1u64 } }

#[trust_vc::ensures(true)]
pub fn probe() -> u64 { trust_vc::assert!(S::make() == 1u64); 0u64 }
"#;
    assert!(!is_verified(&verify("ctl", "probe", SRC)));
}

// ---------------------------------------------------------------------------
// 2. Trait bounds.
// ---------------------------------------------------------------------------

/// The measured CARDINAL: a renamed bound whose spelling is borne by a different
/// trait. Both halves are asserted together, because "the false claim verifies
/// AND the true claim is refuted" is what identifies this class — a one-sided
/// check would pass on an engine that simply rejects everything.
#[test]
fn a_renamed_bound_is_not_answered_by_a_same_named_other_trait() {
    const SRC: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Counter { #[trust_vc::ensures(result == 7u64)] fn peek(&self) -> u64; } }
mod other  { #[trust_vc::trait_spec] pub trait Peek    { #[trust_vc::ensures(result == 9u64)] fn peek(&self) -> u64; } }
use origin::Counter as Peek;

#[trust_vc::ensures(true)]
pub fn liar<T: Peek>(x: T) -> u64 { trust_vc::assert!(x.peek() == 9u64); 0u64 }
#[trust_vc::ensures(true)]
pub fn honest<T: Peek>(x: T) -> u64 { trust_vc::assert!(x.peek() == 7u64); 0u64 }
"#;
    assert!(
        !is_verified(&verify("bound", "liar", SRC)),
        "the bound was answered by `other::Peek` and proved a FALSE claim"
    );
    assert!(
        is_verified(&verify("bound", "honest", SRC)),
        "the TRUE claim from `origin::Counter` was refuted"
    );
}

/// CAPABILITY RESTORED. Before the fix a plain renamed bound named nothing, so
/// the method did not resolve at all and every call errored. Resolution makes
/// the renamed bound dispatch exactly like its qualified twin — in BOTH
/// directions, so the restoration is not just "it answers now".
#[test]
fn a_plain_renamed_bound_dispatches_in_both_directions() {
    const SRC: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Orig { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; } }
use origin::Orig as Alias;

#[trust_vc::ensures(true)]
pub fn honest<T: Alias>(x: T) -> u64 { trust_vc::assert!(x.m() == 7u64); 0u64 }
#[trust_vc::ensures(true)]
pub fn liar<T: Alias>(x: T) -> u64 { trust_vc::assert!(x.m() == 9u64); 0u64 }
"#;
    assert!(is_verified(&verify("plainbound", "honest", SRC)));
    assert!(!is_verified(&verify("plainbound", "liar", SRC)));
}

/// The `&mut self` GENERIC-RECEIVER mutation framing reaches its trait through
/// `TraitBound::trait_name` too. With the bound unresolved the method was
/// unsupported and the whole lane was dark; resolved, `bump()` must havoc the
/// receiver so two `peek()` reads bracketing it are NOT equal, while the same
/// program without the mutation still proves they are. An impl's `peek` can
/// read a `Cell`, so that proof is refused as a repeated call; only a
/// `Verified` answer becomes the refusal.
#[test]
fn a_renamed_bound_keeps_the_mut_self_mutation_framing() {
    const MUTATED: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Counter { fn peek(&self) -> u64; fn bump(&mut self); } }
use origin::Counter as Alias;

#[trust_vc::ensures(true)]
pub fn probe<T: Alias>(t: &mut T) -> u64 {
    let x = t.peek(); t.bump(); let y = t.peek();
    trust_vc::assert!(y == x); 0u64
}
"#;
    const UNMUTATED: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Counter { fn peek(&self) -> u64; fn bump(&mut self); } }
use origin::Counter as Alias;

#[trust_vc::ensures(true)]
pub fn probe<T: Alias>(t: &mut T) -> u64 {
    let x = t.peek(); let y = t.peek();
    trust_vc::assert!(y == x); 0u64
}
"#;
    assert!(
        !is_verified(&verify("framing", "probe", MUTATED)),
        "`bump()` did not havoc the renamed-bound receiver — the dropped-mutation \
         false verify this map exists to prevent"
    );
    let unmutated = verify("framingctl", "probe", UNMUTATED);
    assert!(
        matches!(&unmutated, VerifyResult::Error { message } if message.starts_with("bodiless call repeated")),
        "without the mutation the two reads are one term, which is refused as a repeated \
         call; a refutation here would be the framing over-rejecting: {unmutated:?}"
    );
}

/// An UNDECIDABLE bound records nothing rather than keying the wrong
/// declaration — and must not disturb anything else in the file. Failing the
/// FILE instead was measured and rejected: `mod m { trait Debug }` beside
/// `T: core::fmt::Debug` is ordinary Rust that verifies.
#[test]
fn an_undecidable_bound_is_inert_and_local() {
    const SRC: &str = r#"
mod m {
    #[trust_vc::trait_spec]
    pub trait Debug { #[trust_vc::ensures(result == 4u64)] fn d(&self) -> u64; }
}

#[trust_vc::ensures(true)]
pub fn undecidable_bound<T: core::fmt::Debug>(_x: T) -> u64 { trust_vc::assert!(1u64 == 1u64); 0u64 }
#[trust_vc::ensures(true)]
pub fn qualified_sibling<T: m::Debug>(x: T) -> u64 { trust_vc::assert!(x.d() == 4u64); 0u64 }
#[trust_vc::ensures(true)]
pub fn qualified_sibling_liar<T: m::Debug>(x: T) -> u64 { trust_vc::assert!(x.d() == 5u64); 0u64 }
"#;
    assert!(
        is_verified(&verify("inert", "undecidable_bound", SRC)),
        "a foreign bound whose bare name collides with an in-file trait must not \
         fail the FILE — that is the deferred-fix shape"
    );
    assert!(
        is_verified(&verify("inert", "qualified_sibling", SRC)),
        "omitting one bound must not disturb a sibling that names its declaration"
    );
    assert!(!is_verified(&verify(
        "inert",
        "qualified_sibling_liar",
        SRC
    )));
}

/// NARROWNESS. Bounds written module-locally, and ordinary foreign bounds, must
/// keep working: resolution runs from the module the FUNCTION is written in.
#[test]
fn module_local_and_foreign_bounds_are_unaffected() {
    const MODULE_LOCAL: &str = r#"
mod m {
    #[trust_vc::trait_spec]
    pub trait Tr { #[trust_vc::ensures(result == 4u64)] fn v(&self) -> u64; }
    #[trust_vc::ensures(true)]
    pub fn probe<T: Tr>(x: T) -> u64 { trust_vc::assert!(x.v() == 4u64); 0u64 }
}
"#;
    const FOREIGN: &str = r#"
#[trust_vc::ensures(true)]
pub fn probe<T: Copy + Clone>(_x: T) -> u64 { trust_vc::assert!(1u64 == 1u64); 0u64 }
"#;
    assert!(is_verified(&verify("modlocal", "probe", MODULE_LOCAL)));
    assert!(is_verified(&verify("foreign", "probe", FOREIGN)));
}

// ---------------------------------------------------------------------------
// 3. Supertraits.
// ---------------------------------------------------------------------------

/// The supertrait cardinal, both halves.
#[test]
fn a_renamed_supertrait_is_not_answered_by_a_same_named_other_trait() {
    const SRC: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Base { #[trust_vc::ensures(result == 7u64)] fn b(&self) -> u64; } }
mod other  { #[trust_vc::trait_spec] pub trait Peek { #[trust_vc::ensures(result == 9u64)] fn b(&self) -> u64; } }
use origin::Base as Peek;
#[trust_vc::trait_spec] pub trait Derived: Peek { fn d(&self) -> u64; }

#[trust_vc::ensures(true)]
pub fn liar<T: Derived>(x: T) -> u64 { trust_vc::assert!(x.b() == 9u64); 0u64 }
#[trust_vc::ensures(true)]
pub fn honest<T: Derived>(x: T) -> u64 { trust_vc::assert!(x.b() == 7u64); 0u64 }
"#;
    assert!(
        !is_verified(&verify("super", "liar", SRC)),
        "the supertrait was answered by `other::Peek` and proved a FALSE claim"
    );
    assert!(
        is_verified(&verify("super", "honest", SRC)),
        "the TRUE claim inherited from `origin::Base` was refuted"
    );
}

/// CAPABILITY RESTORED: a plain renamed supertrait inherits its methods instead
/// of leaving them unsupported.
#[test]
fn a_plain_renamed_supertrait_inherits_in_both_directions() {
    const SRC: &str = r#"
mod origin { #[trust_vc::trait_spec] pub trait Base { #[trust_vc::ensures(result == 7u64)] fn b(&self) -> u64; } }
use origin::Base as Alias;
#[trust_vc::trait_spec] pub trait Derived: Alias { fn d(&self) -> u64; }

#[trust_vc::ensures(true)]
pub fn honest<T: Derived>(x: T) -> u64 { trust_vc::assert!(x.b() == 7u64); 0u64 }
#[trust_vc::ensures(true)]
pub fn liar<T: Derived>(x: T) -> u64 { trust_vc::assert!(x.b() == 9u64); 0u64 }
"#;
    assert!(is_verified(&verify("plainsuper", "honest", SRC)));
    assert!(!is_verified(&verify("plainsuper", "liar", SRC)));
}

// ---------------------------------------------------------------------------
// 4. Manual `PartialEq` detection.
// ---------------------------------------------------------------------------

/// A hand-written, non-structural `PartialEq` reached through a rename must
/// still fail `==` closed. Two import spellings, because the gate is a NAME
/// test and every route to the name must reach it.
#[test]
fn a_renamed_partial_eq_impl_still_fails_equality_closed() {
    const DIRECT_RENAME: &str = r#"
use core::cmp::PartialEq as Eq2;
pub struct P { pub a: u64 }
impl Eq2 for P { fn eq(&self, _o: &P) -> bool { false } }

#[trust_vc::ensures(true)]
pub fn probe(x: P) -> u64 { trust_vc::assert!(x == x); 0u64 }
"#;
    const REEXPORT_CHAIN: &str = r#"
mod mid { pub use core::cmp::PartialEq as P; }
use mid::P as Q;
pub struct R { pub a: u64 }
impl Q for R { fn eq(&self, _o: &R) -> bool { false } }

#[trust_vc::ensures(true)]
pub fn probe(x: R) -> u64 { trust_vc::assert!(x == x); 0u64 }
"#;
    for (tag, src) in [("direct", DIRECT_RENAME), ("chain", REEXPORT_CHAIN)] {
        assert!(
            !is_verified(&verify(tag, "probe", src)),
            "`x == x` lowered structurally against a hand-written `eq` that always \
             returns false ({tag})"
        );
    }
}

/// NARROWNESS. A DERIVED `PartialEq` produces no `Item::Impl` at all and must
/// keep lowering structurally — the gate must not start over-collecting.
#[test]
fn a_derived_partial_eq_still_lowers_structurally() {
    const SRC: &str = r#"
#[derive(PartialEq)]
pub struct P { pub a: u64 }

#[trust_vc::ensures(true)]
pub fn probe(x: P) -> u64 { trust_vc::assert!(x == x); 0u64 }
"#;
    assert!(is_verified(&verify("derive", "probe", SRC)));
}
