// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard for a CARDINAL false verify on the trait-BOUND side of the
//! same-named-declaration class, and the capability pins for the lane that
//! rejection used to cost.
//!
//! ## The mechanism
//!
//! `trait_bounds_from_signature` / `append_trait_bounds` record a bound as the
//! path's LAST SEGMENT — `T: real::Tr` and `T: decoy::Tr` are both the string
//! `"Tr"` — and `parse_trait_decl` keys supertraits the same way. `dyn Tr`,
//! `impl Tr` and `where` predicates are the same `syn::TraitBound` node, so they
//! all land in the same key.
//!
//! `prune_shadowed_duplicate_traits` restores bare-ident uniqueness by deleting
//! the same-named declarations nothing names, and the survivor is elected by
//! what the program NAMES. Until now only `impl` headers voted. A bound that did
//! not agree with the impl was therefore answered by the IMPL's survivor:
//!
//! ```text
//! mod decoy { trait Tr { ensures(result == 9) fn m(&self) -> u64; } }
//! mod real  { trait Tr { ensures(result == 7) fn m(&self) -> u64; } }
//! impl decoy::Tr for D { .. }                                 // decoy survives
//! fn g_pos<T: real::Tr>(x: T)  { assert!(x.m() == 7u64); }    // TRUE
//! fn g_liar<T: real::Tr>(x: T) { assert!(x.m() == 9u64); }    // FALSE
//! ```
//!
//! Measured through the production CLI with the bound's vote removed, in BOTH
//! declaration orders: `g_liar` **verified** and `g_pos` did not — the false
//! claim proved and the true claim rejected simultaneously, which is this
//! class's signature. Stock `rustc --edition 2021` compiles and runs the
//! program, and prints `g_real(S)=7 g_decoy(D)=9`.
//!
//! That lane was previously protected by a BLUNT rejection: any file where a
//! duplicated ident reached a `syn::TraitBound` was failed whole, including a
//! fully qualified `T: real::Tr` that is not ambiguous at all.
//!
//! ## The fix these tests pin
//!
//! Bounds VOTE. Every `TraitBound` path is resolved through the same
//! `TraitScopeIndex` scope walk the impl headers use, from the module that wrote
//! it, and the declaration it names is recorded as a reference. A duplicated
//! ident survives only when every naming site — impl headers and bounds alike —
//! agrees on ONE declaration, and the last segment is then faithful again.
//!
//! What still fails CLOSED: a disagreement between two naming sites, and a bound
//! whose last segment is a duplicated ident but which resolves to no in-file
//! declaration (a bare `T: Tr` with two candidates — rustc rejects that too,
//! E0405 — or a qualifier naming no in-file module). Neither can be pruned
//! around, because the last segment would still key to whoever survived.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_bound_shadow_{}_{}.rs",
        std::process::id(),
        tmp_id
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

fn is_error(result: &VerifyResult) -> bool {
    matches!(result, VerifyResult::Error { .. })
}

const DECOY_DECL: &str = r#"
mod decoy {
    #[trust_vc::trait_spec]
    pub trait Tr { #[trust_vc::ensures(result == 9u64)] fn m(&self) -> u64; }
}
"#;

const REAL_DECL: &str = r#"
mod real {
    #[trust_vc::trait_spec]
    pub trait Tr { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
}
"#;

/// `decoy` first, then `real` — and the reverse. The survivor must be chosen by
/// what the program NAMES, never by declaration order, so every fixture below is
/// run through both.
fn both_orders(rest: &str) -> [String; 2] {
    [
        format!("{DECOY_DECL}{REAL_DECL}{rest}"),
        format!("{REAL_DECL}{DECOY_DECL}{rest}"),
    ]
}

// ---------------------------------------------------------------------------
// CARDINAL: the bound must not be answered by the impl header's survivor.
// ---------------------------------------------------------------------------

/// THE CARDINAL. The file's only impl names `decoy::Tr`; the bound names
/// `real::Tr`. With the bound's vote removed this reports `g_liar` VERIFIED (a
/// false claim, `x.m() == 9`) while the TRUE `x.m() == 7` is not verified.
/// Neither may be `Verified` now, in either declaration order.
#[test]
fn a_bound_disagreeing_with_the_impl_header_never_verifies_either_direction() {
    let rest = r#"
pub struct D;
#[trust_vc::trait_impl]
impl decoy::Tr for D { fn m(&self) -> u64 { 9u64 } }
#[trust_vc::ensures(true)]
fn g_pos<T: real::Tr>(x: T) { trust_vc::assert!(x.m() == 7u64); }
#[trust_vc::ensures(true)]
fn g_liar<T: real::Tr>(x: T) { trust_vc::assert!(x.m() == 9u64); }
"#;
    for (index, src) in both_orders(rest).iter().enumerate() {
        let liar = verify(&format!("cardinal_liar_{index}"), "g_liar", src);
        assert!(
            !is_verified(&liar),
            "order {index}: a FALSE claim under the bound's own trait was verified: {liar:?}"
        );
        assert!(
            is_error(&liar),
            "order {index}: the disagreement must fail the file CLOSED: {liar:?}"
        );
        let honest = verify(&format!("cardinal_pos_{index}"), "g_pos", src);
        assert!(
            is_error(&honest),
            "order {index}: the disagreement must fail the file CLOSED: {honest:?}"
        );
    }
}

/// The supertrait spelling of the same disagreement. `parse_trait_decl` records
/// a supertrait by its last segment too.
#[test]
fn a_supertrait_disagreeing_with_the_impl_header_fails_closed() {
    let rest = r#"
pub struct D;
#[trust_vc::trait_impl]
impl decoy::Tr for D { fn m(&self) -> u64 { 9u64 } }
#[trust_vc::trait_spec]
trait Sub: real::Tr { #[trust_vc::ensures(result == 1u64)] fn s(&self) -> u64; }
#[trust_vc::ensures(true)]
fn g_liar<T: Sub>(x: T) { trust_vc::assert!(x.s() == 2u64); }
"#;
    for (index, src) in both_orders(rest).iter().enumerate() {
        let result = verify(&format!("super_disagree_{index}"), "g_liar", src);
        assert!(is_error(&result), "order {index}: {result:?}");
    }
}

/// FAIL CLOSED. A bound whose last segment is a duplicated ident but which
/// resolves to no in-file declaration cannot vote, and its last segment would
/// still key to whoever survived.
#[test]
fn an_unresolvable_bound_on_a_duplicated_ident_fails_closed() {
    let bare = r#"
pub struct S;
#[trust_vc::trait_impl]
impl real::Tr for S { fn m(&self) -> u64 { 7u64 } }
#[trust_vc::ensures(true)]
fn g_liar<T: Tr>(x: T) { trust_vc::assert!(x.m() == 9u64); }
"#;
    let absent_module = r#"
pub struct S;
#[trust_vc::trait_impl]
impl real::Tr for S { fn m(&self) -> u64 { 7u64 } }
#[trust_vc::ensures(true)]
fn g_liar<T: absent::Tr>(x: T) { trust_vc::assert!(x.m() == 9u64); }
"#;
    for (which, rest) in [("bare", bare), ("absent", absent_module)] {
        for (index, src) in both_orders(rest).iter().enumerate() {
            let result = verify(&format!("unresolvable_{which}_{index}"), "g_liar", src);
            assert!(is_error(&result), "{which} order {index}: {result:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// CAPABILITY: the lane the blunt rejection cost. Every one of these was `error`.
// ---------------------------------------------------------------------------

/// THE REGRESSION THIS CLOSES. `T: real::Tr` names exactly one declaration and
/// agrees with the impl, so the file must verify a true claim — and refuse its
/// liar — exactly as the same program with no decoy does.
#[test]
fn a_qualified_bound_agreeing_with_the_impl_verifies_and_its_liar_does_not() {
    let rest = r#"
pub struct S;
#[trust_vc::trait_impl]
impl real::Tr for S { fn m(&self) -> u64 { 7u64 } }
#[trust_vc::ensures(true)]
fn g_pos<T: real::Tr>(x: T) { trust_vc::assert!(x.m() == 7u64); }
#[trust_vc::ensures(true)]
fn g_liar<T: real::Tr>(x: T) { trust_vc::assert!(x.m() == 9u64); }
"#;
    for (index, src) in both_orders(rest).iter().enumerate() {
        let honest = verify(&format!("agree_pos_{index}"), "g_pos", src);
        assert!(
            is_verified(&honest),
            "order {index}: a true claim under a qualified bound must verify: {honest:?}"
        );
        let liar = verify(&format!("agree_liar_{index}"), "g_liar", src);
        assert!(
            !is_verified(&liar),
            "order {index}: the decoy's clause must not be provable: {liar:?}"
        );
    }
}

/// A bound may be the ONLY naming site in the file: it elects a survivor alone.
/// Here the liar is refuted with a counterexample, not merely fail-closed.
#[test]
fn a_bound_alone_elects_its_declaration_and_discriminates() {
    let rest = r#"
#[trust_vc::ensures(true)]
fn g_pos<T: real::Tr>(x: T) { trust_vc::assert!(x.m() == 7u64); }
#[trust_vc::ensures(true)]
fn g_liar<T: real::Tr>(x: T) { trust_vc::assert!(x.m() == 9u64); }
"#;
    for (index, src) in both_orders(rest).iter().enumerate() {
        let honest = verify(&format!("alone_pos_{index}"), "g_pos", src);
        assert!(is_verified(&honest), "order {index}: {honest:?}");
        let liar = verify(&format!("alone_liar_{index}"), "g_liar", src);
        assert!(
            matches!(liar, VerifyResult::Counterexample { .. }),
            "order {index}: the decoy's clause must be REFUTED, not assumed: {liar:?}"
        );
    }
}

/// `where T: real::Tr` and `impl real::Tr` are the same `syn::TraitBound` node
/// and must resolve identically.
#[test]
fn the_where_and_impl_trait_spellings_discriminate_too() {
    let where_clause = r#"
#[trust_vc::ensures(true)]
fn g_pos<T>(x: T) where T: real::Tr { trust_vc::assert!(x.m() == 7u64); }
#[trust_vc::ensures(true)]
fn g_liar<T>(x: T) where T: real::Tr { trust_vc::assert!(x.m() == 9u64); }
"#;
    let impl_trait = r#"
#[trust_vc::ensures(true)]
fn g_pos(x: impl real::Tr) { trust_vc::assert!(x.m() == 7u64); }
#[trust_vc::ensures(true)]
fn g_liar(x: impl real::Tr) { trust_vc::assert!(x.m() == 9u64); }
"#;
    for (which, rest) in [("where", where_clause), ("impl_trait", impl_trait)] {
        for (index, src) in both_orders(rest).iter().enumerate() {
            let honest = verify(&format!("{which}_pos_{index}"), "g_pos", src);
            assert!(is_verified(&honest), "{which} order {index}: {honest:?}");
            let liar = verify(&format!("{which}_liar_{index}"), "g_liar", src);
            assert!(!is_verified(&liar), "{which} order {index}: {liar:?}");
        }
    }
}

/// A supertrait votes like any other naming site, and the subtrait's own
/// contract must still discriminate through it.
#[test]
fn a_supertrait_agreeing_with_the_impl_verifies_and_its_liar_does_not() {
    let rest = r#"
pub struct S;
#[trust_vc::trait_impl]
impl real::Tr for S { fn m(&self) -> u64 { 7u64 } }
#[trust_vc::trait_spec]
trait Sub: real::Tr { #[trust_vc::ensures(result == 1u64)] fn s(&self) -> u64; }
#[trust_vc::ensures(true)]
fn g_pos<T: Sub>(x: T) { trust_vc::assert!(x.s() == 1u64); }
#[trust_vc::ensures(true)]
fn g_liar<T: Sub>(x: T) { trust_vc::assert!(x.s() == 2u64); }
"#;
    for (index, src) in both_orders(rest).iter().enumerate() {
        let honest = verify(&format!("super_pos_{index}"), "g_pos", src);
        assert!(is_verified(&honest), "order {index}: {honest:?}");
        let liar = verify(&format!("super_liar_{index}"), "g_liar", src);
        assert!(!is_verified(&liar), "order {index}: {liar:?}");
    }
}

/// A bound written INSIDE a module resolves against THAT module's scope, not the
/// file root — `mod real { fn g<T: Tr>(..) }` names `real::Tr`.
#[test]
fn a_bound_resolves_from_the_module_that_wrote_it() {
    let src = r#"
mod decoy {
    #[trust_vc::trait_spec]
    pub trait Tr { #[trust_vc::ensures(result == 9u64)] fn m(&self) -> u64; }
}
mod real {
    #[trust_vc::trait_spec]
    pub trait Tr { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
    #[trust_vc::ensures(true)]
    pub fn g_pos<T: Tr>(x: T) { trust_vc::assert!(x.m() == 7u64); }
    #[trust_vc::ensures(true)]
    pub fn g_liar<T: Tr>(x: T) { trust_vc::assert!(x.m() == 9u64); }
}
"#;
    let honest = verify("scoped_pos", "g_pos", src);
    assert!(is_verified(&honest), "{honest:?}");
    let liar = verify("scoped_liar", "g_liar", src);
    assert!(!is_verified(&liar), "{liar:?}");
}

// ---------------------------------------------------------------------------
// NARROWNESS. Without these the vote could quietly become a blanket admission
// (or the rejection a blanket refusal).
// ---------------------------------------------------------------------------

/// A file with NO duplicate is untouched by any of this: the pass returns before
/// it even clones the file.
#[test]
fn a_single_unduplicated_bound_is_unaffected() {
    let src = r#"
#[trust_vc::trait_spec]
trait Tr { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
#[trust_vc::ensures(true)]
fn g_pos<T: Tr>(x: T) { trust_vc::assert!(x.m() == 7u64); }
#[trust_vc::ensures(true)]
fn g_liar<T: Tr>(x: T) { trust_vc::assert!(x.m() == 8u64); }
"#;
    assert!(is_verified(&verify("single_pos", "g_pos", src)));
    assert!(matches!(
        verify("single_liar", "g_liar", src),
        VerifyResult::Counterexample { .. }
    ));
}

/// A bound on a trait that is NOT duplicated must not be disturbed by a
/// duplication elsewhere in the file.
#[test]
fn a_bound_on_a_unique_trait_survives_an_unrelated_duplicate() {
    let rest = r#"
#[trust_vc::trait_spec]
trait Other { #[trust_vc::ensures(result == 3u64)] fn o(&self) -> u64; }
pub struct S;
#[trust_vc::trait_impl]
impl real::Tr for S { fn m(&self) -> u64 { 7u64 } }
#[trust_vc::ensures(true)]
fn g_pos<T: Other>(x: T) { trust_vc::assert!(x.o() == 3u64); }
#[trust_vc::ensures(true)]
fn g_liar<T: Other>(x: T) { trust_vc::assert!(x.o() == 4u64); }
"#;
    for (index, src) in both_orders(rest).iter().enumerate() {
        let honest = verify(&format!("unique_pos_{index}"), "g_pos", src);
        assert!(is_verified(&honest), "order {index}: {honest:?}");
        let liar = verify(&format!("unique_liar_{index}"), "g_liar", src);
        assert!(!is_verified(&liar), "order {index}: {liar:?}");
    }
}

/// A foreign bound (`T: Clone`) in a file that duplicates `Tr` must not be read
/// as a vote or as an unresolvable duplicate.
#[test]
fn a_foreign_bound_does_not_vote_and_does_not_reject() {
    let rest = r#"
pub struct S;
#[trust_vc::trait_impl]
impl real::Tr for S { fn m(&self) -> u64 { 7u64 } }
#[trust_vc::ensures(true)]
fn g_pos<T: real::Tr + Clone>(x: T) { trust_vc::assert!(x.m() == 7u64); }
"#;
    for (index, src) in both_orders(rest).iter().enumerate() {
        let honest = verify(&format!("foreign_pos_{index}"), "g_pos", src);
        assert!(is_verified(&honest), "order {index}: {honest:?}");
    }
}

/// `dyn Tr` PARITY. The `dyn` lane does not lower today; what this pins is that
/// the duplicated file reaches exactly the same outcome as the single-trait file
/// — the collision gate no longer decides it, and it is still never `Verified`.
#[test]
fn a_dyn_bound_reaches_the_same_outcome_as_an_unduplicated_file() {
    let duplicated = format!(
        "{DECOY_DECL}{REAL_DECL}{}",
        r#"
#[trust_vc::ensures(true)]
fn g_liar(x: &dyn real::Tr) { trust_vc::assert!(x.m() == 9u64); }
"#
    );
    let single = format!(
        "{REAL_DECL}{}",
        r#"
#[trust_vc::ensures(true)]
fn g_liar(x: &dyn real::Tr) { trust_vc::assert!(x.m() == 9u64); }
"#
    );
    let dup = verify("dyn_dup", "g_liar", &duplicated);
    let one = verify("dyn_single", "g_liar", &single);
    assert!(!is_verified(&dup), "{dup:?}");
    assert!(
        std::mem::discriminant(&dup) == std::mem::discriminant(&one),
        "the duplicate must not change the outcome: {dup:?} vs {one:?}"
    );
}
