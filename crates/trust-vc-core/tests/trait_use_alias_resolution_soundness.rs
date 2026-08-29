// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard for a CARDINAL false verify: an `impl <Trait> for <Type>` header was
//! matched to a trait DECLARATION by the path's LAST SEGMENT, so an impl could
//! be conformance-checked against a trait the program does not name.
//!
//! ## The mechanism
//!
//! `trait_expand::parse_trait_impl_decl` set `TraitImplDecl::trait_name` from
//! `trait_path.segments.last()`, and `verify_trait_conformance_inner` then did
//! `base.trait_decls.iter().find(|d| d.name == impl_decl.trait_name)` — a
//! first-declaration-wins lookup over a BARE NAME. Two ways to defeat it, both
//! on programs stock `rustc --edition 2021` compiles and runs:
//!
//! ### 1. Two same-named traits in different modules
//!
//! ```text
//! mod decoy { #[trait_spec] trait Tr { #[ensures(true)]        fn m(&self) -> u64; } }
//! mod real  { #[trait_spec] trait Tr { #[ensures(result == 1)] fn m(&self) -> u64; } }
//! #[trait_impl] impl real::Tr for S { fn m(&self) -> u64 { 99 } }
//! ```
//!
//! Measured through the production CLI, cache off:
//! `trait impl conformance Tr::m for S -> verified`. The impl VIOLATES
//! `real::Tr` and was reported conformant, because the lookup answered with
//! `decoy::Tr`.
//!
//! ### 2. `use ... as` — and the same decoy, now reached by rename
//!
//! ```text
//! mod decoy  { #[trait_spec] trait Alias { #[ensures(true)]        fn m(&self) -> u64; } }
//! mod origin { #[trait_spec] trait Orig  { #[ensures(result == 1)] fn m(&self) -> u64; } }
//! use origin::Orig as Alias;
//! #[trait_impl] impl Alias for S { fn m(&self) -> u64 { 99 } }
//! ```
//!
//! `Alias` names `origin::Orig` here; `decoy::Alias` is not in scope at the
//! file root. Measured: `verified`. Flip `decoy::Alias`'s clause to
//! `result == 2` and give the impl the CONFORMING body `1`, and the same
//! fixture reports `counterexample` — the false claim verifies and the true
//! claim is refuted, simultaneously, which is this defect class's signature.
//!
//! Without a decoy the rename was merely fail-closed: `impl Alias for T`
//! hard-errored "missing trait declaration 'Alias'", because no declaration is
//! named `Alias`.
//!
//! ## The fix, and what these tests pin
//!
//! `crate::trait_path_resolution` resolves an impl header's trait path through
//! `use` renames, `pub use` re-export chains, nested module paths,
//! `crate`/`self`/`super` qualifiers and glob imports, and answers with the
//! DECLARATION's ident — the declaration decides, not the syllable the impl
//! wrote.
//!
//! Dropping the entry is NOT the remedy: with competing declarations present,
//! dropping the one the program named PROMOTES the one it did not. So the
//! ambiguity is made unrepresentable instead — every trait registry in the
//! engine is keyed by a bare ident, so a file that declares two traits with the
//! same bare ident is rejected outright rather than resolved by declaration
//! order. And a path that resolves to no in-file trait may keep its last
//! segment ONLY when that segment matches no in-file declaration; otherwise it
//! is an error, never a guess.
//!
//! The NARROWNESS pins matter as much as the cardinal ones: an unaliased
//! `impl Orig for T` must still verify, an aliased TYPE or FN import must not
//! disturb anything, and each true claim must VERIFY while its same-shape liar
//! REFUTES.

use trust_vc_core::{verify_function_from_file, verify_trait_conformance_obligation, VerifyResult};

// ---------------------------------------------------------------------------
// Fixtures.
// ---------------------------------------------------------------------------

/// CARDINAL 1: decoy trait declared FIRST, impl names the real one, body lies.
const DECOY_TRAIT_IMPL_LIES: &str = r#"
mod decoy {
    #[trust_vc::trait_spec]
    pub trait Tr { #[trust_vc::ensures(true)] fn m(&self) -> u64; }
}
mod real {
    #[trust_vc::trait_spec]
    pub trait Tr { #[trust_vc::ensures(result == 1u64)] fn m(&self) -> u64; }
}
pub struct S;
#[trust_vc::trait_impl]
impl real::Tr for S { fn m(&self) -> u64 { 99u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// CARDINAL 2: `use ... as Alias` where a DIFFERENT trait named `Alias` is
/// declared in another module. The rename must win, and the lying body must be
/// refuted against the trait it actually names.
const ALIAS_SHADOWED_BY_DECOY_LIES: &str = r#"
mod decoy {
    #[trust_vc::trait_spec]
    pub trait Alias { #[trust_vc::ensures(true)] fn m(&self) -> u64; }
}
mod origin {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 1u64)] fn m(&self) -> u64; }
}
use origin::Orig as Alias;
pub struct S;
#[trust_vc::trait_impl]
impl Alias for S { fn m(&self) -> u64 { 99u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// The TRUE half of cardinal 2: same shape, CONFORMING body, and a decoy whose
/// clause the body does not satisfy. Before the fix this reported
/// `counterexample` — a true claim refuted.
const ALIAS_SHADOWED_BY_DECOY_HONEST: &str = r#"
mod decoy {
    #[trust_vc::trait_spec]
    pub trait Alias { #[trust_vc::ensures(result == 2u64)] fn m(&self) -> u64; }
}
mod origin {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 1u64)] fn m(&self) -> u64; }
}
use origin::Orig as Alias;
pub struct S;
#[trust_vc::trait_impl]
impl Alias for S { fn m(&self) -> u64 { 1u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// The plain rename, no decoy: this hard-errored "missing trait declaration
/// 'Alias'" before the fix. It must now be an ordinary, checked impl.
const PLAIN_RENAME_HONEST: &str = r#"
mod inner {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
}
use inner::Orig as Alias;
pub struct T;
#[trust_vc::trait_impl]
impl Alias for T { fn m(&self) -> u64 { 7u64 } }

#[trust_vc::ensures(result == 7u64)]
pub fn through_alias_true(t: &T) -> u64 { t.m() }

#[trust_vc::ensures(result == 4u64)]
pub fn through_alias_liar(t: &T) -> u64 { t.m() }
"#;

/// Same, with a LYING body — the rename must not buy an exemption.
const PLAIN_RENAME_LIES: &str = r#"
mod inner {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
}
use inner::Orig as Alias;
pub struct T;
#[trust_vc::trait_impl]
impl Alias for T { fn m(&self) -> u64 { 99u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// A `pub use` RE-EXPORT CHAIN, renamed twice.
const REEXPORT_CHAIN_HONEST: &str = r#"
mod deep {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 5u64)] fn m(&self) -> u64; }
}
mod mid { pub use crate::deep::Orig as Mid; }
use mid::Mid as Outer;
pub struct T;
#[trust_vc::trait_impl]
impl Outer for T { fn m(&self) -> u64 { 5u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// The same chain with a lying body.
const REEXPORT_CHAIN_LIES: &str = r#"
mod deep {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 5u64)] fn m(&self) -> u64; }
}
mod mid { pub use crate::deep::Orig as Mid; }
use mid::Mid as Outer;
pub struct T;
#[trust_vc::trait_impl]
impl Outer for T { fn m(&self) -> u64 { 99u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// NARROWNESS: the unaliased import, which must be byte-for-byte unaffected.
const UNALIASED_IMPORT: &str = r#"
mod inner {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
}
use inner::Orig;
pub struct T;
#[trust_vc::trait_impl]
impl Orig for T { fn m(&self) -> u64 { 7u64 } }

#[trust_vc::ensures(result == 7u64)]
pub fn unaliased_true(t: &T) -> u64 { t.m() }

#[trust_vc::ensures(result == 4u64)]
pub fn unaliased_liar(t: &T) -> u64 { t.m() }
"#;

/// NARROWNESS: an aliased TYPE and an aliased FN import in the same file must
/// not disturb trait resolution, and the trait contract must still flow.
const ALIASED_TYPE_AND_FN_IMPORTS: &str = r#"
mod inner {
    #[trust_vc::trait_spec]
    pub trait Orig { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
    pub struct Thing;
}
use inner::{Orig, Thing as Renamed};
pub struct T;
#[trust_vc::trait_impl]
impl Orig for T { fn m(&self) -> u64 { 7u64 } }

#[trust_vc::ensures(result == 7u64)]
pub fn with_type_alias_true(t: &T) -> u64 { let _r = Renamed; t.m() }

#[trust_vc::ensures(result == 4u64)]
pub fn with_type_alias_liar(t: &T) -> u64 { let _r = Renamed; t.m() }
"#;

/// NARROWNESS, and a regression this fix ITSELF opened before it was measured:
/// a VALUE-namespace import may share an ident with a trait. `use helpers::make
/// as Orig;` next to `pub trait Orig` compiles AND RUNS under stock
/// `rustc --edition 2021`. An earlier cut of the resolver followed the `use`,
/// found no trait, and hard-errored the file — strictly worse than the engine it
/// replaced. The declaration must still win in a trait position.
const VALUE_NAMESPACE_IMPORT_SHARING_TRAIT_IDENT: &str = r#"
mod helpers { pub fn make() -> u64 { 1u64 } }
use helpers::make as Orig;

#[trust_vc::trait_spec]
pub trait Orig { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
pub struct T;
#[trust_vc::trait_impl]
impl Orig for T { fn m(&self) -> u64 { 7u64 } }

#[trust_vc::ensures(result == 7u64)]
pub fn namespace_true(t: &T) -> u64 { t.m() }

#[trust_vc::ensures(result == 4u64)]
pub fn namespace_liar(t: &T) -> u64 { t.m() }
"#;

/// The same shape with a LYING impl body: the declaration wins, so the
/// violation must still be caught.
const VALUE_NAMESPACE_IMPORT_LIES: &str = r#"
mod helpers { pub fn make() -> u64 { 1u64 } }
use helpers::make as Orig;

#[trust_vc::trait_spec]
pub trait Orig { #[trust_vc::ensures(result == 7u64)] fn m(&self) -> u64; }
pub struct T;
#[trust_vc::trait_impl]
impl Orig for T { fn m(&self) -> u64 { 99u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// NARROWNESS: the `crate::`-qualified cross-module shape the ported corpus
/// writes. Honest body verifies; the same shape with a lying body must refute.
const CRATE_QUALIFIED_HONEST: &str = r#"
mod contracts {
    #[trust_vc::trait_spec]
    pub trait Dispatch { #[trust_vc::ensures(result == 3u64)] fn value(&self) -> u64; }
}
mod impls {
    pub struct G;
    #[trust_vc::trait_impl]
    impl crate::contracts::Dispatch for G { fn value(&self) -> u64 { 3u64 } }
}

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

const CRATE_QUALIFIED_LIES: &str = r#"
mod contracts {
    #[trust_vc::trait_spec]
    pub trait Dispatch { #[trust_vc::ensures(result == 3u64)] fn value(&self) -> u64; }
}
mod impls {
    pub struct G;
    #[trust_vc::trait_impl]
    impl crate::contracts::Dispatch for G { fn value(&self) -> u64 { 4u64 } }
}

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// A file declaring two traits with the SAME bare ident has no faithful
/// representation in a bare-name-keyed registry, so it is rejected outright —
/// even when no impl is involved at all.
const DUPLICATE_TRAIT_NAMES_NO_IMPL: &str = r#"
mod a { pub trait Tr { fn m(&self) -> u64; } }
mod b { pub trait Tr { fn m(&mut self) -> u64; } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

/// NARROWNESS: distinct trait names, several modules — the duplicate gate must
/// not fire.
const DISTINCT_TRAIT_NAMES: &str = r#"
mod a {
    #[trust_vc::trait_spec]
    pub trait First { #[trust_vc::ensures(result == 1u64)] fn m(&self) -> u64; }
}
mod b {
    #[trust_vc::trait_spec]
    pub trait Second { #[trust_vc::ensures(result == 2u64)] fn n(&self) -> u64; }
}
pub struct S;
#[trust_vc::trait_impl]
impl a::First for S { fn m(&self) -> u64 { 1u64 } }
#[trust_vc::trait_impl]
impl b::Second for S { fn n(&self) -> u64 { 2u64 } }

#[trust_vc::ensures(result == 0u64)]
pub fn unrelated_probe() -> u64 { 0u64 }
"#;

// ---------------------------------------------------------------------------
// Harness.
// ---------------------------------------------------------------------------

fn fixture_path(tmp_id: &str) -> std::path::PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_usealias_{}_{}.rs", std::process::id(), tmp_id));
    path
}

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let path = fixture_path(tmp_id);
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

/// Conformance obligations are not source functions and have their own entry.
fn conformance(tmp_id: &str, obligation: &str, src: &str) -> VerifyResult {
    let path = fixture_path(tmp_id);
    std::fs::write(&path, src).expect("write fixture");
    let result = verify_trait_conformance_obligation(path.to_str().expect("utf8 path"), obligation)
        .unwrap_or_else(|e| VerifyResult::Error {
            message: e.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

/// Stricter than `!Verified`: an `Error` would mean the obligation stopped
/// being CHECKED, which hollows the guard out. Only a real refutation counts.
fn assert_refuted(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{label}: expected a refutation, got {result:?}"
    );
}

fn assert_verified(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label}: expected Verified, got {result:?}"
    );
}

fn assert_errored(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "{label}: expected an Error, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// CARDINAL: the impl must be checked against the trait the program NAMES.
// ---------------------------------------------------------------------------

#[test]
fn a_decoy_trait_of_the_same_name_does_not_absolve_a_violating_impl() {
    // Before the fix: `verified`, because `decoy::Tr`'s `ensures(true)` answered
    // an obligation belonging to `real::Tr`.
    let result = conformance(
        "decoy_lies",
        "trait impl conformance Tr::m for S",
        DECOY_TRAIT_IMPL_LIES,
    );
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a body violating `real::Tr` must not be reported conformant: {result:?}"
    );
}

#[test]
fn a_renamed_import_resolves_to_the_declaration_not_a_same_named_decoy() {
    // Before the fix: `verified` under the obligation name `Alias::m for S`.
    // The obligation is now named for the DECLARATION, `Orig`.
    assert_refuted(
        "alias shadowed by decoy, lying body",
        conformance(
            "alias_decoy_lies",
            "trait impl conformance Orig::m for S",
            ALIAS_SHADOWED_BY_DECOY_LIES,
        ),
    );
}

#[test]
fn the_true_half_of_the_alias_decoy_pair_verifies() {
    // Before the fix: `counterexample` — a CONFORMING body refuted, because the
    // decoy's `result == 2` answered `origin::Orig`'s obligation. The false
    // claim verifying and the true claim being refuted is one defect, and both
    // directions have to be pinned.
    assert_verified(
        "alias shadowed by decoy, conforming body",
        conformance(
            "alias_decoy_honest",
            "trait impl conformance Orig::m for S",
            ALIAS_SHADOWED_BY_DECOY_HONEST,
        ),
    );
}

// ---------------------------------------------------------------------------
// The renamed / re-exported import now resolves, and still discriminates.
// ---------------------------------------------------------------------------

#[test]
fn a_plain_rename_is_conformance_checked_and_verifies_an_honest_body() {
    // Before the fix this whole file hard-errored
    // "missing trait declaration 'Alias'".
    assert_verified(
        "plain rename, honest body",
        conformance(
            "rename_honest",
            "trait impl conformance Orig::m for T",
            PLAIN_RENAME_HONEST,
        ),
    );
}

#[test]
fn a_plain_rename_refutes_a_violating_body() {
    assert_refuted(
        "plain rename, lying body",
        conformance(
            "rename_lies",
            "trait impl conformance Orig::m for T",
            PLAIN_RENAME_LIES,
        ),
    );
}

#[test]
fn the_trait_contract_flows_to_a_caller_through_a_rename() {
    assert_verified(
        "caller through rename, true claim",
        verify("rename_call_t", "through_alias_true", PLAIN_RENAME_HONEST),
    );
    assert!(
        !matches!(
            verify("rename_call_l", "through_alias_liar", PLAIN_RENAME_HONEST),
            VerifyResult::Verified
        ),
        "a false claim through a renamed trait must not verify"
    );
}

#[test]
fn a_pub_use_reexport_chain_is_followed_to_the_declaration() {
    assert_verified(
        "re-export chain, honest body",
        conformance(
            "chain_honest",
            "trait impl conformance Orig::m for T",
            REEXPORT_CHAIN_HONEST,
        ),
    );
    assert_refuted(
        "re-export chain, lying body",
        conformance(
            "chain_lies",
            "trait impl conformance Orig::m for T",
            REEXPORT_CHAIN_LIES,
        ),
    );
}

// ---------------------------------------------------------------------------
// Competing declarations are UNREPRESENTABLE, not silently resolved.
// ---------------------------------------------------------------------------

#[test]
fn two_traits_with_the_same_bare_name_fail_the_file_closed() {
    // Even with no impl and no trust-vc trait attribute: the self-receiver-kind
    // registry keys unannotated traits by bare name too, and the two
    // declarations here disagree about `&self` vs `&mut self`.
    assert_errored(
        "duplicate trait names, no impl",
        verify(
            "dup_no_impl",
            "unrelated_probe",
            DUPLICATE_TRAIT_NAMES_NO_IMPL,
        ),
    );
}

#[test]
fn the_duplicate_gate_does_not_fire_on_distinct_trait_names() {
    // NARROWNESS: a gate that rejects every multi-module file is a capability
    // disaster. Both impls must still be checked.
    assert_verified(
        "distinct names, first impl",
        conformance(
            "distinct_a",
            "trait impl conformance First::m for S",
            DISTINCT_TRAIT_NAMES,
        ),
    );
    assert_verified(
        "distinct names, second impl",
        conformance(
            "distinct_b",
            "trait impl conformance Second::n for S",
            DISTINCT_TRAIT_NAMES,
        ),
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS pins.
// ---------------------------------------------------------------------------

#[test]
fn an_unaliased_import_is_unaffected() {
    assert_verified(
        "unaliased import, conformance",
        conformance(
            "unaliased_conf",
            "trait impl conformance Orig::m for T",
            UNALIASED_IMPORT,
        ),
    );
    assert_verified(
        "unaliased import, true claim",
        verify("unaliased_t", "unaliased_true", UNALIASED_IMPORT),
    );
    assert!(
        !matches!(
            verify("unaliased_l", "unaliased_liar", UNALIASED_IMPORT),
            VerifyResult::Verified
        ),
        "a false claim through an unaliased trait must not verify"
    );
}

#[test]
fn an_aliased_type_import_does_not_disturb_trait_resolution() {
    assert_verified(
        "aliased type import, conformance",
        conformance(
            "typealias_conf",
            "trait impl conformance Orig::m for T",
            ALIASED_TYPE_AND_FN_IMPORTS,
        ),
    );
    assert_verified(
        "aliased type import, true claim",
        verify(
            "typealias_t",
            "with_type_alias_true",
            ALIASED_TYPE_AND_FN_IMPORTS,
        ),
    );
    assert!(
        !matches!(
            verify(
                "typealias_l",
                "with_type_alias_liar",
                ALIASED_TYPE_AND_FN_IMPORTS
            ),
            VerifyResult::Verified
        ),
        "a false claim alongside an aliased type import must not verify"
    );
}

#[test]
fn a_crate_qualified_cross_module_impl_still_discriminates() {
    assert_verified(
        "crate-qualified, honest body",
        conformance(
            "cratequal_honest",
            "trait impl conformance Dispatch::value for G",
            CRATE_QUALIFIED_HONEST,
        ),
    );
    assert_refuted(
        "crate-qualified, lying body",
        conformance(
            "cratequal_lies",
            "trait impl conformance Dispatch::value for G",
            CRATE_QUALIFIED_LIES,
        ),
    );
}

#[test]
fn a_value_namespace_import_sharing_a_traits_ident_does_not_poison_it() {
    // Ground truth: this program compiles and runs under stock
    // `rustc --edition 2021` (`t.m() == 7`, `Orig() == 1`). An earlier cut of
    // the resolver hard-errored it — a capability regression against the
    // pre-fix engine, caught only by probing my own fix's blast radius.
    assert_verified(
        "value-namespace import, conformance",
        conformance(
            "ns_conf",
            "trait impl conformance Orig::m for T",
            VALUE_NAMESPACE_IMPORT_SHARING_TRAIT_IDENT,
        ),
    );
    assert_verified(
        "value-namespace import, true claim",
        verify(
            "ns_t",
            "namespace_true",
            VALUE_NAMESPACE_IMPORT_SHARING_TRAIT_IDENT,
        ),
    );
    assert!(
        !matches!(
            verify(
                "ns_l",
                "namespace_liar",
                VALUE_NAMESPACE_IMPORT_SHARING_TRAIT_IDENT
            ),
            VerifyResult::Verified
        ),
        "a false claim must not verify just because a value import shares the ident"
    );
}

#[test]
fn a_value_namespace_import_does_not_excuse_a_violating_impl() {
    assert_refuted(
        "value-namespace import, lying body",
        conformance(
            "ns_lies",
            "trait impl conformance Orig::m for T",
            VALUE_NAMESPACE_IMPORT_LIES,
        ),
    );
}
