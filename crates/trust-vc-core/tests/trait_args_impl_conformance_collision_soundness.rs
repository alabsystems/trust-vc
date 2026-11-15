// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// quality-audit: allow-file allow-rust-size — one liar/twin matrix per sibling-impl shape
//! Guard for a CARDINAL false verify on the trait-conformance lane: two impls of
//! ONE parameterized trait for ONE self type (`impl Wc<bool> for S` and
//! `impl Wc<u32> for S`) were treated as a single impl, so the second impl's
//! body was never checked against the trait `ensures`.
//!
//! ```text
//! #[trait_spec] trait Wc<B> { #[ensures(result == 1u8)] fn wc(&self) -> u8; }
//! #[trait_impl] impl Wc<bool> for S { fn wc(&self) -> u8 { 1u8 } }
//! #[trait_impl] impl Wc<u32>  for S { fn wc(&self) -> u8 { 2u8 } }   // violates
//! ```
//!
//! Measured before the fix, cache off: `list_trait_conformance_obligations`
//! returned `trait impl conformance Wc::wc for S` TWICE and both rows came back
//! `Verified`; the production CLI printed a green file and exited 0. Rust gives
//! `<S as Wc<u32>>::wc(&S) == 2` (compiled and run; the caller asserting `== 1`
//! panics). With the violating impl declared FIRST both rows refuted — source
//! order alone decided which body answered.
//!
//! ## Root cause
//!
//! Every per-impl registry the conformance lane reads is keyed WITHOUT the
//! impl's trait type arguments: the minted concrete symbol `S__wc`, the
//! `ImplMethodKey (trait name, S__wc)` that keys captured bodies and impl
//! `ensures` (first registration wins), the helper function context resolved by
//! bare `S__wc`, and the obligation NAME (`{Trait}::{method} for {Type}`). Both
//! impls therefore listed under one name and both checks read the FIRST impl's
//! body.
//!
//! ## The rule these tests pin
//!
//! Fail closed, no new modelling. An impl whose trait name AND concrete method
//! symbol are shared with another impl decl (external ones included, since their
//! bodies are captured under the same key) cannot be told apart from its sibling
//! by any registry the lane reads, so its conformance obligation is still LISTED
//! but answers `NotProved(Incompleteness)` naming the collision — never
//! `Verified`, and it never reads the collided key. Obligation names now carry
//! the trait arguments (`Wc<u32>::wc`) so the two impls are distinct rows.
//! Names of non-parameterized traits are byte-identical to before.
//!
//! The over-rejection is deliberate and recorded: a CONFORMING collided pair is
//! refused too, until the registries are re-keyed by trait arguments.
//!
//! The NARROWNESS controls are the other half: a single instantiation still
//! refutes/verifies on the merits, the same trait on a different self type, a
//! default beside an override and all-defaults impls share no symbol and keep
//! their verdicts, and an unrelated function in a collided file still verifies.
//!
//! ## Measured before the fix (this file, on the untouched engine)
//!
//! ```text
//! L1  Wc<bool>{1} , Wc<u32>{2}           Wc::wc for S  x2  Verified, Verified
//! L2  Wc<u32>{2} first                   Wc::wc for S  x2  Counterexample x2
//! L3  same as L1, impls in `mod a`/`mod b` Wc::wc for S x2  Verified, Verified
//! L4  impl-level ensures, u32 body 2     W2::w2 for S  x2  Verified, Verified
//! L4b only the u32 impl has ensures      Wm::wm for S  x2  Verified, Verified
//! L5  u32 body `x += 2u8`                Wc::wc for S  x2  Verified, Verified
//! L6  #[external] Wc<bool>{1} competitor Wc::wc for S  x1  Verified
//! L7  impl<P> Wc<_> for G<P>             ... (generic struct) x2 Verified x2
//! L8  no-self `fn v() -> u64`            Vc::v for S   x2  Verified, Verified
//! L10 default `b` calls collided `a`     Mm::a x2 Verified; Mm::b x2 Counterexample
//! L9  same-leaf `S` in two modules       enumeration Err (already fail-closed)
//! C1-C8 verdicts were already right; only their names gain the trait arguments
//! ```
//!
//! ## The source census (L11-L17, C9-C10)
//!
//! The decl-level count above under-counts. `register_trait_impl` merges decls
//! whose ERASED fields compare equal, so `Wc<u8>` / `Wc<&'x u8>`, `Wc<HashSet<u8>>`
//! / `Wc<BTreeSet<u8>>`, `Kc<1>` / `Kc<2>`, same-spelled module-local argument
//! types and `impl Tm for S` / `impl Tm for &S` reached the walk as ONE decl with
//! ONE Verified row. And the CALLER lane was never covered: the linking,
//! default-body and impl-`ensures` axioms and the concrete-receiver method
//! resolution are all keyed by (trait, erased self type), so one impl answered
//! calls to its sibling — `Dm::<u32>::d(&s) == 2` verified beside an inherited
//! default returning 2, and the congruence `U::<u32>::f(&s) == U::<bool>::f(&s)`
//! that the first fix left open verified with no conformance
//! obligation in the file.
//!
//! `crate::trait_impl_groups` now censuses every trait impl of the file
//! (unmarked ones included) BEFORE dedup and carries the result on the decl as
//! merged metadata. A member of such a group refuses the conformance rows of the
//! methods a sibling also declares (the rows above), publishes no per-impl axiom,
//! and withholds concrete-receiver resolution, so every call into the group fails
//! closed at lowering. C9 pins that the refused spellings resolve and verify for
//! a single impl; C10 that another trait on the same self type is untouched.
//!
//! L18 widens the census walk to the WHOLE syntax tree: an impl written in a
//! function body, in a `const _: () = { .. };` initializer, in a module nested
//! in a function body or in another impl's method is never registered and never
//! conformance-checked, yet applies crate-wide, and each of those left the file
//! FULLY GREEN with the false `Wc::<u32>::wc(&s) == 1u8` verified.
//!
//! ## Still NOT closed here (separate keys), measured
//!
//! * **A `macro_rules!`-generated sibling.** `syn` does not expand macros, so
//!   `macro_rules! sibling { () => { #[trust_vc::trait_impl] impl Wc<u32> for S
//!   { fn wc(&self) -> u8 { 2u8 } } } } sibling!();` beside a conforming
//!   `impl Wc<bool> for S` still lists ONE Verified row and still verifies
//!   `Wc::<u32>::wc(&s) == 1u8` — a green file. Closing it needs expansion, not
//!   a wider walk, so it is deliberately not pinned here as an accepted verdict.
//! * **A group split across FILES of one crate.** The per-file lane sees one
//!   file. Not measured.
//! * **A BOUND-GENERIC caller** — `fn g<T: Wc<u32>>(t: &T) { t.wc() }` — still
//!   VERIFIES over a group, and over a single non-conforming impl: it consumes
//!   the trait's own postcondition axiom, which is justified per FILE by the
//!   conformance rows rather than per function. C11 pins the control (one impl,
//!   no group, none of this code engaged) and the only guard there is: the file
//!   is red. `assert_caller_fails_closed` below is about the CONCRETE-RECEIVER
//!   lane only.
//! * **An impl the widened walk sees but no producer registers** is counted as
//!   a sibling only. When it is the file's ONLY impl, there is no row to refuse
//!   and it is still neither registered nor checked.

use std::sync::atomic::{AtomicUsize, Ordering};

use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, UnknownCategory, VerifyResult,
};

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn write_fixture(label: &str, src: &str) -> std::path::PathBuf {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_trait_args_collision_{}_{label}_{seq}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write fixture");
    path
}

/// Every listed conformance obligation of `src` with its verdict, in listing
/// order. Cache off: a soundness verdict must never be read out of a warm cache.
fn conformance_rows(label: &str, src: &str) -> Vec<(String, VerifyResult)> {
    let path = write_fixture(label, src);
    let path_str = path.to_str().expect("utf8 path").to_string();
    let rows =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            let names = list_trait_conformance_obligations(&path_str).unwrap_or_else(|err| {
                panic!("{label}: conformance obligations must enumerate: {err}")
            });
            names
                .into_iter()
                .map(|name| {
                    let verdict = verify_trait_conformance_obligation(&path_str, &name)
                        .unwrap_or_else(|err| VerifyResult::Error {
                            message: err.to_string(),
                        });
                    (name, verdict)
                })
                .collect::<Vec<_>>()
        });
    let _ = std::fs::remove_file(&path);
    for (name, verdict) in &rows {
        eprintln!("[{label}] {name} -> {verdict:?}");
    }
    rows
}

fn verify_fn(label: &str, src: &str, func: &str) -> VerifyResult {
    let path = write_fixture(label, src);
    let path_str = path.to_str().expect("utf8 path").to_string();
    let verdict =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(&path_str, func).unwrap_or_else(|err| VerifyResult::Error {
                message: err.to_string(),
            })
        });
    let _ = std::fs::remove_file(&path);
    eprintln!("[{label}] fn {func} -> {verdict:?}");
    verdict
}

fn names(rows: &[(String, VerifyResult)]) -> Vec<&str> {
    rows.iter().map(|(name, _)| name.as_str()).collect()
}

fn row<'a>(label: &str, rows: &'a [(String, VerifyResult)], name: &str) -> &'a VerifyResult {
    rows.iter()
        .find(|(row_name, _)| row_name == name)
        .map(|(_, verdict)| verdict)
        .unwrap_or_else(|| {
            panic!(
                "{label}: no conformance row named `{name}`; got {:?}",
                names(rows)
            )
        })
}

/// THE LIAR ASSERTION. The collided impl's obligation must fail CLOSED with the
/// dedicated collision refusal — not `Verified` (the false verify), and not some
/// unrelated `Error`/unbuildable `Unknown` that would pass for the wrong reason.
fn assert_collision_refused(label: &str, name: &str, verdict: &VerifyResult) {
    match verdict {
        VerifyResult::NotProved {
            reason,
            category: UnknownCategory::Incompleteness,
        } if reason.contains("more than one impl") => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE VERIFY — `{name}` reported Verified although another impl of \
             the same trait shares its concrete method symbol, so the registries this check reads \
             cannot tell the two impls apart"
        ),
        other => panic!(
            "{label}: `{name}` must fail closed with the trait-argument collision refusal \
             (NotProved/Incompleteness naming `more than one impl`), got {other:?}"
        ),
    }
}

fn assert_counterexample(label: &str, name: &str, verdict: &VerifyResult) {
    assert!(
        matches!(verdict, VerifyResult::Counterexample { .. }),
        "{label}: `{name}` is a non-conforming impl checked on its own and must be refuted on the \
         merits, got {verdict:?}"
    );
}

fn assert_verified(label: &str, name: &str, verdict: &VerifyResult) {
    assert!(
        matches!(verdict, VerifyResult::Verified),
        "{label}: `{name}` shares no concrete symbol with another impl of its trait and conforms, \
         so it must still Verify (over-rejection), got {verdict:?}"
    );
}

// ---------------------------------------------------------------------------
// LIARS — every one of these is FALSE in Rust for at least one impl.
// ---------------------------------------------------------------------------

/// L1, the claim repro: the violating `Wc<u32>` impl is declared SECOND.
const L1_SECOND_IMPL_VIOLATES: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 { 2u8 }
}

#[trust_vc::ensures(true)]
fn caller_liar(s: S) {
    let v: u8 = Wc::<u32>::wc(&s);
    trust_vc::assert!(v == 1u8);
}

#[trust_vc::ensures(true)]
fn bystander_true() {
    trust_vc::assert!(true);
}
"#;

#[test]
fn l1_second_impl_violating_trait_ensures_is_not_verified() {
    let rows = conformance_rows("l1", L1_SECOND_IMPL_VIOLATES);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Wc<bool>::wc for S",
            "trait impl conformance Wc<u32>::wc for S",
        ],
        "L1: the two impls must list as two DISTINCT obligations carrying their trait arguments"
    );
    for (name, verdict) in &rows {
        assert_collision_refused("l1", name, verdict);
    }
}

/// The file-level property the CLI reports: a file whose `Wc<u32>` impl
/// returns 2 against `ensures(result == 1)` must not be green. A caller relying
/// on the trait `ensures` still verifies its OWN obligations (ordinary modular
/// reasoning, exactly as for a single non-conforming impl), so the file goes red
/// through the impl's conformance row.
#[test]
fn l1_file_with_violating_impl_is_not_green() {
    let rows = conformance_rows("l1_file", L1_SECOND_IMPL_VIOLATES);
    let caller = verify_fn("l1_file", L1_SECOND_IMPL_VIOLATES, "caller_liar");
    let green =
        matches!(caller, VerifyResult::Verified) && rows.iter().all(|(_, v)| v.is_verified());
    assert!(
        !green,
        "L1: CARDINAL FALSE VERIFY — every function and every conformance obligation of a file \
         whose `Wc<u32>` impl returns 2 against `ensures(result == 1)` reported Verified; rows: \
         {rows:?}"
    );
}

/// L2, order independence: the violating impl declared FIRST.
const L2_FIRST_IMPL_VIOLATES: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 { 2u8 }
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}
"#;

#[test]
fn l2_order_of_collided_impls_does_not_decide_the_verdict() {
    let rows = conformance_rows("l2", L2_FIRST_IMPL_VIOLATES);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Wc<u32>::wc for S",
            "trait impl conformance Wc<bool>::wc for S",
        ],
    );
    for (name, verdict) in &rows {
        assert_collision_refused("l2", name, verdict);
    }
}

/// L3, the spelling that compiles with the real macros (separate modules avoid
/// the E0428 duplicate helper name); rustc returns 2 for `Wc::<u32>::wc(&S)`.
const L3_IMPLS_IN_SEPARATE_MODULES: &str = r#"
pub struct S;

#[trust_vc::trait_spec]
pub trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

mod a {
    use super::*;
    #[trust_vc::trait_impl]
    impl Wc<bool> for S {
        fn wc(&self) -> u8 { 1u8 }
    }
}

mod b {
    use super::*;
    #[trust_vc::trait_impl]
    impl Wc<u32> for S {
        fn wc(&self) -> u8 { 2u8 }
    }
}
"#;

#[test]
fn l3_collided_impls_in_separate_modules_are_not_verified() {
    let rows = conformance_rows("l3", L3_IMPLS_IN_SEPARATE_MODULES);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Wc<bool>::wc for S",
            "trait impl conformance Wc<u32>::wc for S",
        ],
    );
    for (name, verdict) in &rows {
        assert_collision_refused("l3", name, verdict);
    }
}

/// L4, impl-level `ensures`: the trait method has none; the second impl's own
/// `ensures(result == 1)` is false of its body.
const L4_IMPL_LEVEL_ENSURES: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait W2<B> {
    fn w2(&self) -> u8;
}

#[trust_vc::trait_impl]
impl W2<bool> for S {
    #[trust_vc::ensures(result == 1u8)]
    fn w2(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl W2<u32> for S {
    #[trust_vc::ensures(result == 1u8)]
    fn w2(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn l4_collided_impl_own_ensures_is_not_verified() {
    let rows = conformance_rows("l4", L4_IMPL_LEVEL_ENSURES);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance W2<bool>::w2 for S",
            "trait impl conformance W2<u32>::w2 for S",
        ],
    );
    let name = "trait impl conformance W2<u32>::w2 for S";
    assert_collision_refused("l4", name, row("l4", &rows, name));
}

/// L4b, the emission gate over a collided group: only the SECOND impl declares
/// its own `ensures`, the trait declares none. The impl-ensures registry is
/// keyed without trait arguments, so the `Wm<u32>` clauses populate the shared
/// key and the check for EITHER impl read the `Wm<bool>` body (1) against
/// `result == 1` — the false `ensures` of the body that returns 2 was never
/// checked against that body. Both impls must list and both must be refused.
const L4B_ONLY_SECOND_IMPL_DECLARES_ENSURES: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wm<B> {
    fn wm(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wm<bool> for S {
    fn wm(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Wm<u32> for S {
    #[trust_vc::ensures(result == 1u8)]
    fn wm(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn l4b_only_the_violating_impl_declares_ensures_is_not_verified() {
    let rows = conformance_rows("l4b", L4B_ONLY_SECOND_IMPL_DECLARES_ENSURES);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Wm<bool>::wm for S",
            "trait impl conformance Wm<u32>::wm for S",
        ],
        "L4b: an impl `ensures` registered under the shared key must make EVERY member of the \
         collided group emit, so the violating impl cannot drop out of the listing"
    );
    for (name, verdict) in &rows {
        assert_collision_refused("l4b", name, verdict);
    }
}

/// L5, a non-literal violating body (so the fix cannot lean on literal capture).
const L5_NON_LITERAL_SECOND_BODY: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 {
        let mut x: u8 = 0u8;
        x += 2u8;
        x
    }
}
"#;

#[test]
fn l5_non_literal_violating_body_is_not_verified() {
    let rows = conformance_rows("l5", L5_NON_LITERAL_SECOND_BODY);
    assert_eq!(rows.len(), 2, "L5: two obligations, got {:?}", names(&rows));
    for (name, verdict) in &rows {
        assert_collision_refused("l5", name, verdict);
    }
}

/// L6, an EXTERNAL competitor: its body is trusted and lists nothing, but it is
/// captured under the shared key, so it answered the non-external impl's check.
const L6_EXTERNAL_COMPETITOR: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn l6_external_competitor_does_not_answer_the_checked_impl() {
    let rows = conformance_rows("l6", L6_EXTERNAL_COMPETITOR);
    assert_eq!(
        names(&rows),
        ["trait impl conformance Wc<u32>::wc for S"],
        "L6: the external impl lists nothing; the non-external one lists exactly one row"
    );
    let (name, verdict) = &rows[0];
    assert_collision_refused("l6", name, verdict);
}

/// L7, the generic-struct path (`impl<P> Wc<_> for G<P>`, abstract `Poly` self).
const L7_GENERIC_STRUCT_PAIR: &str = r#"
struct G<P> { p: P }

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl<P> Wc<bool> for G<P> {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl<P> Wc<u32> for G<P> {
    fn wc(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn l7_generic_struct_collided_impls_are_not_verified() {
    let rows = conformance_rows("l7", L7_GENERIC_STRUCT_PAIR);
    assert_eq!(rows.len(), 2, "L7: two obligations, got {:?}", names(&rows));
    assert_ne!(
        rows[0].0, rows[1].0,
        "L7: the two impls must list as distinct rows"
    );
    assert!(
        rows[0].0.contains("Wc<bool>::wc") && rows[1].0.contains("Wc<u32>::wc"),
        "L7: generic-struct rows must carry the trait arguments, got {:?}",
        names(&rows)
    );
    for (name, verdict) in &rows {
        assert!(name.ends_with("(generic struct)"), "L7: `{name}`");
        assert_collision_refused("l7", name, verdict);
    }
}

/// L8, a no-`self` associated function.
const L8_NO_SELF_ASSOCIATED_FN: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Vc<B> {
    #[trust_vc::ensures(result == 1u64)]
    fn v() -> u64;
}

#[trust_vc::trait_impl]
impl Vc<bool> for S {
    fn v() -> u64 { 1u64 }
}

#[trust_vc::trait_impl]
impl Vc<u32> for S {
    fn v() -> u64 { 2u64 }
}
"#;

#[test]
fn l8_no_self_associated_fn_collision_is_not_verified() {
    let rows = conformance_rows("l8", L8_NO_SELF_ASSOCIATED_FN);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Vc<bool>::v for S",
            "trait impl conformance Vc<u32>::v for S",
        ],
    );
    for (name, verdict) in &rows {
        assert_collision_refused("l8", name, verdict);
    }
}

/// L10, the rule is PER IMPL, not per method: a collided impl's INHERITED
/// default `b` calls the overridden, collided sibling `a`, so `b` is exactly as
/// unmodelled as `a` even though `b` binds no shared symbol of its own. Rust
/// gives `<S as Mm<u32>>::a(&S) == 2` and `<S as Mm<u32>>::b(&S) == 2`, both
/// against `ensures(result == 1)`. Before the fix both `a` rows Verified (the
/// `u32` body was never checked) while both `b` rows counterexampled against an
/// unconstrained `self.a()`. Every row of both impls — default arm included —
/// must now be refused.
const L10_DEFAULT_CALLS_COLLIDED_SIBLING: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Mm<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn a(&self) -> u8;

    #[trust_vc::ensures(result == 1u8)]
    fn b(&self) -> u8 { self.a() }
}

#[trust_vc::trait_impl]
impl Mm<bool> for S {
    fn a(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Mm<u32> for S {
    fn a(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn l10_inherited_default_of_a_collided_impl_is_not_verified() {
    let rows = conformance_rows("l10", L10_DEFAULT_CALLS_COLLIDED_SIBLING);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Mm<bool>::a for S",
            "trait impl conformance Mm<bool>::b for S",
            "trait impl conformance Mm<u32>::a for S",
            "trait impl conformance Mm<u32>::b for S",
        ],
    );
    for (name, verdict) in &rows {
        assert_collision_refused("l10", name, verdict);
    }
}

// ---------------------------------------------------------------------------
// CONTROLS — non-vacuity and narrowness.
// ---------------------------------------------------------------------------

/// C1: the violating instantiation ALONE is refuted on the merits, under its
/// trait-argument-bearing name — the refusal above is not an over-gate.
const C1_SINGLE_VIOLATING: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn c1_single_violating_instantiation_is_refuted_on_the_merits() {
    let rows = conformance_rows("c1", C1_SINGLE_VIOLATING);
    assert_eq!(names(&rows), ["trait impl conformance Wc<u32>::wc for S"]);
    assert_counterexample("c1", &rows[0].0, &rows[0].1);
}

/// C2: the conforming instantiation alone verifies.
const C2_SINGLE_CONFORMING: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}
"#;

#[test]
fn c2_single_conforming_instantiation_verifies() {
    let rows = conformance_rows("c2", C2_SINGLE_CONFORMING);
    assert_eq!(names(&rows), ["trait impl conformance Wc<bool>::wc for S"]);
    assert_verified("c2", &rows[0].0, &rows[0].1);
}

/// C3: the collision is per (trait, concrete symbol), not per trait — the same
/// parameterized trait on two different self types keeps per-impl verdicts.
const C3_DIFFERENT_SELF_TYPES_CONFORMING: &str = r#"
struct S;
struct T;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Wc<u32> for T {
    fn wc(&self) -> u8 { 1u8 }
}
"#;

const C3_DIFFERENT_SELF_TYPES_T_VIOLATES: &str = r#"
struct S;
struct T;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Wc<u32> for T {
    fn wc(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn c3_same_trait_on_different_self_types_keeps_per_impl_verdicts() {
    let rows = conformance_rows("c3", C3_DIFFERENT_SELF_TYPES_CONFORMING);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Wc<bool>::wc for S",
            "trait impl conformance Wc<u32>::wc for T",
        ],
    );
    for (name, verdict) in &rows {
        assert_verified("c3", name, verdict);
    }

    let rows = conformance_rows("c3_liar", C3_DIFFERENT_SELF_TYPES_T_VIOLATES);
    let s = "trait impl conformance Wc<bool>::wc for S";
    let t = "trait impl conformance Wc<u32>::wc for T";
    assert_verified("c3_liar", s, row("c3_liar", &rows, s));
    assert_counterexample("c3_liar", t, row("c3_liar", &rows, t));
}

/// C4: a non-overridden default beside an override shares no concrete symbol
/// (the default arm never reads a captured body), so both keep their verdicts.
const C4_DEFAULT_BESIDE_OVERRIDE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Dm<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn d(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Dm<bool> for S {}

#[trust_vc::trait_impl]
impl Dm<u32> for S {
    fn d(&self) -> u8 { 1u8 }
}
"#;

const C4_DEFAULT_BESIDE_VIOLATING_OVERRIDE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Dm<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn d(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Dm<bool> for S {}

#[trust_vc::trait_impl]
impl Dm<u32> for S {
    fn d(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn c4_default_beside_override_keeps_per_impl_verdicts() {
    let rows = conformance_rows("c4", C4_DEFAULT_BESIDE_OVERRIDE);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance Dm<bool>::d for S",
            "trait impl conformance Dm<u32>::d for S",
        ],
    );
    for (name, verdict) in &rows {
        assert_verified("c4", name, verdict);
    }

    let rows = conformance_rows("c4_liar", C4_DEFAULT_BESIDE_VIOLATING_OVERRIDE);
    let default_row = "trait impl conformance Dm<bool>::d for S";
    let override_row = "trait impl conformance Dm<u32>::d for S";
    assert_verified("c4_liar", default_row, row("c4_liar", &rows, default_row));
    assert_counterexample("c4_liar", override_row, row("c4_liar", &rows, override_row));

    // The mirror image: the DEFAULT body violates and the override conforms.
    // The default arm must check the default body, never the override's
    // captured body registered under the same `S__d` symbol.
    let rows = conformance_rows("c4_default_liar", C4_VIOLATING_DEFAULT_BESIDE_OVERRIDE);
    assert_counterexample(
        "c4_default_liar",
        default_row,
        row("c4_default_liar", &rows, default_row),
    );
    assert_verified(
        "c4_default_liar",
        override_row,
        row("c4_default_liar", &rows, override_row),
    );
}

const C4_VIOLATING_DEFAULT_BESIDE_OVERRIDE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Dm<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn d(&self) -> u8 { 2u8 }
}

#[trust_vc::trait_impl]
impl Dm<bool> for S {}

#[trust_vc::trait_impl]
impl Dm<u32> for S {
    fn d(&self) -> u8 { 1u8 }
}
"#;

/// C5: two all-defaults impls share no concrete symbol; each default body is
/// checked on its own merits.
const C5_ALL_DEFAULTS_TWICE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Dm<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn d(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Dm<bool> for S {}

#[trust_vc::trait_impl]
impl Dm<u32> for S {}
"#;

const C5_ALL_DEFAULTS_TWICE_VIOLATING: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Dm<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn d(&self) -> u8 { 2u8 }
}

#[trust_vc::trait_impl]
impl Dm<bool> for S {}

#[trust_vc::trait_impl]
impl Dm<u32> for S {}
"#;

#[test]
fn c5_all_defaults_impls_are_checked_on_the_default_body() {
    let expected = [
        "trait impl conformance Dm<bool>::d for S",
        "trait impl conformance Dm<u32>::d for S",
    ];
    let rows = conformance_rows("c5", C5_ALL_DEFAULTS_TWICE);
    assert_eq!(names(&rows), expected);
    for (name, verdict) in &rows {
        assert_verified("c5", name, verdict);
    }

    let rows = conformance_rows("c5_liar", C5_ALL_DEFAULTS_TWICE_VIOLATING);
    assert_eq!(names(&rows), expected);
    for (name, verdict) in &rows {
        assert_counterexample("c5_liar", name, verdict);
    }
}

/// C6: DIFFERENT traits declaring the same method for one type share the
/// concrete symbol `S__v` but not the trait, so they are not collided and their
/// non-parameterized names are byte-identical to before (the literal pins in
/// `trait_inherent_shadow_resolution_soundness.rs` depend on it).
const C6_DIFFERENT_TRAITS_SAME_METHOD: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait A1 {
    #[trust_vc::ensures(result == 1u64)]
    fn v(&self) -> u64;
}

#[trust_vc::trait_spec]
trait A2 {
    #[trust_vc::ensures(result == 2u64)]
    fn v(&self) -> u64;
}

#[trust_vc::trait_impl]
impl A1 for S {
    fn v(&self) -> u64 { 1u64 }
}

#[trust_vc::trait_impl]
impl A2 for S {
    fn v(&self) -> u64 { 2u64 }
}
"#;

#[test]
fn c6_different_traits_sharing_a_method_symbol_keep_names_and_verdicts() {
    let rows = conformance_rows("c6", C6_DIFFERENT_TRAITS_SAME_METHOD);
    assert_eq!(
        names(&rows),
        [
            "trait impl conformance A1::v for S",
            "trait impl conformance A2::v for S",
        ],
    );
    for (name, verdict) in &rows {
        assert_verified("c6", name, verdict);
    }
}

/// C7: a distinct symbol spelling (`self::S`) is a different key, so the
/// violating impl is still checked on its merits through the generic-struct
/// path, and the conforming `S` impl still verifies.
const C7_DISTINCT_SYMBOL_SPELLING: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Wc<u32> for self::S {
    fn wc(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn c7_distinct_symbol_spelling_is_checked_on_the_merits() {
    let rows = conformance_rows("c7", C7_DISTINCT_SYMBOL_SPELLING);
    assert_eq!(rows.len(), 2, "C7: two obligations, got {:?}", names(&rows));
    let s = "trait impl conformance Wc<bool>::wc for S";
    assert_verified("c7", s, row("c7", &rows, s));
    let (self_s, verdict) = rows
        .iter()
        .find(|(name, _)| name.contains("Wc<u32>::wc") && name.ends_with("(generic struct)"))
        .unwrap_or_else(|| panic!("C7: no generic-struct Wc<u32> row in {:?}", names(&rows)));
    assert_counterexample("c7", self_s, verdict);
}

/// C8: an unrelated function in a collided file is not sunk by the refusal.
#[test]
fn c8_bystander_in_collided_file_still_verifies() {
    let verdict = verify_fn("c8", L1_SECOND_IMPL_VIOLATES, "bystander_true");
    assert!(
        matches!(verdict, VerifyResult::Verified),
        "C8: the conformance refusal is the impl's own row and must not sink an unrelated \
         function, got {verdict:?}"
    );
}

/// A misaddressed obligation still fails closed: the old trait-arg-erased name
/// no longer names anything in a parameterized-trait file.
#[test]
fn old_trait_argument_erased_name_is_no_longer_an_obligation() {
    let path = write_fixture("stale_name", C2_SINGLE_CONFORMING);
    let path_str = path.to_str().expect("utf8 path").to_string();
    let verdict =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_trait_conformance_obligation(&path_str, "trait impl conformance Wc::wc for S")
        });
    let _ = std::fs::remove_file(&path);
    assert!(
        matches!(verdict, Ok(VerifyResult::Error { .. })),
        "an obligation name that the listing no longer produces must fail closed with Error, \
         never Verified; got {verdict:?}"
    );
}

/// L9, the same (trait, symbol) collision WITHOUT trait arguments: one
/// non-parameterized trait implemented for two distinct same-named structs in
/// sibling modules. Both impls mint `S__m` under trait `Tm`. Measured before
/// the fix this already fails closed one step earlier — ENUMERATION refuses
/// the file because two types are both named `S` — and that is what this pins;
/// should enumeration ever admit it, every row must hit the collision refusal
/// (the names cannot differ: the trait has no arguments to render).
const L9_SAME_LEAF_SELF_TYPES_IN_SIBLING_MODULES: &str = r#"
#[trust_vc::trait_spec]
pub trait Tm {
    #[trust_vc::ensures(result == 1u8)]
    fn m(&self) -> u8;
}

mod a {
    pub struct S;
    #[trust_vc::trait_impl]
    impl super::Tm for S {
        fn m(&self) -> u8 { 1u8 }
    }
}

mod b {
    pub struct S;
    #[trust_vc::trait_impl]
    impl super::Tm for S {
        fn m(&self) -> u8 { 2u8 }
    }
}
"#;

#[test]
fn l9_same_leaf_self_types_in_sibling_modules_are_not_verified() {
    let path = write_fixture("l9", L9_SAME_LEAF_SELF_TYPES_IN_SIBLING_MODULES);
    let path_str = path.to_str().expect("utf8 path").to_string();
    let outcome =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            list_trait_conformance_obligations(&path_str).map(|names| {
                names
                    .into_iter()
                    .map(|name| {
                        let verdict = verify_trait_conformance_obligation(&path_str, &name)
                            .unwrap_or_else(|err| VerifyResult::Error {
                                message: err.to_string(),
                            });
                        (name, verdict)
                    })
                    .collect::<Vec<_>>()
            })
        });
    let _ = std::fs::remove_file(&path);
    eprintln!("[l9] {outcome:?}");
    match outcome {
        Err(err) => assert!(
            err.to_string().contains("both named `S`"),
            "L9: enumeration must refuse the file for the duplicate `S`, got: {err}"
        ),
        Ok(rows) => {
            assert!(
                !rows.is_empty(),
                "L9: the impls must list at least one obligation"
            );
            for (name, verdict) in &rows {
                assert_collision_refused("l9", name, verdict);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SOURCE-CENSUS LIARS — pairs the decl list could not see, and the caller lane.
//
// Every per-impl registry and encoding is keyed by (trait, ERASED self type),
// and `register_trait_impl` merges decls whose erased fields compare equal, so
// the pairs below reached the conformance walk as ONE decl (one Verified row)
// or as two decls whose linking / default-body / impl-`ensures` axioms answered
// each other's callers. Measured (cache off) before the source census; ground truth from the same items compiled with stock rustc.
// ---------------------------------------------------------------------------

/// A CONCRETE-RECEIVER caller into a sibling-impl group must not resolve:
/// `Wc::<u32>::wc(&s)`, `<S as Tm>::m(&s)` and `s.m()` all lower to the trait UF
/// at the erased self type, which cannot name the impl. The refusal is the
/// withheld concrete-receiver resolution ("unknown return type"), NOT an
/// arbitrary error — the single-impl twins in the controls below resolve the
/// very same spellings and verify.
///
/// This says NOTHING about a bound-generic caller (`fn g<T: Wc<u32>>`), which
/// never mentions the self type and still verifies through the trait's own
/// postcondition axiom; see C11 and the header.
fn assert_caller_fails_closed(label: &str, func: &str, verdict: &VerifyResult) {
    match verdict {
        VerifyResult::Error { message } if message.contains("unknown return type for function") => {
        }
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE VERIFY — `{func}` VERIFIED a claim about a call into a group \
             of impls of one trait for one self type, which the engine cannot tell apart"
        ),
        other => panic!(
            "{label}: `{func}` must fail closed at call resolution (the group's concrete-receiver \
             resolution is withheld), got {other:?}"
        ),
    }
}

/// L11, the review BLOCKER: trait arguments that lower to ONE `TrustVcType`.
/// Each pair merged into a single decl before the decl-level collision count,
/// so one row was listed and checked against the FIRST body (1) while the
/// second impl returns 2. Before: one Verified row per pair, and the CLI exited
/// 0 on the `&u8` and set pairs. `u8`/`&u8` and the sets compile with the real
/// macros (impls in separate modules); rustc gives 2 for the second impl.
fn l11_erased_argument_source(first: &str, second: &str, generics: &str) -> String {
    format!(
        r#"
use std::collections::{{BTreeSet, HashSet}};
pub struct S;

#[trust_vc::trait_spec]
pub trait Wc<B> {{
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}}

mod a {{
    use super::*;
    #[trust_vc::trait_impl]
    impl Wc<{first}> for S {{
        fn wc(&self) -> u8 {{ 1u8 }}
    }}
}}

mod b {{
    use super::*;
    #[trust_vc::trait_impl]
    impl{generics} Wc<{second}> for S {{
        fn wc(&self) -> u8 {{ 2u8 }}
    }}
}}

#[trust_vc::ensures(true)]
fn bystander_true() {{
    trust_vc::assert!(true);
}}
"#
    )
}

#[test]
fn l11_trait_arguments_erased_to_one_type_are_not_verified() {
    for (label, first, second, generics) in [
        ("l11_ref", "u8", "&'x u8", "<'x>"),
        ("l11_mut_ref", "u8", "&'static mut u8", ""),
        ("l11_sets", "HashSet<u8>", "BTreeSet<u8>", ""),
        (
            "l11_vec_deque",
            "Vec<u8>",
            "std::collections::VecDeque<u8>",
            "",
        ),
    ] {
        let src = l11_erased_argument_source(first, second, generics);
        let rows = conformance_rows(label, &src);
        assert!(
            !rows.is_empty(),
            "{label}: the collided impls must still list at least one obligation"
        );
        for (name, verdict) in &rows {
            assert_collision_refused(label, name, verdict);
        }
        let bystander = verify_fn(label, &src, "bystander_true");
        assert!(
            matches!(bystander, VerifyResult::Verified),
            "{label}: an unrelated function must not be sunk by the refusal, got {bystander:?}"
        );
    }
}

/// L11b, const trait arguments: every non-type argument lowers to the same
/// `Opaque("<unsupported-trait-generic-arg>")`, so `Kc<1>` and `Kc<2>` merged.
/// Before: one Verified row `Kc<<unsupported-trait-generic-arg>>::k for S`.
const L11B_CONST_ARGUMENTS: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Kc<const N: usize> {
    #[trust_vc::ensures(result == 1u8)]
    fn k(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Kc<1> for S {
    fn k(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Kc<2> for S {
    fn k(&self) -> u8 { 2u8 }
}
"#;

#[test]
fn l11b_const_trait_arguments_are_not_verified() {
    let rows = conformance_rows("l11b", L11B_CONST_ARGUMENTS);
    assert!(!rows.is_empty(), "L11b: the impls must list");
    for (name, verdict) in &rows {
        assert_collision_refused("l11b", name, verdict);
    }
}

/// L11c, same-SPELLED trait arguments that are different types: a module-local
/// `type A` alias (`u8` in one module, `u16` in the other) and a module-local
/// `struct A`. Both headers print `Wc<A>`, so the decls merged. Before: one
/// Verified row each.
const L11C_SAME_SPELLED_ALIASES: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

mod a {
    use super::*;
    pub type A = u8;
    #[trust_vc::trait_impl]
    impl Wc<A> for S {
        fn wc(&self) -> u8 { 1u8 }
    }
}

mod b {
    use super::*;
    pub type A = u16;
    #[trust_vc::trait_impl]
    impl Wc<A> for S {
        fn wc(&self) -> u8 { 2u8 }
    }
}
"#;

const L11C_SAME_SPELLED_STRUCTS: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

mod a {
    pub struct A;
    #[trust_vc::trait_impl]
    impl super::Wc<A> for super::S {
        fn wc(&self) -> u8 { 1u8 }
    }
}

mod b {
    pub struct A;
    #[trust_vc::trait_impl]
    impl super::Wc<A> for super::S {
        fn wc(&self) -> u8 { 2u8 }
    }
}
"#;

#[test]
fn l11c_same_spelled_distinct_trait_arguments_are_not_verified() {
    for (label, src) in [
        ("l11c_alias", L11C_SAME_SPELLED_ALIASES),
        ("l11c_struct", L11C_SAME_SPELLED_STRUCTS),
    ] {
        let rows = conformance_rows(label, src);
        assert!(!rows.is_empty(), "{label}: the impls must list");
        for (name, verdict) in &rows {
            assert_collision_refused(label, name, verdict);
        }
    }
}

/// L12, the review MAJOR without trait arguments: `impl Tm for S` beside
/// `impl<'a> Tm for &'a S`. Both self types erase to `S` and both mint `S__m`,
/// so the decls merged. Before: one Verified row `Tm::m for S`, a caller
/// asserting `<S as Tm>::m(&s) == 1` Verified, and the CLI exited 0 — while
/// `<&S as Tm>::m(&&S) == 2`.
const L12_REFERENCE_SELF_TYPE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Tm {
    #[trust_vc::ensures(result == 1u8)]
    fn m(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Tm for S {
    fn m(&self) -> u8 { 1u8 }
}

mod e {
    use super::*;
    #[trust_vc::trait_impl]
    impl<'a> Tm for &'a S {
        fn m(&self) -> u8 { 2u8 }
    }
}

#[trust_vc::ensures(true)]
fn caller_eq1(s: S) {
    let v: u8 = <S as Tm>::m(&s);
    trust_vc::assert!(v == 1u8);
}
"#;

#[test]
fn l12_impl_for_reference_self_type_is_not_verified() {
    let rows = conformance_rows("l12", L12_REFERENCE_SELF_TYPE);
    assert!(!rows.is_empty(), "L12: the impls must list");
    for (name, verdict) in &rows {
        assert_collision_refused("l12", name, verdict);
    }
    let caller = verify_fn("l12", L12_REFERENCE_SELF_TYPE, "caller_eq1");
    assert_caller_fails_closed("l12", "caller_eq1", &caller);
}

/// L13, the review caller-lane MAJOR: an impl INHERITING a contract-free default
/// (2) beside an override for another trait argument that declares its own
/// `ensures(result == 1)`. The override is the only claimant of `S__d`, so the
/// conformance census saw no collision, and its impl-`ensures` axiom answered
/// calls to the DEFAULT instantiation. Before: `bool_turbofish_eq1` Verified and
/// the CLI exited 0; `bool_return_eq1` came back VacuousTruth ("Assumptions are
/// contradictory") — rustc gives `Dm::<bool>::d(&S) == 2`.
///
/// The override's own conformance row is checked on its merits (its body does
/// establish its `ensures`) and stays Verified: only calls into the group are
/// refused.
const L13_DEFAULT_BESIDE_OVERRIDE_WITH_IMPL_ENSURES: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Dm<B> {
    fn d(&self) -> u8 { 2u8 }
}

#[trust_vc::trait_impl]
impl Dm<bool> for S {}

#[trust_vc::trait_impl]
impl Dm<u32> for S {
    #[trust_vc::ensures(result == 1u8)]
    fn d(&self) -> u8 { 1u8 }
}

#[trust_vc::ensures(true)]
fn bool_turbofish_eq1(s: S) {
    let v: u8 = Dm::<bool>::d(&s);
    trust_vc::assert!(v == 1u8);
}

#[trust_vc::ensures(result == 1u8)]
fn bool_return_eq1(s: S) -> u8 {
    Dm::<bool>::d(&s)
}

#[trust_vc::ensures(true)]
fn bystander_true() {
    trust_vc::assert!(true);
}
"#;

#[test]
fn l13_impl_ensures_of_an_override_do_not_answer_the_default_instantiation() {
    let src = L13_DEFAULT_BESIDE_OVERRIDE_WITH_IMPL_ENSURES;
    for func in ["bool_turbofish_eq1", "bool_return_eq1"] {
        let verdict = verify_fn("l13", src, func);
        assert_caller_fails_closed("l13", func, &verdict);
    }
    let rows = conformance_rows("l13", src);
    let name = "trait impl conformance Dm<u32>::d for S";
    assert_eq!(names(&rows), [name]);
    assert_verified("l13", name, row("l13", &rows, name));
    let bystander = verify_fn("l13", src, "bystander_true");
    assert!(
        matches!(bystander, VerifyResult::Verified),
        "L13: an unrelated function must not be sunk, got {bystander:?}"
    );
}

/// L14, the same group with NO contract anywhere, so no conformance row exists
/// and nothing but the caller can go red. The bool impl's default-body axiom
/// `Dm__d(Box_S(s)) == 2` and the u32 impl's linking axiom
/// `Dm__d(Box_S(s)) == S__d(s)` defined ONE term for two impls. Before: the
/// FALSE `Dm::<u32>::d(&s) == 2` Verified (rustc: 1), and so did the FALSE
/// congruence `Dm::<bool>::d(&s) == Dm::<u32>::d(&s)` (rustc: 2 vs 1).
const L14_CONTRACT_FREE_DEFAULT_BESIDE_OVERRIDE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Dm<B> {
    fn d(&self) -> u8 { 2u8 }
}

#[trust_vc::trait_impl]
impl Dm<bool> for S {}

#[trust_vc::trait_impl]
impl Dm<u32> for S {
    fn d(&self) -> u8 { 1u8 }
}

#[trust_vc::ensures(true)]
fn u32_eq2(s: S) {
    let v: u8 = Dm::<u32>::d(&s);
    trust_vc::assert!(v == 2u8);
}

#[trust_vc::ensures(true)]
fn instantiations_equal(s: S) {
    let a: u8 = Dm::<bool>::d(&s);
    let b: u8 = Dm::<u32>::d(&s);
    trust_vc::assert!(a == b);
}
"#;

/// L15, DISJOINT overrides: each impl overrides a different defaulted method,
/// so no concrete symbol is shared, but `Pm<bool>` overriding `p` beside
/// `Pm<u32>` inheriting it defined `Pm__p(Box_S(s))` twice. Before: the FALSE
/// `Pm::<bool>::p(&s) == 10` Verified (rustc: 1).
const L15_DISJOINT_OVERRIDES: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Pm<B> {
    fn p(&self) -> u8 { 10u8 }
    fn q(&self) -> u8 { 20u8 }
}

#[trust_vc::trait_impl]
impl Pm<bool> for S {
    fn p(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl Pm<u32> for S {
    fn q(&self) -> u8 { 2u8 }
}

#[trust_vc::ensures(true)]
fn bool_p_eq10(s: S) {
    let v: u8 = Pm::<bool>::p(&s);
    trust_vc::assert!(v == 10u8);
}
"#;

/// L16, the call-lane congruence the first fix left open: a
/// contract-free trait, two overriding impls returning 1 and 2, and a caller
/// asserting the two instantiations are equal. Both calls lowered to the ONE
/// term `U__f(Box_S(s))`, so congruence proved the FALSE equality. Before:
/// Verified, with zero conformance obligations in the file.
const L16_TURBOFISH_CONGRUENCE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait U<B> {
    fn f(&self) -> u8;
}

#[trust_vc::trait_impl]
impl U<bool> for S {
    fn f(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl U<u32> for S {
    fn f(&self) -> u8 { 2u8 }
}

#[trust_vc::ensures(true)]
fn instantiations_equal(s: S) {
    let a: u8 = U::<u32>::f(&s);
    let b: u8 = U::<bool>::f(&s);
    trust_vc::assert!(a == b);
}
"#;

#[test]
fn l14_l15_l16_calls_into_a_sibling_impl_group_do_not_resolve() {
    for (label, src, funcs) in [
        (
            "l14",
            L14_CONTRACT_FREE_DEFAULT_BESIDE_OVERRIDE,
            &["u32_eq2", "instantiations_equal"][..],
        ),
        ("l15", L15_DISJOINT_OVERRIDES, &["bool_p_eq10"][..]),
        (
            "l16",
            L16_TURBOFISH_CONGRUENCE,
            &["instantiations_equal"][..],
        ),
    ] {
        for func in funcs {
            let verdict = verify_fn(label, src, func);
            assert_caller_fails_closed(label, func, &verdict);
        }
    }
}

/// L17, an UNMARKED sibling: `impl Wc<u32> for S` without
/// `#[trust_vc::trait_impl]` is never registered, never checked, and its
/// callers resolved through the marked `Wc<bool>` impl. Before: the `Wc<bool>`
/// row Verified and the FALSE caller `Wc::<u32>::wc(&s) == 1` Verified (rustc:
/// 2) — a fully green file. The source census counts unmarked impls.
const L17_UNMARKED_SIBLING: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 1u8 }
}

impl Wc<u32> for S {
    fn wc(&self) -> u8 { 2u8 }
}

#[trust_vc::ensures(true)]
fn caller_u32_eq1(s: S) {
    let v: u8 = Wc::<u32>::wc(&s);
    trust_vc::assert!(v == 1u8);
}
"#;

#[test]
fn l17_unmarked_sibling_impl_is_counted() {
    let rows = conformance_rows("l17", L17_UNMARKED_SIBLING);
    let name = "trait impl conformance Wc<bool>::wc for S";
    assert_eq!(names(&rows), [name]);
    assert_collision_refused("l17", name, row("l17", &rows, name));
    let caller = verify_fn("l17", L17_UNMARKED_SIBLING, "caller_u32_eq1");
    assert_caller_fails_closed("l17", "caller_u32_eq1", &caller);
}

// ---------------------------------------------------------------------------
// SOURCE-CENSUS CONTROLS — the same spellings resolve and verify for ONE impl,
// and a group of one trait does not touch another trait's resolution.
// ---------------------------------------------------------------------------

/// C9: the caller spellings refused above resolve when the trait has a SINGLE
/// impl for the self type — the truthful caller verifies and its liar twin is
/// REFUTED — so the L11-L17 refusals are the group rule, not an unsupported
/// spelling. (The return form is used because it refutes; the assert form of
/// the same liar comes back `EmptyModel` Unknown on this surface.)
const C9_SINGLE_IMPL_TURBOFISH: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 { 1u8 }
}

#[trust_vc::ensures(result == 1u8)]
fn caller_eq1(s: S) -> u8 {
    Wc::<u32>::wc(&s)
}

#[trust_vc::ensures(result == 2u8)]
fn caller_eq2_liar(s: S) -> u8 {
    Wc::<u32>::wc(&s)
}
"#;

const C9_SINGLE_IMPL_QSELF: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Tm {
    #[trust_vc::ensures(result == 1u8)]
    fn m(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Tm for S {
    fn m(&self) -> u8 { 1u8 }
}

#[trust_vc::ensures(result == 1u8)]
fn caller_eq1(s: S) -> u8 {
    <S as Tm>::m(&s)
}

#[trust_vc::ensures(result == 2u8)]
fn caller_eq2_liar(s: S) -> u8 {
    <S as Tm>::m(&s)
}
"#;

fn assert_truth_verifies_and_liar_refuted(label: &str, src: &str) {
    let truth = verify_fn(label, src, "caller_eq1");
    assert!(
        matches!(truth, VerifyResult::Verified),
        "{label}: the single-impl caller must verify, got {truth:?}"
    );
    let liar = verify_fn(label, src, "caller_eq2_liar");
    assert!(
        matches!(liar, VerifyResult::Counterexample { .. }),
        "{label}: the single-impl liar twin must be refuted, got {liar:?}"
    );
}

#[test]
fn c9_single_impl_callers_resolve_on_the_merits() {
    assert_truth_verifies_and_liar_refuted("c9_turbofish", C9_SINGLE_IMPL_TURBOFISH);
    assert_truth_verifies_and_liar_refuted("c9_qself", C9_SINGLE_IMPL_QSELF);
}

/// C10: the group rule is per (trait, self type). A second trait implemented
/// ONCE for the same self type keeps its callers while the first trait's group
/// is refused.
const C10_OTHER_TRAIT_ON_SAME_SELF_TYPE: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait U<B> {
    fn f(&self) -> u8;
}

#[trust_vc::trait_impl]
impl U<bool> for S {
    fn f(&self) -> u8 { 1u8 }
}

#[trust_vc::trait_impl]
impl U<u32> for S {
    fn f(&self) -> u8 { 2u8 }
}

#[trust_vc::trait_spec]
trait Other {
    #[trust_vc::ensures(result == 7u8)]
    fn g(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Other for S {
    fn g(&self) -> u8 { 7u8 }
}

#[trust_vc::ensures(result == 7u8)]
fn caller_eq1(s: S) -> u8 {
    s.g()
}

#[trust_vc::ensures(result == 8u8)]
fn caller_eq2_liar(s: S) -> u8 {
    s.g()
}

#[trust_vc::ensures(true)]
fn group_instantiations_equal(s: S) {
    let a: u8 = U::<u32>::f(&s);
    let b: u8 = U::<bool>::f(&s);
    trust_vc::assert!(a == b);
}
"#;

#[test]
fn c10_other_trait_on_the_same_self_type_keeps_its_callers() {
    let src = C10_OTHER_TRAIT_ON_SAME_SELF_TYPE;
    assert_truth_verifies_and_liar_refuted("c10", src);
    let group = verify_fn("c10", src, "group_instantiations_equal");
    assert_caller_fails_closed("c10", "group_instantiations_equal", &group);
    let rows = conformance_rows("c10", C10_OTHER_TRAIT_ON_SAME_SELF_TYPE);
    let name = "trait impl conformance Other::g for S";
    assert_verified("c10", name, row("c10", &rows, name));
}

// ---------------------------------------------------------------------------
// L18 — SIBLINGS OUTSIDE THE MODULE ITEM LIST (the census residual). `collect_traits` and `collect_source_trait_declarations` walk
// module items, so an impl written inside a function body, inside a
// `const _: () = { .. };` initializer, inside a module nested in a function
// body, or inside another impl's method is never registered and never
// conformance-checked — while Rust applies it CRATE-WIDE. rustc even says so
// while compiling these very shapes: "an `impl` is never scoped, even when it
// is nested inside an item". Ground truth, the five shapes compiled and run:
// `Wc<bool>` → 1, `Wc<u32>` (fn body) → 2, `Wc<i16>` (const block) → 3,
// `Wc<u64>` (fn-local module) → 4, `Wc<i8>` (impl method) → 5.
//
// Measured BEFORE this fix, cache off, every shape: the visible `Wc<bool>` row
// Verified, the FALSE caller `Wc::<u32>::wc(&s) == 1u8` Verified, and the file
// fully GREEN against a hidden body returning 2. The census now walks the whole
// syntax tree, so the visible impl is a group member: its row is refused and
// its callers fail closed.
//
// STILL NOT reachable: an impl produced by expanding a `macro_rules!`
// invocation (`syn` does not expand macros) — see the header.
// ---------------------------------------------------------------------------

/// The L18 fixture: one visible conforming impl, `hidden` written somewhere the
/// module item walk never reaches, and the liar caller into the hidden
/// instantiation. With `hidden` empty this is the CONTROL: one impl, nothing
/// hidden, and the same spellings must resolve and decide on the merits.
fn l18_source(hidden: &str) -> String {
    format!(
        r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {{
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}}

#[trust_vc::trait_impl]
impl Wc<bool> for S {{
    fn wc(&self) -> u8 {{ 1u8 }}
}}

{hidden}

#[trust_vc::ensures(result == 1u8)]
fn caller_eq1(s: S) -> u8 {{
    Wc::<bool>::wc(&s)
}}

#[trust_vc::ensures(result == 2u8)]
fn caller_eq2_liar(s: S) -> u8 {{
    Wc::<bool>::wc(&s)
}}
"#
    )
}

/// The liar caller into the HIDDEN instantiation, appended to the group
/// fixtures only (the control has no such impl, so the call would not compile).
fn l18_hidden_caller(args: &str) -> String {
    format!(
        r#"
#[trust_vc::ensures(true)]
fn caller_hidden_eq1(s: S) {{
    let v: u8 = Wc::<{args}>::wc(&s);
    trust_vc::assert!(v == 1u8);
}}
"#
    )
}

#[test]
fn l18_sibling_impls_the_module_walk_never_reaches_are_counted() {
    for (label, args, hidden) in [
        (
            "l18_fn_body",
            "u32",
            "fn hidden_holder() { #[trust_vc::trait_impl] impl Wc<u32> for S { fn wc(&self) -> u8 { 2u8 } } }",
        ),
        (
            "l18_const_block",
            "i16",
            "const _: () = { #[trust_vc::trait_impl] impl Wc<i16> for S { fn wc(&self) -> u8 { 3u8 } } };",
        ),
        (
            "l18_fn_local_module",
            "u64",
            "fn outer_holder() { mod inner { use super::*; #[trust_vc::trait_impl] impl Wc<u64> for S { fn wc(&self) -> u8 { 4u8 } } } }",
        ),
        (
            "l18_impl_method_body",
            "i8",
            "impl S { fn helper() { #[trust_vc::trait_impl] impl Wc<i8> for S { fn wc(&self) -> u8 { 5u8 } } } }",
        ),
    ] {
        let src = format!("{}{}", l18_source(hidden), l18_hidden_caller(args));
        let rows = conformance_rows(label, &src);
        // The hidden impl has no row of its own — it is not registered — so the
        // VISIBLE impl's row is the whole file verdict, and it must be refused.
        let name = "trait impl conformance Wc<bool>::wc for S";
        assert_eq!(
            names(&rows),
            [name],
            "{label}: the hidden impl is not registered, so exactly one row is listed"
        );
        assert_collision_refused(label, name, row(label, &rows, name));
        assert_caller_fails_closed(label, "caller_hidden_eq1", &verify_fn(label, &src, "caller_hidden_eq1"));
        // Over-rejection, deliberate and measured: the TRUE claim about the
        // visible impl fails closed too, because every caller-lane fact is keyed
        // by (trait, erased self type).
        assert_caller_fails_closed(label, "caller_eq1", &verify_fn(label, &src, "caller_eq1"));
    }
}

/// The L18 control: with nothing hidden, the same file, the same spellings and
/// the same trait resolve — the truthful caller verifies, its liar twin is
/// REFUTED, and the conformance row is Verified. So the refusals above are the
/// hidden sibling, not the `const`/`fn`/`mod` wrapper and not the spelling.
#[test]
fn l18_control_single_impl_with_nothing_hidden_decides_on_the_merits() {
    let src = l18_source("");
    let rows = conformance_rows("l18_control", &src);
    let name = "trait impl conformance Wc<bool>::wc for S";
    assert_eq!(names(&rows), [name]);
    assert_verified("l18_control", name, row("l18_control", &rows, name));
    assert_truth_verifies_and_liar_refuted("l18_control", &src);
}

// ---------------------------------------------------------------------------
// C11 — WHAT THE CALLER-LANE CLOSURE DOES **NOT** COVER.
// `assert_caller_fails_closed` above is about the CONCRETE-RECEIVER lane
// (`Wc::<u32>::wc(&s)`, `<S as Tm>::m(&s)`, `s.m()`), whose resolution this fix
// withholds. A BOUND-GENERIC caller — `fn g<T: Wc<u32>>(t: &T) { t.wc() }` —
// never mentions `S`: it consumes the TRAIT's own postcondition axiom, which is
// published for the trait declaration and justified PER FILE by the conformance
// rows, not per function. It therefore still VERIFIES over a group (measured),
// and the guard is that the file is red.
//
// This is not the group machinery: the CONTROL below reproduces it with a
// SINGLE impl and no group at all, so none of the census code is engaged. It is
// keyed separately (pre-existing hole: "generic-bound caller consumes an
// unjustified trait postcondition axiom"); closing it needs the trait axiom to
// be justified per function, which this fix cannot do.
// ---------------------------------------------------------------------------

const C11_SINGLE_IMPL_CONTROL: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 { 2u8 }
}

#[trust_vc::ensures(true)]
fn g_bound<T: Wc<u32>>(t: &T) {
    let v: u8 = t.wc();
    trust_vc::assert!(v == 1u8);
}
"#;

const C11_GROUP: &str = r#"
struct S;

#[trust_vc::trait_spec]
trait Wc<B> {
    #[trust_vc::ensures(result == 1u8)]
    fn wc(&self) -> u8;
}

#[trust_vc::trait_impl]
impl Wc<bool> for S {
    fn wc(&self) -> u8 { 3u8 }
}

#[trust_vc::trait_impl]
impl Wc<u32> for S {
    fn wc(&self) -> u8 { 2u8 }
}

#[trust_vc::ensures(true)]
fn g_bool<T: Wc<bool>>(t: &T) {
    let v: u8 = t.wc();
    trust_vc::assert!(v == 1u8);
}

#[trust_vc::ensures(true)]
fn g_u32<T: Wc<u32>>(t: &T) {
    let v: u8 = t.wc();
    trust_vc::assert!(v == 1u8);
}
"#;

#[test]
fn c11_bound_generic_caller_is_guarded_only_by_the_file_verdict() {
    // The control: ONE impl returning 2 against `ensures(result == 1)`. Its
    // conformance row is refuted on the merits — a real liar, refuted — and the
    // bound-generic caller was measured Verified all the same.
    let control_rows = conformance_rows("c11_control", C11_SINGLE_IMPL_CONTROL);
    let control_name = "trait impl conformance Wc<u32>::wc for S";
    assert_eq!(names(&control_rows), [control_name]);
    assert_counterexample(
        "c11_control",
        control_name,
        row("c11_control", &control_rows, control_name),
    );

    // The group: both rows refused (the census), both bound-generic callers
    // still Verified.
    let group_rows = conformance_rows("c11_group", C11_GROUP);
    assert_eq!(
        names(&group_rows),
        [
            "trait impl conformance Wc<bool>::wc for S",
            "trait impl conformance Wc<u32>::wc for S",
        ]
    );
    for (name, verdict) in &group_rows {
        assert_collision_refused("c11_group", name, verdict);
    }

    // THE GUARD, and the only one: neither file may be green. If a bound-generic
    // caller verifies while every conformance row of the file also verifies,
    // that is a false verify with nothing left to catch it.
    for (label, src, callers) in [
        ("c11_control", C11_SINGLE_IMPL_CONTROL, &["g_bound"][..]),
        ("c11_group", C11_GROUP, &["g_bool", "g_u32"][..]),
    ] {
        let rows = conformance_rows(label, src);
        assert!(
            !rows.is_empty(),
            "{label}: a file whose impl bodies contradict the trait `ensures` must list \
             conformance obligations; with none, nothing is left to go red"
        );
        let rows_green = rows.iter().all(|(_, v)| v.is_verified());
        let callers_green = callers
            .iter()
            .all(|func| matches!(verify_fn(label, src, func), VerifyResult::Verified));
        assert!(
            !(rows_green && callers_green),
            "{label}: CARDINAL FALSE VERIFY — every bound-generic caller AND every conformance \
             obligation of a file whose impl returns 2 against `ensures(result == 1)` reported \
             Verified; rows: {rows:?}"
        );
    }
}
