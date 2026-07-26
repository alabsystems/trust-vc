// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Trait-impl conformance is ATTRIBUTED to the IMPL, not to whatever function
//! happened to be verified in the same file — and EVERY impl is still checked.
//!
//! WHY THIS EXISTS. Conformance used to be folded into every function's verdict:
//! one deliberately non-conforming impl sank every unrelated function in the
//! file. That made upstream Verus trait files structurally unportable (upstream
//! compiles each `test_verify_one_file!` case as its own file, so a violating
//! impl can never touch a sibling; our port files must carry a file's conforming
//! AND violating impls together — upstream
//! `returns_postcondition.rs::trait_returns_on_trait_method_decl` pins exactly
//! this: the generic caller `test_call<T: Tr>` VERIFIES while impls Y/Z/W of
//! that same trait FAIL).
//!
//! The fix moves the BLAME, never the CHECK. The obvious alternative — skipping
//! conformance for impls the query does not reach — is CARDINALLY UNSOUND: an
//! upstream file whose non-conforming impl has no in-file caller still expects
//! `Err`, so skipping it reports `Verified` where Verus errors, i.e. proving MORE
//! than Verus. See the internal conformance-attribution design note.
//!
//! These guards pin the soundness contract of the attribution design:
//!
//!   1. an unrelated function is no longer sunk, AND the non-conforming impl's
//!      OWN obligation still counterexamples when addressed by name;
//!   2. THE CARDINAL ONE — a non-conforming impl that NOTHING in the file calls
//!      is STILL listed and STILL refuted. If it can go unreported, the change is
//!      unsound;
//!   3. an EMPTY impl (`impl Tr for bool {}`), which has no syn method item to
//!      enumerate at all, is listed and its inherited violating default refuted;
//!   4. the enumeration is COMPLETE — a conforming and a violating impl in the
//!      same file both appear, so nothing can hide behind a sibling.
//!
//! A regression in 2 or 3 (an impl that goes unlisted or reports `Verified`) is a
//! CARDINAL soundness failure, not a completeness loss.

use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

/// Writes `src` to a UNIQUE path (parallel test threads must not race on one
/// fixture — see the same fix in `trait_conformance_body_shapes.rs`).
fn fixture(src: &str, case: &str) -> std::path::PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);

    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_conf_attr_{}_{}_{case}.rs",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, src).expect("write fixture");
    path
}

fn obligations(path: &std::path::Path) -> Vec<String> {
    list_trait_conformance_obligations(path.to_str().unwrap())
        .unwrap_or_else(|err| panic!("conformance obligations should enumerate: {err}"))
}

fn verify_obligation(path: &std::path::Path, name: &str) -> VerifyResult {
    verify_trait_conformance_obligation(path.to_str().unwrap(), name).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    })
}

fn verify_fn(path: &std::path::Path, func: &str) -> VerifyResult {
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    })
}

/// The impl's OWN obligation must COUNTEREXAMPLE. Stricter than `!Verified` on
/// purpose: an `Error` would mean the obligation stopped being CHECKED (the body
/// never reached the solver), which would hollow the guard out — the test would
/// "pass" while testing nothing.
fn assert_refuted(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE-VERIFY — a contract-violating impl's own conformance \
             obligation reported Verified. The impl was never checked, so trust-vc certifies a \
             file that Verus rejects."
        ),
        other => panic!(
            "{label}: expected a conformance Counterexample (proving the impl body actually \
             reached the solver), got {other:?}"
        ),
    }
}

// ---------------------------------------------------------------------------
// (1) A conforming trait + a NON-conforming trait + a function touching neither.
// ---------------------------------------------------------------------------

const MIXED: &str = r#"
#[trust_vc::trait_spec]
trait Good {
    #[trust_vc::ensures(result >= 10)]
    fn get(&self) -> i32;
}

struct GoodWidget(i32);

#[trust_vc::trait_impl]
impl Good for GoodWidget {
    fn get(&self) -> i32 { 20 }
}

#[trust_vc::trait_spec]
trait Bad {
    #[trust_vc::ensures(result >= 10)]
    fn get(&self) -> i32;
}

struct BadWidget(i32);

#[trust_vc::trait_impl]
impl Bad for BadWidget {
    fn get(&self) -> i32 { 0 }
}

#[trust_vc::requires(x < 100u32)]
#[trust_vc::ensures(result == x + 1u32)]
fn untouched(x: u32) -> u32 {
    x + 1u32
}
"#;

/// The unrelated function VERIFIES — it is no longer sunk by an impl it has
/// nothing to do with. (Pre-attribution this returned the `Bad` impl's
/// conformance counterexample.)
#[test]
fn untouched_function_is_not_sunk_by_an_unrelated_nonconforming_impl() {
    let path = fixture(MIXED, "untouched");
    let result = verify_fn(&path, "untouched");
    let _ = std::fs::remove_file(&path);
    match result {
        VerifyResult::Verified => {}
        other => panic!(
            "expected VERIFIED: `untouched` touches neither trait, so no other impl's \
             conformance may be folded into its verdict. Got {other:?}"
        ),
    }
}

/// ...and the violating impl is STILL refuted, addressed by its own name. The
/// conforming sibling still verifies, so the check is discriminating rather than
/// blanket-failing.
#[test]
fn nonconforming_impl_is_refuted_by_name_while_conforming_sibling_verifies() {
    let path = fixture(MIXED, "by_name");
    let names = obligations(&path);
    let bad = "trait impl conformance Bad::get for BadWidget".to_string();
    let good = "trait impl conformance Good::get for GoodWidget".to_string();
    assert!(
        names.contains(&bad) && names.contains(&good),
        "both impls must be enumerated as addressable obligations, got {names:?}"
    );

    let bad_result = verify_obligation(&path, &bad);
    let good_result = verify_obligation(&path, &good);
    let _ = std::fs::remove_file(&path);

    assert_refuted("violating impl (Bad::get for BadWidget)", bad_result);
    match good_result {
        VerifyResult::Verified => {}
        other => panic!(
            "the CONFORMING impl must still verify (the check must discriminate, not \
             blanket-fail): {other:?}"
        ),
    }
}

// ---------------------------------------------------------------------------
// (2) THE CARDINAL ONE: a non-conforming impl NOTHING in the file calls.
// ---------------------------------------------------------------------------

/// `Orphan` is implemented by `Stray` with a body that violates the contract,
/// and NOTHING in the file mentions either — no caller, no generic bound. Verus
/// still errors on this file. If reachability/liveness ever gates the check, this
/// impl silently disappears and trust-vc reports a clean file: proving MORE than
/// Verus, the cardinal sin.
const UNCALLED: &str = r#"
#[trust_vc::trait_spec]
trait Orphan {
    #[trust_vc::ensures(result >= 10)]
    fn get(&self) -> i32;
}

struct Stray(i32);

#[trust_vc::trait_impl]
impl Orphan for Stray {
    fn get(&self) -> i32 { 0 }
}

#[trust_vc::requires(x < 100u32)]
#[trust_vc::ensures(result == x + 1u32)]
fn lonely(x: u32) -> u32 {
    x + 1u32
}
"#;

#[test]
fn nonconforming_impl_with_no_caller_is_still_listed_and_refuted() {
    let path = fixture(UNCALLED, "uncalled");
    let names = obligations(&path);
    let target = "trait impl conformance Orphan::get for Stray".to_string();
    assert!(
        names.contains(&target),
        "CARDINAL: an impl NOTHING in the file calls must still be ENUMERATED — an unlisted \
         obligation is an unchecked one, and `cargo trust-vc check` would certify a file Verus \
         rejects. Got {names:?}"
    );
    let result = verify_obligation(&path, &target);
    let _ = std::fs::remove_file(&path);
    assert_refuted("uncalled violating impl (Orphan::get for Stray)", result);
}

// ---------------------------------------------------------------------------
// (3) An EMPTY impl whose inherited DEFAULT body violates the contract.
// ---------------------------------------------------------------------------

/// `impl Tr for bool {}` supplies NO method item, so there is nothing in the AST
/// to enumerate — the obligation must come from the trait/impl decls. The
/// inherited default body returns `false` while the contract promises
/// `returns(true)`.
const EMPTY_IMPL: &str = r#"
#[trust_vc::trait_spec]
trait Tr: Sized {
    #[trust_vc::returns(true)]
    fn m(self) -> bool {
        false
    }
}

#[trust_vc::trait_impl]
impl Tr for bool {}
"#;

#[test]
fn empty_impl_with_violating_default_is_listed_and_refuted() {
    let path = fixture(EMPTY_IMPL, "empty_impl");
    let names = obligations(&path);
    let target = "trait impl conformance Tr::m for bool".to_string();
    assert!(
        names.contains(&target),
        "an EMPTY impl has no syn method item, so the obligation must be derived from the \
         trait/impl decls — otherwise the inherited default body goes unchecked while its \
         contract axiom still reaches callers. Got {names:?}"
    );
    let result = verify_obligation(&path, &target);
    let _ = std::fs::remove_file(&path);
    assert_refuted(
        "empty impl inheriting a violating default (Tr::m for bool)",
        result,
    );
}

/// A file with NO functions at all still enumerates and checks its impls: the
/// conformance context is built from the FILE, not from a function.
#[test]
fn file_with_no_functions_still_enumerates_its_impls() {
    let path = fixture(EMPTY_IMPL, "no_fns");
    let names = obligations(&path);
    let _ = std::fs::remove_file(&path);
    assert_eq!(
        names,
        vec!["trait impl conformance Tr::m for bool".to_string()],
        "a file whose only content is a trait + empty impl must still have a checkable \
         conformance obligation"
    );
}

// ---------------------------------------------------------------------------
// (4) NON-VACUITY. Attribution must not buy caller-`Verified` with an
//     inconsistent axiom set.
// ---------------------------------------------------------------------------

/// THE VACUITY CONTROL. A caller of a NON-conforming impl now verifies (it
/// assumes the declared contract — exactly what Verus does; the impl's violation
/// is reported against the impl, and the FILE still fails). That is only sound if
/// the caller's axiom set stays CONSISTENT. If the impl's body axiom (`get() ==
/// 0`) and its contract axiom (`get() >= 10`) were BOTH in the caller's query,
/// the query would be inconsistent and the caller would prove ANYTHING —
/// including `assert!(false)`, which Verus reports as an error. Then a port case
/// pinned "verified" could be verified for a junk reason.
///
/// Both shapes — CONCRETE receiver and GENERIC dispatch — must still refute
/// `assert!(false)` after calling into the violating impl.
const VACUITY: &str = r#"
#[trust_vc::trait_spec]
trait Broken {
    #[trust_vc::ensures(result >= 10)]
    fn get(&self) -> i32;
}

struct Rotten(i32);

#[trust_vc::trait_impl]
impl Broken for Rotten {
    fn get(&self) -> i32 { 0 }
}

#[trust_vc::ensures(true)]
fn concrete_caller_then_false(r: Rotten) {
    let v = r.get();
    trust_vc::assert!(v >= 10);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn generic_caller_then_false<T: Broken>(t: T) {
    let v = t.get();
    trust_vc::assert!(v >= 10);
    trust_vc::assert!(false);
}
"#;

#[test]
fn caller_of_a_nonconforming_impl_still_refutes_assert_false() {
    let path = fixture(VACUITY, "vacuity");
    let concrete = verify_fn(&path, "concrete_caller_then_false");
    let generic = verify_fn(&path, "generic_caller_then_false");
    let conformance = verify_obligation(&path, "trait impl conformance Broken::get for Rotten");
    let _ = std::fs::remove_file(&path);

    for (label, result) in [
        ("concrete receiver", concrete),
        ("generic dispatch", generic),
    ] {
        match result {
            VerifyResult::Counterexample { .. } => {}
            VerifyResult::Verified => panic!(
                "{label}: CARDINAL — `assert!(false)` VERIFIED after calling a NON-conforming \
                 impl. The caller's axiom set is INCONSISTENT (it holds both the impl's body \
                 and its violated contract), so attribution is buying caller-Verified with \
                 vacuity: it would prove anything, and every `verified` port case in such a \
                 file would be junk."
            ),
            other => panic!("{label}: expected `assert!(false)` to be refuted, got {other:?}"),
        }
    }
    // ...and the impl itself is still refuted, so the FILE fails, exactly as
    // Verus rejects it.
    assert_refuted("violating impl behind the vacuity control", conformance);
}

// ---------------------------------------------------------------------------
// (5) Fail-closed addressing.
// ---------------------------------------------------------------------------

/// A name that is not an obligation of this file must ERROR, never `Verified`. A
/// mis-addressed obligation that answered `Verified` would let a typo in the
/// check harness certify an unchecked impl.
#[test]
fn unknown_obligation_name_fails_closed() {
    let path = fixture(EMPTY_IMPL, "unknown_name");
    let result = verify_obligation(&path, "trait impl conformance Nope::nope for bool");
    let _ = std::fs::remove_file(&path);
    match result {
        VerifyResult::Error { .. } => {}
        other => panic!(
            "an unknown conformance obligation name must fail CLOSED (Error), never be \
             mistaken for a discharged obligation. Got {other:?}"
        ),
    }
}
