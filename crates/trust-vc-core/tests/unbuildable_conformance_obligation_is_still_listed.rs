// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pins the ordering invariant that keeps an UNBUILDABLE conformance obligation
//! from vanishing silently.
//!
//! `register_trait` publishes `forall self. Trait__m(self) <ensures>` for every
//! trait method unconditionally, and a generic-bounded caller
//! `fn g<T: Trait>(t: T) { t.m() }` consumes it directly. For a trait with NO
//! impl, `verify_implless_trait_defaults` is what justifies that axiom by
//! checking the default body against its `ensures`.
//!
//! When the conformance context cannot be BUILT, that pass does:
//!
//! ```ignore
//! Err(_) => match walk.unbuildable(&obligation_name) {
//!     Some(result) => return result,  // addressed BY NAME -> fail-closed Unknown
//!     None => continue,               // otherwise -> skipped
//! },
//! ```
//!
//! and the `continue` is justified as "fail SAFE ... no worse than the prior
//! (no-check) state". "No worse than before" is NOT the same as sound: a skipped
//! conformance check leaves the published postcondition axiom unjustified, and a
//! generic caller consumes it.
//!
//! IT IS SOUND TODAY, FOR A REASON WORTH PINNING. `ConformanceWalk` has exactly
//! two variants, `List` and `VerifyOne` — there is no aggregate verify — and
//! `select` PUSHES THE NAME BEFORE the build is attempted. So an unbuildable
//! obligation is still enumerated, and any driver that lists-then-verifies-each
//! reaches `VerifyOne`, where `unbuildable` fails closed. The `None => continue`
//! arm is only reachable under `List`, where continuing is correct.
//!
//! Two things hold that up. Adding a walk variant is compiler-enforced, because
//! `unbuildable` matches on `self` exhaustively. THE ORDERING IS NOT: move
//! `select` after the build attempt and unbuildable obligations disappear from
//! the list, so nothing ever addresses them by name and the skip becomes the
//! silent hole the comment describes. Nothing pinned that ordering; this does.
//!
//! Measured cache-off. The fixture's default body returns 2 against
//! `ensures(result == 1)`, so it is BOTH unbuildable and non-conforming — if it
//! ever starts building, the violation is caught on the merits and this test
//! still passes for the right reason.

use trust_vc_core::{list_trait_conformance_obligations, verify_trait_conformance_obligation};

/// `[2u64, 3u64][0]` does not lower onto the abstract conformance surface (it
/// needs a collection constructor absent from that context), and it returns 2
/// against `ensures(result == 1)`.
const UNBUILDABLE_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
pub trait T {
    #[trust_vc::ensures(result == 1u64)]
    fn m(&self) -> u64 { let a = [2u64, 3u64]; a[0] }
}
"#;

/// A body that DOES lower and violates the same `ensures`. Without this control,
/// "listed and not Verified" could hold trivially for every trait.
const BUILDABLE_VIOLATING_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
pub trait T {
    #[trust_vc::ensures(result == 1u64)]
    fn m(&self) -> u64 { 2u64 }
}
"#;

fn write_fixture(tmp_id: &str, src: &str) -> String {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_unbld_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    p.to_str().expect("utf8 path").to_string()
}

/// THE PIN. An obligation whose context cannot be built must still be
/// ENUMERATED — that is what gives a driver something to address by name.
#[test]
fn an_unbuildable_default_conformance_obligation_is_still_enumerated() {
    let path = write_fixture("list", UNBUILDABLE_DEFAULT);
    let names = list_trait_conformance_obligations(&path).expect("list obligations");
    let _ = std::fs::remove_file(&path);

    assert!(
        names.iter().any(|n| n.contains("T::m")),
        "REGRESSION: an unbuildable default-conformance obligation vanished from the list. \
         `select` must record the name BEFORE the build attempt — otherwise nothing addresses \
         it by name, the `None => continue` arm skips it silently, and the unjustified \
         postcondition axiom is trusted by a generic caller. Got: {names:?}"
    );
}

/// The other half: once addressed by name, it must fail CLOSED rather than
/// report success for a body that was never actually checked.
#[test]
fn an_unbuildable_default_conformance_obligation_fails_closed_when_addressed() {
    let path = write_fixture("verify", UNBUILDABLE_DEFAULT);
    let names = list_trait_conformance_obligations(&path).expect("list obligations");
    let target = names
        .iter()
        .find(|n| n.contains("T::m"))
        .expect("obligation enumerated")
        .clone();
    let verdict = verify_trait_conformance_obligation(&path, &target).expect("verify obligation");
    let _ = std::fs::remove_file(&path);

    assert!(
        !matches!(verdict, trust_vc_core::VerifyResult::Verified),
        "REGRESSION: an obligation whose body never lowered onto the conformance surface \
         reported success. It must fail closed — reporting Verified for a body that was not \
         checked is exactly the unjustified-axiom hole. Got: {verdict:?}"
    );
}

/// The control. A default body that DOES lower and violates its `ensures` is
/// refuted on the merits, so the assertions above are not vacuously true.
#[test]
fn a_buildable_violating_default_is_refuted_on_the_merits() {
    let path = write_fixture("control", BUILDABLE_VIOLATING_DEFAULT);
    let names = list_trait_conformance_obligations(&path).expect("list obligations");
    let target = names
        .iter()
        .find(|n| n.contains("T::m"))
        .expect("obligation enumerated")
        .clone();
    let verdict = verify_trait_conformance_obligation(&path, &target).expect("verify obligation");
    let _ = std::fs::remove_file(&path);

    assert!(
        matches!(verdict, trust_vc_core::VerifyResult::Counterexample { .. }),
        "control: a lowerable default body returning 2 against `ensures(result == 1)` must be \
         refuted with a counterexample: {verdict:?}"
    );
}
