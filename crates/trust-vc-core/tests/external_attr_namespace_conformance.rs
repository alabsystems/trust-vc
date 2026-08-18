// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS: only trust-vc's OWN `#[trust_vc::external]` may skip trait-impl
//! body conformance. Another tool's `external` must not.
//!
//! `#[external]` was matched by trailing path segment only, so
//! `#[verifier::external]` — or any `#[whatever::external]` — granted trust-vc's
//! trust hatch. That hatch skips body conformance while the trait's
//! `forall self, params. requires ==> ensures` axiom stays published to callers,
//! so honouring another tool's attribute is a proof hole with someone else's
//! name on it. In Verus, `#[verifier::external]` means "outside the verification
//! universe", NOT "trust this body against a published in-file contract".
//!
//! These assert the EFFECT, not the parse. The fix was landed with a unit-level
//! check only, because the entry that exercises conformance was not obvious;
//! `list_trait_conformance_obligations` / `verify_trait_conformance_obligation`
//! are the public API that reaches it, and they take a file path.
//!
//! Each fixture contains an impl whose body VIOLATES the trait's declared
//! `ensures` (returns 2 where the contract says 1). Whether that violation is
//! caught is exactly what the hatch controls, so the obligation list is the
//! observable: a skipped impl contributes no obligation, an examined one
//! contributes an obligation that must be refuted.

use trust_vc_core::{list_trait_conformance_obligations, verify_trait_conformance_obligation};

fn write_fixture(tmp_id: &str, src: &str) -> String {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_extns_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    p.to_str().expect("utf8 path").to_string()
}

const FOREIGN_NAMESPACE: &str = r#"
#[trust_vc::trait_spec]
pub trait T { #[trust_vc::ensures(result == 1u64)] fn f(&self) -> u64; }
pub struct Honest;
#[trust_vc::trait_impl]
impl T for Honest { fn f(&self) -> u64 { 2u64 } }

pub struct Foreign;
#[trust_vc::trait_impl]
#[verifier::external]
impl T for Foreign { fn f(&self) -> u64 { 2u64 } }
"#;

const OWN_NAMESPACE: &str = r#"
#[trust_vc::trait_spec]
pub trait T { #[trust_vc::ensures(result == 1u64)] fn f(&self) -> u64; }
pub struct Honest;
#[trust_vc::trait_impl]
impl T for Honest { fn f(&self) -> u64 { 2u64 } }

pub struct Hatched;
#[trust_vc::trait_impl]
#[trust_vc::external]
impl T for Hatched { fn f(&self) -> u64 { 2u64 } }
"#;

#[test]
fn a_foreign_external_attribute_does_not_skip_conformance() {
    let path = write_fixture("foreign", FOREIGN_NAMESPACE);
    let names = list_trait_conformance_obligations(&path).expect("list obligations");
    let _ = std::fs::remove_file(&path);

    assert_eq!(
        names.len(),
        2,
        "`#[verifier::external]` must NOT grant trust-vc's hatch, so BOTH impls owe a \
         conformance obligation; got {names:?}"
    );
    assert!(
        names.iter().any(|n| n.contains("Foreign")),
        "the foreign-attributed impl must still be examined: {names:?}"
    );
}

#[test]
fn a_foreign_external_impl_is_still_refuted_when_its_body_violates_the_contract() {
    let path = write_fixture("foreign_verdict", FOREIGN_NAMESPACE);
    let names = list_trait_conformance_obligations(&path).expect("list obligations");
    let target = names
        .iter()
        .find(|n| n.contains("Foreign"))
        .expect("foreign impl owes an obligation")
        .clone();
    let verdict = verify_trait_conformance_obligation(&path, &target).expect("verify obligation");
    let _ = std::fs::remove_file(&path);

    assert!(
        matches!(verdict, trust_vc_core::VerifyResult::Counterexample { .. }),
        "a body returning 2 against `ensures(result == 1)` must be refuted, not merely \
         unexamined: {verdict:?}"
    );
}

/// The counterpart. trust-vc's OWN attribute is a documented trust hatch and must
/// keep working — without this, the fix above could be "tightened" into rejecting
/// every `external`, silently deleting a deliberate capability.
#[test]
fn trust_vcs_own_external_attribute_still_skips_conformance() {
    let path = write_fixture("own", OWN_NAMESPACE);
    let names = list_trait_conformance_obligations(&path).expect("list obligations");
    let _ = std::fs::remove_file(&path);

    assert_eq!(
        names.len(),
        1,
        "`#[trust_vc::external]` is the documented hatch and must still skip conformance, \
         leaving only the honest impl's obligation; got {names:?}"
    );
    assert!(
        !names.iter().any(|n| n.contains("Hatched")),
        "the trust-vc-attributed impl must be skipped: {names:?}"
    );
}
