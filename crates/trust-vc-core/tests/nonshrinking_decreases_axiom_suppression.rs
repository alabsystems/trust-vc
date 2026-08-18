// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pins that a NON-SHRINKING `#[decreases]` does not buy a recursive spec fn's
//! body axiom — the difference between over-rejection and a false `Verified`.
//!
//! A recursive spec fn's body axiom is only sound if the recursion terminates.
//! `f(n) == f(n) + 1` as an axiom is CONTRADICTORY, and a contradictory premise
//! proves everything, so publishing it on the strength of a merely-PRESENT
//! `#[decreases]` would be a cardinal false `Verified`.
//!
//! WHY THIS FILE EXISTS. `ill_founded_recursive_function_names` documents itself
//! as an "honest partial": its structural stage trusts any cycle whose every
//! member carries a `#[decreases]` WITHOUT proving the measure shrinks, and says
//! the non-shrinking mutual case "is NOT caught here". Read at face value that
//! describes a live false-verify. It is not one — the semantic Stage-2 measure
//! check catches it elsewhere — but nothing pinned that, so a Stage-2 regression
//! would silently open the hole while every local comment still read as intended.
//!
//! Measured cache-off; the four rows discriminate on exactly one axis, whether
//! the measure shrinks:
//!
//! | fixture                                   | verdict | axiom     |
//! |-------------------------------------------|---------|-----------|
//! | well-founded + `decreases`                | Verified| usable    |
//! | non-recursive control                     | Verified| usable    |
//! | recursive, NO `decreases`                 | ctrex   | suppressed|
//! | non-shrinking `decreases`, contradictory  | ctrex   | suppressed|
//!
//! Rows 1-2 are what make rows 3-4 meaningful: without them, "refuted" could
//! just mean spec-fn axioms never work at all.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Well-founded: the measure genuinely shrinks, so the axiom is sound and IS
/// published. `f(0)` must unfold to `1`.
const WELL_FOUNDED: &str = r#"
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn f(n: u64) -> u64 { if n == 0u64 { 1u64 } else { f(n - 1u64) } }

#[trust_vc::ensures(result == 1u64)]
pub fn unfold_base() -> u64 { f(0u64) }
"#;

/// No recursion at all — the baseline that a spec fn's axiom is usable.
const NON_RECURSIVE: &str = r#"
#[trust_vc::spec]
fn g(n: u64) -> u64 { if n == 0u64 { 1u64 } else { 2u64 } }

#[trust_vc::ensures(result == 1u64)]
pub fn unfold_base() -> u64 { g(0u64) }
"#;

/// SELF-recursive with a present but NON-SHRINKING measure, and a body whose
/// axiom is contradictory (`bad(n) == bad(n) + 1`). `exploit` returns 0 while
/// claiming 1, so it can only verify if False is derivable.
const SELF_NON_SHRINKING: &str = r#"
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn bad(n: u64) -> u64 { bad(n) + 1u64 }

#[trust_vc::ensures(result == 1u64)]
pub fn exploit(k: u64) -> u64 { let _w = bad(k); 0u64 }
"#;

/// The MUTUAL analog — the exact case the source comment says "is NOT caught
/// here". Both members carry a non-shrinking `#[decreases]`.
const MUTUAL_NON_SHRINKING: &str = r#"
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn p(n: u64) -> u64 { q(n) + 1u64 }

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn q(n: u64) -> u64 { p(n) }

#[trust_vc::ensures(result == 1u64)]
pub fn exploit(k: u64) -> u64 { let _w = p(k); 0u64 }
"#;

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nsdec_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

/// Capability baseline A. A well-founded recursive spec fn's axiom IS published,
/// so the suppression below is attributable to the measure, not to spec-fn
/// axioms being broadly unusable.
#[test]
fn a_well_founded_recursive_spec_fn_axiom_is_usable() {
    let result = verify("wf", "unfold_base", WELL_FOUNDED);
    assert!(
        matches!(result, VerifyResult::Verified),
        "a shrinking `#[decreases]` must keep the body axiom usable — losing this is \
         over-rejection, not unsoundness, but it would invalidate the suppression tests: \
         {result:?}"
    );
}

/// Capability baseline B. Same, with no recursion in play at all.
#[test]
fn a_non_recursive_spec_fn_axiom_is_usable() {
    let result = verify("nr", "unfold_base", NON_RECURSIVE);
    assert!(
        matches!(result, VerifyResult::Verified),
        "a non-recursive spec fn's body axiom must be usable: {result:?}"
    );
}

/// THE GUARD. A contradictory self-recursive body must not be trusted on the
/// strength of a merely-present `#[decreases]`.
#[test]
fn a_self_recursive_non_shrinking_decreases_does_not_buy_the_axiom() {
    let result = verify("self", "exploit", SELF_NON_SHRINKING);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL: `bad(n) == bad(n) + 1` is contradictory, so publishing its axiom proves \
         anything. `exploit` returns 0 while claiming 1 — verifying means a non-shrinking \
         `#[decreases]` bought the axiom. Got: {result:?}"
    );
}

/// THE GUARD, mutual form — the case the source comment names as uncaught by the
/// structural stage. It is caught, by Stage 2; this pins that it stays caught.
#[test]
fn a_mutually_recursive_non_shrinking_decreases_does_not_buy_the_axiom() {
    let result = verify("mut", "exploit", MUTUAL_NON_SHRINKING);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "CARDINAL: a mutually-recursive pair with non-shrinking `#[decreases]` on both \
         members is contradictory via `p(n) == p(n) + 1`. Verifying means the structural \
         stage's documented gap is no longer covered by the semantic Stage-2 check. \
         Got: {result:?}"
    );
}
