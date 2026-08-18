// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS: a `requires` declared on a trait method must gate the impl
//! method's unconditional body axiom EVEN WHEN THE TRAIT IS DECLARED INSIDE A
//! `mod`.
//!
//! `trait_method_declares_requires` iterated `file.items` only, while the
//! collector that REGISTERS the same declarations
//! (`trait_contracts::collect_source_trait_declarations`) recurses into
//! `syn::Item::Mod`. A module-nested trait was therefore a fully supported,
//! contract-bearing shape that the safety gate could not see.
//!
//! The gate's own justification — an unresolved trait "can't be
//! body-axiom-lowered into an obligation, so it stays fail-closed regardless" —
//! is true for a trait genuinely outside the file, and FALSE for a nested one:
//! it is in the file and it is registered. So the body axiom published
//! unconditionally, dropping the precondition, and a call that violates the
//! `requires` could verify.
//!
//! Scope, stated honestly: this arm only admits zero-parameter no-`self`
//! associated fns, so the reachable predicate is over constants and spec fns
//! rather than arguments. Narrow, but the direction is a false-verify.
//!
//! WHAT THESE TESTS DO AND DO NOT SHOW. The divergence they guard against is
//! real and was confirmed by reading: the registry recursed into `mod`, the
//! safety gate did not. But these fixtures do NOT demonstrate the exploit —
//! verified by reverting the fix and re-running, after which all three still
//! pass, so the fixtures are not reaching the body-axiom path that drops the
//! precondition. Something earlier (impl resolution, or the goal failing for an
//! unrelated reason) decides them first.
//!
//! They are therefore a CONSISTENCY guard, not an exploit witness. The
//! load-bearing one is the third: nesting a declaration must not change the
//! verdict. That is exactly the property the defect violated, and it holds
//! whether or not this particular shape can be driven through the gate.
//!
//! A true exploit witness still needs a fixture that provably reaches
//! `trait_method_declares_requires` with a nested declaration. Finding one is
//! tracked; asserting these fixtures do it would be a false claim about my own
//! test.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_trqnm_{}_{}.rs", std::process::id(), tmp_id));
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

/// The trait is declared at TOP LEVEL. This is the control: the gate has always
/// seen this shape, so the requires-bearing method must not publish an
/// unconditional body axiom, and the false postcondition must not verify.
const TOP_LEVEL: &str = r#"
pub trait Cfg {
    #[trust_vc::requires(false)]
    fn limit() -> u64;
}

pub struct S;

#[trust_vc::trait_impl]
impl Cfg for S {
    fn limit() -> u64 { 7u64 }
}

#[trust_vc::ensures(result == 999u64)]
pub fn caller() -> u64 {
    S::limit()
}
"#;

/// The SAME shape with the trait nested in a `mod`. Before the fix the gate
/// could not see the declaration, so `limit`'s body axiom published
/// unconditionally and the goal could be discharged from it.
const NESTED: &str = r#"
pub mod cfg {
    pub trait Cfg {
        #[trust_vc::requires(false)]
        fn limit() -> u64;
    }
}

pub struct S;

#[trust_vc::trait_impl]
impl cfg::Cfg for S {
    fn limit() -> u64 { 7u64 }
}

#[trust_vc::ensures(result == 999u64)]
pub fn caller() -> u64 {
    S::limit()
}
"#;

fn assert_not_verified(label: &str, result: &VerifyResult) {
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{label}: a false postcondition must NOT verify, got {result:?}"
    );
}

#[test]
fn top_level_trait_requires_gates_the_body_axiom() {
    let result = verify("top", "caller", TOP_LEVEL);
    assert_not_verified("top-level control", &result);
}

/// The nested shape must reach the same conclusion. NOTE: this does not fail on
/// the pre-fix code — see the module docs. It pins the intended behaviour, not
/// the exploit.
#[test]
fn module_nested_trait_requires_also_gates_the_body_axiom() {
    let result = verify("nested", "caller", NESTED);
    assert_not_verified("module-nested trait", &result);
}

/// Both shapes must reach the SAME verdict. Stated separately because the defect
/// was precisely a divergence between two views of the same file — the registry
/// recursed into modules and the safety gate did not — and an equality assertion
/// is what pins that they cannot drift apart again.
#[test]
fn nesting_a_trait_declaration_does_not_change_the_verdict() {
    let top = verify("eq_top", "caller", TOP_LEVEL);
    let nested = verify("eq_nested", "caller", NESTED);
    assert_eq!(
        std::mem::discriminant(&top),
        std::mem::discriminant(&nested),
        "nesting a trait in a `mod` must not change the verdict: top={top:?} nested={nested:?}"
    );
}
