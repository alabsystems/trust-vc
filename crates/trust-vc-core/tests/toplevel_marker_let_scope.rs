// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression guard: a TOP-LEVEL `==>` / `<==>` in an assert whose operand is a
//! LET-BOUND local resolves and is soundly checked.
//!
//! `==>` / `<==>` lower to the `__trust_vc_implies!` / `__trust_vc_iff!` binary
//! MARKER macros. Pre-fix, a top-level marker fell through the scoped-string
//! renderer's `Expr::Macro` arm to the verbatim `extract_expr_string` fallback,
//! so a let-local operand (e.g. `p` in `let p = ..; assert!(p ==> Q)`) was left
//! unresolved ("unresolved variable `p`"). The fix routes the two markers through
//! `format_two_expr_macro`, which scope-substitutes each operand and re-emits the
//! marker. (The inside-a-quantifier case is handled separately, with
//! capture-avoidance, by `scoped_closure_string` — see
//! `forall_let_implies_scope.rs`.)
//!
//! Both directions are pinned: a TRUE marker over a let-local VERIFIES, and a
//! FALSE one is REFUTED (never a false `Verified`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_tlm_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const IMPLIES_TRUE: &str = r#"
#[trust_vc::ensures(true)]
fn t() {
    let p: bool = false;
    trust_vc::assert!(p ==> false);
}
"#;
const IMPLIES_FALSE: &str = r#"
#[trust_vc::ensures(true)]
fn t() {
    let p: bool = true;
    trust_vc::assert!(p ==> false);
}
"#;
const IFF_TRUE: &str = r#"
#[trust_vc::ensures(true)]
fn t() {
    let p: bool = true;
    trust_vc::assert!(p <==> true);
}
"#;
const IFF_FALSE: &str = r#"
#[trust_vc::ensures(true)]
fn t() {
    let p: bool = true;
    trust_vc::assert!(p <==> false);
}
"#;

#[test]
fn true_toplevel_implies_over_let_local_verifies() {
    assert!(
        matches!(verify("impl_t", IMPLIES_TRUE, "t"), VerifyResult::Verified),
        "a true `p ==> false` (p=false) over a let-local must VERIFY, not fail 'unresolved variable `p`'"
    );
}

#[test]
fn false_toplevel_implies_over_let_local_is_refuted() {
    let r = verify("impl_f", IMPLIES_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "a false `p ==> false` (p=true) over a let-local must be REFUTED, never a false Verified; got: {r:?}"
    );
}

#[test]
fn true_toplevel_iff_over_let_local_verifies() {
    assert!(
        matches!(verify("iff_t", IFF_TRUE, "t"), VerifyResult::Verified),
        "a true `p <==> true` (p=true) over a let-local must VERIFY"
    );
}

#[test]
fn false_toplevel_iff_over_let_local_is_refuted() {
    let r = verify("iff_f", IFF_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "a false `p <==> false` (p=true) over a let-local must be REFUTED; got: {r:?}"
    );
}
