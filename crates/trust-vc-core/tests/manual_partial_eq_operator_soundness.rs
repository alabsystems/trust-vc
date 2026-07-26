// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL / SOUNDNESS REGRESSION: the `==` / `!=` OPERATOR did not enforce the
//! Structural gate. A datatype with a hand-written NON-structural `impl PartialEq`
//! (`fn eq(&self, _) -> bool { false }`) still had its `==` operator lowered to the
//! structural SMT equality, so an exec `fn f(a: T) -> bool { a == a }` with
//! `#[ensures(result == true)]` VERIFIED — while the custom impl returns `false`
//! at runtime, violating the postcondition on every call. Found by the 2026-07-24
//! adversarial re-audit (row 365 Structural equality).
//!
//! FIX: track datatypes with a hand-written `impl PartialEq` (`manual_partial_eq_types`)
//! and fail-close the `==`/`!=` operator on them — directly, or transitively through
//! a field (cycle-guarded for recursive datatypes). This mirrors the `.eq()` METHOD
//! gate. It is fail-closed and does NOT over-reject: a `#[derive(PartialEq)]`
//! datatype stays structural, and a datatype with NO `PartialEq` (reachable only via
//! spec `==`, which IS extensional structural equality in Verus) is unaffected.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    std::env::set_var("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_mpe_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func)
        .unwrap_or_else(|e| VerifyResult::Error { message: e.to_string() });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
#[derive(Clone, Copy, Eq)]
struct ManualEq { v: u64 }
impl PartialEq for ManualEq {
    fn eq(&self, _other: &Self) -> bool { false }
}

// FALSE-VERIFY: real value is `false` (custom eq), yet `result == true`.
#[trust_vc::ensures(result == true)]
fn fv_exec_op_reflexive(a: ManualEq) -> bool { a == a }

// FALSE-VERIFY (transitive): derived wrapper delegates to ManualEq::eq.
#[derive(Clone, Copy, PartialEq, Eq)]
struct WrapManual { m: ManualEq }
#[trust_vc::ensures(result == true)]
fn fv_nested_op_reflexive(a: WrapManual) -> bool { a == a }

// LEGIT (derived struct → structural `==` is correct): must VERIFY.
#[derive(Clone, Copy, PartialEq, Eq)]
struct DerivedEq { v: u64 }
#[trust_vc::ensures(result == true)]
fn legit_derived_op_reflexive(a: DerivedEq) -> bool { a == a }

// LEGIT (derived enum): must VERIFY.
#[derive(PartialEq, Eq)]
enum ColorD { Red, Green }
#[trust_vc::ensures(result == true)]
fn legit_derived_enum_reflexive(c: ColorD) -> bool { c == c }
"#;

#[test]
fn manual_partial_eq_operator_false_verify_is_refuted() {
    for f in ["fv_exec_op_reflexive", "fv_nested_op_reflexive"] {
        let r = verify(f, f, SRC);
        assert!(
            !verified(&r),
            "CARDINAL: `{f}`: `==` on a datatype with a hand-written non-structural \
             `PartialEq` must NOT structural-lower (its exec `==` returns `false`) — \
             the false postcondition `result == true` must not verify; got {r:?}"
        );
    }
}

#[test]
fn derived_partial_eq_operator_still_verifies() {
    for f in ["legit_derived_op_reflexive", "legit_derived_enum_reflexive"] {
        let r = verify(f, f, SRC);
        assert!(
            verified(&r),
            "`{f}`: a `#[derive(PartialEq)]` datatype's `==` IS the structural equality \
             and must still verify (no over-rejection); got {r:?}"
        );
    }
}
