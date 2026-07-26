// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Row 296 (const items) slice: a module-level `const` referenced ONLY in a
//! `requires`/`ensures` clause (not the function body) now resolves. Previously
//! `apply_referenced_scalar_consts` scanned only `func.block`, so a const used
//! solely in a contract attribute was never declared and the clause failed to
//! lower. The fix also scans the contract-attribute token streams
//! (`expr_path_idents_in_contract_attrs`).
//!
//! SOUNDNESS: declaring the const's value (`N == 10`) is an unconditionally true
//! fact, and the existing `get_variable_type(..).is_none()` guard prevents it
//! from shadowing a parameter/local. A false consequence still fails closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_cic_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
const N: u64 = 10;
// const ONLY in a requires clause (not the body)
#[trust_vc::requires(x < N)]
#[trust_vc::ensures(result == x)]
fn req_only(x: u64) -> u64 { x }
// const in requires pins the value → the ensures follows
#[trust_vc::requires(x == N)]
#[trust_vc::ensures(result == 10u64)]
fn req_pins(x: u64) -> u64 { x }
// CARDINAL LIAR: ensures result == N but the body returns x (only x < N known)
#[trust_vc::requires(x < N)]
#[trust_vc::ensures(result == N)]
fn ens_liar(x: u64) -> u64 { x }
"#;

#[test]
fn const_referenced_only_in_contract_resolves() {
    for f in ["req_only", "req_pins"] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}`: a const referenced only in a requires/ensures clause should resolve; got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn const_in_contract_liar_fails_closed() {
    assert!(
        !verified(&verify("ens_liar", "ens_liar", SRC)),
        "CARDINAL: `ensures result == N` must NOT verify when the body returns an \
         `x` known only to be `< N`"
    );
}
