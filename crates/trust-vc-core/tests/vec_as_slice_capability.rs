// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `v.as_slice()` on a Vec/collection receiver is an IMMUTABLE VIEW with the same
//! elements, so it now renders as the receiver itself (identity) — previously it
//! failed closed ("unsupported method `as_slice()` on type `Seq<..>`") because the
//! encoder has no `as_slice` on a modeled `Seq`. Fires for both a concrete
//! push-chain receiver and a collection-typed param/local. Sound: every read
//! through the slice (`len`/index) equals the same read on the receiver. A false
//! claim must still COUNTEREXAMPLE. (`as_mut_slice` is deliberately NOT folded —
//! a write through it must reach the deref-write path.)

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_slice_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const PARAM_LEN: &str = r#"
#[trust_vc::requires(v.len() >= 2usize)]
#[trust_vc::ensures(true)]
fn t(v: Vec<u32>) { let s = v.as_slice(); trust_vc::assert!(s.len() >= 2usize); }
"#;
const PARAM_LEN_FALSE: &str = r#"
#[trust_vc::requires(v.len() == 3usize)]
#[trust_vc::ensures(true)]
fn t(v: Vec<u32>) { let s = v.as_slice(); trust_vc::assert!(s.len() == 5usize); }
"#;
const PUSHCHAIN_IDX: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(10u32); v.push(20u32); let s = v.as_slice(); trust_vc::assert!(s[1usize] == 20u32); }
"#;

#[test]
fn param_vec_as_slice_len_verifies() {
    assert!(
        matches!(verify("plen", PARAM_LEN, "t"), VerifyResult::Verified),
        "a param `v.as_slice().len()` must equal `v.len()`"
    );
}
#[test]
fn param_vec_as_slice_false_counterexamples() {
    assert!(
        matches!(
            verify("plenf", PARAM_LEN_FALSE, "t"),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: `v.as_slice().len() == 5` with `v.len() == 3` must COUNTEREXAMPLE"
    );
}
#[test]
fn pushchain_as_slice_index_verifies() {
    assert!(
        matches!(verify("pidx", PUSHCHAIN_IDX, "t"), VerifyResult::Verified),
        "a concrete `v.as_slice()[1]` must equal `v[1]`"
    );
}
