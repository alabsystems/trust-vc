// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `v.extend(other)` where `other` is a BY-VALUE Vec local now models the exact
//! concat post-state `v = v.add(other)` (mirror of `append`), instead of the
//! conservative receiver havoc. Only the whole-Vec-by-value argument form is
//! modeled; `&other` / `other.iter()` / a range / an iterator adaptor is not a
//! bare vec-model path, so it declines and keeps the existing havoc (fail-closed).
//! Sound-by-construction: extending by a whole Vec is exactly `v ++ other`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_ext_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const LEN: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); let mut o: Vec<u32> = Vec::new(); o.push(2u32); o.push(3u32); v.extend(o); trust_vc::assert!(v.len() == 3usize); }
"#;
const LEN_FALSE: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); let mut o: Vec<u32> = Vec::new(); o.push(2u32); o.push(3u32); v.extend(o); trust_vc::assert!(v.len() == 2usize); }
"#;
const ELEM: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(10u32); let mut o: Vec<u32> = Vec::new(); o.push(20u32); v.extend(o); trust_vc::assert!(v[0usize] == 10u32 && v[1usize] == 20u32); }
"#;

#[test]
fn extend_vec_len_verifies() {
    assert!(
        matches!(verify("len", LEN, "t"), VerifyResult::Verified),
        "v.extend(o) must model `v = v ++ o`, so `v.len() == 3`"
    );
}
#[test]
fn extend_vec_false_counterexamples() {
    assert!(
        matches!(
            verify("lenf", LEN_FALSE, "t"),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: `v.len() == 2` after extend must COUNTEREXAMPLE"
    );
}
#[test]
fn extend_vec_element_correctness_verifies() {
    assert!(
        matches!(verify("elem", ELEM, "t"), VerifyResult::Verified),
        "extend preserves order: v[0] from v, v[1] from o"
    );
}
