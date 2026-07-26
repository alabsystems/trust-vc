// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A discarded `v.pop()` on a Vec local now models the EXACT post-state
//! (`v = v.subrange(0, v.len() - 1)`, the receiver minus its last element)
//! instead of the conservative receiver havoc, so a subsequent `v.len()` / `v[i]`
//! reasons about the popped vector — previously it failed closed ("unresolved
//! variable"/havoc).
//!
//! SOUNDNESS: the model is exact for a non-empty receiver. The EMPTY case is
//! handled by `subrange`'s own `start <= end` precondition — at length 0 this is
//! `subrange(0, -1)`, whose `0 <= -1` obligation is FALSE, so any later use of the
//! receiver is NotProved (fail-closed), NEVER a false-verify. Uses INT arithmetic
//! (`len - 1int`) to avoid a usize underflow check the overflow pass cannot encode.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_pop_{}_{}.rs", std::process::id(), name));
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
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.pop(); trust_vc::assert!(v.len() == 1usize); }
"#;
const LEN_FALSE: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.pop(); trust_vc::assert!(v.len() == 2usize); }
"#;
const ELEM: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(10u32); v.push(20u32); v.pop(); trust_vc::assert!(v[0usize] == 10u32); }
"#;
const ELEM_FALSE: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(10u32); v.push(20u32); v.pop(); trust_vc::assert!(v[0usize] == 20u32); }
"#;
const TWICE: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.push(3u32); v.pop(); v.pop(); trust_vc::assert!(v.len() == 1usize); }
"#;
const POP_PUSH: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.pop(); v.push(9u32); trust_vc::assert!(v.len() == 2usize && v[1usize] == 9u32); }
"#;
// SOUNDNESS: a WRONG claim after popping an EMPTY vec must NOT verify (subrange
// precondition `0 <= -1` fails -> NotProved).
const EMPTY_WRONG: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.pop(); trust_vc::assert!(v.len() == 5usize); }
"#;

const CLEAR: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.clear(); trust_vc::assert!(v.len() == 0usize); }
"#;
const CLEAR_FALSE: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.clear(); trust_vc::assert!(v.len() == 2usize); }
"#;
const TRUNCATE: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(10u32); v.push(20u32); v.push(30u32); v.truncate(2usize); trust_vc::assert!(v.len() == 2usize && v[1usize] == 20u32); }
"#;
const TRUNCATE_BEYOND: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.truncate(5usize); trust_vc::assert!(v.len() == 99usize); }
"#;

const SPLIT_OFF: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.push(3u32); let _ = v.split_off(1usize); trust_vc::assert!(v.len() == 1usize && v[0usize] == 1u32); }
"#;
const SPLIT_OFF_BEYOND: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); let _ = v.split_off(5usize); trust_vc::assert!(v.len() == 99usize); }
"#;
const DRAIN_ALL: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); let _ = v.drain(..); trust_vc::assert!(v.len() == 0usize); }
"#;

const DRAIN_FROM: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.push(3u32); let _ = v.drain(1usize..); trust_vc::assert!(v.len() == 1usize); }
"#;
const DRAIN_TO: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.push(2u32); v.push(3u32); let _ = v.drain(..2usize); trust_vc::assert!(v.len() == 1usize && v[0usize] == 3u32); }
"#;

const RESIZE_SHRINK: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(10u32); v.push(20u32); v.push(30u32); v.resize(1usize, 0u32); trust_vc::assert!(v.len() == 1usize && v[0usize] == 10u32); }
"#;
const RESIZE_GROW: &str = r#"
#[trust_vc::ensures(true)]
fn t() { let mut v: Vec<u32> = Vec::new(); v.push(1u32); v.resize(5usize, 9u32); trust_vc::assert!(v.len() == 5usize); }
"#;

#[test]
fn pop_len_verifies() {
    assert!(
        matches!(verify("len", LEN, "t"), VerifyResult::Verified),
        "pop after 2 pushes must verify `v.len() == 1`"
    );
}
#[test]
fn pop_len_false_counterexamples() {
    assert!(
        matches!(
            verify("lenf", LEN_FALSE, "t"),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: `v.len() == 2` after a pop must COUNTEREXAMPLE"
    );
}
#[test]
fn pop_preserves_first_element() {
    assert!(
        matches!(verify("elem", ELEM, "t"), VerifyResult::Verified),
        "pop keeps the first element: `v[0] == 10`"
    );
}
#[test]
fn pop_element_false_counterexamples() {
    assert!(
        matches!(
            verify("elemf", ELEM_FALSE, "t"),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: `v[0] == 20` (the popped element) must COUNTEREXAMPLE"
    );
}
#[test]
fn pop_twice_verifies() {
    assert!(
        matches!(verify("twice", TWICE, "t"), VerifyResult::Verified),
        "two pops from a 3-element vec must verify `v.len() == 1`"
    );
}
#[test]
fn pop_then_push_verifies() {
    assert!(
        matches!(verify("popush", POP_PUSH, "t"), VerifyResult::Verified),
        "pop then push must verify the length and the pushed element"
    );
}
#[test]
fn empty_pop_wrong_claim_does_not_verify() {
    let r = verify("emptyw", EMPTY_WRONG, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: after popping an EMPTY vec, a wrong `v.len() == 5` must NOT verify \
         (subrange precondition fails, fail-closed); got {r:?}"
    );
}

#[test]
fn clear_empties_verifies() {
    assert!(
        matches!(verify("clr", CLEAR, "t"), VerifyResult::Verified),
        "clear must model the empty post-state: `v.len() == 0`"
    );
}
#[test]
fn clear_false_counterexamples() {
    assert!(
        matches!(
            verify("clrf", CLEAR_FALSE, "t"),
            VerifyResult::Counterexample { .. }
        ),
        "CARDINAL: `v.len() == 2` after clear must COUNTEREXAMPLE"
    );
}
#[test]
fn truncate_keeps_prefix_verifies() {
    assert!(
        matches!(verify("trunc", TRUNCATE, "t"), VerifyResult::Verified),
        "truncate(2) keeps the first 2 elements: len and `v[1]`"
    );
}
#[test]
fn truncate_beyond_len_wrong_does_not_verify() {
    let r = verify("truncb", TRUNCATE_BEYOND, "t");
    assert!(!matches!(r, VerifyResult::Verified),
        "CARDINAL: truncate(5) on a 1-element vec then a wrong `len == 99` must NOT verify          (n > len fails the subrange precondition); got {r:?}");
}

#[test]
fn split_off_keeps_prefix_verifies() {
    assert!(
        matches!(verify("so", SPLIT_OFF, "t"), VerifyResult::Verified),
        "split_off(1) keeps the first element: len 1 and v[0]"
    );
}
#[test]
fn split_off_beyond_len_wrong_does_not_verify() {
    let r = verify("sob", SPLIT_OFF_BEYOND, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: split_off(5) on a 1-element vec then a wrong claim must NOT verify; got {r:?}"
    );
}
#[test]
fn drain_full_empties_verifies() {
    assert!(
        matches!(verify("dr", DRAIN_ALL, "t"), VerifyResult::Verified),
        "drain(..) empties the vec: len 0"
    );
}

#[test]
fn drain_from_keeps_prefix_verifies() {
    assert!(
        matches!(verify("drfrom", DRAIN_FROM, "t"), VerifyResult::Verified),
        "drain(1..) keeps the prefix [0,1): len 1"
    );
}
#[test]
fn drain_to_keeps_suffix_verifies() {
    assert!(
        matches!(verify("drto", DRAIN_TO, "t"), VerifyResult::Verified),
        "drain(..2) keeps the suffix [2,len): len 1, v[0]=3"
    );
}

#[test]
fn resize_shrink_verifies() {
    assert!(
        matches!(verify("rss", RESIZE_SHRINK, "t"), VerifyResult::Verified),
        "resize(1, _) shrinks like truncate: len 1 and v[0]"
    );
}
#[test]
fn resize_grow_wrong_does_not_verify() {
    let r = verify("rsg", RESIZE_GROW, "t");
    assert!(!matches!(r, VerifyResult::Verified),
        "CARDINAL: resize(5,_) GROW on a 1-element vec is unmodeled (subrange precondition fails); a `len == 5` claim must NOT verify; got {r:?}");
}
