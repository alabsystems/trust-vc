// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pins that the concrete-receiver contract key survives reference and alias
//! layers, so no `requires` is dropped by a receiver-TYPE mismatch.
//!
//! `concrete_impl_method_requires` keys on the impl's
//! `concrete_type.to_type_string()` while the call site keys on
//! `receiver_ty.to_type_string()`, and its doc used to warn that a mismatch
//! "e.g. `&S` vs `S`" would fail closed as "a missed obligation, conservative".
//!
//! That warning was wrong twice over, and both halves matter:
//!
//! 1. The mismatch DOES NOT OCCUR for these shapes — reference and alias layers
//!    normalise away before the key is formed. Every case below is refuted.
//! 2. Had it occurred it would NOT have been conservative. A dropped `requires`
//!    lets a precondition-VIOLATING call pass unflagged; that is a missed bug
//!    report, not a false proof, but it is not "conservative" either. Three such
//!    drops were live until `29c4526d`, `2cab5434` and `9852a5e8` — each one
//!    guarded by a copy of that same wording, which is why it is corrected at
//!    every site and pinned here rather than merely deleted.
//!
//! Every fixture VIOLATES `requires(x < 10)` with `x = 999`, so a fired
//! obligation means a non-`Verified` verdict. A `Verified` here is a HOLE: the
//! call-site precondition was never checked.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r#"
#[trust_vc::trait_spec]
pub trait T { #[trust_vc::requires(x < 10u64)] fn f(&self, x: u64) -> u64; }
pub struct S;
#[trust_vc::trait_impl]
impl T for S { fn f(&self, x: u64) -> u64 { x } }
pub type A = S;

#[trust_vc::ensures(result == 0u64)]
pub fn by_shared_ref(s: &S) -> u64 { let _w = s.f(999u64); 0u64 }

#[trust_vc::ensures(result == 0u64)]
pub fn by_value(s: S) -> u64 { let _w = s.f(999u64); 0u64 }

#[trust_vc::ensures(result == 0u64)]
pub fn by_mut_ref(s: &mut S) -> u64 { let _w = s.f(999u64); 0u64 }

#[trust_vc::ensures(result == 0u64)]
pub fn by_double_ref(s: &&S) -> u64 { let _w = s.f(999u64); 0u64 }

#[trust_vc::ensures(result == 0u64)]
pub fn by_alias_ref(s: &A) -> u64 { let _w = s.f(999u64); 0u64 }
"#;

fn verify(func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_rtshape_{}_{}.rs", std::process::id(), func));
    std::fs::write(&p, SRC).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

/// A `Verified` verdict for ANY of these means the obligation was never emitted
/// for that receiver type — the exact drop the corrected comment describes.
#[test]
fn every_reference_and_alias_receiver_shape_still_emits_the_precondition() {
    for func in [
        "by_shared_ref",
        "by_value",
        "by_mut_ref",
        "by_double_ref",
        "by_alias_ref",
    ] {
        let result = verify(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "`{func}`: a call violating `requires(x < 10)` with 999 must not verify — \
             verifying means the receiver type failed to key into the contract map and the \
             precondition was silently dropped. Got: {result:?}"
        );
    }
}
