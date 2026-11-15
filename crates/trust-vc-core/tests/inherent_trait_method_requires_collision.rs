// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard for the THIRD member of the call-site-precondition drop class.
//!
//! When a type has BOTH an inherent requires-bearing `m` and a trait-supplied
//! requires-bearing `m`, `vc_extraction.rs` dropped the colliding `(S, m)` key
//! so NEITHER contract fired. The justification in the source read "a missed
//! obligation is always sound" — TRUE FOR AN ASSUMPTION AND FALSE FOR A
//! `requires`. A precondition-violating call passed unflagged.
//!
//! Siblings, same class, both fixed: the unresolvable-receiver drop
//! (`body_extract.rs`, `receiver_shape_precondition_drop_witness.rs`) and the
//! two-trait ambiguity drop (`trait_contracts.rs`,
//! `ambiguous_trait_method_requires_conjunction.rs`).
//!
//! CONJUNCTION, NOT DISJUNCTION. The call is one of the candidates and we cannot
//! tell which, so requiring BOTH is stronger than either — it over-rejects and
//! never misses. The disjunction is weaker than either and would preserve the
//! hole. Here the inherent `m` requires `k < 10` and the trait `m` requires
//! `k > 100`, so the violating call `s.m(5)` satisfies the disjunction.
//!
//! Measured three ways, cache-off, with the fix stashed and restored:
//!
//! | fixture                          | HEAD         | fixed     |
//! |----------------------------------|--------------|-----------|
//! | inherent + trait, violating call | **Verified** | NotProved |
//! | inherent only, satisfying call   | Verified     | Verified  |
//! | inherent only, violating call    | NotProved    | NotProved |
//!
//! Only the colliding row moves. The verdict is `NotProved` rather than a
//! counterexample because this path carries a PRE-EXISTING quantifier
//! incompleteness — the third row shows the same `NotProved` at HEAD and after,
//! so it is not attributable to this change. `NotProved` is a failing verdict
//! (Verus-faithful incompleteness-to-failure), so the violating program is
//! rejected either way; the assertion is written as "not Verified" so it stays
//! correct if that incompleteness is later closed and the verdict sharpens into
//! a counterexample.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// `S` has an inherent `m` requiring `k < 10` AND a trait-supplied `m` requiring
/// `k > 100`. No argument satisfies both, and `s.m(5)` violates the trait one.
const COLLIDING: &str = r#"
#[trust_vc::trait_spec]
pub trait T { #[trust_vc::requires(k > 100u64)] fn m(&self, k: u64) -> u64; }

pub struct S;
#[trust_vc::trait_impl]
impl T for S { fn m(&self, k: u64) -> u64 { k } }

impl S {
    #[trust_vc::proof]
    #[trust_vc::requires(k < 10u64)]
    fn m(&self, k: u64) -> u64 { k }
}

#[trust_vc::ensures(result == 0u64)]
pub fn calls_colliding(s: &S) -> u64 { let _w = s.m(5u64); 0u64 }
"#;

/// No collision: the inherent `m` is the only candidate.
const INHERENT_ONLY: &str = r#"
pub struct S;

impl S {
    #[trust_vc::proof]
    #[trust_vc::requires(k < 10u64)]
    fn m(&self, k: u64) -> u64 { k }
}

#[trust_vc::ensures(result == 0u64)]
pub fn calls_satisfying(s: &S) -> u64 { let _w = s.m(5u64); 0u64 }
"#;

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_inhcol_{}_{}.rs", std::process::id(), tmp_id));
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

/// The control. One candidate, precondition satisfied, call verifies — so the
/// merge did not simply start rejecting inherent method calls. `m` is a proof
/// method, which panics when the exec body calls it at run time, so the
/// ghost-call rule refuses the answer; it refuses only a `Verified` answer.
#[test]
fn a_non_colliding_inherent_call_satisfying_its_precondition_still_verifies() {
    let result = verify("ok", "calls_satisfying", INHERENT_ONLY);
    assert!(
        matches!(
            &result,
            VerifyResult::Error { message }
                if message.contains("ghost function called from exec code")
        ),
        "control: `s.m(5)` against a lone inherent `requires(k < 10)` must still verify (a \
         `Verified` answer, refused by the ghost-call rule) — without this the subject's \
         verdict would not be attributable to the collision: {result:?}"
    );
}

/// THE GUARD. Same call, same argument; the only difference is that a trait also
/// supplies a requires-bearing `m` for `S`.
///
/// At HEAD this returned `Verified`: the colliding key was dropped, so no
/// call-site obligation was emitted and BOTH preconditions went unchecked.
#[test]
fn a_colliding_inherent_and_trait_method_is_checked_not_dropped() {
    let result = verify("collide", "calls_colliding", COLLIDING);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "REGRESSION: when an inherent and a trait-supplied `m` collide, the call-site \
         precondition must still be checked; verifying means the key was dropped again and \
         neither candidate's `requires` was enforced. Got: {result:?}"
    );
}
