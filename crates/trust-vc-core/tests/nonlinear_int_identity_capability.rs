// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN — nonlinear integer identities over `int` verify.
//!
//! Audit row 327 was recorded as confirmed MISSING **and** confirmed valuable,
//! on the basis that over `int` a LINEAR identity verified while the RING
//! identity returned `Unknown` — real nonlinear incompleteness rather than `u64`
//! overflow. It was carried as "the one capability finding worth acting on".
//!
//! Re-probed cache-off after this session's ay pin advanced: all four identities
//! below VERIFY, including distribution, the expanded square, and commutativity.
//! So the row wants re-scoring rather than work.
//!
//! HEDGE, deliberately: this fixture is mine, not the one that produced the
//! original finding, which was not preserved. It is therefore evidence that
//! these four shapes work TODAY — not proof that the exact original gap was the
//! same shape. Treat it as "re-score and re-probe", not "row 327 was wrong".
//!
//! Pinned because nonlinear arithmetic is completeness-sensitive and rides on
//! the ay pin: a future bump could regress it silently, and a capability that
//! quietly disappears is how a stale MISSING row gets recorded in the first
//! place.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r#"
use trust_vc_types::int;

#[trust_vc::ensures(result == a + b)]
pub fn linear_identity(a: int, b: int) -> int { a + b }

#[trust_vc::ensures(result == a * (b + c))]
pub fn ring_distribute(a: int, b: int, c: int) -> int { a * b + a * c }

#[trust_vc::ensures(result == (a + b) * (a + b))]
pub fn square_of_sum(a: int, b: int) -> int { a * a + 2 * a * b + b * b }

#[trust_vc::ensures(result == a * b)]
pub fn commute(a: int, b: int) -> int { b * a }
"#;

fn verify(func: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_nlint_{}_{}.rs", std::process::id(), func));
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

/// The baseline the original finding used as its control: a LINEAR identity.
/// If this ever fails, the regression is far broader than nonlinear arithmetic.
#[test]
fn a_linear_int_identity_verifies() {
    let result = verify("linear_identity");
    assert!(
        matches!(result, VerifyResult::Verified),
        "linear `a + b` must verify — this is the control: {result:?}"
    );
}

/// THE ROW-327 SHAPE. `a * (b + c) == a * b + a * c` — recorded as returning
/// `Unknown`. It verifies now.
#[test]
fn the_ring_distribution_identity_verifies() {
    let result = verify("ring_distribute");
    assert!(
        matches!(result, VerifyResult::Verified),
        "REGRESSION (or row 327 re-opened): ring distribution over `int` must verify. This is \
         the exact shape audit row 327 recorded as MISSING; it works today, and losing it again \
         is a nonlinear-arithmetic regression most likely riding on an ay pin: {result:?}"
    );
}

/// Deeper nonlinear: the expanded square. Two multiplications plus a
/// cross-term, so it needs more than one-step distribution.
#[test]
fn the_expanded_square_identity_verifies() {
    let result = verify("square_of_sum");
    assert!(
        matches!(result, VerifyResult::Verified),
        "`(a+b)^2 == a^2 + 2ab + b^2` over `int` must verify: {result:?}"
    );
}

/// Multiplicative commutativity — the simplest nonlinear fact, included so a
/// failure elsewhere can be localised as "distribution" vs "any nonlinearity".
#[test]
fn multiplicative_commutativity_verifies() {
    let result = verify("commute");
    assert!(
        matches!(result, VerifyResult::Verified),
        "`a * b == b * a` over `int` must verify: {result:?}"
    );
}
