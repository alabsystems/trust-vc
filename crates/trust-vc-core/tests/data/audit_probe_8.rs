// SPDX-License-Identifier: Apache-2.0
// FRESH probe: a refutable LITERAL pattern in `if let` (`if let 0 = n`). The
// literal is a refinement that must NOT be dropped (cf. the `@`-binding drop).

// TARGET — correct verdict: NOT Verified.
// `if let 0u64 = n` matches only when n == 0; the desugared `_ => n` arm handles
// n != 0. `ensures(result == 42)` is FALSE: witness `n = 1` -> result 1 != 42. A
// Verified would mean the literal refinement `0u64` was dropped (arm treated as
// irrefutable/always-match), pinning result to 42 — the same class of
// false-verify as a dropped pattern refinement.
#[trust_vc::ensures(result == 42u64)]
fn if_let_literal_must_cx(n: u64) -> u64 {
    if let 0u64 = n { 42u64 } else { n }
}

// POSITIVE CONTROL — should Verify.
// n = 5 does NOT match `0u64`, so the else arm runs -> result == 42. This
// confirms the literal refinement is actually EVALUATED (the else path is taken
// for n != 0); were the refinement dropped, this control would instead yield 0
// and FAIL — so it cross-checks the exact machinery the target depends on.
#[trust_vc::ensures(result == 42u64)]
fn if_let_literal_positive() -> u64 {
    let n = 5u64;
    if let 0u64 = n { 0u64 } else { 42u64 }
}
