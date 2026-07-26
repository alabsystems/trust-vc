// SPDX-License-Identifier: Apache-2.0
// FRESH probe: an OR-pattern in `if let`, payload binding + wildcard reachability.
enum Tri { A(u64), B(u64), C(u64) }

// TARGET — correct verdict: NOT Verified.
// `Tri::A(x) | Tri::B(x)` covers only A and B; a `Tri::C(_)` scrutinee reaches
// the desugared `_ => 0` arm. The matched arm returns the bound payload `x`, so
// `ensures(result == 3)` is FALSE. Witness `t = Tri::C(0)` -> result 0 != 3
// (also `t = Tri::A(0)` -> x = 0 != 3). A Verified would mean the desugar/match
// treated the OR arm as always-matching (wildcard dropped) or pinned the
// payload -> "never assume match success" broke for OR-patterns.
#[trust_vc::ensures(result == 3u64)]
fn if_let_or_pattern_must_cx(t: Tri) -> u64 {
    if let Tri::A(x) | Tri::B(x) = t { x } else { 0u64 }
}

// POSITIVE CONTROL — should Verify.
// `t = Tri::B(7)` matches through the SECOND alternative, binding x = 7, so
// result == 7. Confirms the OR desugar lowers and per-alternative payload
// selection is correct (a first-alternative-only binding bug would break this).
#[trust_vc::ensures(result == 7u64)]
fn if_let_or_pattern_positive() -> u64 {
    let t = Tri::B(7u64);
    if let Tri::A(x) | Tri::B(x) = t { x } else { 0u64 }
}
