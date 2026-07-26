// SPDX-License-Identifier: Apache-2.0
enum Opt { Some(u64), None }

// POSITIVE: expression-form if-let now verifies (Some(100) -> payload 100).
#[trust_vc::ensures(result == 100u64)]
fn if_let_expr_verifies() -> u64 {
    if let Opt::Some(payload) = Opt::Some(100u64) { payload } else { 0u64 }
}

// NEVER-ASSUME-SUCCESS (the crux): o is symbolic, so the `_ => F` arm is
// reachable. `ensures(result == 7)` holds ONLY on the matched branch; the else
// yields 0. A sound desugar (both arms lowered) => Counterexample (o == None).
// If the desugar assumed the match succeeds, it would false-verify.
#[trust_vc::ensures(result == 7u64)]
fn if_let_expr_must_not_assume_match(o: Opt) -> u64 {
    if let Opt::Some(v) = o { 7u64 } else { 0u64 }
}

// BOTH-ARMS control: a postcondition true on both arms must verify (proves the
// else arm is genuinely lowered, not that everything just CXs).
#[trust_vc::ensures(result == 7u64 || result == 0u64)]
fn if_let_expr_both_arms_verify(o: Opt) -> u64 {
    if let Opt::Some(v) = o { 7u64 } else { 0u64 }
}

// SOUNDNESS BOUNDARY: a let-chain condition (`Expr::Binary` wrapping the let)
// must NOT desugar — its inner `Expr::Let` still fails closed.
#[trust_vc::ensures(true)]
fn if_let_chain_must_stay_blocked(o: Opt, b: bool) -> u64 {
    if let Opt::Some(v) = o && b { v } else { 0u64 }
}
