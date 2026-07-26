// SPDX-License-Identifier: Apache-2.0
// FRESH probe: an `if let` whose scrutinee is a side-effect-free function CALL.
enum Opt { Some(u64), None }

// Side-effect-free (spec) chooser: None when b is false.
#[trust_vc::spec]
fn pick(b: bool) -> Opt {
    if b { Opt::Some(7u64) } else { Opt::None }
}

// TARGET — correct verdict: NOT Verified.
// The scrutinee is the call `pick(b)`, which is `None` when `b == false`, so the
// desugared `_ => 0` arm is reachable. `ensures(result == 7)` is FALSE: witness
// `b = false` -> pick(false) = None -> result 0 != 7. A Verified would mean the
// desugar assumed the call's result matched `Some` (never-assume-success broke
// for a call scrutinee). If exec-calling-spec is unmodeled the call fails CLOSED
// -> still NOT Verified; never a false-verify.
#[trust_vc::ensures(result == 7u64)]
fn if_let_call_scrutinee_must_cx(b: bool) -> u64 {
    if let Opt::Some(v) = pick(b) { v } else { 0u64 }
}

// POSITIVE CONTROL — should Verify.
// `pick(true) == Some(7)`, so the match succeeds and v == 7. Confirms the call
// scrutinee is evaluated and its payload extracted (so a non-verify of the
// target is a genuine CX, not a parse/lowering failure).
#[trust_vc::ensures(result == 7u64)]
fn if_let_call_scrutinee_positive() -> u64 {
    if let Opt::Some(v) = pick(true) { v } else { 0u64 }
}
