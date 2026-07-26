// SPDX-License-Identifier: Apache-2.0
// FRESH probe: nested `if let` desugar; both else arms reachable; the outer
// binding flows into the inner matched body.
enum Opt { Some(u64), None }

// TARGET — correct verdict: NOT Verified.
// result == 5 requires BOTH o == Some(5) AND p == Some(_). Every other shape
// hits a reachable else: o == None -> 2; o == Some(_), p == None -> 1;
// o == Some(3), p == Some(_) -> 3. Witness `o = Opt::None` (or `p = Opt::None`,
// or `o = Opt::Some(3)`) -> result != 5. A Verified would mean one of the two
// nested desugars assumed its match succeeded (an else arm was dropped) or
// collapsed the arms to a constant.
#[trust_vc::ensures(result == 5u64)]
fn if_let_nested_must_cx(o: Opt, p: Opt) -> u64 {
    if let Opt::Some(a) = o {
        if let Opt::Some(b) = p { a } else { 1u64 }
    } else {
        2u64
    }
}

// POSITIVE CONTROL — should Verify.
// o = Some(5), p = Some(9): outer binds a = 5, inner matches, result == a == 5.
// Confirms the nested desugar lowers and the outer binding reaches the inner
// matched body correctly (non-verify of the target is a real CX, not a parse
// failure).
#[trust_vc::ensures(result == 5u64)]
fn if_let_nested_positive() -> u64 {
    let o = Opt::Some(5u64);
    let p = Opt::Some(9u64);
    if let Opt::Some(a) = o {
        if let Opt::Some(b) = p { a } else { 1u64 }
    } else {
        2u64
    }
}
