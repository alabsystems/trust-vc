// SPDX-License-Identifier: Apache-2.0
enum POpt { Some(u64), None }

// If the engine HANDLES if-let: i == 20, so `assert!(i == 999)` is a genuine
// Counterexample. If the engine SILENTLY DROPS the if-let statement, the assert
// vanishes and the function verifies vacuously -> false-verify.
#[trust_vc::ensures(true)]
fn if_let_then_assert_false_must_not_verify() {
    let o = POpt::Some(20u64);
    if let POpt::Some(i) = o {
        trust_vc::assert!(i == 999u64);
    }
}

// If-let else-branch reachability: o == None, the else runs `assert!(false)`.
// Handled -> Counterexample; dropped -> vacuous verify (false-verify).
#[trust_vc::ensures(true)]
fn if_let_else_reachable_assert_false_must_not_verify() {
    let o = POpt::None;
    if let POpt::Some(i) = o {
        trust_vc::assert!(i == 20u64);
    } else {
        trust_vc::assert!(false);
    }
}
