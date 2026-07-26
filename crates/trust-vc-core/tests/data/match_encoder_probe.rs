// SPDX-License-Identifier: Apache-2.0
enum E { A(u64), B }

// GUARD must not be ignored. Faithful: arm1 (n>5) takes x>5; arm2 (no guard)
// takes x<=5, where assert!(n>5) is FALSE -> CX at x=3. If the guard is ignored,
// arm1 (bare binding) is irrefutable -> arm2 vacuous -> assert discharged =>
// false-verify.
#[trust_vc::ensures(true)]
fn guard_must_not_be_ignored(x: u64) {
    match x {
        n if n > 5u64 => {}
        n => trust_vc::assert!(n > 5u64),
    }
}

// NON-EXHAUSTIVE (no wildcard, B arm missing an assert path): must not assume the
// scrutinee is A. For e == E::B, arm1 does not match; a sound engine must not
// prove the A-only property. ensures references the A payload only via the arm.
#[trust_vc::ensures(true)]
fn non_exhaustive_must_not_assume(e: E) -> u64 {
    match e {
        E::A(v) => { trust_vc::assert!(v == 0u64); v }
        E::B => 0u64,
    }
}

// OVERLAPPING / first-match: arm1 `A(0)` then `A(v)`. For A(5), arm2 fires,
// assert v==0 FALSE -> CX. (Same literal-drop family but via the IR encoder's
// match value path; cross-check the fix holds here too.)
#[trust_vc::ensures(true)]
fn overlapping_first_match_wins(e: E) {
    match e {
        E::A(0) => {}
        E::A(v) => trust_vc::assert!(v == 0u64),
        E::B => {}
    }
}

// POSITIVE control: a guard that genuinely holds in its arm must verify.
#[trust_vc::ensures(true)]
fn guard_positive(x: u64) {
    match x {
        n if n > 5u64 => trust_vc::assert!(n > 5u64),
        _ => {}
    }
}
