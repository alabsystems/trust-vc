// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Soundness fixtures for the recursive spec-function termination gate.
//
// A recursive spec function's defining axiom `forall x. f(x) == body(x)` is
// faithful only if the recursion terminates. A `#[decreases]` measure that does
// NOT actually shrink yields an UNSATISFIABLE axiom, which would let any goal
// verify vacuously (catastrophic false `Verified`). The gate must therefore PROVE
// the measure strictly decreases before trusting the axiom; bogus measures must
// fail closed at EVERY integer type (bit-vector AND `int`/`nat`).

// ===========================================================================
// CATASTROPHIC DIRECTION — these must NOT verify (Counterexample / Error).
// ===========================================================================

// --- bogus self-recursion: f(n) == f(n) + 1, measure does not decrease ---

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn bogus_u64(n: u64) -> u64 {
    bogus_u64(n) + 1u64
}

#[trust_vc::ensures(true)]
fn bogus_u64_proves_false() {
    trust_vc::assert!(bogus_u64(0u64) == bogus_u64(0u64));
    trust_vc::assert!(0u64 == 1u64);
}

#[trust_vc::ensures(true)]
fn bogus_u64_proves_literal_false() {
    trust_vc::assert!(bogus_u64(0u64) == bogus_u64(0u64));
    trust_vc::assert!(false);
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn bogus_u32(n: u32) -> u32 {
    bogus_u32(n) + 1u32
}

#[trust_vc::ensures(true)]
fn bogus_u32_proves_false() {
    trust_vc::assert!(bogus_u32(0u32) == bogus_u32(0u32));
    trust_vc::assert!(0u32 == 1u32);
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn bogus_usize(n: usize) -> usize {
    bogus_usize(n) + 1usize
}

#[trust_vc::ensures(true)]
fn bogus_usize_proves_false() {
    trust_vc::assert!(bogus_usize(0usize) == bogus_usize(0usize));
    trust_vc::assert!(0usize == 1usize);
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn bogus_int(n: int) -> int {
    bogus_int(n) + 1
}

#[trust_vc::ensures(true)]
fn bogus_int_proves_false() {
    trust_vc::assert!(bogus_int(0) == bogus_int(0));
    trust_vc::assert!(0 == 1);
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn bogus_nat(n: nat) -> nat {
    bogus_nat(n) + 1
}

#[trust_vc::ensures(true)]
fn bogus_nat_proves_false() {
    trust_vc::assert!(bogus_nat(0) == bogus_nat(0));
    trust_vc::assert!(0 == 1);
}

// --- bogus mutual recursion: f(n) == g(n) + 1, g(n) == f(n) + 1 ---

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn mut_f(n: u64) -> u64 {
    mut_g(n) + 1u64
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn mut_g(n: u64) -> u64 {
    mut_f(n) + 1u64
}

#[trust_vc::ensures(true)]
fn mutual_proves_false() {
    trust_vc::assert!(mut_f(0u64) == mut_f(0u64));
    trust_vc::assert!(0u64 == 1u64);
}

// --- decreases on an unrelated/constant value while recursing on n ---

#[trust_vc::spec]
#[trust_vc::decreases(7u64)]
fn const_measure(n: u64) -> u64 {
    const_measure(n) + 1u64
}

#[trust_vc::ensures(true)]
fn const_measure_proves_false() {
    trust_vc::assert!(const_measure(0u64) == const_measure(0u64));
    trust_vc::assert!(0u64 == 1u64);
}

// --- recurse on n+1 with decreases(n): measure grows, not decreases ---

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn grow(n: u64) -> u64 {
    grow(n + 1u64) + 1u64
}

#[trust_vc::ensures(true)]
fn grow_proves_false() {
    trust_vc::assert!(grow(0u64) == grow(0u64));
    trust_vc::assert!(0u64 == 1u64);
}

// --- nat-saturating recursion with NO base case: f(n) == f(n - 1) + 1 ---
// At `nat`, `0 - 1` saturates to 0, so f(0) == f(0) + 1 is contradictory.
// Without a base-case guard the decrease `n - 1 < n` fails at n == 0.

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn nat_no_base(n: nat) -> nat {
    (nat_no_base((n - 1) as nat) + 1) as nat
}

#[trust_vc::ensures(true)]
fn nat_no_base_proves_false() {
    trust_vc::assert!(nat_no_base(0) == nat_no_base(0));
    trust_vc::assert!(0 == 1);
}

// --- MISSING decreases control: stays fail-closed (uninterpreted helper) ---

#[trust_vc::spec]
fn missing(n: u64) -> u64 {
    missing(n) + 1u64
}

#[trust_vc::ensures(true)]
fn missing_proves_false() {
    trust_vc::assert!(missing(0u64) == missing(0u64));
    trust_vc::assert!(0u64 == 1u64);
}

// ===========================================================================
// CORRECT DIRECTION — these MUST keep verifying their true goals.
// ===========================================================================

// --- good(n) recurses on n - 1 with decreases(n) ---

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn good(n: u64) -> u64 {
    if n == 0u64 { 0u64 } else { good(n - 1u64) + 1u64 }
}

#[trust_vc::ensures(true)]
fn good_true_goal() {
    trust_vc::assert!(good(0u64) == 0u64);
}

// --- lexicographic decreases: Ackermann on (m, n) ---

#[trust_vc::spec]
#[trust_vc::decreases(m, n)]
fn ack(m: nat, n: nat) -> nat {
    if m == 0 {
        (n + 1) as nat
    } else if n == 0 {
        ack((m - 1) as nat, 1)
    } else {
        ack((m - 1) as nat, ack(m, (n - 1) as nat))
    }
}

#[trust_vc::ensures(true)]
fn ack_true_goal() {
    trust_vc::assert!(ack(0, 0) == 1);
}

// --- decreases on a Seq length ---

#[trust_vc::spec]
#[trust_vc::decreases(s.len())]
fn seq_len(s: Seq<int>) -> nat {
    if s.len() == 0 {
        0
    } else {
        (1 + seq_len(s.drop_first())) as nat
    }
}

#[trust_vc::ensures(true)]
fn seq_len_true_goal(t: Seq<int>) {
    trust_vc::assert!(seq_len(t) == seq_len(t));
}

// --- correctly-decreasing mutual recursion (count down on nat) ---

#[trust_vc::spec]
#[trust_vc::decreases(i)]
fn count_down_a(i: nat) -> nat {
    if i == 0 { 0 } else { (1 + count_down_b((i - 1) as nat)) as nat }
}

#[trust_vc::spec]
#[trust_vc::decreases(i)]
fn count_down_b(i: nat) -> nat {
    if i == 0 { 0 } else { (1 + count_down_a((i - 1) as nat)) as nat }
}

#[trust_vc::ensures(true)]
fn mutual_decreasing_true_goal() {
    trust_vc::assert!(count_down_b(0) == 0);
}

// A FALSE goal about a correctly-decreasing function must still be a
// Counterexample: the emitted defining axiom is FAITHFUL, not vacuous.
// (Uses `nat` to avoid a pre-existing engine limitation where counterexample
// search over a *bit-vector* recursive axiom — whose `f(n - 1)` wraps at the
// floor — diverges; see `good`'s u64 body. The faithfulness property itself is
// type-independent.)
#[trust_vc::ensures(true)]
fn mutual_decreasing_false_goal() {
    trust_vc::assert!(count_down_b(0) == 1);
}
