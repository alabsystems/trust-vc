// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the CONCRETE-SET extensional-equality soundness fix.
//
// `Set<T>` membership is an `Array(T -> Bool)` carrier and `==` lowers to the
// pointwise membership biconditional `forall e. A.contains(e) == B.contains(e)`,
// which the verifier skolemizes (a fresh element constant). ay's array theory
// fails to refute the negated goal for an `Int`-indexed (`Set<int>`) membership
// array — it validates a model where the skolem read disagrees with the
// const-array empty base — so a strict-superset equality such as `{1,2} == {1}`
// was unsoundly `Verified` (while the BV-element `nat`/`i32`/`usize` variants were
// already sound). The fix specializes the equality of two CONCRETE
// `empty().insert(..)` chains to the skolem-free two-way membership conjunction
// `(⋀ a∈A. B.contains(a)) ∧ (⋀ b∈B. A.contains(b))` — BOTH inclusions at the
// concrete insert keys, decided directly by the array + EUF layers.
//
// Soundness battery (the critical risk is the false Verified):
//   * strict-superset / differing concrete sets -> Counterexample;
//   * genuinely-equal concrete sets             -> still Verified (no over-rejection);
//   * cardinality / membership controls         -> unchanged.

#![allow(dead_code, unused_variables)]

// ════════════ FALSE: LHS strict superset of RHS (the closed hole) ════════════

// {1,2} == {1}: FALSE (2 is in LHS, not RHS).
#[trust_vc::ensures(true)]
fn lhs_super_int() {
    trust_vc::assert!(
        Set::<int>::empty().insert(1 as int).insert(2 as int)
            == Set::<int>::empty().insert(1 as int)
    );
}

// {1,2,3} == {1}: FALSE.
#[trust_vc::ensures(true)]
fn lhs_super3_int() {
    trust_vc::assert!(
        Set::<int>::empty().insert(1 as int).insert(2 as int).insert(3 as int)
            == Set::<int>::empty().insert(1 as int)
    );
}

// {1,2} == {2}: FALSE (the "extra" element is the inner insert).
#[trust_vc::ensures(true)]
fn lhs_super_rhs2_int() {
    trust_vc::assert!(
        Set::<int>::empty().insert(1 as int).insert(2 as int)
            == Set::<int>::empty().insert(2 as int)
    );
}

// {1} == {}: FALSE (superset of empty).
#[trust_vc::ensures(true)]
fn singleton_eq_empty_int() {
    trust_vc::assert!(Set::<int>::empty().insert(1 as int) == Set::<int>::empty());
}

// ════════════ FALSE controls (already sound before the fix) ════════════

// {1} == {2}: disjoint, FALSE.
#[trust_vc::ensures(true)]
fn disjoint_int() {
    trust_vc::assert!(Set::<int>::empty().insert(1 as int) == Set::<int>::empty().insert(2 as int));
}

// {1} == {1,2}: RHS strict superset, FALSE.
#[trust_vc::ensures(true)]
fn rhs_super_int() {
    trust_vc::assert!(
        Set::<int>::empty().insert(1 as int)
            == Set::<int>::empty().insert(1 as int).insert(2 as int)
    );
}

// {1,2} == {1,3}: same cardinality, one differing element, FALSE.
#[trust_vc::ensures(true)]
fn same_card_diff_int() {
    trust_vc::assert!(
        Set::<int>::empty().insert(1 as int).insert(2 as int)
            == Set::<int>::empty().insert(1 as int).insert(3 as int)
    );
}

// ════════════ TRUE: genuinely-equal sets -> still Verified ════════════

// {1,2} == {1,2}: TRUE.
#[trust_vc::ensures(true)]
fn equal_int() {
    trust_vc::assert!(
        Set::<int>::empty().insert(1 as int).insert(2 as int)
            == Set::<int>::empty().insert(1 as int).insert(2 as int)
    );
}

// {1,2} == {2,1}: TRUE (insert order is irrelevant to set identity).
#[trust_vc::ensures(true)]
fn equal_reordered_int() {
    trust_vc::assert!(
        Set::<int>::empty().insert(1 as int).insert(2 as int)
            == Set::<int>::empty().insert(2 as int).insert(1 as int)
    );
}

// {} == {}: TRUE.
#[trust_vc::ensures(true)]
fn empty_eq_empty_int() {
    trust_vc::assert!(Set::<int>::empty() == Set::<int>::empty());
}

// ════════════ cardinality / membership controls (unchanged) ════════════

// len({1,2}) == 2: TRUE (insert(2) is genuinely present).
#[trust_vc::ensures(true)]
fn len_two_int() {
    trust_vc::assert!(Set::<int>::empty().insert(1 as int).insert(2 as int).len() == 2);
}

// {1,2}.contains(2): TRUE.
#[trust_vc::ensures(true)]
fn contains_pos_int() {
    trust_vc::assert!(Set::<int>::empty().insert(1 as int).insert(2 as int).contains(2 as int));
}

// !{1}.contains(2): TRUE.
#[trust_vc::ensures(true)]
fn not_contains_int() {
    trust_vc::assert!(!Set::<int>::empty().insert(1 as int).contains(2 as int));
}

// ════════════ element-type controls: nat (Int-indexed) stays sound ════════════

// {1,2} == {1} over nat: FALSE.
#[trust_vc::ensures(true)]
fn lhs_super_nat() {
    trust_vc::assert!(
        Set::<nat>::empty().insert(1 as nat).insert(2 as nat)
            == Set::<nat>::empty().insert(1 as nat)
    );
}

// {1,2} == {1,2} over nat: TRUE.
#[trust_vc::ensures(true)]
fn equal_nat() {
    trust_vc::assert!(
        Set::<nat>::empty().insert(1 as nat).insert(2 as nat)
            == Set::<nat>::empty().insert(1 as nat).insert(2 as nat)
    );
}
