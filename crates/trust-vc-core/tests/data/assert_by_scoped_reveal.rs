// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// `assert … by { .. }` with a SCOPED `reveal` — file path (#34).
//
// Upstream: source/rust_verify_test/tests/assert_forall_by.rs
// (pinned ref a40d57c73650cd3648b09386bfdb96ab5c270626)
//
//   #[verifier(opaque)] spec fn f1(i: int) -> int { i + 1 }
//
//   test_assertby1        assert(f1(3) > 3) by { reveal(f1); } assert(f1(3) > 3);   PASSES
//   test_assertby1_fail1  assert(f1(3) > 4) by { reveal(f1); }                      FAILS
//   test_assertby1_fail2  assert(f1(3) > 3) by { reveal(f1); } assert(f1(3) == 4);  FAILS
//
// The cardinal property: the by-block's `reveal` is SCOPED to the block. The
// block's proven CONCLUSION persists as a fact, but f1 is OPAQUE again outside —
// so `f1(3) == 4` (provable only from f1's body) must NOT verify. A reveal that
// leaked past the block would prove MORE than Verus.
//
// NOT Rust-compiled — only syn-parsed by verify_function_from_file.
#![allow(dead_code, unused_variables)]

use trust_vc_types::int;

// upstream: #[verifier(opaque)] spec fn f1(i: int) -> int { i + 1 }
#[trust_vc::spec]
#[trust_vc::opaque]
fn f1(i: int) -> int {
    i + 1
}

// --- (1) the by-block's scoped reveal actually discharges the conclusion ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_reveal_proves() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
    });
}

// --- (2) upstream test_assertby1: the proven FACT persists past the block ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_fact_persists() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) > 3int); // upstream: VERIFIES (fact persists)
}

// --- (3) THE CARDINAL PIN — upstream test_assertby1_fail2: the reveal does NOT
// leak past the block. `f1(3) == 4` is provable ONLY from f1's body, which is
// opaque again out here, so this must NOT verify. If it does, the scoped reveal
// leaked and we prove MORE than Verus. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_reveal_does_not_leak() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) == 4int); // upstream: FAILS (f1 still opaque)
}

// --- (4) no reveal in the block ⇒ f1 stays opaque ⇒ the conclusion is not
// provable. Pins that (1) verifies BECAUSE of the reveal, not because opacity is
// broken. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn no_reveal_stays_opaque() {
    trust_vc::assert_by!(f1(3int) > 3int, {});
}

// --- (5) upstream test_assertby1_fail1: a FALSE conclusion fails even with the
// reveal (f1(3) == 4, not > 4). ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_false_conclusion_fails() {
    trust_vc::assert_by!(f1(3int) > 4int, {
        trust_vc::reveal!(f1);
    });
}

// --- (6) trivial by-block: the plumbing itself works with an empty block. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_trivial() {
    trust_vc::assert_by!(1int + 1int == 2int, {});
}

// --- (7) the block's own inner assertions are CHECKED (a by-block is not a
// free-pass `assume`): an inner assert that is false must sink the query. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_inner_assert_is_checked() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
        trust_vc::assert!(f1(3int) == 5int); // FALSE under the revealed body
    });
}

// --- (8) an inner assert that IS provable under the scoped reveal, and whose
// fact feeds the conclusion. Pins the in-scope reveal reaches the inner
// assertions too, not just the conclusion. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_inner_assert_uses_scoped_reveal() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
        trust_vc::assert!(f1(3int) == 4int);
    });
}

// --- (9) typo guard survives scoping: reveal!(unknown) inside a by-block must
// still fail closed, exactly like a top-level reveal!(unknown). ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn by_block_reveal_typo_fails_closed() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(no_such_function_anywhere);
    });
}

// --- (10) scope isolation across by-blocks: a reveal in block A must not be
// visible in block B. Block B's conclusion is provable only from f1's body, so
// it must NOT verify. Same leak class as (3), one level out. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn reveal_does_not_leak_into_sibling_block() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert_by!(f1(3int) == 4int, {});
}

// --- (11) the QUANTIFIED by-block (upstream `assert forall |i| .. by { .. }`,
// the assert_forall_by.rs keystone shape): the scoped reveal discharges the
// quantified conclusion. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn forall_by_block_reveal_proves() {
    trust_vc::assert_forall_by!(|i: int| f1(i) > i, {
        trust_vc::reveal!(f1);
    });
}

// --- (12) CARDINAL PIN for the quantified form: the forall-by block's reveal
// must not leak either. `f1(3) == 4` after the block is provable only from f1's
// body and must NOT verify. ---
#[trust_vc::ensures(true)]
#[trust_vc::proof]
fn forall_by_block_reveal_does_not_leak() {
    trust_vc::assert_forall_by!(|i: int| f1(i) > i, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) == 4int); // f1 opaque again out here
}

// --- (13) CARDINAL PIN, postcondition direction: the by-block's scoped reveal
// must not leak into the function's ENSURES either. `f1(3) == 4` is provable
// only from f1's body, which is opaque at the postcondition — Verus rejects,
// so trust-vc must too. ---
#[trust_vc::ensures(f1(3int) == 4int)]
#[trust_vc::proof]
fn scoped_reveal_does_not_leak_into_ensures() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
    });
}
