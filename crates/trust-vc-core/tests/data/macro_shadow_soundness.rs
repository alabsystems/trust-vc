// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Cardinal reproducers: a `macro_rules!` declared in the FILE textually
//! shadows the macro trust-vc believed it was reading. Legal single-file Rust;
//! `rustc --edition 2021` confirms the user macro wins at every call site.

macro_rules! assume {
    ($e:expr) => {};
}

macro_rules! matches {
    ($e:expr, $p:pat) => {
        false
    };
}

/// FALSE: the user `assume!` is a NO-OP, so `x` is unconstrained and
/// `x <= 255` is false at `u64::MAX`. It was consumed as a spec ASSUMPTION.
#[trust_vc::ensures(true)]
fn shadowed_assume_must_not_verify(x: u64) -> u64 {
    assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}

/// FALSE: the user `matches!` always yields `false`.
#[trust_vc::ensures(true)]
fn shadowed_matches_must_not_verify() -> u64 {
    let y: u8 = 7u8;
    trust_vc::assert!(matches!(y, 7u8));
    0u64
}

/// TRUE: the user `matches!` always yields `false`, so its negation holds.
/// The desugar refuted this one — the other direction of the same defect.
#[trust_vc::ensures(true)]
fn shadowed_matches_negation_is_true() -> u64 {
    let y: u8 = 7u8;
    trust_vc::assert!(!matches!(y, 7u8));
    0u64
}

/// FALSE, and reachable only through a TOKEN STREAM: no `syn` visitor descends
/// into a macro's tokens, so the nested `assume!` is invisible to any
/// AST-position-based gate.
#[trust_vc::ensures(true)]
fn shadowed_assume_in_proof_block_must_not_verify(x: u64) -> u64 {
    trust_vc::proof_block!({
        assume!(x == 0u64);
    });
    trust_vc::assert!(x <= 255u64);
    0u64
}

/// FALSE: same token-stream route, through `assert_by!`'s proof block.
#[trust_vc::ensures(true)]
fn shadowed_assume_in_assert_by_must_not_verify(x: u64) -> u64 {
    trust_vc::assert_by!(x <= 255u64, {
        assume!(x == 0u64);
    });
    0u64
}

/// FALSE: a contract ATTRIBUTE carries its predicate as an opaque token
/// stream, which is a third position the AST does not reach.
#[trust_vc::requires(y == 7u8)]
#[trust_vc::ensures(matches!(y, 7u8))]
fn shadowed_matches_in_contract_must_not_verify(y: u8) -> u64 {
    0u64
}

// --- The EXPRESSION-macro lane, which keys by bare name exactly the same way ---

macro_rules! seq {
    ($($e:expr),*) => {
        trust_vc_types::Seq::<u64>::empty()
    };
}

macro_rules! equal {
    ($a:expr, $b:expr) => {
        false
    };
}

/// FALSE: the user `seq!` yields an EMPTY sequence, so its length is 0, not 3.
#[trust_vc::ensures(true)]
fn shadowed_seq_must_not_verify() -> u64 {
    let s = seq![1u64, 2u64, 3u64];
    trust_vc::assert!(s.len() == 3);
    0u64
}

/// FALSE: the user `equal!` always yields `false`.
#[trust_vc::ensures(true)]
fn shadowed_equal_must_not_verify(x: u64) -> u64 {
    trust_vc::assert!(equal!(x, x));
    0u64
}
