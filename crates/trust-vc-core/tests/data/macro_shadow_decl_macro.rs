// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! A declarative macro 2.0 binds the name exactly as `macro_rules!` does, but
//! `syn` hands it back as `Item::Verbatim` — a node an item-kind match misses.
#![feature(decl_macro)]

pub macro assume($e: expr) {}

/// FALSE: the `macro` item's `assume` is a NO-OP.
#[trust_vc::ensures(true)]
fn decl_macro_assume_must_not_verify(x: u64) -> u64 {
    assume!(x == 0u64);
    trust_vc::assert!(x <= 255u64);
    0u64
}
