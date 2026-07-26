// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// requires-only proof contracts with an empty body are rejected at macro
// expansion time because they create an assumptions-only verification context.

#[trust_vc::contract(requires(n > 0))]
#[trust_vc::proof]
fn lemma_positive(n: u32) {}

fn main() {}
