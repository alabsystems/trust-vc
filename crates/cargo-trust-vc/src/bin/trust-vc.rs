// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `trust-vc` — the one-word command.
//!
//! A front door, not a second verifier: `cargo_trust_vc::run_one_word_cli`
//! translates the friendlier argv and then runs the same dispatch
//! `cargo-trust-vc` runs. See `src/one_word.rs`.

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    std::process::exit(cargo_trust_vc::run_one_word_cli(&argv));
}
