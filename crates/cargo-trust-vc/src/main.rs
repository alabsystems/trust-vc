// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `targo-trust-vc` — the Trust-native subcommand entry point (also built as
//! the `cargo-trust-vc` back-compat alias bin, which shares this file).
//!
//! The CLI itself lives in the `cargo_trust_vc` library (this file used to BE
//! that library, as `src/main.rs`) so that the one-word `trust-vc` bin can
//! drive the very same dispatch instead of a second copy of it. Behavior of
//! this command is unchanged: the process argv is handed to
//! `cargo_trust_vc::run_cargo_cli`, which exits the process exactly where it
//! always did.

fn main() {
    let argv: Vec<String> = std::env::args().collect();
    cargo_trust_vc::run_cargo_cli(&argv);
}
