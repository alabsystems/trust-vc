// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Mirrors upstream basic.rs `test_big_and_syntax_vs_forall`:
//
//     spec fn test() -> bool {
//         &&& forall|i: int| true
//         &&& i == 0
//     }
//
// The point the upstream test pins: the `forall` binder `i` scopes ONLY over
// the first `&&&` bullet, so the `i` in the second bullet is unresolved and
// rustc rejects it with E0425 ("cannot find value `i`") — a Rust-channel
// error (`assert_rust_error_msg`), not a verifier diagnostic. In compiled
// trust-vc surface the bullets are the plain conjunction and the quantifier
// is the `trust_vc::forall!` macro; the binder scoping — and therefore the
// exact rustc error — is identical. The evidence gate's cargo-fixture
// rust-error channel runs a real `cargo check` on this crate and matches
// "cannot find value `i`" against the emitted diagnostic.
use trust_vc_types::int;

#[trust_vc::spec]
pub fn test() -> bool {
    trust_vc::forall!(|i: int| true) && i == 0
}
