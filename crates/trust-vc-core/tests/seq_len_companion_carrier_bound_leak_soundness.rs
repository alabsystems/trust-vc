// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness guards for the Int->BV length COMPANION bridge: it must never leak
//! `len <= usize::MAX` for an unbounded spec `Seq<T>`.
//!
//! THE HOLE. Every collection encoding that needs a pure-BV index carrier mints
//! a `BitVec(pw)` companion `c` for the Int length and bridges it with
//! `bv2int(c) == len` (`collection_shared::len_index_companion`), or under a
//! `len >= 0` antecedent (`..._maybe_negative`). `bv2int(c) <= 2^pw - 1` holds
//! by SORT, and every declared collection length is separately asserted
//! `len >= 0` at declaration, so either bridge ENTAILS the standalone fact
//! `len <= 2^pw - 1` in the enclosing solver context.
//!
//! That is exactly the assertion `AYEncoder::assert_len_usize_bounded` documents
//! as SOUNDNESS-CRITICAL to emit ONLY for a `bounded_len` exec `Vec`/slice/array
//! and NEVER for a spec `Seq<T>`, because it "would make every huge-length
//! guard's context UNSAT and vacuously verify". The companion sites emitted it
//! for everything. It also made the NC4 carrier-representability obligation
//! SELF-JUSTIFYING: the bridge lands in the PARENT context and the obligation is
//! discharged in a CHILD `SolverScope` that inherits it, so the guard was proved
//! from the assumption it exists to guard.
//!
//! THE DISCRIMINATOR is the pair `*_with_op` / `*_without_op`: the assertion
//! `a.len() <= u64::MAX` is UNPROVABLE for an unbounded `Seq` and is correctly
//! refuted on its own. Adding an unrelated `requires` that merely mentions a
//! collection OP over the same sequence used to flip it to `Verified` — the op's
//! own companion bridge was the sole premise. Nothing else differs between the
//! two programs.
//!
//! Fix: a length not established carrier-bounded gets the bridge under the
//! representability antecedent `0 <= len <= 2^pw - 1` (inert in the huge-length
//! regime, delivered unchanged everywhere the carrier could index the sequence),
//! and the extensional-equality site drops the companion entirely in favour of
//! an Int-domain guard `bv2nat(i) < len`. A genuinely `usize`-bounded length
//! (exec `Vec`/slice/array, concrete or pinned lengths, and derived views of
//! those) keeps the unconditional bridge — there it restates a fact already on
//! the assertion stack.
//!
//! The `vec_*` tests are the NARROWNESS PINS in the other direction: a `Vec`
//! length really IS `<= usize::MAX`, so that bound must STILL be provable, and
//! `requires(a == b) |- assert!(a == b)` must still verify. Over-rejection here
//! would break every collection equality proof in the corpus.

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// `u64::MAX` written out — the largest value a `usize`-bounded length can take,
/// and therefore the exact bound the companion bridge used to leak.
const USIZE_MAX_LIT: &str = "18446744073709551615";

fn verify(code: &str, name: &str) -> VerifyResult {
    let dir = Path::new("target/seq_len_companion_carrier_bound_leak_soundness");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    verify_function_from_file(f.to_str().unwrap(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify: {e}"))
}

/// A `Seq` length bound that is NOT entailed must never come back `Verified`.
/// Any non-`Verified` verdict is acceptable (the point is the absence of a
/// proof); `Counterexample` is the expected one.
fn assert_not_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        !matches!(r, VerifyResult::Verified),
        "{name}: `len <= usize::MAX` is NOT entailed for an unbounded spec \
         Seq<T>, so this must never be Verified — a Verified verdict means a \
         length companion bridge leaked the carrier bound into the context \
         (and with it, vacuous proofs for every huge-length guard). Got {r:?}"
    );
}

fn assert_verified(code: &str, name: &str) {
    let r = verify(code, name);
    assert!(
        matches!(r, VerifyResult::Verified),
        "{name}: this is a TRUE claim that verified before the companion-bridge \
         fix and must keep verifying — the fix must not be paid for with \
         over-rejection. Got {r:?}"
    );
}

/// `assert!(a.len() <= u64::MAX)` over `Seq` params, with an optional extra
/// `requires` clause that drags a collection OP (and hence its length
/// companion) into the same solver context.
fn seq_len_bound_program(name: &str, extra_requires: &str) -> String {
    format!(
        "use trust_vc_types::{{Seq, SpecFn}};\n\
         #[allow(unused_imports)]\n\
         use trust_vc_types::SpecFn as _SpecFnAlias;\n\
         {extra_requires}\
         #[trust_vc::ensures(true)]\n\
         pub fn {name}(a: Seq<i32>, b: Seq<i32>) {{\n    \
         trust_vc::assert!(a.len() <= {USIZE_MAX_LIT});\n}}\n"
    )
}

// ---------------------------------------------------------------------------
// The ISOLATING CONTROL. No collection op at all: the bound is unprovable and
// is correctly refuted. Every `*_with_op` case below differs from this program
// by exactly one `requires` clause.
// ---------------------------------------------------------------------------

#[test]
fn seq_len_usize_bound_without_op_is_refuted() {
    let name = "seq_len_usize_bound_without_op_is_refuted";
    assert_not_verified(&seq_len_bound_program(name, ""), name);
}

// ---------------------------------------------------------------------------
// One case per companion site. Each `requires` is logically IRRELEVANT to the
// asserted length bound; it exists only to make the encoder mint that site's
// length companion.
// ---------------------------------------------------------------------------

/// `encode_seq_extensional_eq` — the site the hole was found at. Both operand
/// companions were bridged under a bare `len >= 0`.
#[test]
fn seq_ext_eq_does_not_leak_carrier_bound() {
    let name = "seq_ext_eq_does_not_leak_carrier_bound";
    assert_not_verified(
        &seq_len_bound_program(name, "#[trust_vc::requires(a == b)]\n"),
        name,
    );
}

/// `encode_seq_concat` (`seq_transforms.rs`) — both operand companions.
#[test]
fn seq_concat_does_not_leak_carrier_bound() {
    let name = "seq_concat_does_not_leak_carrier_bound";
    assert_not_verified(
        &seq_len_bound_program(
            name,
            "#[trust_vc::requires(a.add(b).len() == a.len() + b.len())]\n",
        ),
        name,
    );
}

/// `encode_seq_filter` (`map_filter.rs`) — the RESULT-length companion here used
/// the fully UNCONDITIONAL `len_index_companion`, with no `len >= 0` antecedent
/// at all, so it was strictly the worst of the family.
#[test]
fn seq_filter_does_not_leak_carrier_bound() {
    let name = "seq_filter_does_not_leak_carrier_bound";
    assert_not_verified(
        &seq_len_bound_program(
            name,
            "#[trust_vc::requires(a.filter(SpecFn::new(|x: i32| x > 0i32)).len() <= a.len())]\n",
        ),
        name,
    );
}

/// `encode_seq_map_values` (`map_filter.rs`).
#[test]
fn seq_map_values_does_not_leak_carrier_bound() {
    let name = "seq_map_values_does_not_leak_carrier_bound";
    assert_not_verified(
        &seq_len_bound_program(
            name,
            "#[trust_vc::requires(a.map_values(SpecFn::new(|x: i32| x + 1i32)).len() == a.len())]\n",
        ),
        name,
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS.
//
// (1) An exec `Vec` length genuinely IS `<= usize::MAX` (`bounded_len` ->
//     `assert_len_usize_bounded`), so the SAME assertion must still be PROVED
//     there. This is what separates the fix from blanket rejection: it
//     distinguishes exec `Vec` from spec `Seq`, which `TrustVcType` conflates.
// (2) A collection equality must still prove itself, for BOTH `Seq` and `Vec`.
//     Four earlier attempts at this fix died on this pin.
// ---------------------------------------------------------------------------

#[test]
fn vec_len_usize_bound_still_verifies() {
    let name = "vec_len_usize_bound_still_verifies";
    let code = format!(
        "#[trust_vc::requires(a == b)]\n\
         #[trust_vc::ensures(true)]\n\
         pub fn {name}(a: Vec<i32>, b: Vec<i32>) {{\n    \
         trust_vc::assert!(a.len() <= {USIZE_MAX_LIT});\n}}\n"
    );
    assert_verified(&code, name);
}

#[test]
fn seq_reflexive_equality_still_verifies() {
    let name = "seq_reflexive_equality_still_verifies";
    let code = format!(
        "use trust_vc_types::Seq;\n\
         #[trust_vc::requires(a == b)]\n\
         #[trust_vc::ensures(true)]\n\
         pub fn {name}(a: Seq<i32>, b: Seq<i32>) {{\n    \
         trust_vc::assert!(a == b);\n}}\n"
    );
    assert_verified(&code, name);
}

#[test]
fn vec_reflexive_equality_still_verifies() {
    let name = "vec_reflexive_equality_still_verifies";
    let code = format!(
        "#[trust_vc::requires(a == b)]\n\
         #[trust_vc::ensures(true)]\n\
         pub fn {name}(a: Vec<i32>, b: Vec<i32>) {{\n    \
         trust_vc::assert!(a == b);\n}}\n"
    );
    assert_verified(&code, name);
}

/// NEGATIVE control for the pin: assuming `a == b` must not let an arbitrary
/// concrete length claim through. Guards against "fix" shapes that keep the pin
/// verifying by making the equality assumption globally poisonous.
#[test]
fn seq_equality_does_not_prove_a_concrete_length() {
    let name = "seq_equality_does_not_prove_a_concrete_length";
    let code = format!(
        "use trust_vc_types::Seq;\n\
         #[trust_vc::requires(a == b)]\n\
         #[trust_vc::ensures(true)]\n\
         pub fn {name}(a: Seq<i32>, b: Seq<i32>) {{\n    \
         trust_vc::assert!(a.len() == 5usize);\n}}\n"
    );
    assert_not_verified(&code, name);
}
