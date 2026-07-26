// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression: a let-bound GHOST collection built with a value-producing builder
//! chain (`Seq::empty().push(..).push(..)`, `Set::empty().insert(..)`) must
//! survive a later PURE combinator applied to it (`s.map(..)`, `s.subrange(..)`),
//! so the original binding is still resolvable in a subsequent assertion.
//!
//! Before the fix, `expr_models_ghost_collection` only recognised a chain built
//! from `pure_ghost_collection_combinator` methods; `push`/`insert`/`update`/
//! `remove` were excluded (they name in-place mutators on the *exec* twins
//! `Vec`/`HashSet`), so `let s = Seq::empty().push(1).push(2)` was NOT ghost-
//! marked. A following `let t = s.map(f)` then fell through the receiver-
//! preservation gate, invalidated `s`, and a later `s.len()` failed to lower with
//! `unresolved variable s`.
//!
//! SOUNDNESS: `expr_models_ghost_collection`'s recursion bottoms out at a ghost
//! CONSTRUCTOR (`Seq::empty`/`Set::new`/…), so an exec chain (`Vec::new().push`)
//! is never marked. The mark only enables preservation for genuinely pure
//! combinators (the receiver value is unchanged), so no mutated receiver can
//! carry stale state forward — see `ghost_collection_value_producing_method`.

use super::*;
use crate::encoder::VerifyResult;

fn verify_named(code: &str, name: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    let vc = extract_verification_conditions(func).unwrap_or_else(|err| {
        panic!("fn {name} should extract cleanly (not unresolved-var): {err}")
    });
    vc.verify()
}

fn assert_verified(code: &str, name: &str) {
    match verify_named(code, name) {
        VerifyResult::Verified => {}
        other => panic!(
            "fn {name} should verify (ghost-collection binding must survive), got: {other:?}"
        ),
    }
}

/// `let s = Seq::empty().push(..)..; let t = s.map(..); assert(t.len() == s.len())`.
/// The `.map` receiver `s` must survive so the trailing `s.len()` resolves.
#[test]
fn seq_push_chain_survives_later_map() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let s = trust_vc_types::Seq::<i32>::empty().push(10i32).push(20i32).push(30i32);
            let t = s.map(trust_vc_types::SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a));
            trust_vc::assert!(t.len() == s.len());
        }
    "#;
    assert_verified(code, "test");
}

/// The same for a length-preserving pure combinator reached through `subrange`:
/// `let s = ..push chain..; let u = s.subrange(0,2); assert(u.len() == 2 && s.len() == 3)`.
#[test]
fn seq_push_chain_survives_later_subrange() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            let s = trust_vc_types::Seq::<i32>::empty().push(10i32).push(20i32).push(30i32);
            let u = s.subrange(0usize, 2usize);
            trust_vc::assert!(u.len() == 2usize);
            trust_vc::assert!(s.len() == 3usize);
        }
    "#;
    assert_verified(code, "test");
}
