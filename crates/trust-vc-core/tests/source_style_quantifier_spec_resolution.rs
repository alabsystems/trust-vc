// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression: a SOURCE-STYLE quantifier / choose (`forall|..|`, `exists|..|`,
//! `choose|..|`) whose body calls a free spec function must have that spec fn
//! resolved (its body axiom emitted, its return type registered).
//!
//! `assert!((choose|n: nat| cnatf(n)) >= 0)` does NOT parse as plain Rust — the
//! bare `choose|n|` reads as a bitwise-or — so the spec-fn reference collector
//! (`called_names_in_block`) silently skipped the closure body and never applied
//! `cnatf`, and lowering the obligation failed with "unknown return type for
//! function 'cnatf'". The `choose!(..)` MACRO form parsed fine and worked. The
//! collector now falls back to the chain-aware parser, so the source-style form
//! resolves the spec fn too. This unblocks the choose.rs `test_refine*` family
//! (#2777) and every source-style `forall|i| spec_fn(i)` in an assert/assume.
//!
//! Guards check BOTH directions: a true spec-fn property verifies, and a FALSE
//! one still fails closed (the fix resolves the fn, it does not fabricate truth).

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/source_style_quantifier_spec_resolution");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn verified(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Verified))
}

const PRELUDE: &str = r#"
use trust_vc_types::{int, nat};
#[trust_vc::spec]
fn cnatf(n: nat) -> bool { true }
#[trust_vc::spec]
fn cintf(n: int) -> bool { true }
#[trust_vc::spec]
fn is_neg(n: nat) -> bool { n < 0 }
"#;

fn src(body: &str) -> String {
    format!("{PRELUDE}\n#[trust_vc::ensures(true)]\nfn test() {{\n{body}\n}}\n")
}

#[test]
fn source_style_forall_resolves_spec_fn() {
    let code = src("    trust_vc::assert!(forall|n: nat| cnatf(n));");
    let r = verify(&code, "test");
    assert!(
        verified(&r),
        "source-style forall with a spec fn should verify, got {r:?}"
    );
}

#[test]
fn source_style_exists_resolves_spec_fn() {
    let code = src("    trust_vc::assume!(exists|n: nat| cnatf(n));\n    trust_vc::assert!(true);");
    let r = verify(&code, "test");
    assert!(
        verified(&r),
        "source-style exists with a spec fn should verify, got {r:?}"
    );
}

#[test]
fn source_style_choose_nat_refinement_resolves_spec_fn() {
    // choose over nat is >= 0 (nat refinement), even for an unsatisfiable body;
    // the spec-fn call `cintf(n as int)` must resolve. Mirrors choose.rs test_refine.
    let code = src("    trust_vc::assert!((choose|n: nat| cintf(n as int) && n < 0) >= 0);");
    let r = verify(&code, "test");
    assert!(
        verified(&r),
        "source-style choose (nat refinement) with a spec fn should verify, got {r:?}"
    );
}

#[test]
fn source_style_forall_false_spec_fn_still_fails_closed() {
    // SOUNDNESS: resolving the spec fn must not fabricate truth — a forall over a
    // FALSE predicate (`is_neg(n) == n < 0`, false for every nat) must NOT verify.
    let code = src("    trust_vc::assert!(forall|n: nat| is_neg(n));");
    let r = verify(&code, "test");
    assert!(
        !verified(&r),
        "a source-style forall over a FALSE spec-fn property must fail closed, got {r:?}"
    );
}
