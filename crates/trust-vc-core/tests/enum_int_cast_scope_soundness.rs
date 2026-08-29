// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL: the enum→int cast desugar resolved a written path against ONE
//! scope and silently answered with a confident WRONG value.
//!
//! `collect_castable_enums` walked `file.items` alone and keyed every enum by
//! its BARE name; `literal_variant_value` then read the second-to-last path
//! segment as the enum name and discarded every qualifier. So with
//! `mod m { enum E { A, B, C } }` beside a top-level `enum E { C, A, B }`, the
//! path `m::E::C` was resolved to the TOP-LEVEL `E` and rewritten to the literal
//! `0`, when `m::E::C` is 2. Both directions were wrong at once:
//!
//! * `assert!((m::E::C as u8) == 0)`  ->  VERIFIED   (it is 2)  -- false verify
//! * `assert!((m::E::C as u8) == 2)`  ->  refuted    (it is 2)  -- false refute
//!
//! and the identical defect fired for a BARE `E::C` written inside `mod m`,
//! where `E` denotes `m::E` and the pass reached for the top-level `E`. Neither
//! shape needs a trait, a generic or a macro; both are legal single-file Rust
//! and both were green under the production CLI.
//!
//! Resolution now runs through `EnumPathScopes` (use-site module + the
//! module-keyed declaration index), which answers `Undecided` — leaving the cast
//! fail-closed — wherever the file cannot settle the path. The pins below hold
//! that against degenerating into blanket rejection: resolving the path
//! CORRECTLY also made module-qualified casts work for the first time, so the
//! truths in `*_truth` verify rather than merely failing closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_eics_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

/// `m::E::C` is 2. The top-level `E::C` is 0. Declaration order differs between
/// the two constants so that neither "first wins" nor "last wins" can pass.
const COLLIDE_MOD_FIRST: &str = r#"
mod m {
    pub enum E { A, B, C }
}
enum E { C, A, B }

#[trust_vc::ensures(true)]
fn qualified_false() -> u64 {
    trust_vc::assert!((m::E::C as u8) == 0u8);
    0u64
}

#[trust_vc::ensures(true)]
fn qualified_truth() -> u64 {
    trust_vc::assert!((m::E::C as u8) == 2u8);
    0u64
}

#[trust_vc::ensures(true)]
fn toplevel_control() -> u64 {
    trust_vc::assert!((E::C as u8) == 0u8);
    0u64
}
"#;

const COLLIDE_TOP_FIRST: &str = r#"
enum E { C, A, B }
mod m {
    pub enum E { A, B, C }
}

#[trust_vc::ensures(true)]
fn qualified_false() -> u64 {
    trust_vc::assert!((m::E::C as u8) == 0u8);
    0u64
}
"#;

/// A BARE `E::C` written INSIDE `mod m` denotes `m::E::C` (== 2). Items in an
/// ancestor module are not in scope in a child, so the top-level `E` must never
/// supply this discriminant.
const INNER_BARE_NAME: &str = r#"
enum E { C, A, B }
mod m {
    pub enum E { A, B, C }

    #[trust_vc::ensures(true)]
    pub fn inner_false() -> u64 {
        trust_vc::assert!((E::C as u8) == 0u8);
        0u64
    }

    #[trust_vc::ensures(true)]
    pub fn inner_truth() -> u64 {
        trust_vc::assert!((E::C as u8) == 2u8);
        0u64
    }
}
"#;

// ---------------- CARDINAL: none of these may verify ----------------

#[test]
fn qualified_path_must_not_adopt_a_top_level_enum() {
    let r = verify("qf_modfirst", "qualified_false", COLLIDE_MOD_FIRST);
    eprintln!("[EIC-SCOPE-1] qualified_false (mod first) => {r:?}");
    assert!(
        !verified(&r),
        "FALSE-VERIFY: `m::E::C` is 2, not 0 — the top-level `E` supplied the \
         discriminant for a qualified path; got {r:?}"
    );
}

#[test]
fn qualified_path_must_not_verify_in_either_declaration_order() {
    let r = verify("qf_topfirst", "qualified_false", COLLIDE_TOP_FIRST);
    eprintln!("[EIC-SCOPE-2] qualified_false (top first) => {r:?}");
    assert!(
        !verified(&r),
        "FALSE-VERIFY: declaration order must not decide soundness; got {r:?}"
    );
}

#[test]
fn bare_name_inside_a_module_must_not_adopt_the_top_level_enum() {
    let r = verify("inner_false", "inner_false", INNER_BARE_NAME);
    eprintln!("[EIC-SCOPE-3] inner_false => {r:?}");
    assert!(
        !verified(&r),
        "FALSE-VERIFY: inside `mod m`, `E::C` is `m::E::C` == 2, not the \
         top-level `E::C` == 0; got {r:?}"
    );
}

// ---- NARROWNESS PINS: resolving correctly, not rejecting everything ----

#[test]
fn qualified_path_truth_verifies() {
    let r = verify("qt", "qualified_truth", COLLIDE_MOD_FIRST);
    eprintln!("[EIC-SCOPE-PIN1] qualified_truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: `m::E::C == 2` is TRUE and must be proved, not declined \
         — a fix that merely strikes colliding names fails here; got {r:?}"
    );
}

#[test]
fn bare_name_inside_a_module_proves_its_own_enums_truth() {
    let r = verify("it", "inner_truth", INNER_BARE_NAME);
    eprintln!("[EIC-SCOPE-PIN2] inner_truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: inside `mod m`, `E::C == 2` is TRUE; got {r:?}"
    );
}

#[test]
fn top_level_cast_beside_a_colliding_module_enum_still_verifies() {
    let r = verify("tc", "toplevel_control", COLLIDE_MOD_FIRST);
    eprintln!("[EIC-SCOPE-PIN3] toplevel_control => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: the top-level `E::C == 0` is TRUE and unaffected by a \
         same-named module enum; got {r:?}"
    );
}

/// Before the fix a module-declared enum had NO cast support at all (the
/// registry never left `file.items`), so `m::E::C as u8` fail-closed whenever
/// there was nothing to collide with. Scope-correct resolution is what turned
/// that into a real capability.
const NO_COLLISION: &str = r#"
mod m {
    pub enum E { A, B, C }
}

#[trust_vc::ensures(true)]
fn truth() -> u64 {
    trust_vc::assert!((m::E::C as u8) == 2u8);
    0u64
}

#[trust_vc::ensures(true)]
fn falsehood() -> u64 {
    trust_vc::assert!((m::E::C as u8) == 0u8);
    0u64
}

#[trust_vc::ensures(true)]
fn crate_rooted_truth() -> u64 {
    trust_vc::assert!((crate::m::E::C as u8) == 2u8);
    0u64
}

#[trust_vc::ensures(true)]
fn self_rooted_truth() -> u64 {
    trust_vc::assert!((self::m::E::C as u8) == 2u8);
    0u64
}
"#;

#[test]
fn module_qualified_cast_is_supported_not_merely_declined() {
    let r = verify("nc_t", "truth", NO_COLLISION);
    eprintln!("[EIC-SCOPE-PIN4] no-collision truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: `m::E::C == 2` must be PROVED; got {r:?}"
    );
}

#[test]
fn module_qualified_cast_still_refutes_a_falsehood() {
    let r = verify("nc_f", "falsehood", NO_COLLISION);
    eprintln!("[EIC-SCOPE-PIN5] no-collision falsehood => {r:?}");
    assert!(
        !verified(&r),
        "`m::E::C == 0` is FALSE and must not verify; got {r:?}"
    );
}

#[test]
fn crate_rooted_path_resolves() {
    let r = verify("nc_c", "crate_rooted_truth", NO_COLLISION);
    eprintln!("[EIC-SCOPE-PIN6] crate_rooted_truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: `crate::m::E::C == 2` must resolve; got {r:?}"
    );
}

#[test]
fn self_rooted_path_resolves() {
    let r = verify("nc_s", "self_rooted_truth", NO_COLLISION);
    eprintln!("[EIC-SCOPE-PIN7] self_rooted_truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: `self::m::E::C == 2` must resolve; got {r:?}"
    );
}

/// The PARAMETER lane resolves its type path through the same scopes. Both the
/// top-level form (a pre-existing capability) and the in-module form must model
/// the right enum and still refute a falsehood.
const PARAM_LANE: &str = r#"
enum Color { Red, Green, Blue }

#[trust_vc::ensures(true)]
fn param_top_truth(c: Color) -> u64 {
    trust_vc::assert!((c as u8) <= 2u8);
    0u64
}

#[trust_vc::ensures(true)]
fn param_top_false(c: Color) -> u64 {
    trust_vc::assert!((c as u8) <= 1u8);
    0u64
}

mod m {
    pub enum E { A, B, C }

    #[trust_vc::ensures(true)]
    pub fn param_inner_truth(c: E) -> u64 {
        trust_vc::assert!((c as u8) <= 2u8);
        0u64
    }

    #[trust_vc::ensures(true)]
    pub fn param_inner_false(c: E) -> u64 {
        trust_vc::assert!((c as u8) <= 1u8);
        0u64
    }
}
"#;

#[test]
fn top_level_parameter_lane_still_verifies() {
    let r = verify("pt", "param_top_truth", PARAM_LANE);
    eprintln!("[EIC-SCOPE-PIN8] param_top_truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: the pre-existing top-level parameter lane must survive; got {r:?}"
    );
}

#[test]
fn top_level_parameter_lane_still_refutes() {
    let r = verify("pf", "param_top_false", PARAM_LANE);
    eprintln!("[EIC-SCOPE-PIN9] param_top_false => {r:?}");
    assert!(!verified(&r), "`c as u8 <= 1` is FALSE for Blue; got {r:?}");
}

#[test]
fn in_module_parameter_lane_resolves_to_its_own_enum() {
    let r = verify("pit", "param_inner_truth", PARAM_LANE);
    eprintln!("[EIC-SCOPE-PIN10] param_inner_truth => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: a parameter typed by the enclosing module's own enum \
         must resolve; got {r:?}"
    );
}

#[test]
fn in_module_parameter_lane_still_refutes() {
    let r = verify("pif", "param_inner_false", PARAM_LANE);
    eprintln!("[EIC-SCOPE-PIN11] param_inner_false => {r:?}");
    assert!(
        !verified(&r),
        "`c as u8 <= 1` is FALSE for `E::C`; got {r:?}"
    );
}

// ---- DECLINE PINS: shapes the file cannot settle must fail closed ----

/// A NON-CASTABLE declaration occupies its name. The top-level `E` here is
/// fielded, so `E::B as u8` must stay fail-closed rather than fall through to
/// the castable `m::E`. This is what `all_enum_names` buys.
const NON_CASTABLE_SHADOW: &str = r#"
enum E { A(u8), B }
mod m {
    pub enum E { A, B }
}

#[trust_vc::ensures(true)]
fn shadowed() -> u64 {
    trust_vc::assert!((E::B as u8) == 1u8);
    0u64
}
"#;

#[test]
fn a_non_castable_local_enum_is_not_replaced_by_a_castable_one_elsewhere() {
    let r = verify("ncs", "shadowed", NON_CASTABLE_SHADOW);
    eprintln!("[EIC-SCOPE-DECLINE1] shadowed => {r:?}");
    assert!(
        !verified(&r),
        "a fielded top-level `E` occupies the name; `m::E` must not supply its \
         discriminants; got {r:?}"
    );
}

/// A glob can introduce `E` from anywhere, so a qualified head is undecidable.
const GLOB_IMPORT: &str = r#"
mod other {
    pub enum E { A, B, C }
}
use other::*;

#[trust_vc::ensures(true)]
fn globbed() -> u64 {
    trust_vc::assert!((other::E::C as u8) == 9u8);
    0u64
}
"#;

#[test]
fn a_glob_import_makes_a_qualified_head_undecidable() {
    let r = verify("glob", "globbed", GLOB_IMPORT);
    eprintln!("[EIC-SCOPE-DECLINE2] globbed => {r:?}");
    assert!(
        !verified(&r),
        "a falsehood must never verify under a glob import; got {r:?}"
    );
}

/// An out-of-line `mod m;` has no content in this file, so nothing it declares
/// can be resolved and a same-named inline enum must not stand in for it.
const OUT_OF_LINE: &str = r#"
mod far;
enum E { C, A, B }

#[trust_vc::ensures(true)]
fn out_of_line() -> u64 {
    trust_vc::assert!((far::E::C as u8) == 0u8);
    0u64
}
"#;

#[test]
fn an_out_of_line_module_path_fails_closed() {
    let r = verify("ool", "out_of_line", OUT_OF_LINE);
    eprintln!("[EIC-SCOPE-DECLINE3] out_of_line => {r:?}");
    assert!(
        !verified(&r),
        "`far::E` is not in this file; the top-level `E` must not supply it; got {r:?}"
    );
}

/// A parameter typed by a QUALIFIED path makes the generated `match` arms
/// `m::E::A => 0`. Both directions must be right: before the fix, `c: m::E`
/// never resolved at all (`path.get_ident()` requires a single segment).
const QUALIFIED_PARAM: &str = r#"
mod m {
    pub enum E { A, B, C }
}

#[trust_vc::ensures(true)]
fn qualified_param_true(c: m::E) -> u64 {
    trust_vc::assert!((c as u8) <= 2u8);
    0u64
}

#[trust_vc::ensures(true)]
fn qualified_param_false(c: m::E) -> u64 {
    trust_vc::assert!((c as u8) <= 1u8);
    0u64
}
"#;

#[test]
fn qualified_parameter_type_resolves_and_verifies() {
    let r = verify("qpt", "qualified_param_true", QUALIFIED_PARAM);
    eprintln!("[EIC-SCOPE-PIN12] qualified_param_true => {r:?}");
    assert!(
        verified(&r),
        "NARROWNESS PIN: `c: m::E` must resolve and `c as u8 <= 2` is TRUE; got {r:?}"
    );
}

#[test]
fn qualified_parameter_type_still_refutes() {
    let r = verify("qpf", "qualified_param_false", QUALIFIED_PARAM);
    eprintln!("[EIC-SCOPE-PIN13] qualified_param_false => {r:?}");
    assert!(
        !verified(&r),
        "`c as u8 <= 1` is FALSE for `m::E::C`; got {r:?}"
    );
}
