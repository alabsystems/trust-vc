// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The boundary of scope-relative bare-type-name resolution, in tests.
//!
//! FV-1 (`module_type_shadow_soundness.rs`) closed a cardinal false-verify by
//! STRIKING every colliding bare type name from the source-type registry, which
//! is sound but answers nothing. This harness pins the two halves of the
//! replacement: the cases the use site's module scope genuinely settles (which
//! must now produce a real verdict), and the cases it cannot (which must still
//! decline). Every pin below discriminates three ways — `Verified`,
//! `Counterexample` and `Err` are distinct outcomes, so a test can tell
//! "resolved to the right declaration" from "resolved to the wrong one" from
//! "declined".
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}

const RESOLUTION: &str = "module_type_shadow_resolution.rs";
const USE_IMPORT: &str = "module_type_shadow_use_import.rs";
const USE_IMPORT_FLIP: &str = "module_type_shadow_use_import_flip.rs";
const INNER_SCOPE: &str = "module_type_shadow_inner_scope.rs";
const DECLINES: &str = "module_type_shadow_declines.rs";
const CROSS_SCOPE: &str = "module_type_shadow_cross_scope.rs";

// ---- RESOLVABLE: a real verdict, not a decline ----------------------------

/// A top-level use site names the top-level declaration even though an inline
/// module declares the same bare name. `p.x <= 255u8` is provable only for the
/// top-level `u8` field, so `Verified` is the discriminating outcome.
#[test]
fn top_level_use_site_resolves_to_top_level_declaration() {
    let v = verify_function_from_file(&fx(RESOLUTION), "top_level_declaration_wins");
    eprintln!("[RES-TOP] top_level_declaration_wins => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "a top-level use site must resolve to the top-level declaration, not decline; got {v:?}"
    );
}

/// The same use site written with an explicit `self::` qualifier that names the
/// declaration scope resolution already chose.
#[test]
fn qualified_path_naming_the_winner_resolves() {
    let v = verify_function_from_file(&fx(RESOLUTION), "qualified_path_naming_the_winner_resolves");
    eprintln!("[RES-QUAL] qualified_path_naming_the_winner_resolves => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "an explicit qualifier that names the resolved declaration must be accepted; got {v:?}"
    );
}

/// A use site whose `use` binding names the SECOND-declared type resolves to
/// that one, so declaration order is not the tiebreak.
#[test]
fn use_binding_resolves_to_the_imported_declaration() {
    let v = verify_function_from_file(&fx(USE_IMPORT), "use_binding_selects_declaration");
    eprintln!("[RES-USE] use_binding_selects_declaration => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "`use alpha::T` must select the `u8` declaration; got {v:?}"
    );
}

/// IMPORT-FLIP control: identical declarations in identical order, `use beta::T`
/// instead of `use alpha::T`. The verdict must follow the import — and must not
/// be `Verified`, which is what adopting the first-declared `u8` shape would
/// produce.
#[test]
fn use_binding_flip_follows_the_import_not_the_order() {
    let v = verify_function_from_file(&fx(USE_IMPORT_FLIP), "use_binding_selects_declaration");
    eprintln!("[RES-USE-FLIP] use_binding_selects_declaration => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "`use beta::T` names the `u64` declaration, so `t.v <= 255` is refutable; got {v:?}"
    );
}

/// A use site inside `mod inner` resolves to `inner`'s own declaration, not the
/// top-level one.
#[test]
fn inner_scope_use_site_resolves_to_the_inner_declaration() {
    let v = verify_function_from_file(&fx(INNER_SCOPE), "inner_scope_declaration_wins");
    eprintln!("[RES-INNER] inner_scope_declaration_wins => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "the innermost declaration must win at a use site inside that module; got {v:?}"
    );
}

// ---- DECLINE PINS: what resolution deliberately refuses to settle ---------

/// A decline surfaces either as an extraction `Err` or as a lowering
/// `VerifyResult::Error`; both mean "no verdict was claimed". What must never
/// appear is `Verified`, and — since the whole point is that the shape is
/// unknown — a `Counterexample` would equally be a claim about a type the
/// engine could not identify.
fn assert_declines(fixture: &str, function: &str, tag: &str, why: &str) {
    let v = verify_function_from_file(&fx(fixture), function);
    eprintln!("[{tag}] {function} => {v:?}");
    let declined = match &v {
        Err(_) => true,
        Ok(VerifyResult::Error { message }) => {
            message.contains("unsupported expression") || message.contains("unknown type")
        }
        Ok(_) => false,
    };
    assert!(
        declined,
        "DECLINE PIN ({why}): resolution must fail closed here, never guess; got {v:?}"
    );
}

/// The bare carrier holds one shape, so a qualifier naming the OTHER
/// declaration has nothing to resolve to.
#[test]
fn qualified_path_naming_the_loser_declines() {
    assert_declines(
        RESOLUTION,
        "qualified_path_naming_the_loser_declines",
        "DEC-QUAL",
        "one shape per bare carrier",
    );
}

#[test]
fn glob_import_declines() {
    assert_declines(
        DECLINES,
        "glob_import_declines",
        "DEC-GLOB",
        "a glob's contents are not knowable from this file",
    );
}

#[test]
fn cfg_gated_declaration_declines() {
    assert_declines(
        DECLINES,
        "cfg_gated_declaration_declines",
        "DEC-CFG",
        "no cfg is evaluated, so both arms are live in one module",
    );
}

#[test]
fn out_of_file_import_declines() {
    assert_declines(
        DECLINES,
        "out_of_file_import_declines",
        "DEC-EXTERN",
        "an import from another file must not fall through to an in-file leaf",
    );
}

#[test]
fn renamed_import_declines() {
    assert_declines(
        DECLINES,
        "renamed_import_declines",
        "DEC-RENAME",
        "an introduced name is not a declaration this arbitration can choose among",
    );
}

/// Two code-bearing scopes disagree about one bare name, so NEITHER scope gets
/// an answer: a single bare sort cannot carry both shapes, and the other
/// scope's contracts can be lowered into the same verification context.
#[test]
fn cross_scope_disagreement_declines_at_the_outer_scope() {
    assert_declines(
        CROSS_SCOPE,
        "top_level_reads_d",
        "DEC-CROSS-OUT",
        "two code-bearing scopes resolve the name differently",
    );
}

#[test]
fn cross_scope_disagreement_declines_at_the_inner_scope() {
    assert_declines(
        CROSS_SCOPE,
        "inner_reads_d",
        "DEC-CROSS-IN",
        "two code-bearing scopes resolve the name differently",
    );
}
