// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (modules cluster, 2026-09-11): two top-level
//! functions of one file that both `use self::m::{f, T};` in their outer block
//! no longer refuse each other. The alias equality `f == m::f` is query-global,
//! so it is admitted only when every OTHER function referencing the spelling
//! is a top-level fn whose own outer-block import binds the same spelling to
//! the same source path and whose contract attributes do not mention it. The
//! liars pin that everything else keeps failing closed: the same spelling
//! imported from another module, the spelling used in an attribute, a reference
//! without any import, a nested-block import, and a function inside an inline
//! module.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> Result<VerifyResult, String> {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_buasi_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    result
}

const SHARED: &str = r#"
mod m {
    pub struct Car {
        pub four_doors: bool,
    }

    #[trust_vc::spec]
    #[trust_vc::opaque]
    pub fn opaque_is_four_doors(c: Car) -> bool {
        c.four_doors
    }

    #[trust_vc::spec]
    pub fn is_four_doors(c: Car) -> bool {
        c.four_doors
    }
}

// CONTROL: the import is shared with `without_reveal` below; the reveal opens
// the body and the assertion verifies.
#[trust_vc::ensures(true)]
fn imported_reveal_verifies() {
    use self::m::{opaque_is_four_doors, Car};
    let c = Car { four_doors: true };
    trust_vc::reveal!(opaque_is_four_doors);
    trust_vc::assert!(opaque_is_four_doors(c));
}

// CONTROL (opacity kept): the same import without a reveal leaves the body
// hidden — the assertion is NOT proved (a Counterexample or a solver "not
// proved", depending on the datatype shape), and in particular it is NOT the
// cross-function alias refusal and NOT Verified.
#[trust_vc::ensures(true)]
fn without_reveal_is_refuted() {
    use self::m::{opaque_is_four_doors, Car};
    let c = Car { four_doors: true };
    trust_vc::assert!(opaque_is_four_doors(c));
}

// CONTROL (non-opaque): two functions sharing a plain spec import.
#[trust_vc::ensures(true)]
fn shared_plain_import_verifies() {
    use self::m::{is_four_doors, Car};
    let c = Car { four_doors: true };
    trust_vc::assert!(is_four_doors(c));
}

// LIAR: the shared import does not make a false assertion true.
#[trust_vc::ensures(true)]
fn shared_plain_import_liar() {
    use self::m::{is_four_doors, Car};
    let c = Car { four_doors: false };
    trust_vc::assert!(is_four_doors(c));
}
"#;

const OTHER_MODULE: &str = r#"
mod m {
    #[trust_vc::spec]
    pub fn shared() -> bool { true }
}
mod other {
    #[trust_vc::spec]
    pub fn shared() -> bool { false }
}

#[trust_vc::ensures(true)]
fn target() {
    use self::m::shared;
    trust_vc::assert!(shared());
}

// The same SPELLING, a different item: must keep refusing.
#[trust_vc::ensures(true)]
fn sibling_imports_other() {
    use self::other::shared;
    trust_vc::assert!(!shared());
}
"#;

const ATTRIBUTE_REFERENCE: &str = r#"
mod m {
    #[trust_vc::spec]
    pub fn shared() -> bool { true }
}

#[trust_vc::ensures(true)]
fn target() {
    use self::m::shared;
    trust_vc::assert!(shared());
}

// Identical body import, but the spelling ALSO appears in a contract attribute,
// which resolves at module scope: must keep refusing.
#[trust_vc::ensures(shared())]
fn sibling_attribute_reference() -> bool {
    use self::m::shared;
    shared()
}
"#;

const NO_IMPORT: &str = r#"
mod m {
    #[trust_vc::spec]
    pub fn shared() -> bool { true }
}

#[trust_vc::spec]
fn wrapper() -> bool { shared() }

#[trust_vc::ensures(true)]
fn target() {
    use self::m::shared;
    trust_vc::assert!(shared());
    trust_vc::assert!(wrapper());
}
"#;

const NESTED_BLOCK_IMPORT: &str = r#"
mod m {
    #[trust_vc::spec]
    pub fn shared() -> bool { true }
}

#[trust_vc::ensures(true)]
fn target() {
    use self::m::shared;
    trust_vc::assert!(shared());
}

// The sibling's import is NESTED (not its outer block): must keep refusing.
#[trust_vc::ensures(true)]
fn sibling_nested_import() {
    {
        use self::m::shared;
        trust_vc::assert!(shared());
    }
}
"#;

const INLINE_MODULE_SIBLING: &str = r#"
mod m {
    #[trust_vc::spec]
    pub fn shared() -> bool { true }
}

#[trust_vc::ensures(true)]
fn target() {
    use self::m::shared;
    trust_vc::assert!(shared());
}

mod inner {
    // Textually the same import, but `self::m` is resolved from `inner`: must
    // keep refusing.
    #[trust_vc::ensures(true)]
    pub fn sibling_in_module() {
        use self::m::shared;
        trust_vc::assert!(shared());
    }
}
"#;

fn expect_verified(id: &str, func: &str, src: &str) {
    match verify(id, func, src) {
        Ok(VerifyResult::Verified) => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str, src: &str) {
    match verify(id, func, src) {
        Ok(VerifyResult::Counterexample { .. }) => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

fn expect_alias_refusal(id: &str, func: &str, src: &str) {
    let message = match verify(id, func, src) {
        Ok(VerifyResult::Error { message }) => message,
        Err(message) => message,
        other => panic!("{func}: expected the alias refusal, got {other:?}"),
    };
    assert!(
        message.contains("is also referenced from source function"),
        "{func}: expected the cross-function alias refusal, got: {message}"
    );
}

#[test]
fn control_shared_import_with_reveal_verifies() {
    expect_verified("c1", "imported_reveal_verifies", SHARED);
}

#[test]
fn control_shared_import_without_reveal_keeps_opacity() {
    match verify("c2", "without_reveal_is_refuted", SHARED) {
        Ok(VerifyResult::Counterexample { .. })
        | Ok(VerifyResult::NotProved { .. })
        | Ok(VerifyResult::Unknown { .. }) => {}
        other => panic!(
            "without_reveal_is_refuted: the opaque body must stay hidden (not Verified) and the \
             shared import must not be refused (not Error), got {other:?}"
        ),
    }
}

#[test]
fn control_shared_plain_import_verifies() {
    expect_verified("c3", "shared_plain_import_verifies", SHARED);
}

#[test]
fn liar_shared_plain_import_is_refuted() {
    expect_counterexample("l1", "shared_plain_import_liar", SHARED);
}

#[test]
fn same_spelling_from_another_module_still_fails_closed() {
    expect_alias_refusal("f1", "target", OTHER_MODULE);
}

#[test]
fn attribute_reference_in_sibling_still_fails_closed() {
    expect_alias_refusal("f2", "target", ATTRIBUTE_REFERENCE);
}

#[test]
fn reference_without_import_still_fails_closed() {
    expect_alias_refusal("f3", "target", NO_IMPORT);
}

#[test]
fn nested_block_import_in_sibling_still_fails_closed() {
    expect_alias_refusal("f4", "target", NESTED_BLOCK_IMPORT);
}

#[test]
fn sibling_inside_inline_module_still_fails_closed() {
    expect_alias_refusal("f5", "target", INLINE_MODULE_SIBLING);
}
