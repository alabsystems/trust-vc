// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Identifiers that rustc reads as one name and the lane read as two.
//!
//! rustc reads every identifier in Unicode normalization form C, so `\u{212A}`
//! (KELVIN SIGN) is `K`, and `W` followed by `e` and a combining acute accent
//! is `W\u{e9}`. The lane compared the strings `syn` gives as written. Beside
//! `mod a { pub type K = u64; }`, it read a `K` that rustc binds to `mod z {
//! pub type \u{212A} = u8; }` as `a::K`, and `v / 2 + 200` over that byte
//! overflows at `v = 255` (built with `trustc`, `size_of::<K>()` is 1).
//!
//! Every liar below was `Verified`. Each Kelvin-sign liar spells the sign in
//! one line, and its twin replaces that line with an ASCII one that keeps the
//! program true; the twin verifies. A file that spells an identifier outside
//! ASCII is now refused whatever it means (`vc_extraction::identifier_spelling`),
//! so a decomposed-accent liar, which spells one in every line that names the
//! type, has no twin that verifies: its true variant is refused too. A `use`
//! or a path that reaches the Kelvin-sign alias is refused already by the
//! type-name rule, whose message comes first.

use trust_vc_core::{verify_function_from_file, VerifyResult};

static FIXTURE_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The tag every refusal of the identifier rule starts with.
const TAG: &str = "identifier spelling";

fn verify(src: &str, func: &str) -> Result<VerifyResult, String> {
    let seq = FIXTURE_SEQ.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_identifier_spelling_{}_{}_{seq}.rs",
        std::process::id(),
        func
    ));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(path.to_str().expect("utf8 path"), func)
        })
        .map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&path);
    result
}

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// A true program: must verify.
    Verified,
    /// Refused by the identifier rule: an `Error` carrying the tag and this
    /// text.
    Refused(&'static str),
    /// Any answer but `Verified`.
    NotVerified,
}

fn render(r: &Result<VerifyResult, String>) -> String {
    match r {
        Ok(VerifyResult::Verified) => "Verified".into(),
        Ok(VerifyResult::Counterexample {
            obligation_name, ..
        }) => format!("Counterexample({obligation_name})"),
        Ok(VerifyResult::Error { message }) => {
            format!("Error({})", message.chars().take(300).collect::<String>())
        }
        Ok(other) => format!("{:.300}", format!("{other:?}")),
        Err(e) => format!("Err({})", e.chars().take(300).collect::<String>()),
    }
}

/// Runs every `(program, function, expectation)` row and fails once, listing
/// each mismatch.
fn check(rows: &[(&str, &str, Expect)]) {
    let mut failures = Vec::new();
    for (src, func, expect) in rows {
        let r = verify(src, func);
        let ok = match expect {
            Expect::Verified => matches!(r, Ok(VerifyResult::Verified)),
            Expect::Refused(text) => matches!(&r, Ok(VerifyResult::Error { message })
                if message.starts_with(TAG) && message.contains(text)),
            Expect::NotVerified => !matches!(r, Ok(VerifyResult::Verified)),
        };
        println!(
            "{func}: expect={expect:?} got={} {}",
            render(&r),
            if ok { "ok" } else { "MISMATCH" }
        );
        if !ok {
            failures.push(format!("{func}: expected {expect:?}, got {}", render(&r)));
        }
    }
    assert!(
        failures.is_empty(),
        "{} mismatch(es):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

use Expect::{NotVerified, Refused, Verified};

const KELVIN: &str = "the identifier `\u{212A}`, whose character U+212A";

/// `use z::*;` binds `K` to `z`'s byte, declared with the Kelvin sign.
const SRC_GLOB: &str = "mod a { pub type K = u64; }\n\
                        mod z { pub type \u{212A} = u8; }\n\
                        use z::*;\n\
                        fn u1(v: K) { let z = v / 2 + 200; }\n";

const SRC_GLOB_TWIN: &str = "mod a { pub type K = u64; }\n\
                             mod z { pub use super::a::K; }\n\
                             use z::*;\n\
                             fn u1(v: K) { let z = v / 2 + 200; }\n";

/// `use z::K;` imports the byte.
const SRC_USE: &str = "mod a { pub type K = u64; }\n\
                       mod z { pub type \u{212A} = u8; }\n\
                       use z::K;\n\
                       fn u2(v: K) { let z = v / 2 + 200; }\n";

const SRC_USE_TWIN: &str = "mod a { pub type K = u64; }\n\
                            mod z { pub use super::a::K; }\n\
                            use z::K;\n\
                            fn u2(v: K) { let z = v / 2 + 200; }\n";

/// The path `z::K` names the byte.
const SRC_PATH: &str = "mod a { pub type K = u64; }\n\
                        mod z { pub type \u{212A} = u8; }\n\
                        fn u3(v: z::K) { let z = v / 2 + 200; }\n";

const SRC_PATH_TWIN: &str = "mod a { pub type K = u64; }\n\
                             mod z { pub use super::a::K; }\n\
                             fn u3(v: z::K) { let z = v / 2 + 200; }\n";

/// In `mod m`, the alias declared with the Kelvin sign shadows nothing the
/// lane sees, and is the `K` of `u7`.
const SRC_SHADOW: &str = "mod a { pub type K = u64; }\n\
                          use a::K;\n\
                          mod m {\n\
                          pub type \u{212A} = u8;\n\
                          pub fn u7(v: K) { let z = v / 2 + 200; }\n\
                          }\n";

const SRC_SHADOW_TWIN: &str = "mod a { pub type K = u64; }\n\
                               use a::K;\n\
                               mod m {\n\
                               use super::K;\n\
                               pub fn u7(v: K) { let z = v / 2 + 200; }\n\
                               }\n";

/// The decomposed `We\u{301}` in `mod z` is the `W\u{e9}` the glob imports.
const SRC_NFD_GLOB: &str = "mod a { pub type W\u{e9} = u64; }\n\
                            mod z { pub type We\u{301} = u8; }\n\
                            use z::*;\n\
                            fn u15(v: W\u{e9}) { let z = v / 2 + 200; }\n";

/// True, and refused: `z`'s alias is `u64` too.
const SRC_NFD_GLOB_TRUE: &str = "mod a { pub type W\u{e9} = u64; }\n\
                                 mod z { pub type We\u{301} = u64; }\n\
                                 use z::*;\n\
                                 fn u15(v: W\u{e9}) { let z = v / 2 + 200; }\n";

/// The same through a `use`, which the type-name rule refuses first.
const SRC_NFD_USE: &str = "mod a { pub type W\u{e9} = u64; }\n\
                           mod z { pub type We\u{301} = u8; }\n\
                           use z::W\u{e9};\n\
                           fn u5(v: W\u{e9}) { let z = v / 2 + 200; }\n";

#[test]
fn an_identifier_rustc_normalizes_refuses_the_file() {
    check(&[
        (SRC_GLOB, "u1", Refused(KELVIN)),
        (SRC_GLOB_TWIN, "u1", Verified),
        (SRC_SHADOW, "u7", Refused(KELVIN)),
        (SRC_SHADOW_TWIN, "u7", Verified),
        (SRC_USE, "u2", NotVerified),
        (SRC_USE_TWIN, "u2", Verified),
        (SRC_PATH, "u3", NotVerified),
        (SRC_PATH_TWIN, "u3", Verified),
        (SRC_NFD_GLOB, "u15", Refused("U+00E9")),
        (SRC_NFD_GLOB_TRUE, "u15", Refused("U+00E9")),
        (SRC_NFD_USE, "u5", NotVerified),
    ]);
}
