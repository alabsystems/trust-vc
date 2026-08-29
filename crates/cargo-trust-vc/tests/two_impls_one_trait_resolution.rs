// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One trait, TWO impls: each impl's method must be verified against its OWN
//! contract, and a legal program must not be failed for containing both.
//!
//! # The defect
//!
//! `cargo trust-vc check <file>` scans the file, records each annotated
//! function's signature-identifier LINE, and then asked the resolver for the
//! body by BARE NAME — throwing the line away. With `impl G for P` and
//! `impl G for Q` the name `w` denotes two methods, so the resolver correctly
//! refused, and BOTH entries came back
//! `error: Function 'w' is ambiguous ... 2 definitions share that name`.
//!
//! The ambiguity was manufactured by the round-trip. The scan never had any
//! doubt which item it meant. The cost was total: ordinary two-impl trait code
//! could not be checked at all.
//!
//! This is the FUNCTION-name member of the family fixed for trait names at
//! `3f12aff3` and for type names at `a10aea13` — a duplicate-name gate that
//! failed the FILE instead of resolving the name it had the information to
//! resolve.
//!
//! # The soundness boundary these tests pin
//!
//! Resolving more must never let the WRONG impl's contract answer. The
//! cross-wire pin below is the exact shape of the cardinal defect closed at
//! `63e3bcf3`: two impls with DIFFERENT `ensures`, one of them a LIAR, run in
//! BOTH assignments. If a verdict were borrowed from the sibling impl, the liar
//! would be reported `verified` in one of the two — so the liar is required to
//! be refuted in each position, and the truthful one is required to keep its
//! proof in each position.
//!
//! Ground truth was established by compiling and running the corresponding
//! plain-Rust program under stock `rustc --edition 2021`: `P.w() == 7` and
//! `Q.w() == 9`.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn temp_file(label: &str, source: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "trust_vc_two_impls_{label}_{}_{}_{}",
        std::process::id(),
        unique,
        sequence
    ));
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");
    let path = dir.join(format!("{label}.rs"));
    std::fs::write(&path, source).expect("fixture should be writable");
    path
}

fn cargo_trust_vc_bin() -> PathBuf {
    for key in [
        "CARGO_BIN_EXE_cargo-trust-vc",
        "CARGO_BIN_EXE_cargo_trust_vc",
    ] {
        if let Ok(path) = std::env::var(key) {
            return PathBuf::from(path);
        }
    }
    let binary_name = format!("cargo-trust-vc{}", std::env::consts::EXE_SUFFIX);
    if let Ok(target_dir) = std::env::var("CARGO_TARGET_DIR") {
        let candidate = PathBuf::from(target_dir).join("debug").join(&binary_name);
        if candidate.exists() {
            return candidate;
        }
    }
    let fallback = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/debug")
        .join(&binary_name);
    if fallback.exists() {
        return fallback;
    }
    panic!("cargo-trust-vc binary not found; run `cargo build` first");
}

fn check_json(path: &PathBuf) -> String {
    let output = Command::new(cargo_trust_vc_bin())
        .args(["trust-vc", "check", "--json"])
        .arg(path)
        .env("TRUST_VC_DISABLE_VC_CACHE", "1")
        .output()
        .expect("cargo-trust-vc should be runnable");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn verdicts_by_line(stdout: &str, name: &str) -> BTreeMap<u64, String> {
    let parsed: serde_json::Value = serde_json::from_str(stdout)
        .unwrap_or_else(|err| panic!("check --json output must parse: {err}\n{stdout}"));
    let mut out = BTreeMap::new();
    for entry in parsed["functions"]
        .as_array()
        .expect("`functions` must be an array")
    {
        if entry["name"].as_str() == Some(name) {
            let line = entry["line"].as_u64().expect("entry must carry a line");
            let result = entry["result"]
                .as_str()
                .expect("entry must carry a result")
                .to_string();
            assert!(
                out.insert(line, result).is_none(),
                "two entries for `{name}` on line {line}: {stdout}"
            );
        }
    }
    out
}

/// In every fixture below `impl G for P`'s method body is on line 6 and
/// `impl G for Q`'s is on line 8.
const P_LINE: u64 = 6;
const Q_LINE: u64 = 8;

/// Both impls truthful. This is the CAPABILITY assertion: an ordinary
/// two-impl program must verify. Before the fix both entries were `error`.
const BOTH_TRUE: &str = r#"#[trust_vc::trait_spec]
trait G { fn w(&self) -> u64; }
struct P;
struct Q;
#[trust_vc::trait_impl]
impl G for P { #[trust_vc::ensures(result == 7u64)] fn w(&self) -> u64 { 7u64 } }
#[trust_vc::trait_impl]
impl G for Q { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64 { 9u64 } }
"#;

/// CROSS-WIRE, liar in the P slot: P's body returns 7 but claims 9. Q is
/// truthful. If P's target borrowed Q's body, `result == 9` would VERIFY.
const LIAR_IN_P: &str = r#"#[trust_vc::trait_spec]
trait G { fn w(&self) -> u64; }
struct P;
struct Q;
#[trust_vc::trait_impl]
impl G for P { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64 { 7u64 } }
#[trust_vc::trait_impl]
impl G for Q { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64 { 9u64 } }
"#;

/// CROSS-WIRE, liar in the Q slot — the mirror. Q's body returns 9 but claims
/// 7. Running BOTH assignments is what makes this a discriminator rather than a
/// coincidence: a resolver that always picked the first (or the last) candidate
/// passes exactly one of the two.
const LIAR_IN_Q: &str = r#"#[trust_vc::trait_spec]
trait G { fn w(&self) -> u64; }
struct P;
struct Q;
#[trust_vc::trait_impl]
impl G for P { #[trust_vc::ensures(result == 7u64)] fn w(&self) -> u64 { 7u64 } }
#[trust_vc::trait_impl]
impl G for Q { #[trust_vc::ensures(result == 7u64)] fn w(&self) -> u64 { 9u64 } }
"#;

/// CAPABILITY. The whole point of the change: this legal program used to be
/// uncheckable.
#[test]
fn two_truthful_impls_of_one_trait_both_verify() {
    let stdout = check_json(&temp_file("both_true", BOTH_TRUE));
    let verdicts = verdicts_by_line(&stdout, "w");

    assert_eq!(
        verdicts.get(&P_LINE).map(String::as_str),
        Some("verified"),
        "`impl G for P`'s method proves its own ensures: {stdout}"
    );
    assert_eq!(
        verdicts.get(&Q_LINE).map(String::as_str),
        Some("verified"),
        "`impl G for Q`'s method proves its own ensures: {stdout}"
    );
    assert!(
        !stdout.contains("is ambiguous in"),
        "two impls of one trait is legal Rust and must not be reported ambiguous: {stdout}"
    );
}

/// CARDINAL, half one: the liar sits in the FIRST impl.
#[test]
fn cross_wired_liar_in_the_first_impl_is_refuted() {
    let stdout = check_json(&temp_file("liar_p", LIAR_IN_P));
    let verdicts = verdicts_by_line(&stdout, "w");

    assert_eq!(
        verdicts.get(&P_LINE).map(String::as_str),
        Some("counterexample"),
        "`impl G for P` returns 7 and claims 9 — it must NOT verify, whatever its same-named \
         neighbour proves: {stdout}"
    );
    assert_eq!(
        verdicts.get(&Q_LINE).map(String::as_str),
        Some("verified"),
        "NARROWNESS: the truthful neighbour must keep its proof: {stdout}"
    );
}

/// CARDINAL, half two: the mirror. Together with the test above this pins that
/// the verdict follows the ITEM and not the source position.
#[test]
fn cross_wired_liar_in_the_second_impl_is_refuted() {
    let stdout = check_json(&temp_file("liar_q", LIAR_IN_Q));
    let verdicts = verdicts_by_line(&stdout, "w");

    assert_eq!(
        verdicts.get(&Q_LINE).map(String::as_str),
        Some("counterexample"),
        "`impl G for Q` returns 9 and claims 7 — it must NOT verify: {stdout}"
    );
    assert_eq!(
        verdicts.get(&P_LINE).map(String::as_str),
        Some("verified"),
        "NARROWNESS: the truthful neighbour must keep its proof: {stdout}"
    );
}

/// The two cross-wire fixtures are byte-identical except for which slot lies,
/// so the pair of verdict maps must be MIRRORED. Asserting this directly means
/// a future resolver that reintroduces a positional winner reddens here even if
/// someone "fixes" the two tests above by loosening them.
#[test]
fn liar_verdict_tracks_the_impl_not_the_position() {
    let liar_p = verdicts_by_line(&check_json(&temp_file("mirror_p", LIAR_IN_P)), "w");
    let liar_q = verdicts_by_line(&check_json(&temp_file("mirror_q", LIAR_IN_Q)), "w");

    assert_eq!(
        (
            liar_p.get(&P_LINE).map(String::as_str),
            liar_p.get(&Q_LINE).map(String::as_str)
        ),
        (Some("counterexample"), Some("verified")),
        "liar in slot 1: {liar_p:?}"
    );
    assert_eq!(
        (
            liar_q.get(&P_LINE).map(String::as_str),
            liar_q.get(&Q_LINE).map(String::as_str)
        ),
        (Some("verified"), Some("counterexample")),
        "liar in slot 2 — the exact mirror: {liar_q:?}"
    );
}

/// THE SOUNDNESS BOUNDARY, stated at the CALL SITE: with one trait implemented
/// by two types, a call on a receiver of one type must get THAT impl's contract
/// and never the sibling's.
///
/// Resolving the impl-method targets (everything above) and answering a call
/// site are different lanes, so passing the former proves nothing about the
/// latter. Both directions are cross-wired here: asserting P's promise on a `Q`
/// receiver, and Q's promise on a `P` receiver, must each be REFUTED — while
/// the matching assertion still verifies, so the pin cannot be satisfied by
/// declining to answer.
///
/// Ground truth under stock `rustc --edition 2021`: `P.w() == 7`, `Q.w() == 9`.
#[test]
fn a_call_site_gets_its_own_impls_contract_not_the_siblings() {
    const CALL_SITES: &str = r#"#[trust_vc::trait_spec]
trait G { fn w(&self) -> u64; }
struct P;
struct Q;
#[trust_vc::trait_impl]
impl G for P { #[trust_vc::ensures(result == 7u64)] fn w(&self) -> u64 { 7u64 } }
#[trust_vc::trait_impl]
impl G for Q { #[trust_vc::ensures(result == 9u64)] fn w(&self) -> u64 { 9u64 } }
#[trust_vc::ensures(true)]
fn p_true(p: P) { trust_vc::assert!(p.w() == 7u64); }
#[trust_vc::ensures(true)]
fn p_crosswired(p: P) { trust_vc::assert!(p.w() == 9u64); }
#[trust_vc::ensures(true)]
fn q_true(q: Q) { trust_vc::assert!(q.w() == 9u64); }
#[trust_vc::ensures(true)]
fn q_crosswired(q: Q) { trust_vc::assert!(q.w() == 7u64); }
"#;
    let stdout = check_json(&temp_file("call_sites", CALL_SITES));
    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).expect("check --json output must parse");
    let by_name: BTreeMap<String, String> = parsed["functions"]
        .as_array()
        .expect("`functions` must be an array")
        .iter()
        .filter_map(|entry| {
            Some((
                entry["name"].as_str()?.to_string(),
                entry["result"].as_str()?.to_string(),
            ))
        })
        .collect();

    for (func, expected) in [
        ("p_true", "verified"),
        ("q_true", "verified"),
        ("p_crosswired", "counterexample"),
        ("q_crosswired", "counterexample"),
    ] {
        assert_eq!(
            by_name.get(func).map(String::as_str),
            Some(expected),
            "`{func}` must be {expected} — the sibling impl's contract must never answer for a \
             receiver it does not describe: {stdout}"
        );
    }
}

/// A trait method DECLARATION has no body, so it is reported `skipped` with a
/// reason, never `verified`.
///
/// This is a soundness pin, not a cosmetic one. While the resolver worked by
/// bare name, a file with ONE impl answered the declaration's target with the
/// IMPL's body — reporting a single proof twice, once under an item that had
/// nothing to prove. `verified` on this row would mean that borrowing is back.
#[test]
fn bodyless_trait_declaration_is_skipped_not_verified() {
    const ONE_IMPL: &str = r#"#[trust_vc::trait_spec]
trait G { #[trust_vc::ensures(result == 5u64)] fn g(&self) -> u64; }
struct X;
#[trust_vc::trait_impl]
impl G for X { fn g(&self) -> u64 { 5u64 } }
"#;
    let stdout = check_json(&temp_file("bodyless", ONE_IMPL));
    let verdicts = verdicts_by_line(&stdout, "g");

    // Line 2 is the declaration `fn g(&self) -> u64;` inside the trait.
    assert_eq!(
        verdicts.get(&2).map(String::as_str),
        Some("skipped"),
        "a bodyless trait method declaration has nothing to verify: {stdout}"
    );
}

/// NARROWNESS for the skip above: skipping the declaration must not stop a
/// contract-violating impl from being caught. The per-impl conformance
/// obligation is what carries that weight, so a bad impl still fails the file.
#[test]
fn skipping_the_declaration_still_catches_a_nonconforming_impl() {
    const BAD_IMPL: &str = r#"#[trust_vc::trait_spec]
trait G { #[trust_vc::ensures(result == 5u64)] fn g(&self) -> u64; }
struct X;
#[trust_vc::trait_impl]
impl G for X { fn g(&self) -> u64 { 6u64 } }
"#;
    let stdout = check_json(&temp_file("bad_impl", BAD_IMPL));
    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).expect("check --json output must parse");

    let conformance = parsed["functions"]
        .as_array()
        .expect("`functions` must be an array")
        .iter()
        .find(|entry| {
            entry["name"]
                .as_str()
                .is_some_and(|name| name.contains("conformance") && name.contains("for X"))
        })
        .unwrap_or_else(|| {
            panic!("the impl's conformance obligation must be enumerated: {stdout}")
        });

    assert_eq!(
        conformance["result"].as_str(),
        Some("counterexample"),
        "`impl G for X` returns 6 where the trait promises 5 — conformance must refute it: \
         {stdout}"
    );
    assert_eq!(
        parsed["summary"]["verified"].as_u64(),
        Some(0),
        "nothing in this file should be reported verified: {stdout}"
    );
}
