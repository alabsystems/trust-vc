// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end guard for FV-A: the CLI must never report a verdict computed from
//! a DIFFERENT function's body and contract.
//!
//! `cargo-trust-vc` used to carry its own copy of trust-vc-core's name→function
//! walk. The copy's comment claimed to match core; it did not — core collects
//! every non-root candidate and refuses unless exactly one matches, while the
//! copy returned the FIRST source-order match. In a file with two same-named
//! methods the CLI therefore verified one method's body against that method's
//! contract and printed the verdict once per method, so a false contract on the
//! second method was reported `verified`. Swapping the two impl blocks flipped
//! both verdicts, which is the discriminator these tests encode.
//!
//! There is now ONE resolver (`trust_vc_core::resolve_function_in_file`) and a
//! bare name that denotes several functions is reported rather than silently
//! resolved.
//!
//! # Why these assertions changed shape
//!
//! The first version of this file asserted the ABSENCE of a verified verdict
//! and the PRESENCE of the string "is ambiguous in". Both were proxies. The
//! property that actually matters is the one in the first line above — each
//! verdict must be computed from the body and contract of the function it is
//! reported under — and refusing to answer is only one way to achieve it.
//!
//! Refusing turned out to be too blunt. The file scan already knows exactly
//! which item each target is (it records the signature identifier's line), and
//! it threw that away and re-asked by bare name, so the ambiguity was
//! manufactured: a legal program with `impl G for P` and `impl G for Q` could
//! not be checked at all, both methods erroring. The resolver now takes the
//! scan's line, and each method is verified against its own contract.
//!
//! So the assertions below check the real property head-on, which is STRICTER
//! than what they replaced: the verdicts are keyed by LINE, and swapping the two
//! impl blocks must move each verdict WITH its method rather than leaving it in
//! place. A resolver that returned a source-order winner passes neither. The
//! bare-name ambiguity gate itself is still exercised — by
//! `bare_function_flag_still_refuses_an_ambiguous_name`, which is the entry
//! point that genuinely has no provenance.

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
        "trust_vc_ambig_{label}_{}_{}_{}",
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

/// `line -> result` for every entry named `name`.
///
/// Keying by LINE is the whole point: a verdict is only meaningful as a claim
/// about one source item, and two entries that share a name are told apart by
/// nothing else.
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
                "two entries for `{name}` on line {line} — a line must denote one item: {stdout}"
            );
        }
    }
    out
}

/// `Risky::check` promises `result == x + 1` for the body `x`. It is FALSE.
/// `Safe::check` promises `result == x` for the same body. It is TRUE.
/// Both are spelled `check`, so neither may be reported as the other.
const SAFE_FIRST: &str = r#"
struct Safe;
struct Risky;

impl Safe {
    #[trust_vc::ensures(result == x)]
    fn check(x: u32) -> u32 {
        x
    }
}

impl Risky {
    #[trust_vc::ensures(result == x + 1)]
    fn check(x: u32) -> u32 {
        x
    }
}
"#;

const RISKY_FIRST: &str = r#"
struct Safe;
struct Risky;

impl Risky {
    #[trust_vc::ensures(result == x + 1)]
    fn check(x: u32) -> u32 {
        x
    }
}

impl Safe {
    #[trust_vc::ensures(result == x)]
    fn check(x: u32) -> u32 {
        x
    }
}
"#;

/// In both fixtures the FIRST `check` body starts on line 7 and the SECOND on
/// line 14; only WHICH struct's impl sits in each slot differs.
const FIRST_SLOT: u64 = 7;
const SECOND_SLOT: u64 = 14;

#[test]
fn same_named_methods_never_report_a_borrowed_verified() {
    // The cardinal direction: `Risky::check` promises `result == x + 1` for the
    // body `x`. That is FALSE and must be refuted no matter what its same-named
    // neighbour does. Before FV-A was closed it was printed `verified`, having
    // borrowed `Safe::check`'s verdict.
    let stdout = check_json(&temp_file("safe_first", SAFE_FIRST));
    let verdicts = verdicts_by_line(&stdout, "check");

    assert_eq!(
        verdicts.get(&SECOND_SLOT).map(String::as_str),
        Some("counterexample"),
        "SAFE_FIRST line {SECOND_SLOT} is `Risky::check`, whose postcondition is FALSE; it must \
         be refuted on its own contract: {stdout}"
    );
    // The narrowness half, in the same breath: refusing to answer would also
    // keep the false contract from being verified, and would be worthless.
    assert_eq!(
        verdicts.get(&FIRST_SLOT).map(String::as_str),
        Some("verified"),
        "SAFE_FIRST line {FIRST_SLOT} is `Safe::check`, whose postcondition is TRUE; a same-named \
         neighbour must not cost it its proof: {stdout}"
    );
}

#[test]
fn verdict_does_not_depend_on_impl_block_source_order() {
    // THE DISCRIMINATOR. These two programs differ only in the order two
    // independent impl blocks are written, so each method's verdict must travel
    // WITH the method. A source-order resolver produced the identical map for
    // both (whatever sat first won); a refusing resolver produced the identical
    // map for both as well (everything errored). Only per-item resolution makes
    // the two maps swap.
    let safe_first = check_json(&temp_file("order_safe_first", SAFE_FIRST));
    let risky_first = check_json(&temp_file("order_risky_first", RISKY_FIRST));

    let safe_first_verdicts = verdicts_by_line(&safe_first, "check");
    let risky_first_verdicts = verdicts_by_line(&risky_first, "check");

    // `Safe::check` (true contract) is in slot 1 of SAFE_FIRST and slot 2 of
    // RISKY_FIRST; `Risky::check` (false contract) is the other way round.
    assert_eq!(
        safe_first_verdicts.get(&FIRST_SLOT).map(String::as_str),
        Some("verified"),
        "SAFE_FIRST slot 1 holds Safe::check: {safe_first}"
    );
    assert_eq!(
        safe_first_verdicts.get(&SECOND_SLOT).map(String::as_str),
        Some("counterexample"),
        "SAFE_FIRST slot 2 holds Risky::check: {safe_first}"
    );
    assert_eq!(
        risky_first_verdicts.get(&FIRST_SLOT).map(String::as_str),
        Some("counterexample"),
        "RISKY_FIRST slot 1 holds Risky::check: {risky_first}"
    );
    assert_eq!(
        risky_first_verdicts.get(&SECOND_SLOT).map(String::as_str),
        Some("verified"),
        "RISKY_FIRST slot 2 holds Safe::check: {risky_first}"
    );

    // Stated as the invariant rather than four constants: the verdict is a
    // property of the method, so reordering the file must PERMUTE the map.
    assert_ne!(
        safe_first_verdicts, risky_first_verdicts,
        "if reordering two impl blocks leaves the line->verdict map unchanged, the verdicts are \
         tracking POSITION, not the method:\n{safe_first}\n{risky_first}"
    );
}

/// `--function NAME` is a FILTER over the same scanned targets, not a second
/// resolver, so it must inherit the per-item guarantee rather than fall back to
/// a name lookup. Naming a duplicated method checks BOTH, each against its own
/// contract; it does not pick one and it does not silently check nothing.
///
/// (The genuinely provenance-free entry point is the library gate,
/// `trust_vc_core::verify_function_from_file`, which still refuses an ambiguous
/// bare name outright. That refusal is pinned by
/// `crates/trust-vc/tests/external_traits_rs_trust_vc_regressions.rs`, which
/// asserts on the "is ambiguous in" / "2 definitions share that name" strings.)
#[test]
fn function_flag_checks_every_match_against_its_own_contract() {
    let path = temp_file("bare_flag", SAFE_FIRST);
    let output = Command::new(cargo_trust_vc_bin())
        .args(["trust-vc", "check", "--json", "--function", "check"])
        .arg(&path)
        .env("TRUST_VC_DISABLE_VC_CACHE", "1")
        .output()
        .expect("cargo-trust-vc should be runnable");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();

    let verdicts = verdicts_by_line(&stdout, "check");
    assert_eq!(
        verdicts.get(&SECOND_SLOT).map(String::as_str),
        Some("counterexample"),
        "`Risky::check`'s false postcondition must be refuted under --function too: {stdout}"
    );
    assert_eq!(
        verdicts.get(&FIRST_SLOT).map(String::as_str),
        Some("verified"),
        "`Safe::check`'s true postcondition must still be proven under --function: {stdout}"
    );
}

/// NARROWNESS PIN. Closing FV-A must not cost the unambiguous cases: declining
/// everything would pass the two tests above and verify nothing. A single
/// candidate must still resolve and still be PROVEN, and a false contract on a
/// uniquely-named method must still fail closed on its own merits.
#[test]
fn unambiguous_functions_still_verify_and_still_fail_closed() {
    let proven = temp_file(
        "pin_true",
        r#"
struct Counter;

impl Counter {
    #[trust_vc::requires(x < 100)]
    #[trust_vc::ensures(result == x + 1)]
    fn bump(x: u32) -> u32 {
        x + 1
    }
}
"#,
    );
    let stdout = check_json(&proven);
    assert!(
        stdout.contains("\"result\": \"verified\""),
        "a uniquely-named method must still verify: {stdout}"
    );
    assert!(
        !stdout.contains("is ambiguous in"),
        "a single candidate is not ambiguous: {stdout}"
    );

    let refuted = temp_file(
        "pin_false",
        r#"
struct Counter;

impl Counter {
    #[trust_vc::requires(x < 100)]
    #[trust_vc::ensures(result == x + 2)]
    fn bump(x: u32) -> u32 {
        x + 1
    }
}
"#,
    );
    let stdout = check_json(&refuted);
    assert!(
        stdout.contains("\"result\": \"counterexample\""),
        "a false contract on a uniquely-named method must still be refuted: {stdout}"
    );
}
