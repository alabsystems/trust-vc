// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VC-level caching at the prepared-context boundary.
//!
//! Computes a deterministic fingerprint over `PreparedVerificationContext`
//! and persists `VerifyResult::Verified` entries in a filesystem cache under
//! a hex-encoded SHA-256 fingerprint filename.
//! Cache hits skip both typed verification and trait-conformance
//! verification. Cache I/O failures become misses and run fresh verification.
//!
//! Part of #2646.

mod cache_canonical;

use std::path::PathBuf;

use sha2::{Digest, Sha256};

use crate::encoder::types::VerifyResult;
use crate::prepared_context::PreparedVerificationContext;

// Bump whenever verification *semantics* change so that pre-change cached
// `verified` entries (keyed by a fingerprint that does not — and cannot —
// encode the verifier's behavior) are invalidated instead of masking the new
// result. v2: division/remainder in BitVector mode now fail closed on the
// div-by-zero / signed-MIN-over-(-1) partiality obligation, which earlier
// builds wrongly reported as `verified` and persisted here. v3: the
// broadcast-vacuity gate now downgrades goals proven only because a #[broadcast]
// lemma published a contradictory assumption (vacuous Verified) across every
// goal chokepoint, so pre-v3 entries that recorded such a vacuous `verified`
// must be invalidated. v4: the Seq extensional-equality operand companion
// (`compare_seq.rs`) and the concat operand companions (`seq_transforms.rs`)
// now route a length-DECREASING view's length (subrange/skip/drop, which goes
// NEGATIVE exactly when its precondition is violated) through the
// precondition-guarded `len_index_companion_maybe_negative`. The old
// unconditional bridge asserted `bv2int(companion) == negative_len` (UNSAT),
// poisoning the context into a vacuous proof that wrongly recorded `verified`
// for goals like `seq![..].subrange(2,1) == seq![99]` (and its negation, and
// `.add(..).len() == 999`); pre-v4 entries holding such a poisoned `verified`
// must be invalidated. v5: the SAME length-decreasing-view UNSAT-poison class is
// now closed at the downstream CONSUMER transforms that re-bridge the registered
// (possibly NEGATIVE) source length — `map_values`/`map`/`filter`/`fold_left`/
// `fold_right`/`reverse` (`map_filter.rs`, `fold.rs`, `seq_transforms.rs`), plus
// `filter`'s `result_len <= source_len` bound (guarded by `source_len >= 0`).
// Pre-v5 builds wrongly recorded `verified` for goals like
// `seq![..].skip(5).map_values(..).len() == 99` / `.filter(..).len() == 99` /
// `.reverse().len() == 99` / `.fold_left(..) == 99`, `subrange(i>j)` feeding the
// same, and `empty().drop_first().map_values(..).len() == 99`; those poisoned
// entries must be invalidated. v6: a trait DEFAULT method's `ensures` whose
// trait has NO impl in the file is now verified against the (sibling-inlined)
// default body on an abstract receiver before a generic-bounded caller may trust
// the published postcondition axiom (`verify_implless_trait_defaults` in
// `trait_conformance.rs`). Pre-v6 builds wrongly recorded `verified` for a
// generic caller relying on an unestablished/contradictory default `ensures`
// (e.g. body `0u32` with `ensures(result > 100)`, body `3u32` with
// `ensures(result == 7)`, or body `self.helper()` calling a contract-less
// declaration-only sibling with `ensures(result == 7)`); those entries must be
// invalidated. v7: the fingerprint now includes the trait-impl method BODIES
// (`trait_impl_method_bodies`) and the conformance-exempt method set
// (`conformance_exempt_methods`). The impl body is decisive for trait
// conformance (the conformance pass binds the method result to the captured
// body and refutes the trait `ensures` against it), but pre-v7 the body was
// absent from the key, so two contexts differing ONLY in an impl body collided:
// a `Verified` stored for a conforming body (e.g. `m(&self)->bool { true }`)
// was served on a cache hit for a NON-conforming body (`{ false }`) against a
// `returns(true)`/`ensures` trait contract, skipping conformance entirely — a
// false-`Verified`. Pre-v7 entries that recorded such a body-blind `verified`
// must be invalidated. v8: a GENERIC-struct trait impl (`impl<P> Tr for W<P>`,
// whose Opaque self has no ay datatype) is now conformance-checked on an
// abstract (`Poly`) self — the overriding method body (or inherited default) is
// bound `result == (<body>)` and refuted against the trait `ensures`
// (`verify_generic_struct_impl_conformance` in `trait_conformance.rs`). Pre-v8
// builds SKIPPED such impls wholesale (the `contains_opaque()` guard), wrongly
// recording `verified` for a generic-bounded caller relying on an
// unestablished/contradictory `ensures` (e.g. an override `p(&self)->u32 {0u32}`
// or an all-defaults impl inheriting a default `0u32` against
// `ensures(result > 0)`); those entries must be invalidated. v9: the DEFAULT
// prover profile now refuses hint-free nonlinear-REAL goals (a product of two
// non-constant real terms, or division by a non-constant real divisor) as
// genuine theory INCOMPLETENESS — the Verus-faithful `smt.arith.nl=false`
// analog (`unhinted_nonlinear_real_construct` in `nonlinear_real.rs`; upstream
// real.rs `real_nonlinear2` pins that such goals FAIL hint-free). Builds since
// ay's NRA interval branch-and-prune lane (ay 43034c4b0c) recorded `verified`
// for such goals via the bare solver; serving those entries would mask the
// restored Verus-parity failure, so they must be invalidated. v10: the
// canonical payload now includes `hidden_fns` (the `hide!` directive set) —
// pre-hide entries were fingerprinted without it, and replaying an unhidden
// `verified` for a query that hides the function would be an unsound replay.
// v11: retry policy is now canonicalized too. `demand_inline` and
// `skip_retry_cascade` can change a fail-closed Unknown into Verified, so
// omitting them let an entry produced with stronger retries replay for a
// context whose caller disabled those retries. v12: trait type parameters,
// impl trait arguments, and default-body `ensures` are now canonicalized. They
// drive generic instantiation and default-body conformance, so omitting them
// allowed semantically different trait contexts to share an entry. v13 binds
// the build/target semantic profile and ambient encoding/resource switches;
// feature-distinct binaries and the quantified Seq::flat_map mode share a disk
// cache directory but must never share verdict authority. Pre-v13 entries must
// therefore be invalidated. v14 binds the full, clean-checkout Git revision of
// the verifier implementation and requires the cache entry to match the exact
// canonical JSON shape. Builds without an authenticated source identity bypass
// the persistent cache; malformed scalar/metadata lines can no longer smuggle
// trailing or unknown material into an otherwise authoritative entry. v15
// removes verdict authority from every pre-existing disk entry. A `Verified`
// entry may now be replayed only after this process has independently produced
// and stored that exact fingerprint, serialized entry, and canonical path. Disk
// remains a within-process accelerator; cross-process reuse requires a
// replayable certificate checked by the kernel.
pub(in crate::encoder::verification) const VC_CACHE_SCHEMA_VERSION: u32 = 15;

/// Attempt cached verification. Returns `Some(VerifyResult::Verified)` on
/// cache hit, `None` on miss or any I/O error.
/// Only exact cache entries this process stored during this run carry authority.
///
/// SOUNDNESS: the JSON file has no MAC, signature, certificate, or independent
/// writer identity. Its `entry.fingerprint == filename` check is only
/// self-consistency, so a writable file cannot itself justify `Verified` in
/// either the default target directory or an environment-redirected directory.
/// `SESSION_WRITTEN_ENTRIES` records the independent fact that this process
/// already solved and stored the same canonical context, exact serialized
/// content, and canonical path. Including path and content is essential:
/// storing a fingerprint in one directory must not authorize a forged file in
/// another directory, and a post-store mutation at the same path must revoke
/// authority. This makes disk a within-process accelerator without letting any
/// pre-existing or subsequently modified file substitute for proof. Certified
/// cross-process reuse belongs to the checked-certificate cache, not this
/// verdict-only cache.
static SESSION_WRITTEN_ENTRIES: std::sync::OnceLock<
    std::sync::Mutex<std::collections::BTreeSet<(PathBuf, String)>>,
> = std::sync::OnceLock::new();

fn session_written() -> &'static std::sync::Mutex<std::collections::BTreeSet<(PathBuf, String)>> {
    SESSION_WRITTEN_ENTRIES.get_or_init(|| std::sync::Mutex::new(std::collections::BTreeSet::new()))
}

fn record_session_write(entry_path: PathBuf, content_digest: String) {
    if let Ok(mut set) = session_written().lock() {
        set.insert((entry_path, content_digest));
    }
}

fn session_wrote(entry_path: &std::path::Path, content: &str) -> bool {
    let key = (entry_path.to_path_buf(), sha256_hex(content.as_bytes()));
    session_written()
        .lock()
        .map(|set| set.contains(&key))
        .unwrap_or(false)
}

pub(in crate::encoder) fn lookup_cache(ctx: &PreparedVerificationContext) -> Option<VerifyResult> {
    if is_cache_disabled() {
        return None;
    }
    let payload = fingerprint_payload(ctx)?;
    let hash_hex = payload.fingerprint_hex();
    let cache_dir = cache_directory()?;
    let entry_path = cache_dir.join(format!("{}.json", hash_hex));

    let content = std::fs::read_to_string(&entry_path).ok()?;
    let entry: CacheEntry = serde_json_parse(&content)?;
    let canonical_entry_path = std::fs::canonicalize(&entry_path).ok()?;

    if entry.schema_version != VC_CACHE_SCHEMA_VERSION {
        return None;
    }
    if entry.fingerprint != hash_hex {
        return None;
    }
    if entry.result != "verified" {
        return None;
    }
    // No disk location is a verdict authority. The entry is reusable only
    // after this process independently verified and stored this exact entry.
    if !session_wrote(&canonical_entry_path, &content) {
        return None;
    }

    bump_cache_hit_count();
    Some(VerifyResult::Verified)
}

/// Store a verified result in the cache. Any I/O error leaves the entry
/// unauthorized, so a later lookup misses and performs a fresh solve.
pub(in crate::encoder) fn store_cache(ctx: &PreparedVerificationContext, result: &VerifyResult) {
    if is_cache_disabled() {
        return;
    }
    if !matches!(result, VerifyResult::Verified) {
        return;
    }
    let Some(payload) = fingerprint_payload(ctx) else {
        return;
    };
    let hash_hex = payload.fingerprint_hex().to_string();
    let Some(cache_dir) = cache_directory() else {
        return;
    };

    let entry = CacheEntry {
        schema_version: VC_CACHE_SCHEMA_VERSION,
        fingerprint: hash_hex.clone(),
        display_name: payload.display_name,
        primary_location: payload.primary_location,
        result: "verified".to_string(),
    };

    let Some(json) = serialize_entry(&entry) else {
        return;
    };

    // Create parent dirs on demand.
    if std::fs::create_dir_all(&cache_dir).is_err() {
        return;
    }

    // Write to temp file, then rename into place (atomic on same filesystem).
    let tmp_path = cache_dir.join(format!("{hash_hex}.tmp"));
    let final_path = cache_dir.join(format!("{hash_hex}.json"));
    let content_digest = sha256_hex(json.as_bytes());
    if std::fs::write(&tmp_path, &json).is_ok() && std::fs::rename(&tmp_path, &final_path).is_ok() {
        if let Ok(canonical_entry_path) = std::fs::canonicalize(&final_path) {
            record_session_write(canonical_entry_path, content_digest);
        }
    }
}

// --- Cache entry ---

struct CacheEntry {
    schema_version: u32,
    fingerprint: String,
    display_name: Option<String>,
    primary_location: Option<String>,
    result: String,
}

fn serialize_entry(entry: &CacheEntry) -> Option<String> {
    let display_name = entry
        .display_name
        .as_deref()
        .map_or("null".to_string(), |n| format!("{:?}", n));
    let primary_location = entry
        .primary_location
        .as_deref()
        .map_or("null".to_string(), |l| format!("{:?}", l));
    // Manual JSON to avoid adding serde_json dependency.
    Some(format!(
        "{{\n  \"schema_version\": {},\n  \"fingerprint\": {:?},\n  \"display_name\": {},\n  \"primary_location\": {},\n  \"result\": {:?}\n}}",
        entry.schema_version,
        entry.fingerprint,
        display_name,
        primary_location,
        entry.result,
    ))
}

fn serde_json_parse(content: &str) -> Option<CacheEntry> {
    // Parse the one canonical shape emitted by `serialize_entry`. Cache files
    // carry proof authority, so merely finding a valid field prefix is not
    // sufficient: ordering, keys, commas, scalar grammar, and end-of-input all
    // have to match exactly. Unknown/duplicate/trailing material is a miss.
    let mut lines = content.trim().lines().map(str::trim);
    if lines.next()? != "{" {
        return None;
    }
    let schema_version = parse_json_u32_field(lines.next()?, "schema_version", true)?;
    let fingerprint = parse_json_string_field(lines.next()?, "fingerprint", true)?;
    let _display_name = parse_json_optional_string_field(lines.next()?, "display_name", true)?;
    let _primary_location =
        parse_json_optional_string_field(lines.next()?, "primary_location", true)?;
    let result = parse_json_string_field(lines.next()?, "result", false)?;
    if lines.next()? != "}" || lines.next().is_some() {
        return None;
    }
    Some(CacheEntry {
        schema_version,
        fingerprint,
        display_name: None,
        primary_location: None,
        result,
    })
}

fn parse_json_field_value<'a>(line: &'a str, key: &str, comma: bool) -> Option<&'a str> {
    let prefix = format!("\"{key}\": ");
    let value = line.strip_prefix(&prefix)?;
    if comma {
        value.strip_suffix(',')
    } else if value.ends_with(',') {
        None
    } else {
        Some(value)
    }
}

fn parse_json_u32_field(line: &str, key: &str, comma: bool) -> Option<u32> {
    let value = parse_json_field_value(line, key, comma)?;
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    value.parse().ok()
}

fn parse_json_string_field(line: &str, key: &str, comma: bool) -> Option<String> {
    parse_json_string_literal(parse_json_field_value(line, key, comma)?)
}

fn parse_json_optional_string_field(line: &str, key: &str, comma: bool) -> Option<Option<String>> {
    let value = parse_json_field_value(line, key, comma)?;
    if value == "null" {
        Some(None)
    } else {
        parse_json_string_literal(value).map(Some)
    }
}

fn parse_json_string_literal(value: &str) -> Option<String> {
    let value = value.strip_prefix('"')?;
    let mut chars = value.chars();
    let mut result = String::new();
    loop {
        match chars.next()? {
            '"' => return chars.next().is_none().then_some(result),
            '\\' => match chars.next()? {
                '"' => result.push('"'),
                '\\' => result.push('\\'),
                '/' => result.push('/'),
                'b' => result.push('\u{0008}'),
                'f' => result.push('\u{000c}'),
                'n' => result.push('\n'),
                'r' => result.push('\r'),
                't' => result.push('\t'),
                'u' => {
                    let hex: String = chars.by_ref().take(4).collect();
                    if hex.len() != 4 || !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                        return None;
                    }
                    let code = u32::from_str_radix(&hex, 16).ok()?;
                    result.push(char::from_u32(code)?);
                }
                _ => return None,
            },
            c if !c.is_control() => result.push(c),
            _ => return None,
        }
    }
}

// --- Environment controls ---

#[cfg(test)]
fn is_cache_disabled() -> bool {
    // Unit tests default to cache-off through the thread-local. Cache-specific
    // tests opt in explicitly, which must remain deterministic even when the
    // surrounding soundness command exports TRUST_VC_DISABLE_VC_CACHE=1. An
    // opt-in is accepted only with an explicit test cache directory, so no
    // unrelated unit test can accidentally override the ambient soundness
    // control merely by inheriting a thread-local flag.
    is_test_cache_disabled() || !has_test_cache_dir_override()
}

#[cfg(not(test))]
fn is_cache_disabled() -> bool {
    std::env::var("TRUST_VC_DISABLE_VC_CACHE")
        .map(|v| v == "1")
        .unwrap_or(false)
}

/// Test-only accessor for the resolved cache directory, so a witness test can
/// write a file where `lookup_cache` will look for one.
#[cfg(test)]
pub(in crate::encoder) fn cache_directory_for_test() -> Option<PathBuf> {
    cache_directory()
}

fn cache_directory() -> Option<PathBuf> {
    #[cfg(test)]
    {
        let dir_override = VC_CACHE_DIR_OVERRIDE.with(|cell| cell.borrow().clone());
        if let Some(dir) = dir_override {
            return Some(dir);
        }
    }
    if let Ok(dir) = std::env::var("TRUST_VC_VC_CACHE_DIR") {
        return Some(PathBuf::from(dir));
    }
    // Derive from current_exe — go up from the binary to find target/.
    let exe = std::env::current_exe().ok()?;
    // Typical layout: target/debug/deps/test_binary or target/worker_1/debug/deps/test_binary
    // Walk up to find a directory named "target".
    let mut dir = exe.parent()?;
    loop {
        if dir.file_name().is_some_and(|n| n == "target") {
            return Some(dir.join("trust-vc-cache").join("v1"));
        }
        dir = dir.parent()?;
    }
}

#[cfg(test)]
fn has_test_cache_dir_override() -> bool {
    VC_CACHE_DIR_OVERRIDE.with(|cell| cell.borrow().is_some())
}

// --- Fingerprint payload ---

struct FingerprintPayload {
    fingerprint_hex: String,
    display_name: Option<String>,
    primary_location: Option<String>,
}

impl FingerprintPayload {
    fn fingerprint_hex(&self) -> &str {
        &self.fingerprint_hex
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    const HEX_DIGITS: &[u8; 16] = b"0123456789abcdef";
    for byte in digest {
        hex.push(HEX_DIGITS[(byte >> 4) as usize] as char);
        hex.push(HEX_DIGITS[(byte & 0x0f) as usize] as char);
    }
    hex
}

fn fingerprint_payload(ctx: &PreparedVerificationContext) -> Option<FingerprintPayload> {
    let build_source_identity = authenticated_build_source_identity()?;
    let mut text = String::with_capacity(4096);
    cache_canonical::write_context(
        &mut text,
        ctx,
        VC_CACHE_SCHEMA_VERSION,
        &build_source_identity,
    );
    let display_name = ctx.function_context.as_ref().map(|fc| fc.name.clone());
    let primary_location = ctx.obligations.first().and_then(|o| o.location.clone());
    Some(FingerprintPayload {
        fingerprint_hex: sha256_hex(text.as_bytes()),
        display_name,
        primary_location,
    })
}

fn authenticated_build_source_identity() -> Option<String> {
    #[cfg(test)]
    {
        if let Some(overridden) =
            VC_CACHE_BUILD_SOURCE_IDENTITY_OVERRIDE.with(|cell| cell.borrow().clone())
        {
            return overridden.filter(|identity| is_full_git_revision(identity));
        }
        return Some(TEST_BUILD_SOURCE_IDENTITY.to_string());
    }

    #[cfg(not(test))]
    {
        option_env!("TVC_CORE_BUILD_GIT_HEAD")
            .filter(|identity| is_full_git_revision(identity))
            .map(str::to_string)
    }
}

pub(in crate::encoder) fn is_full_git_revision(value: &str) -> bool {
    matches!(value.len(), 40 | 64)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

// --- Test hooks ---

#[cfg(test)]
thread_local! {
    // Default: cache disabled in tests. Cache-specific tests opt in via
    // reset_test_cache_disable() which sets this to false. This prevents
    // cache hits from interfering with setup_from_prepared_count assertions
    // in existing solver-behavior tests.
    pub(in crate::encoder) static VC_CACHE_DISABLE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(true) };
    pub(in crate::encoder) static VC_CACHE_DIR_OVERRIDE:
        std::cell::RefCell<Option<PathBuf>> =
        const { std::cell::RefCell::new(None) };
    pub(in crate::encoder) static VC_CACHE_HIT_COUNT: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    pub(in crate::encoder) static VC_CACHE_MISS_COUNT: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    pub(in crate::encoder) static VC_CACHE_BUILD_SOURCE_IDENTITY_OVERRIDE:
        std::cell::RefCell<Option<Option<String>>> =
        const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
const TEST_BUILD_SOURCE_IDENTITY: &str = "1111111111111111111111111111111111111111";

#[cfg(test)]
fn is_test_cache_disabled() -> bool {
    VC_CACHE_DISABLE.with(|flag| flag.get())
}

#[cfg(test)]
fn bump_cache_hit_count() {
    VC_CACHE_HIT_COUNT.with(|count| count.set(count.get() + 1));
}

#[cfg(not(test))]
fn bump_cache_hit_count() {}

#[cfg(test)]
pub(in crate::encoder) fn bump_cache_miss_count() {
    VC_CACHE_MISS_COUNT.with(|count| count.set(count.get() + 1));
}

#[cfg(not(test))]
pub(in crate::encoder) fn bump_cache_miss_count() {}

#[cfg(test)]
pub(in crate::encoder) fn cache_hit_count() -> usize {
    VC_CACHE_HIT_COUNT.with(|count| count.get())
}

#[cfg(test)]
pub(in crate::encoder) fn cache_miss_count() -> usize {
    VC_CACHE_MISS_COUNT.with(|count| count.get())
}

#[cfg(test)]
pub(in crate::encoder) fn reset_cache_counts() {
    VC_CACHE_HIT_COUNT.with(|count| count.set(0));
    VC_CACHE_MISS_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub(in crate::encoder) fn reset_test_cache_disable() {
    VC_CACHE_DISABLE.with(|flag| flag.set(false));
}

#[cfg(test)]
pub(in crate::encoder) fn set_test_cache_dir(dir: PathBuf) {
    VC_CACHE_DIR_OVERRIDE.with(|cell| *cell.borrow_mut() = Some(dir));
}

#[cfg(test)]
pub(in crate::encoder) fn clear_test_cache_dir() {
    VC_CACHE_DIR_OVERRIDE.with(|cell| *cell.borrow_mut() = None);
}

#[cfg(test)]
pub(in crate::encoder) fn set_test_build_source_identity(identity: Option<&str>) {
    VC_CACHE_BUILD_SOURCE_IDENTITY_OVERRIDE
        .with(|cell| *cell.borrow_mut() = Some(identity.map(str::to_string)));
}

#[cfg(test)]
pub(in crate::encoder) fn clear_test_build_source_identity() {
    VC_CACHE_BUILD_SOURCE_IDENTITY_OVERRIDE.with(|cell| *cell.borrow_mut() = None);
}

/// Test-only: compute the fingerprint payload for a prepared context.
/// Used by the corrupt-cache-entry test to know what filename to write.
#[cfg(test)]
pub(in crate::encoder) fn fingerprint_payload_for_test(
    ctx: &PreparedVerificationContext,
) -> TestFingerprintPayload {
    let payload = fingerprint_payload(ctx).expect("test cache fingerprint requires build identity");
    TestFingerprintPayload {
        hex: payload.fingerprint_hex().to_string(),
    }
}

#[cfg(test)]
pub(in crate::encoder) struct TestFingerprintPayload {
    hex: String,
}

#[cfg(test)]
impl TestFingerprintPayload {
    pub(in crate::encoder) fn fingerprint_hex_for_test(&self) -> String {
        self.hex.clone()
    }
}

#[cfg(test)]
mod session_authority_tests {
    use super::*;

    /// A store records its exact path so a matching lookup in this process is
    /// authoritative. The same fingerprint in another directory remains
    /// untrusted.
    #[test]
    fn a_stored_entry_is_recorded_only_at_its_exact_path() {
        let root = PathBuf::from("session-authority-test");
        let first = root.join("first").join("hash.json");
        let second = root.join("second").join("hash.json");
        let content = "canonical verified entry";
        assert!(
            !session_wrote(&first, content),
            "unwritten entry must not be recorded"
        );
        record_session_write(first.clone(), sha256_hex(content.as_bytes()));
        assert!(
            session_wrote(&first, content),
            "a stored entry must be recorded for this session"
        );
        assert!(
            !session_wrote(&second, content),
            "the same fingerprint at a different path must remain untrusted"
        );
        assert!(
            !session_wrote(&first, "mutated verified entry"),
            "mutating a stored file's content must revoke session authority"
        );
    }
}
