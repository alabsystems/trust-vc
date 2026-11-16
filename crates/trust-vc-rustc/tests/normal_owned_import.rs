// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual owned producer -> normal after-expansion/MIR/erase/AY entry pairs.
//! Requires a genuine @2 staging request template in
//! TRUST_VC_OWNED_NORMAL_REQUEST. Each test changes only its fresh output path;
//! no staged artifact, saved successful report or expected-outcome input is used.

mod common;
#[path = "normal_owned_import/stream.rs"]
mod stream;

use serde_json::{json, Value};
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

fn pair(name: &str, body: &str, yes: &str, no: &str, outcome: &str, error: &str) {
    assert_eq!(body.matches(yes).count(), 1);
    let template = PathBuf::from(
        std::env::var_os("TRUST_VC_OWNED_NORMAL_REQUEST")
            .expect("set TRUST_VC_OWNED_NORMAL_REQUEST to a genuine fresh-build @2 request"),
    );
    let mut request: Value =
        serde_json::from_slice(&std::fs::read(&template).expect("request bytes"))
            .expect("request JSON");
    assert_eq!(
        request["schema"],
        "trust-vc.native-declaration-staging-request@2"
    );
    assert!(request.get("builtin").is_none() && request.get("macros").is_none());
    let root = std::env::temp_dir().join(format!(
        "trust-vc-normal-owned-{}-{name}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&root).expect("fresh test output");
    let root = root.canonicalize().expect("canonical fresh test output");
    let output = root.join("staging");
    request["output"] = json!(output);
    let request_path = root.join("request.json");
    std::fs::write(
        &request_path,
        serde_json::to_vec_pretty(&request).expect("request encoding"),
    )
    .expect("request copy");
    let imported =
        "proof fn imported_control<A>(s: vstd::set::Set<A>) { assert(s.len() as int >= 0); }\n";
    let source = format!(
        "{}\nextern crate vstd;\nverus! {{\n{imported}{body}\n}}\n",
        common::PRELUDE
    );
    let twin = source.replace(yes, no);
    assert_eq!(
        source
            .lines()
            .zip(twin.lines())
            .filter(|(a, b)| a != b)
            .count(),
        1
    );
    let positive = root.join("positive.rs");
    let negative = root.join("negative.rs");
    std::fs::write(&positive, &source).expect("positive source");
    std::fs::write(&negative, &twin).expect("false source");
    let actual = Command::new(env!("CARGO_BIN_EXE_vstd_normal_client_verify"))
        .args([&request_path, &positive, &negative])
        .current_dir(&root)
        .env("VSTD_KIND", "IsVstd")
        .output()
        .expect("normal owned process");
    // Preserve actual terminal bytes before any verdict assertion.
    std::fs::write(root.join("stdout.log"), &actual.stdout).expect("save stdout");
    std::fs::write(root.join("stderr.log"), &actual.stderr).expect("save stderr");
    let producer: Value = serde_json::from_slice(
        &std::fs::read(output.join("declarations.json")).expect("actual producer observation"),
    )
    .expect("actual producer observation JSON");
    let source_pin = request["manifest"]["sha256"]
        .as_str()
        .expect("approved source pin");
    assert_eq!(source_pin.len(), 64);
    let source_digest = source_pin
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).expect("source pin byte")
        })
        .collect::<Vec<_>>();
    let boundary = json!({"schema": "trust-vc.owned-normal-stream@1",
        "event": "clients-begin", "output": output, "clients": 2,
        "source_manifest_sha256": source_digest,
        "erase_metadata_sha256": producer["erase_metadata_sha256"],
        "compiler_driver_sha256": producer["compiler_driver_sha256"]});
    let (producer_bytes, boundary_bytes, client_bytes) =
        stream::split(&actual.stderr, &boundary).expect("one exact owned producer/client boundary");
    std::fs::write(root.join("producer.stderr.log"), producer_bytes)
        .expect("save raw producer stream");
    std::fs::write(root.join("stream-boundary.jsonl"), boundary_bytes)
        .expect("save actual boundary");
    std::fs::write(root.join("clients.stderr.jsonl"), client_bytes)
        .expect("save raw client stream");
    assert_eq!(
        [producer_bytes, boundary_bytes, client_bytes].concat(),
        actual.stderr
    );
    let phases = std::fs::read_to_string(output.join("phases.jsonl"))
        .expect("actual phase records")
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).expect("phase JSON"))
        .collect::<Vec<_>>();
    assert_eq!(
        phases
            .iter()
            .map(|row| row["phase"].as_str().unwrap())
            .collect::<Vec<_>>(),
        vec![
            "EraseCompileAndEmit",
            "LoadFreshEraseMetadata",
            "ConsumeInActualKeepCallback",
            "OwnedNormalClientVerify0",
            "OwnedNormalClientVerify1"
        ]
    );
    assert!(phases[..3]
        .iter()
        .all(|row| row["compiler_result"] == "Returned"
            && row["compiler_error"].is_null()
            && row["callback"]["state"] == "Checked"));
    assert_eq!(
        actual.status.code(),
        Some(1),
        "pair contains a genuine negative: {}",
        root.display()
    );
    let read = |index| -> Value {
        serde_json::from_slice(
            &std::fs::read(output.join(format!("OwnedNormalClientVerify{index}.json")))
                .expect("actual normal report"),
        )
        .expect("actual report JSON")
    };
    let first = read(0);
    assert_eq!(first["compiler_returned"], true, "{first}");
    assert_eq!(first["normal_verdict"]["outcome"], "checked", "{first}");
    assert_eq!(first["normal_verdict"]["exit_code"], 0);
    assert_eq!(first["normal_verdict"]["erase_exit"], 0);
    assert_eq!(
        first["publication"],
        "CompilerReturned0AndOwnedInputsRevalidated"
    );
    assert!(
        first["imported_declarations"]
            .as_u64()
            .expect("actual import count")
            > 0
    );
    assert_eq!(first["imported_verified_functions"], 0);
    assert_eq!(first["ordinary_import_cli_enabled"], false);
    let second = read(1);
    if name.starts_with("imported_math_") {
        let minimum = if name == "imported_math_max3" { 2 } else { 1 };
        for report in [&first, &second] {
            let definitions = report["imported_spec_definitions"]
                .as_u64()
                .expect("actual checked definition count");
            assert!(definitions >= minimum, "{report}");
        }
    }
    assert_eq!(second["normal_verdict"]["outcome"], outcome, "{second}");
    assert_eq!(second["normal_verdict"]["exit_code"], 1);
    assert_eq!(second["publication"], "NoSuccessfulPublication");
    if error == "E0382" {
        assert!(second["normal_verdict"]["functions"]
            .as_array()
            .expect("normal functions")
            .iter()
            .all(|f| f["verdict"] != "verified"));
        if outcome == "erase-rejected" {
            assert_eq!(second["normal_verdict"]["erase_exit"], 1);
        } else {
            assert!(
                first["original_native_ownership_roots"]
                    .as_u64()
                    .expect("actual native roots")
                    > 0
            );
            assert_eq!(second["normal_verdict"]["erase_exit"], 0);
        }
    }
    let errors = stream::diagnostics(client_bytes)
        .expect("every client stderr line must be native JSON")
        .into_iter()
        .filter(|d| {
            d["level"] == "error"
                && !d["message"]
                    .as_str()
                    .is_some_and(|m| m.starts_with("aborting due to"))
        })
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1, "{errors:?}; {}", root.display());
    let diagnostic = &errors[0];
    if error == "E0382" {
        assert_eq!(diagnostic["code"]["code"], error);
    } else {
        assert_eq!(diagnostic["message"], error);
    }
    let changed_line = source
        .lines()
        .zip(twin.lines())
        .position(|(a, b)| a != b)
        .expect("one changed line")
        + 1;
    let primary = diagnostic["spans"]
        .as_array()
        .expect("diagnostic spans")
        .iter()
        .filter(|span| span["is_primary"] == true)
        .collect::<Vec<_>>();
    assert_eq!(primary.len(), 1, "{primary:?}");
    assert_eq!(primary[0]["line_start"].as_u64(), Some(changed_line as u64));
    assert_eq!(primary[0]["file_name"].as_str(), negative.to_str());
}

#[test]
fn actual_exec_assertion_and_false_twin_use_the_normal_pipeline() {
    pair(
        "exec_assert",
        "fn check() { let n: u64 = 7; assert(n == 7); }",
        "assert(n == 7)",
        "assert(n == 8)",
        "verification-failed",
        "assertion failed",
    );
}

#[test]
fn actual_exec_moves_are_checked_in_the_genuine_erase_child() {
    pair(
        "exec_move",
        "struct Token {}\nfn consume(a: Token) {}\nfn check(a: Token) { consume(a); }",
        "fn check(a: Token) { consume(a); }",
        "fn check(a: Token) { consume(a); consume(a); }",
        "erase-rejected",
        "E0382",
    );
}

#[test]
fn tracked_proof_moves_are_checked_in_the_original_mir() {
    pair(
        "tracked_move",
        "proof fn consume<A>(tracked a: A) {}\nproof fn check<A>(tracked a: A) { consume(a); }",
        "proof fn check<A>(tracked a: A) { consume(a); }",
        "proof fn check<A>(tracked a: A) { consume(a); consume(a); }",
        "verus-rejected",
        "E0382",
    );
}

#[test]
fn genuine_imported_math_add_and_false_twin_use_checked_definitions() {
    pair(
        "imported_math_add",
        "proof fn check(x: int, y: int) { assert(vstd::math::add(x, y) == x + y); }",
        "== x + y",
        "== x + y + 1",
        "verification-failed",
        "assertion failed",
    );
}

#[test]
fn genuine_imported_math_max_and_false_twin_use_checked_definitions() {
    pair(
        "imported_math_max",
        "proof fn check(x: int, y: int) { assert(vstd::math::max(x, y) >= x); }",
        ">= x",
        "< x",
        "verification-failed",
        "assertion failed",
    );
}

#[test]
fn genuine_imported_math_max3_and_false_twin_use_the_complete_dependency_graph() {
    pair(
        "imported_math_max3",
        "proof fn check(x: int, y: int, z: int) { assert(vstd::math::max3(x, y, z) >= x); }",
        ">= x",
        "< x",
        "verification-failed",
        "assertion failed",
    );
}

#[test]
fn genuine_imported_length_type_fact_does_not_prove_a_zero_value() {
    // These outcomes check native proof behavior, not structural absence of
    // every possible value equation. The bodyless/channel guards remain separate.
    pair(
        "imported_signature_only",
        "proof fn check(items: vstd::set::Set<int>) { assert(items.len() as int >= 0); }",
        "assert(items.len() as int >= 0)",
        "assert(items.len() as int == 0)",
        "verification-failed",
        "assertion failed",
    );
}
