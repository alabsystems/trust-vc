// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ordinary stream bytes, never forged compiler/import capabilities. The
//! unchanged native positive/false pairs exercise the real owned boundary.

#[path = "normal_owned_import/stream.rs"]
mod stream;

use serde_json::{json, Value};

fn cohort() -> Value {
    json!({"schema": "trust-vc.owned-normal-stream@1", "event": "clients-begin",
        "output": "/ordinary-test-data/cohort", "clients": 2,
        "source_manifest_sha256": vec![1u8; 32], "erase_metadata_sha256": vec![3u8; 32],
        "compiler_driver_sha256": vec![5u8; 32]})
}

fn framed(prefix: &[u8], boundary: &Value, clients: &[u8]) -> Vec<u8> {
    [
        prefix,
        serde_json::to_vec(boundary).unwrap().as_slice(),
        b"\n",
        clients,
    ]
    .concat()
}

#[test]
fn framing_preserves_all_producer_and_client_bytes_without_filtering() {
    let expected = cohort();
    let prefix =
        b"warning: actual setup text\nvstd-function-identity-inventory: ordinary data\n\xff\n";
    let clients = b"{\"level\":\"error\",\"message\":\"assertion failed\"}\n";
    let raw = framed(prefix, &expected, clients);
    let (a, b, c) = stream::split(&raw, &expected).unwrap();
    assert_eq!(a, prefix);
    assert_eq!(c, clients);
    assert_eq!([a, b, c].concat(), raw);
    assert_eq!(
        stream::diagnostics(c).unwrap()[0]["message"],
        "assertion failed"
    );
}

#[test]
fn missing_wrong_output_and_wrong_actual_cohort_boundaries_refuse() {
    let expected = cohort();
    assert!(stream::split(b"setup failed before client entry\n", &expected).is_err());
    let mut wrong = expected.clone();
    wrong["output"] = json!("/ordinary-test-data/another-cohort");
    assert!(stream::split(&framed(b"", &wrong, b""), &expected).is_err());
    let mut wrong = expected.clone();
    wrong["clients"] = json!(1);
    assert!(stream::split(&framed(b"", &wrong, b""), &expected).is_err());
    for field in [
        "source_manifest_sha256",
        "erase_metadata_sha256",
        "compiler_driver_sha256",
    ] {
        let mut wrong = expected.clone();
        wrong[field][0] = json!(8);
        assert!(stream::split(&framed(b"", &wrong, b""), &expected).is_err());
    }
    assert!(stream::split(&serde_json::to_vec(&expected).unwrap(), &expected).is_err());
    let mut extra = expected.clone();
    extra["unexpected"] = json!(true);
    assert!(stream::split(&framed(b"", &extra, b""), &expected).is_err());
}

#[test]
fn a_spoofed_or_repeated_frame_never_hides_the_real_owned_boundary() {
    let expected = cohort();
    let fake = framed(b"producer data\n", &expected, b"ordinary text\n");
    let raw = framed(&fake, &expected, b"{\"level\":\"error\"}\n");
    assert!(stream::split(&raw, &expected).is_err());
}

#[test]
fn plaintext_after_the_boundary_is_still_a_client_stream_failure() {
    let expected = cohort();
    for late in [
        b"unexpected late setup failure\n".as_slice(),
        b"\xff\n".as_slice(),
    ] {
        let raw = framed(b"preserved producer text\n", &expected, late);
        let (_, _, clients) = stream::split(&raw, &expected).unwrap();
        assert!(stream::diagnostics(clients).is_err());
    }
}

#[test]
fn extra_native_errors_are_retained_for_the_unchanged_sole_error_check() {
    let expected = cohort();
    let raw = framed(b"setup data\n", &expected,
        b"{\"level\":\"error\",\"message\":\"expected failure\"}\n{\"level\":\"error\",\"message\":\"unexpected second failure\"}\n");
    let (_, _, clients) = stream::split(&raw, &expected).unwrap();
    let values = stream::diagnostics(clients).unwrap();
    assert_eq!(
        values
            .iter()
            .filter(|value| value["level"] == "error")
            .count(),
        2
    );
}
