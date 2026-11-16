use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(".ubd").join(format!(
            "trust-vc-output-sinks-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn record(label: &str) -> Record {
    Record {
        argv: vec!["original-rust_verify".into(), label.into()],
        entry_file: Some("source/entry.rs".into()),
        output_file: Some("test_inputs/same-case/libtest_crate.rmeta".into()),
        outcome: Some(Outcome::VerificationFailed),
        exit_code: Some(1),
        functions: vec![FnVerdict {
            def_path: label.into(),
            kind: "Fn".into(),
            verdict: Verdict::Failed,
            tag: None,
            lines: None,
            sites: Some(SiteCounts {
                proved: 2,
                failed: 1,
            }),
        }],
        ..Record::default()
    }
}

#[test]
fn concurrent_requests_keep_original_records_and_separate_output_paths() {
    let scratch = Scratch::new();
    let mut requests = Vec::new();
    for label in ["first", "second"] {
        let cwd = scratch.0.join(label);
        std::fs::create_dir_all(cwd.join("test_inputs/same-case")).unwrap();
        let record = record(label);
        let expected = format!("{}\n", record.to_json());
        let outputs =
            OutputSinks::for_request(&cwd, Some("records".into()), Some("reader.vcir".into()))
                .unwrap();
        let child_cwd = cwd.clone();
        let child = std::thread::spawn(move || {
            assert!(record.write_to(&outputs).is_empty());
            outputs.write_vcir(label).unwrap();
            assert_eq!(record.argv, ["original-rust_verify", label]);
            assert_eq!(
                record.output_file,
                Some("test_inputs/same-case/libtest_crate.rmeta".into())
            );
            child_cwd
        });
        requests.push((child, expected, label));
    }
    for (child, expected, label) in requests {
        let cwd = child.join().unwrap();
        assert_eq!(
            std::fs::read_to_string(cwd.join("test_inputs/same-case/trust-vc-verdict.jsonl"))
                .unwrap(),
            expected
        );
        assert_eq!(
            std::fs::read_to_string(cwd.join("records/same-case.jsonl")).unwrap(),
            expected
        );
        assert_eq!(
            std::fs::read_to_string(cwd.join("reader.vcir")).unwrap(),
            label
        );
        assert!(!cwd.join("source/trust-vc-verdict.jsonl").exists());
    }
}

#[test]
fn absolute_sinks_keep_their_original_destinations() {
    let scratch = Scratch::new();
    let cwd = scratch.0.join("request");
    let elsewhere = scratch.0.join("elsewhere");
    std::fs::create_dir_all(cwd.join("test_inputs/same-case")).unwrap();
    std::fs::create_dir_all(&elsewhere).unwrap();
    let outputs = OutputSinks::for_request(
        &cwd,
        Some(elsewhere.join("records")),
        Some(elsewhere.join("reader.vcir")),
    )
    .unwrap();
    let record = record("absolute");
    let expected = record.to_json();
    assert!(record.write_to(&outputs).is_empty());
    outputs.write_vcir("actual dump").unwrap();
    let line = std::fs::read_to_string(elsewhere.join("records/same-case.jsonl")).unwrap();
    assert_eq!(serde_json::from_str::<Value>(&line).unwrap(), expected);
    assert_eq!(
        std::fs::read_to_string(elsewhere.join("reader.vcir")).unwrap(),
        "actual dump"
    );
    assert_eq!(record.to_json(), expected);
}

#[test]
fn default_context_writes_only_beside_output_and_does_not_dump() {
    let scratch = Scratch::new();
    let output = scratch.0.join("test_inputs/same-case");
    std::fs::create_dir_all(&output).unwrap();
    let mut record = record("default");
    record.entry_file = Some(scratch.0.join("examples/entry.rs"));
    record.output_file = Some(output.join("libtest_crate.rmeta"));
    let outputs = OutputSinks::default();
    assert!(record.write_to(&outputs).is_empty());
    assert!(!outputs.wants_vcir_dump());
    outputs.write_vcir("no requested destination").unwrap();
    assert!(output.join("trust-vc-verdict.jsonl").is_file());
    assert!(!scratch.0.join("examples/trust-vc-verdict.jsonl").exists());
    assert_eq!(std::fs::read_dir(&output).unwrap().count(), 1);
}

#[test]
fn absent_output_uses_entry_name_only_for_the_requested_collector() {
    let scratch = Scratch::new();
    let mut record = record("entry-name");
    record.entry_file = Some("examples/original-case/entry.rs".into());
    record.output_file = None;
    let outputs = OutputSinks::for_request(&scratch.0, Some("records".into()), None).unwrap();
    assert!(record.write_to(&outputs).is_empty());
    assert!(scratch.0.join("records/original-case.jsonl").is_file());
    assert!(!scratch
        .0
        .join("examples/original-case/trust-vc-verdict.jsonl")
        .exists());
}

#[test]
fn failed_sinks_leave_the_verdict_and_local_record_unchanged() {
    let scratch = Scratch::new();
    std::fs::create_dir_all(scratch.0.join("test_inputs/same-case")).unwrap();
    let blocked = scratch.0.join("blocked");
    std::fs::write(&blocked, "existing file").unwrap();
    let outputs = OutputSinks::for_request(
        &scratch.0,
        Some("blocked".into()),
        Some("blocked/reader.vcir".into()),
    )
    .unwrap();
    let record = record("write-failure");
    let expected = record.to_json();
    assert!(!record.write_to(&outputs).is_empty());
    assert!(outputs.write_vcir("dump").is_err());
    assert_eq!(record.to_json(), expected);
    assert_eq!(std::fs::read_to_string(blocked).unwrap(), "existing file");
    let local = std::fs::read_to_string(
        scratch
            .0
            .join("test_inputs/same-case/trust-vc-verdict.jsonl"),
    )
    .unwrap();
    assert_eq!(serde_json::from_str::<Value>(&local).unwrap(), expected);
}

#[test]
fn next_request_does_not_inherit_previous_optional_sinks() {
    let scratch = Scratch::new();
    let first = scratch.0.join("first");
    let second = scratch.0.join("second");
    for cwd in [&first, &second] {
        std::fs::create_dir_all(cwd.join("test_inputs/same-case")).unwrap();
    }
    let first_outputs =
        OutputSinks::for_request(&first, Some("records".into()), Some("reader.vcir".into()))
            .unwrap();
    assert!(record("first").write_to(&first_outputs).is_empty());
    first_outputs.write_vcir("first dump").unwrap();
    let next = OutputSinks::for_request(&second, None, None).unwrap();
    assert!(record("second").write_to(&next).is_empty());
    next.write_vcir("second dump").unwrap();
    assert!(!second.join("records").exists());
    assert!(!second.join("reader.vcir").exists());
    let collected = std::fs::read_to_string(first.join("records/same-case.jsonl")).unwrap();
    assert_eq!(collected.lines().count(), 1);
    assert_eq!(
        std::fs::read_to_string(first.join("reader.vcir")).unwrap(),
        "first dump"
    );
}

#[test]
fn request_paths_require_an_explicit_absolute_working_directory() {
    for cwd in [Path::new("relative"), Path::new("")] {
        assert_eq!(
            OutputSinks::for_request(cwd, None, None)
                .unwrap_err()
                .kind(),
            std::io::ErrorKind::InvalidInput
        );
    }
}
