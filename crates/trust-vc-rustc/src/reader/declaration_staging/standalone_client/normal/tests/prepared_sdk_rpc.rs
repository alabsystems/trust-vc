// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise the real native request callback while the genuine owner is live.

use super::*;
use crate::native_requests::{self, Dispatch, OutputContext, Request};
use crate::reader::declaration_staging::standalone_client::coordinator::Session;
use std::ffi::OsString;
use std::time::Duration;

pub(super) fn check(
    owner: &StandaloneImported<'_>,
    sdk: &PreparedSdk<'_>,
    source: &ClientSource,
    root: &Path,
) {
    // Compile the raw relative/empty environment values in both the actual
    // verify callback and its genuine erasure child. Output destinations are
    // anchored independently; rebasing them must not change env!/option_env!.
    let text = std::fs::read_to_string(&source.file().path).unwrap();
    let environment_path = root.join("rpc-output-environment.rs");
    std::fs::write(
        &environment_path,
        format!(
            "{text}\nconst _: [(); 12] = [(); env!(\"TRUST_VC_VERDICT_DIR\").len()];\n\
             const _: () = match option_env!(\"TRUST_VC_DUMP_VCIR\") {{\n\
                 Some(value) => assert!(value.is_empty()),\n\
                 None => panic!(\"the request explicitly supplied an empty value\"),\n\
             }};"
        ),
    )
    .unwrap();
    let environment_source = ClientSource::read(&environment_path).unwrap();
    let source = &environment_source;
    let original = invocation(owner, sdk, source, &root.join("rpc-client.rmeta"));
    let split = original.original().unwrap();
    let mut argv = vec![OsString::from("original-private-client")];
    argv.extend(split.rustc.iter().map(OsString::from));
    argv.extend([
        OsString::from("--import"),
        OsString::from(
            split
                .verus
                .iter()
                .find(|option| option.name == "import")
                .unwrap()
                .value
                .as_ref()
                .unwrap(),
        ),
    ]);
    let verdict_dir = root.join("rpc-verdicts");
    let expected_argv = json!(argv
        .iter()
        .map(|arg| arg.to_str().unwrap())
        .collect::<Vec<_>>());
    let expected_options = json!(split
        .verus
        .iter()
        .map(|option| json!({"name": option.name, "value": option.value}))
        .collect::<Vec<_>>());
    let request = Request {
        argv,
        cwd: root.to_owned(),
        outputs: OutputContext {
            verdict_dir: Some("rpc-verdicts".into()),
            dump_vcir: Some("".into()),
        },
        verusdoc: None,
    };
    let (server, client) = native_requests::pair().unwrap();
    let sender = std::thread::spawn(move || {
        let response = client.submit(&request, Duration::from_secs(30)).unwrap();
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let exit = response.copy_to(&mut stdout, &mut stderr).unwrap();
        (exit, stdout, stderr)
    });
    let cwd = std::env::current_dir().unwrap();
    let mut session = Session::new(owner, sdk).unwrap();
    // SAFETY: the only other thread performs socket I/O and owns no native
    // compiler, cwd, stdio or spawn activity. The compiler callback joins fully.
    let outcome = unsafe {
        server.dispatch(Duration::from_secs(30), |request, reply| {
            session.handle(request, reply)
        })
    }
    .unwrap();
    assert_eq!(outcome, Dispatch::Completed(1));
    let (exit, _, stderr) = sender.join().unwrap();
    assert_eq!(exit, 1);
    assert_eq!(std::env::current_dir().unwrap(), cwd);
    assert!(String::from_utf8(stderr)
        .unwrap()
        .contains("assertion failed"));
    let report: Value = serde_json::from_slice(
        &std::fs::read(owner.library().inputs.output.join("NativeRequest1.json")).unwrap(),
    )
    .unwrap();
    let verdict = &report["normal_verdict"];
    assert_eq!(verdict["argv"], expected_argv);
    assert_eq!(verdict["verus_options"], expected_options);
    assert_eq!(verdict["outcome"], "verification-failed");
    assert_eq!(verdict["erase_exit"], 0);
    assert!(verdict["crate_refusals"].as_array().unwrap().is_empty());
    let functions = verdict["functions"].as_array().unwrap();
    assert_eq!(functions.len(), 3);
    assert_eq!(
        functions
            .iter()
            .filter(|row| row["verdict"] == "verified")
            .count(),
        1
    );
    assert_eq!(
        functions
            .iter()
            .filter(|row| row["verdict"] == "failed")
            .count(),
        2
    );
    let records = std::fs::read_dir(verdict_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    assert_eq!(records.len(), 1);
    let rows = std::fs::read_to_string(&records[0]).unwrap();
    let records = rows
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0]["functions"], verdict["functions"]);
    assert_eq!(records[0]["argv"], expected_argv);
    assert_eq!(records[0]["verus_options"], expected_options);
    owner.check_retained_inputs().unwrap();
    sdk.check_owner(owner).unwrap();
}
