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
        cargo: crate::native_requests::CargoContext::default(),
        macro_package_name: None,
    };
    let imported_again = request.clone();
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
    ordinary_workers_do_not_share_the_imported_macro_cache(
        owner,
        sdk,
        root,
        &mut session,
        &imported_again,
    );
}

fn dispatch(session: &mut Session<'_>, request: Request) -> (u8, Vec<u8>) {
    let (server, client) = native_requests::pair().unwrap();
    let sender = std::thread::spawn(move || {
        let response = client.submit(&request, Duration::from_secs(30)).unwrap();
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let exit = response.copy_to(&mut out, &mut err).unwrap();
        (exit, err)
    });
    // SAFETY: the sender performs only socket I/O; every compiler child is
    // directly joined inside the one serial owner callback before return.
    unsafe {
        server.dispatch(Duration::from_secs(30), |request, reply| {
            session.handle(request, reply)
        })
    }
    .unwrap();
    sender.join().unwrap()
}

fn ordinary_workers_do_not_share_the_imported_macro_cache(
    owner: &StandaloneImported<'_>,
    sdk: &PreparedSdk<'_>,
    root: &Path,
    session: &mut Session<'_>,
    imported: &Request,
) {
    for (label, assertion, exit) in [
        ("ordinary-positive", "true", 0),
        ("ordinary-false", "false", 1),
    ] {
        let path = root.join(format!("{label}.rs"));
        std::fs::write(&path,format!("use verus_builtin::*; use verus_builtin_macros::*;\nverus! {{ proof fn ordinary() {{ assert({assertion}); }} }}\n")).unwrap();
        let output = root.join(format!("{label}.rmeta"));
        let argv = vec![
            OsString::from("original-private-client"),
            OsString::from("--internal-test-mode"),
            OsString::from("--crate-type=lib"),
            OsString::from("--crate-name=ordinary_cohort"),
            OsString::from("--edition=2021"),
            OsString::from("--emit=metadata"),
            OsString::from("--error-format=json"),
            OsString::from("-Z"),
            OsString::from("unstable-options"),
            OsString::from("--sysroot"),
            OsString::from(env!("VC_SHIM_COMPILER_SYSROOT")),
            OsString::from("--cfg"),
            OsString::from("verus_no_vstd"),
            OsString::from("--extern"),
            OsString::from(format!(
                "force:verus_builtin={}",
                sdk.root().join("libverus_builtin.rlib").display()
            )),
            OsString::from("--extern"),
            OsString::from(format!(
                "force:verus_builtin_macros={}",
                sdk.root().join("libverus_builtin_macros.dylib").display()
            )),
            OsString::from("--extern"),
            OsString::from(format!(
                "force:verus_state_machines_macros={}",
                sdk.root()
                    .join("libverus_state_machines_macros.dylib")
                    .display()
            )),
            OsString::from("-L"),
            OsString::from(format!("dependency={}", sdk.root().display())),
            OsString::from("-o"),
            output.into_os_string(),
            path.into_os_string(),
        ];
        let verdicts = root.join(format!("{label}-verdicts"));
        let request = Request {
            argv,
            cwd: root.to_owned(),
            outputs: OutputContext {
                verdict_dir: Some(verdicts.clone()),
                dump_vcir: None,
            },
            verusdoc: None,
            cargo: crate::native_requests::CargoContext::default(),
            macro_package_name: None,
        };
        if exit == 0 {
            let mut private = request.clone();
            private.outputs.dump_vcir = Some(root.join("forged-private-worker.vcir"));
            let private_cwd = private.cwd.clone();
            // SAFETY: this exact dedicated test is serial; the earlier sender
            // and compiler children have joined. The private controls retain
            // and join their actual children before this scope can return.
            let (controls, _stdout, _stderr) = unsafe {
                crate::stdio_capture::run(
                    &owner.library().inputs.output,
                    "PrivateOrdinaryWorkerControls",
                    &private_cwd,
                    || session.private_ordinary_worker_controls(private),
                )
            }
            .unwrap();
            controls.unwrap();
        }
        let mut alias = request.clone();
        alias.argv.extend([
            "--extern".into(),
            format!(
                "arbitrary_alias={}",
                sdk.root().join("libvstd.rlib").display()
            )
            .into(),
        ]);
        let (alias_exit, alias_stderr) = dispatch(session, alias);
        assert_eq!(alias_exit, 1);
        assert!(String::from_utf8_lossy(&alias_stderr)
            .contains("outside the exact owned image inventory"));
        let (actual, stderr) = dispatch(session, request);
        assert_eq!(actual, exit, "{}", String::from_utf8_lossy(&stderr));
        let records = std::fs::read_dir(verdicts)
            .unwrap()
            .map(|p| std::fs::read_to_string(p.unwrap().path()).unwrap())
            .collect::<String>();
        let records = records
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(records.len(), 1);
        let fns = records[0]["functions"].as_array().unwrap();
        assert_eq!(fns.len(), 1);
        assert_eq!(
            fns[0]["verdict"],
            if exit == 0 { "verified" } else { "failed" }
        );
        assert_eq!(fns[0]["sites_failed"], if exit == 0 { 0 } else { 1 });
        assert_eq!(records[0]["erase_exit"], 0);
        assert!(records[0]["crate_refusals"].as_array().unwrap().is_empty());
        // Parent macro/environment state and real owner remain the same after
        // both native worker compilers, erasure, and AY have actually returned.
        owner.current().unwrap();
        sdk.check_owner(owner).unwrap();
    }
    // Re-use the imported source with a fresh original output operand after
    // NoVstd workers. The source's real false assertion must still fail.
    let mut again = imported.clone();
    let at = again.argv.iter().position(|arg| arg == "-o").unwrap();
    again.argv[at + 1] = root
        .join("rpc-imported-after-ordinary.rmeta")
        .into_os_string();
    let (exit, stderr) = dispatch(session, again);
    assert_eq!(exit, 1);
    assert!(String::from_utf8_lossy(&stderr).contains("assertion failed"));
    owner.current().unwrap();
    sdk.check_owner(owner).unwrap();
}
