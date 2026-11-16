// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The actual forwarder executable is data transport, with no proof credit.

use super::*;
use std::fs::File;
use std::process::Command;

#[test]
#[ignore = "needs the actual freshly compiled private forwarding executable"]
fn actual_forwarder_preserves_bytes_outputs_status_and_refuses_missing_handles() {
    let executable = PathBuf::from(
        std::env::var_os("TRUST_VC_NATIVE_REQUEST_FORWARDER")
            .expect("actual compiled private forwarding executable"),
    );
    assert!(executable.is_absolute() && executable.is_file());
    let root = std::env::temp_dir().join(format!("trust-vc-forwarding-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let root = root.canonicalize().unwrap();
    let stdout = root.join("stdout");
    let stderr = root.join("stderr");
    let arguments = [
        OsString::from("a path with spaces.rs"),
        OsString::from_vec(b"--original-non-utf8=\xff".to_vec()),
    ];
    let (server, client) = pair().unwrap();
    let mut command = Command::new(&executable);
    command
        .args(&arguments)
        .current_dir(&root)
        .env("TRUST_VC_VERDICT_DIR", "relative verdicts")
        .env("TRUST_VC_DUMP_VCIR", root.join("actual dump.vcir"))
        .env("VSTD_KIND", "arbitrary-data-not-a-producer")
        .env("VERUSDOC", "1")
        .stdout(File::create(&stdout).unwrap())
        .stderr(File::create(&stderr).unwrap());
    let child = client.spawn(command).unwrap();
    // SAFETY: only the already spawned data-only child runs concurrently;
    // this process has no other exec/spawn and this callback compiles nothing.
    let result = unsafe {
        server.dispatch(Duration::from_secs(30), |request, reply| {
            assert_eq!(request.argv[0], executable.as_os_str());
            assert_eq!(request.argv[1..], arguments);
            assert_eq!(request.cwd, root);
            assert_eq!(request.verusdoc.as_deref(), Some(std::ffi::OsStr::new("1")));
            assert_eq!(
                request.outputs,
                OutputContext {
                    verdict_dir: Some("relative verdicts".into()),
                    dump_vcir: Some(root.join("actual dump.vcir")),
                }
            );
            reply.stdout(b"actual output\x00\xff\n")?;
            reply.stderr(b"actual error\x00\xfe\n")?;
            Ok(17)
        })
    }
    .unwrap();
    assert_eq!(result, Dispatch::Completed(17));
    assert_eq!(child.wait().unwrap().code(), Some(17));
    assert_eq!(std::fs::read(stdout).unwrap(), b"actual output\x00\xff\n");
    assert_eq!(std::fs::read(stderr).unwrap(), b"actual error\x00\xfe\n");
    assert!(!root.join("relative verdicts").exists());
    assert!(!root.join("actual dump.vcir").exists());
    for locator in [None, Some("999999")] {
        let mut command = Command::new(&executable);
        command.env_remove(INHERITED_CONTROL_ENV);
        if let Some(locator) = locator {
            command.env(INHERITED_CONTROL_ENV, locator);
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(75));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8(output.stderr)
            .unwrap()
            .contains("native request forwarding failed"));
    }
    std::fs::remove_dir_all(root).unwrap();
}
