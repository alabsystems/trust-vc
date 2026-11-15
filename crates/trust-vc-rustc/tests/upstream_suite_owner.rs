//! Keep the real explicit-unverified Targo ancestor alive for the full runner.
//!
//! The endpoint is only inherited DATA. Nested Targo authenticates it; this
//! host neither creates it nor grants a compilation or verification lane.

#![feature(rustc_private)]

use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, ExitStatus, Stdio};

const PLAN: &str = "TRUST_VC_UPSTREAM_SUITE_PLAN";
const ENDPOINT: &str = "TRUST_TARGO_NESTED_UNVERIFIED_ENDPOINT";

/// Own and directly reap the runner process, including on a host failure.
/// The private stdin pipe is liveness only. Closing its writer requests
/// cooperative cleanup of the runner's held session roots before direct reap.
/// SIGKILL and operating-system failures cannot execute cooperative cleanup.
struct Runner {
    child: Child,
    input: Option<ChildStdin>,
    waited: bool,
}

impl Runner {
    fn wait(&mut self) -> std::io::Result<ExitStatus> {
        let status = self.child.wait()?;
        self.waited = true;
        Ok(status)
    }
}

impl Drop for Runner {
    fn drop(&mut self) {
        if !self.waited {
            // EOF wakes the runner's owner watcher. It cleans held native
            // session roots before exiting; SIGKILL would bypass that cleanup.
            drop(self.input.take());
            let _ = self.child.wait();
        }
    }
}

fn full_native_arguments(arguments: &[String]) {
    for required in ["--full-suite", "--include-ignored"] {
        assert_eq!(
            arguments
                .iter()
                .filter(|arg| arg.as_str() == required)
                .count(),
            1,
            "the owner requires the complete original suite, including ignored cases"
        );
    }
    let mut frontends = 0;
    for (index, argument) in arguments.iter().enumerate() {
        if !argument.starts_with("--") {
            continue;
        }
        assert!(
            !"--owned-stdin".starts_with(argument.split('=').next().unwrap()),
            "runner lifetime input is appended by the actual host"
        );
        let (name, inline_value) = match argument.split_once('=') {
            Some((name, value)) => (name, Some(value)),
            None => (argument.as_str(), None),
        };
        assert!(
            !["--only", "--exclude", "--summarize-only"]
                .iter()
                .any(|selector| selector.starts_with(name)),
            "the owner does not run a selected or summary-only suite"
        );
        if "--frontend".starts_with(name) {
            // Do not let argparse abbreviations or repeated last-wins values
            // change the native frontend this host promises to exercise.
            assert_eq!(name, "--frontend", "spell the native frontend explicitly");
            let value = inline_value.or_else(|| arguments.get(index + 1).map(String::as_str));
            assert_eq!(
                value,
                Some("trust-vc"),
                "the owner requires the native frontend"
            );
            frontends += 1;
        }
    }
    assert_eq!(frontends, 1, "select the native frontend exactly once");
}

#[test]
#[ignore = "requires a genuine Targo-owned process and a bound full-suite DATA plan"]
fn full_upstream_suite_under_targo_owner() {
    assert!(
        std::env::var_os(ENDPOINT).is_some_and(|value| !value.is_empty()),
        "run this exact test through genuine targo --unverified test; an endpoint locator alone grants no authority"
    );
    let plan_path = PathBuf::from(std::env::var_os(PLAN).expect("bound full-suite DATA plan"));
    assert!(
        plan_path.is_absolute(),
        "the DATA plan path must be absolute"
    );
    let plan: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&plan_path).expect("read the full-suite DATA plan"))
            .expect("parse the full-suite DATA plan");
    let object = plan.as_object().expect("the DATA plan is an object");
    assert!(
        object
            .keys()
            .all(|key| ["schema", "python", "runner_argv"].contains(&key.as_str())),
        "unsupported DATA plan field"
    );
    assert_eq!(plan["schema"], "trust-vc.upstream-suite-plan@1");
    let python = Path::new(
        plan["python"]
            .as_str()
            .expect("actual Python executable path"),
    );
    assert!(
        python.is_absolute() && python.is_file(),
        "Python must name an absolute executable file"
    );
    let arguments = plan["runner_argv"]
        .as_array()
        .expect("runner_argv DATA array")
        .iter()
        .map(|value| {
            value
                .as_str()
                .expect("runner argument is a string")
                .to_owned()
        })
        .collect::<Vec<_>>();
    full_native_arguments(&arguments);

    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("compiled repository path");
    let runner = repository.join("scripts/verus_suite/run_suite.py");
    assert!(
        runner.is_file(),
        "the compiled repository's maintained runner is missing"
    );
    let mut child = Command::new(python)
        .arg(&runner)
        .arg("--owned-stdin")
        .args(&arguments)
        .current_dir(repository)
        .stdin(Stdio::piped())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("start the maintained full-suite runner");
    let input = child.stdin.take().expect("retain the runner liveness pipe");
    let mut owned = Runner {
        child,
        input: Some(input),
        waited: false,
    };
    let status = owned
        .wait()
        .expect("directly wait for the maintained runner");
    assert!(
        status.success(),
        "the maintained full-suite runner returned {status}"
    );
}

#[test]
#[ignore = "requires an explicitly bound genuine Python for the lifetime control"]
fn dropping_the_runner_requests_cleanup_through_its_owned_pipe() {
    use std::io::BufRead;

    let python = PathBuf::from(
        std::env::var_os("TRUST_VC_UPSTREAM_OWNER_CONTROL_PYTHON")
            .expect("bind the genuine Python executable for this control"),
    );
    assert!(python.is_absolute() && python.is_file());
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("compiled repository path");
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system time")
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("suite-owner-{}-{stamp}", std::process::id()));
    std::fs::create_dir(&directory).expect("fresh control directory");
    let record = directory.join("children.json");
    let program = r#"
import pathlib, subprocess, sys, time
sys.path.insert(0, sys.argv[1])
import owned_processes as owned
with owned.scope(owned_stdin=True) as registry:
    registry.record_path = pathlib.Path(sys.argv[2])
    with owned.Child([sys.executable, '-u', '-c',
                      "import time;print('child-ready',flush=True);time.sleep(120)"],
                     stdout=subprocess.PIPE, text=True) as child:
        with child.process.stdout:
            print(child.process.stdout.readline().strip(), flush=True)
            while not child.exited():
                registry.check()
                time.sleep(.05)
"#;
    let mut child = Command::new(python)
        .arg("-u")
        .arg("-c")
        .arg(program)
        .arg(repository.join("scripts/verus_suite"))
        .arg(&record)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("start the genuine lifetime control");
    let input = child.stdin.take().expect("owned liveness pipe");
    let mut output = std::io::BufReader::new(child.stdout.take().expect("control readiness pipe"));
    let owned = Runner {
        child,
        input: Some(input),
        waited: false,
    };
    let mut ready = String::new();
    output
        .read_line(&mut ready)
        .expect("read actual child readiness");
    assert_eq!(ready.trim(), "child-ready");
    drop(owned);
    let observed: serde_json::Value = serde_json::from_slice(
        &std::fs::read(&record).expect("runner wrote its actual held-child lifecycle"),
    )
    .expect("parse actual lifecycle");
    assert_eq!(observed["cancelled"], "owner input closed");
    let children = observed["children"]
        .as_array()
        .expect("actual child records");
    assert_eq!(children.len(), 1);
    assert_eq!(
        children[0]["group_signal_delivered_before_owner_reap"],
        true
    );
    assert_eq!(children[0]["owner_direct_waited"], true);
    assert!(children[0]["command_raw_exit"].is_null());
    assert_eq!(children[0]["command_direct_waited"], false);
    assert_eq!(children[0]["owner_raw_exit"], -9);
    std::fs::remove_dir_all(directory).expect("remove the closed control output");
}
