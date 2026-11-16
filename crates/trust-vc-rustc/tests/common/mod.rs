//! Running the `rust_verify` binary on a Verus program the way upstream's
//! harness does, for the integration tests.
//!
//! The binary needs the trustc-built `verus_builtin` crates. Set
//! `TRUST_VC_VERUS_BUILTINS` to the directory
//! `scripts/verus_suite/build_verus_builtins.sh` wrote them to.

// Each test target uses part of this module.
#![allow(dead_code)]

use std::path::PathBuf;
use std::process::Command;

/// The harness's prelude (`rust_verify_test/tests/common/mod.rs`,
/// `FEATURE_PRELUDE` and `USE_PRELUDE`), so test programs see what harness
/// programs see.
pub const PRELUDE: &str = "\
#![feature(fmt_internals)]
#![allow(unused_imports)]
#![allow(unused_macros)]
#![allow(deprecated)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]
#![allow(unused_comparisons)]
#![allow(noop_method_call)]
#![feature(allocator_api)]
#![feature(proc_macro_hygiene)]
#![feature(never_type)]
#![feature(core_intrinsics)]
#![feature(ptr_metadata)]
#![feature(sized_hierarchy)]
#![feature(const_destruct)]
use verus_builtin::*;
use verus_builtin_macros::*;
";

fn builtins() -> PathBuf {
    match std::env::var_os("TRUST_VC_VERUS_BUILTINS") {
        Some(dir) => PathBuf::from(dir),
        None => panic!(
            "set TRUST_VC_VERUS_BUILTINS to the directory holding the trustc-built \
             libverus_builtin.rlib and macro dylibs (scripts/verus_suite/build_verus_builtins.sh)"
        ),
    }
}

/// One diagnostic, with lines counted from the first line of the program
/// (the prelude excluded).
#[derive(Debug, Clone)]
pub struct Diag {
    pub level: String,
    pub code: Option<String>,
    pub message: String,
    /// Every span: line and label.
    pub spans: Vec<(usize, Option<String>)>,
    /// Lines of the primary spans.
    pub primary_lines: Vec<usize>,
}

/// What one run produced.
#[derive(Debug)]
pub struct Run {
    pub exit: i32,
    /// The verdict record (JSON null when there is none).
    pub record: serde_json::Value,
    /// Diagnostics, `aborting due to ..` and failure notes left out.
    pub diags: Vec<Diag>,
    /// Standard error lines that are not JSON.
    pub raw: Vec<String>,
    /// The VcIR dump the reader wrote, if any.
    pub vcir: Option<String>,
}

impl Run {
    /// The record's outcome, as text.
    pub fn outcome(&self) -> String {
        self.record["outcome"]
            .as_str()
            .unwrap_or("none")
            .to_string()
    }

    /// The error diagnostics.
    pub fn errors(&self) -> Vec<&Diag> {
        self.diags.iter().filter(|d| d.level == "error").collect()
    }
}

/// Run the binary on `source` (the prelude is prepended) with the Verus
/// options `verus_args`.
pub fn run(name: &str, source: &str, verus_args: &[&str]) -> Run {
    run_with_prelude(name, PRELUDE, source, verus_args, &[])
}

/// Apply explicit child environment values without changing the test process.
pub fn run_with_environment(
    name: &str,
    source: &str,
    verus_args: &[&str],
    environment: &[(&str, Option<&str>)],
) -> Run {
    run_with_prelude(name, PRELUDE, source, verus_args, environment)
}

/// Run the binary on `source` as a whole file, with no prelude.
pub fn run_raw(name: &str, source: &str, verus_args: &[&str]) -> Run {
    run_with_prelude(name, "", source, verus_args, &[])
}

/// Run the binary on `prelude` followed by `source`; lines are counted from
/// the first line of `source`.
fn run_with_prelude(
    name: &str,
    prelude: &str,
    source: &str,
    verus_args: &[&str],
    environment: &[(&str, Option<&str>)],
) -> Run {
    let builtins = builtins();
    let dir = std::env::temp_dir().join(format!("trust-vc-test-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let entry = dir.join("test.rs");
    std::fs::write(&entry, format!("{prelude}{source}")).expect("write test.rs");
    let dump = dir.join("vcir.txt");
    let _ = std::fs::remove_file(&dump);
    let _ = std::fs::remove_file(dir.join("trust-vc-verdict.jsonl"));
    let b = |file: &str| format!("{}", builtins.join(file).display());
    let mut command = Command::new(env!("CARGO_BIN_EXE_rust_verify"));
    for (key, value) in environment {
        match value {
            Some(value) => {
                command.env(key, value);
            }
            None => {
                command.env_remove(key);
            }
        }
    }
    let output = command
        .arg("--internal-test-mode")
        .args(verus_args)
        .args(["--crate-name", "test_crate", "--crate-type", "lib"])
        .args([
            "--extern",
            &format!("verus_builtin={}", b("libverus_builtin.rlib")),
        ])
        .args([
            "--extern",
            &format!(
                "verus_builtin_macros={}",
                b("libverus_builtin_macros.dylib")
            ),
        ])
        .args([
            "--extern",
            &format!(
                "verus_state_machines_macros={}",
                b("libverus_state_machines_macros.dylib")
            ),
        ])
        .args(["-L", &format!("dependency={}", builtins.display())])
        .args([
            "-Z",
            "write_long_types_to_disk=no",
            "-A",
            "non_snake_case",
            "-A",
            "deprecated",
        ])
        .args([
            "-o",
            &format!("{}", dir.join("libtest_crate.rmeta").display()),
        ])
        .args(["--emit=metadata", "--error-format=json"])
        .arg(&entry)
        .args(["--cfg", "verus_no_vstd"])
        .env("TRUST_VC_DUMP_VCIR", &dump)
        .env_remove("TRUST_VC_VERDICT_DIR")
        .output()
        .expect("run rust_verify");

    let prelude_lines = prelude.lines().count();
    let record = std::fs::read_to_string(dir.join("trust-vc-verdict.jsonl")).unwrap_or_default();
    let record: serde_json::Value = record
        .lines()
        .next()
        .and_then(|l| serde_json::from_str(l).ok())
        .unwrap_or(serde_json::Value::Null);
    let mut diags = Vec::new();
    let mut raw = Vec::new();
    for line in String::from_utf8_lossy(&output.stderr).lines() {
        let diag: serde_json::Value = match serde_json::from_str(line) {
            Ok(d) => d,
            Err(_) => {
                raw.push(line.to_string());
                continue;
            }
        };
        let message = diag["message"].as_str().unwrap_or("").to_string();
        if message.starts_with("aborting due to") || diag["level"] == "failure-note" {
            continue;
        }
        let mut spans = Vec::new();
        let mut primary_lines = Vec::new();
        for s in diag["spans"].as_array().into_iter().flatten() {
            let line = s["line_start"].as_u64().unwrap_or(0) as usize;
            let line = line.saturating_sub(prelude_lines);
            spans.push((line, s["label"].as_str().map(str::to_string)));
            if s["is_primary"].as_bool() == Some(true) {
                primary_lines.push(line);
            }
        }
        diags.push(Diag {
            level: diag["level"].as_str().unwrap_or("?").to_string(),
            code: diag["code"]["code"].as_str().map(str::to_string),
            message,
            spans,
            primary_lines,
        });
    }
    let vcir = std::fs::read_to_string(&dump).ok();
    let _ = std::fs::remove_dir_all(&dir);
    Run {
        exit: output.status.code().unwrap_or(-1),
        record,
        diags,
        raw,
        vcir,
    }
}
