//! Golden tests for the reader.
//!
//! Each `tests/golden/<name>.rs` is a Verus program. The test runs the
//! `rust_verify` binary on it the way upstream's harness does (the same
//! prelude, the same arguments) and compares what came out with
//! `tests/golden/<name>.expected`: the run's outcome, every diagnostic
//! (level, code, message, line in the golden file), the function statuses and
//! the VcIR the reader produced, printed by `trust_vc_vcir::pretty`.
//!
//! The binary needs the trustc-built `verus_builtin` crates (see
//! `common`). Set `TRUST_VC_GOLDEN_UPDATE=1` to rewrite the expected files
//! from the current output (then review the diff).

use std::path::Path;

mod common;

/// Run the binary on one golden program and render what it produced.
fn run(name: &str, source: &str) -> String {
    let run = common::run(name, source, &[]);
    let mut text = String::new();
    text.push_str(&format!("exit: {}\n", run.exit));
    text.push_str(&format!("outcome: {}\n", run.record["outcome"]));
    text.push_str("diagnostics:\n");
    for line in &run.raw {
        text.push_str(&format!("  NOT JSON: {line}\n"));
    }
    for diag in &run.diags {
        let lines: Vec<String> = diag
            .spans
            .iter()
            .map(|(line, label)| match label {
                Some(label) => format!("{line}:{label}"),
                None => format!("{line}"),
            })
            .collect();
        text.push_str(&format!(
            "  {} {} {} @[{}]\n",
            diag.level,
            diag.code.as_deref().unwrap_or("-"),
            diag.message,
            lines.join(", ")
        ));
    }
    text.push_str("functions:\n");
    if let Some(functions) = run.record["functions"].as_array() {
        for f in functions {
            text.push_str(&format!(
                "  {} {} {}\n",
                f["def_path"].as_str().unwrap_or("?"),
                f["verdict"].as_str().unwrap_or("?"),
                f["tag"].as_str().unwrap_or("-")
            ));
        }
    }
    text.push_str("vcir:\n");
    if let Some(dump) = &run.vcir {
        // The dump ends with the reader's per-function statuses, whose Debug
        // form holds spans; the VcIR part is what is compared.
        for line in dump.lines().take_while(|l| *l != "-- statuses --") {
            text.push_str(line);
            text.push('\n');
        }
    }
    text
}

#[test]
fn golden_programs() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden");
    let update = std::env::var_os("TRUST_VC_GOLDEN_UPDATE").is_some();
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .expect("tests/golden")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "rs"))
        .filter_map(|p| p.file_stem().map(|s| s.to_string_lossy().into_owned()))
        .collect();
    names.sort();
    assert!(!names.is_empty(), "no golden programs in {}", dir.display());
    let mut failures = Vec::new();
    for name in &names {
        let source = std::fs::read_to_string(dir.join(format!("{name}.rs"))).expect("read golden");
        let actual = run(name, &source);
        let expected_path = dir.join(format!("{name}.expected"));
        if update {
            std::fs::write(&expected_path, &actual).expect("write expected");
            continue;
        }
        let expected = std::fs::read_to_string(&expected_path).unwrap_or_default();
        if expected != actual {
            failures.push(format!(
                "--- {name}: expected\n{expected}\n--- {name}: actual\n{actual}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
