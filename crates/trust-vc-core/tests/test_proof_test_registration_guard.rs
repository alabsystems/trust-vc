//! Structural regression guard: every `*_proof_tests.rs` companion file must
//! be registered as a `#[cfg(test)]` module in a parent module, otherwise the
//! tests inside are dead code that cargo never compiles.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::fs;
use std::path::{Path, PathBuf};

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

fn is_ignored_line(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.is_empty() || trimmed.starts_with("//")
}

fn is_module_declaration(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.ends_with(';') && trimmed.contains("mod ")
}

/// Returns true if `registrar_content` contains a real proof-test registration
/// block for `proof_test_filename`:
///
/// #[cfg(test)]
/// #[path = "...filename..."]
/// mod ...;
fn has_test_module_registration(registrar_content: &str, proof_test_filename: &str) -> bool {
    let lines: Vec<&str> = registrar_content
        .lines()
        .map(str::trim)
        .filter(|line| !is_ignored_line(line))
        .collect();

    for start in 0..lines.len() {
        if lines[start] != "#[cfg(test)]" {
            continue;
        }

        let mut saw_matching_path = false;
        for line in &lines[start + 1..] {
            if line.starts_with("#[path") {
                if line.contains(proof_test_filename) {
                    saw_matching_path = true;
                    continue;
                }
                break;
            }

            if line.starts_with("#[") {
                if saw_matching_path {
                    continue;
                }
                break;
            }

            if saw_matching_path && is_module_declaration(line) {
                return true;
            }

            break;
        }
    }

    false
}

#[test]
fn test_all_proof_test_companions_are_registered() {
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");

    let mut all_rs = Vec::new();
    collect_rs_files(&src_dir, &mut all_rs);

    let proof_test_files: Vec<&PathBuf> = all_rs
        .iter()
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with("_proof_tests.rs"))
        })
        .collect();

    assert!(
        !proof_test_files.is_empty(),
        "Expected at least one *_proof_tests.rs companion file under src/"
    );

    // Pre-read all non-proof-test .rs files (potential registrars).
    let registrars: Vec<(PathBuf, String)> = all_rs
        .iter()
        .filter(|p| {
            !p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with("_proof_tests.rs"))
        })
        .filter_map(|p| fs::read_to_string(p).ok().map(|c| (p.clone(), c)))
        .collect();

    let mut unwired: Vec<String> = Vec::new();

    for proof_file in &proof_test_files {
        let filename = proof_file.file_name().unwrap().to_str().unwrap();

        let registered = registrars
            .iter()
            .any(|(_, content)| has_test_module_registration(content, filename));

        if !registered {
            // Show path relative to src/ for readability.
            let rel = proof_file.strip_prefix(&src_dir).unwrap_or(proof_file);
            unwired.push(rel.display().to_string());
        }
    }

    assert!(
        unwired.is_empty(),
        "Found {} proof_tests companion file(s) without module registration:\n\
         {}\n\n\
         Each *_proof_tests.rs file must be registered in its parent module:\n\
         \n\
         #[cfg(test)]\n\
         #[path = \"<name>_proof_tests.rs\"]\n\
         mod <any_module_name>;\n",
        unwired.len(),
        unwired
            .iter()
            .map(|f| format!("  - {f}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn accepts_cfg_test_path_module_registration() {
    let registrar = r#"
        #[cfg(test)]
        #[path = "proof_session_proof_tests.rs"]
        mod proof_tests;
    "#;

    assert!(has_test_module_registration(
        registrar,
        "proof_session_proof_tests.rs"
    ));
}

#[test]
fn accepts_cfg_test_path_with_nondefault_module_name() {
    let registrar = r#"
        #[cfg(test)]
        #[path = "mut_ref_proof_tests.rs"]
        mod soundness_tests;
    "#;

    assert!(has_test_module_registration(
        registrar,
        "mut_ref_proof_tests.rs"
    ));
}

#[test]
fn rejects_path_without_cfg_test_gate() {
    let registrar = r#"
        #[cfg(not(test))]
        #[path = "proof_session_proof_tests.rs"]
        mod proof_tests;
    "#;

    assert!(!has_test_module_registration(
        registrar,
        "proof_session_proof_tests.rs"
    ));
}

#[test]
fn rejects_path_without_module_declaration() {
    let registrar = r#"
        #[cfg(test)]
        #[path = "proof_session_proof_tests.rs"]
    "#;

    assert!(!has_test_module_registration(
        registrar,
        "proof_session_proof_tests.rs"
    ));
}
