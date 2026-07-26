// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

// Authenticated Targo reserves the `TRUST_` prefix for process-authority
// channels. This value is only compiled into the CLI as a provenance stamp.
const BUILD_GIT_HEAD_ENV: &str = "TVC_BUILD_GIT_HEAD";

fn main() {
    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));
    let repo_root = find_repo_root(&manifest_dir);
    if let Some(root) = repo_root.as_deref() {
        emit_git_rerun_paths(root);
        if let Some(head) = git_head(root) {
            println!("cargo:rustc-env={BUILD_GIT_HEAD_ENV}={head}");
            return;
        }
    }
    println!("cargo:rustc-env={BUILD_GIT_HEAD_ENV}=unknown");
}

fn find_repo_root(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .find(|path| path.join(".git").exists())
        .map(Path::to_path_buf)
}

fn git_head(repo_root: &Path) -> Option<String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(repo_root)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let head = String::from_utf8(output.stdout).ok()?;
    let head = head.trim();
    if head.is_empty() {
        None
    } else {
        Some(head.to_string())
    }
}

fn emit_git_rerun_paths(repo_root: &Path) {
    let dot_git = repo_root.join(".git");
    if dot_git.is_file() {
        println!("cargo:rerun-if-changed={}", dot_git.display());
        if let Ok(contents) = std::fs::read_to_string(&dot_git) {
            if let Some(path) = contents.trim().strip_prefix("gitdir:") {
                emit_head_rerun_paths(&repo_root.join(path.trim()));
            }
        }
    } else {
        emit_head_rerun_paths(&dot_git);
    }
}

fn emit_head_rerun_paths(git_dir: &Path) {
    let head = git_dir.join("HEAD");
    println!("cargo:rerun-if-changed={}", head.display());
    if let Ok(contents) = std::fs::read_to_string(&head) {
        if let Some(reference) = contents.trim().strip_prefix("ref:") {
            println!(
                "cargo:rerun-if-changed={}",
                git_dir.join(reference.trim()).display()
            );
        }
    }
}
