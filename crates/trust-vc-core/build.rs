// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

// Authenticated Targo reserves the `TRUST_` prefix for process-authority
// channels. This value is only compiled into this crate as a cache provenance
// stamp, so keep it outside that namespace.
const BUILD_GIT_HEAD_ENV: &str = "TVC_CORE_BUILD_GIT_HEAD";

fn main() {
    // SOUNDNESS: emit the variable on EVERY path, including the failure paths.
    //
    // The consumer reads it with `option_env!`, which falls back to the ambient
    // process environment when Cargo sets nothing. So "deliberately leave the
    // build identity unset" did not leave it unset — it left it open. An
    // exported `TVC_CORE_BUILD_GIT_HEAD=<40 hex chars>` in the build shell
    // satisfies the consumer's `is_full_git_revision` check (which tests only
    // length and hex-ness, never that the revision exists or that the tree
    // matches it) and re-enables the persistent VC cache on precisely the builds
    // this function means to lock out: dirty trees, git-less environments,
    // malformed HEADs.
    //
    // Emitting an empty value on those paths makes Cargo's value always win.
    // Empty is not a full git revision, so the consumer's existing check rejects
    // it and the intended "bypass the cache" behaviour is preserved — now
    // because the compiled-in value says so, rather than because nothing was
    // said.
    //
    // `rerun-if-env-changed` is declared so the ambient value is a tracked build
    // input rather than an untracked one that can change under a cached build.
    println!("cargo:rerun-if-env-changed={BUILD_GIT_HEAD_ENV}");

    let Some(manifest_dir) = std::env::var_os("CARGO_MANIFEST_DIR").map(PathBuf::from) else {
        emit_unauthenticated_build_identity();
        return;
    };
    let Some(repo_root) = find_repo_root(&manifest_dir) else {
        emit_unauthenticated_build_identity();
        return;
    };

    emit_source_rerun_paths(&repo_root);
    emit_git_rerun_paths(&repo_root);

    // A Git revision authenticates the bytes being compiled only for a clean
    // checkout. If Git is unavailable, HEAD is abbreviated/malformed, or any
    // tracked/untracked byte differs from HEAD, the build identity is emitted
    // EMPTY. The verifier then bypasses its persistent VC cache.
    let Some(head) = clean_full_git_head(&repo_root) else {
        emit_unauthenticated_build_identity();
        return;
    };
    println!("cargo:rustc-env={BUILD_GIT_HEAD_ENV}={head}");
}

/// Pin the build identity to a value that cannot authenticate anything, so an
/// ambient environment variable cannot supply one instead.
fn emit_unauthenticated_build_identity() {
    println!("cargo:rustc-env={BUILD_GIT_HEAD_ENV}=");
}

fn find_repo_root(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .find(|path| path.join(".git").exists())
        .map(Path::to_path_buf)
}

fn clean_full_git_head(repo_root: &Path) -> Option<String> {
    let head = git_stdout(repo_root, &["rev-parse", "HEAD"])?;
    if !is_full_git_revision(&head) {
        return None;
    }

    let status = git_stdout(
        repo_root,
        &["status", "--porcelain=v1", "--untracked-files=all"],
    )?;
    status.is_empty().then_some(head)
}

fn git_stdout(repo_root: &Path, args: &[&str]) -> Option<String> {
    let output = Command::new("git")
        .args(args)
        .current_dir(repo_root)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout)
        .ok()
        .map(|value| value.trim().to_string())
}

fn is_full_git_revision(value: &str) -> bool {
    matches!(value.len(), 40 | 64)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn emit_source_rerun_paths(repo_root: &Path) {
    // Emitting any `rerun-if-changed` directive replaces Cargo's default
    // package-wide source scan. Watch every in-repository crate so a source
    // edit cannot reuse an earlier clean-checkout identity. Workspace inputs
    // can also change dependency resolution or compiler semantics.
    for path in [
        repo_root.join("crates"),
        repo_root.join("Cargo.toml"),
        repo_root.join("Cargo.lock"),
        repo_root.join(".cargo/config.toml"),
        repo_root.join("rust-toolchain.toml"),
    ] {
        if path.exists() {
            println!("cargo:rerun-if-changed={}", path.display());
        }
    }
}

fn emit_git_rerun_paths(repo_root: &Path) {
    let dot_git = repo_root.join(".git");
    println!("cargo:rerun-if-changed={}", dot_git.display());

    // `git rev-parse --git-path` handles ordinary repositories and linked
    // worktrees. HEAD/ref changes alter the revision; index changes alter the
    // cleanliness claim. Re-run the build script for each authority input.
    for git_path in ["HEAD", "index"] {
        if let Some(path) = git_stdout(repo_root, &["rev-parse", "--git-path", git_path]) {
            let path = PathBuf::from(path);
            let path = if path.is_absolute() {
                path
            } else {
                repo_root.join(path)
            };
            println!("cargo:rerun-if-changed={}", path.display());

            if git_path == "HEAD" {
                if let Ok(contents) = std::fs::read_to_string(&path) {
                    if let Some(reference) = contents.trim().strip_prefix("ref:") {
                        if let Some(ref_path) =
                            git_stdout(repo_root, &["rev-parse", "--git-path", reference.trim()])
                        {
                            let ref_path = PathBuf::from(ref_path);
                            let ref_path = if ref_path.is_absolute() {
                                ref_path
                            } else {
                                repo_root.join(ref_path)
                            };
                            println!("cargo:rerun-if-changed={}", ref_path.display());
                        }
                    }
                }
            }
        }
    }
}
