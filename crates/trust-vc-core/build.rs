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
    // This script only reads the repository it watches. Without
    // GIT_OPTIONAL_LOCKS=0, `git status` takes and drops `index.lock` to save
    // refreshed stat data, which writes into the git directory after Cargo
    // recorded this run, so the next build would find a watched path newer
    // than the run and re-run it, rebuilding every crate that depends on this
    // one.
    let output = Command::new("git")
        .env("GIT_OPTIONAL_LOCKS", "0")
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
    // Cargo scans a watched directory recursively, so a watched `.git`
    // directory re-ran this script after any git command wrote into it (a
    // fetch, a gc, a lock taken and dropped), none of which moves HEAD or the
    // index. A `.git` file (a linked worktree, a submodule's gitfile) names the
    // repository and changes only when it is re-pointed, so only a file is
    // watched; the paths below cover a directory.
    let dot_git = repo_root.join(".git");
    if dot_git.is_file() {
        emit_existing_rerun_path(&dot_git);
    }

    // `git rev-parse --git-path` handles ordinary repositories and linked
    // worktrees. HEAD and the ref it names alter the revision; the index alters
    // the cleanliness claim.
    let Some(head) = git_path(repo_root, "HEAD") else {
        return;
    };
    emit_existing_rerun_path(&head);
    if let Some(index) = git_path(repo_root, "index") {
        emit_existing_rerun_path(&index);
    }
    let Ok(contents) = std::fs::read_to_string(&head) else {
        return;
    };
    let Some(reference) = contents.trim().strip_prefix("ref:") else {
        return;
    };
    let Some(loose) = git_path(repo_root, reference.trim()) else {
        return;
    };
    if loose.is_file() {
        emit_existing_rerun_path(&loose);
        return;
    }
    // A packed branch has no loose ref file: its revision is in packed-refs,
    // and the next commit on it writes the loose file into this directory.
    if let Some(packed) = git_path(repo_root, "packed-refs") {
        emit_existing_rerun_path(&packed);
    }
    // Packing can remove the whole nested branch directory. Watch its nearest
    // existing ancestor inside refs so creating that directory invalidates the
    // identity, without recursively watching unrelated Git metadata.
    if let Some(refs) = git_path(repo_root, "refs") {
        for directory in loose.ancestors().skip(1) {
            if !directory.starts_with(&refs) {
                break;
            }
            if directory.is_dir() {
                emit_existing_rerun_path(directory);
                break;
            }
        }
    }
}

fn git_path(repo_root: &Path, name: &str) -> Option<PathBuf> {
    let path = PathBuf::from(git_stdout(repo_root, &["rev-parse", "--git-path", name])?);
    Some(if path.is_absolute() {
        path
    } else {
        repo_root.join(path)
    })
}

/// Cargo re-runs a build script on every build while one of its watched paths
/// is missing, so a path is watched only when it exists.
fn emit_existing_rerun_path(path: &Path) {
    if path.exists() {
        println!("cargo:rerun-if-changed={}", path.display());
    }
}
