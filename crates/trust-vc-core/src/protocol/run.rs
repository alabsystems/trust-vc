//! One `ty check` run over an obligation, in a private directory.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The spec and the canonical config are written into a fresh directory only
//! this user can read (mode 0700, a unique name under the temporary
//! directory, removed when the run ends). `ty` runs there with the
//! environment cleared but `HOME` and `TMPDIR`, both that directory, and
//! stdin closed: no `TY_*` setting, module search path (`TLA_PATH`,
//! `TLA_LIBRARY`), result cache or other inherited state reaches the check.
//! No timeout and no size limit: a `ty` that does not return holds the call,
//! as an in-process check would.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

/// The flags check-json-contract-v2 freezes: one JSON document, no result
/// cache, no progress output, one sequential breadth-first search, no
/// partial-order or symmetry reduction, every state evaluated by the
/// interpreter (no native or GPU engine).
pub(super) const CHECK_FLAGS: [&str; 11] = [
    "--output",
    "json",
    "--no-cache",
    "--quiet",
    "--workers",
    "1",
    "--bfs-only",
    "--no-reduction",
    "--backend",
    "interpreter",
    "--no-gpu",
];

/// What the binary did.
#[derive(Debug, Clone)]
pub(super) struct Run {
    /// The binary that ran.
    pub(super) bin: PathBuf,
    /// Its exit status; `None` when a signal ended it.
    pub(super) exit: Option<i32>,
    pub(super) stdout: Vec<u8>,
    pub(super) stderr: Vec<u8>,
}

/// Run `bin check` on `spec` and `config`.
pub(super) fn check(bin: &Path, spec: &str, config: &str) -> Result<Run, String> {
    let dir = PrivateDir::create()?;
    let stem = module_file_stem(spec);
    let spec_path = dir.0.join(format!("{stem}.tla"));
    let config_path = dir.0.join(format!("{stem}.cfg"));
    std::fs::write(&spec_path, spec)
        .map_err(|error| format!("write {}: {error}", spec_path.display()))?;
    std::fs::write(&config_path, config)
        .map_err(|error| format!("write {}: {error}", config_path.display()))?;
    let output = Command::new(bin)
        .arg("check")
        .arg(&spec_path)
        .arg("-c")
        .arg(&config_path)
        .args(CHECK_FLAGS)
        .env_clear()
        .env("HOME", &dir.0)
        .env("TMPDIR", &dir.0)
        .current_dir(&dir.0)
        .stdin(Stdio::null())
        .output()
        .map_err(|error| format!("spawn {}: {error}", bin.display()))?;
    Ok(Run {
        bin: bin.to_path_buf(),
        exit: output.status.code(),
        stdout: output.stdout,
        stderr: output.stderr,
    })
}

/// The file name the spec is written under: the name of the module it
/// starts, as SANY requires a file to be named like its first module (and
/// `ty check` refuses one that is not, check-exact-source-v2). The name is
/// read after SANY's begin-module token (four or more `-`, spaces only,
/// `MODULE`) and kept only when it is an identifier; otherwise `Spec`, which
/// `ty` then refuses, as it refuses anything SANY would not read.
pub(super) fn module_file_stem(spec: &str) -> String {
    let bytes = spec.as_bytes();
    let mut at = 0;
    while let Some(offset) = spec[at..].find("----") {
        let mut i = at + offset + 4;
        while bytes.get(i) == Some(&b'-') {
            i += 1;
        }
        while bytes.get(i) == Some(&b' ') {
            i += 1;
        }
        if spec[i..].starts_with("MODULE") {
            let rest = spec[i + "MODULE".len()..].trim_start();
            let name: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if name.chars().any(|c| c.is_ascii_alphabetic()) {
                return name;
            }
        }
        at = i.max(at + offset + 1);
    }
    "Spec".to_string()
}

/// A directory created for one run, removed when it drops.
struct PrivateDir(PathBuf);

impl PrivateDir {
    fn create() -> Result<Self, String> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |elapsed| elapsed.as_nanos());
        let path = std::env::temp_dir().join(format!(
            "trust-vc-ty-{}-{}-{nanos}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let mut builder = std::fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            builder.mode(0o700);
        }
        // `create`, not `create_all`: a name that exists is someone else's.
        builder
            .create(&path)
            .map_err(|error| format!("create {}: {error}", path.display()))?;
        Ok(Self(path))
    }
}

impl Drop for PrivateDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
