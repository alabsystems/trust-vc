//! Which `ty` binary checks a protocol obligation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Read for every obligation, never cached: `TRUST_VC_TY_BIN` when it is
//! set (an absolute path to a regular file, with no fallback), otherwise the
//! first executable `ty` on `PATH`. Nothing here judges the binary; the
//! capabilities in the document it writes do.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use super::document::REQUIRED_CAPABILITIES;

/// The variable naming the `ty` binary. Deliberately not a `TY_*` name: ty
/// reads those, and this one is trust-vc's.
pub const BIN_VAR: &str = "TRUST_VC_TY_BIN";

/// The binary this process would run now.
pub(super) fn resolve() -> Result<PathBuf, String> {
    resolve_from(std::env::var_os(BIN_VAR), std::env::var_os("PATH"))
}

/// [`resolve`] over explicit values of `TRUST_VC_TY_BIN` and `PATH`.
pub(super) fn resolve_from(
    bin: Option<OsString>,
    path: Option<OsString>,
) -> Result<PathBuf, String> {
    if let Some(bin) = bin {
        let bin = PathBuf::from(bin);
        if !bin.is_absolute() {
            return Err(format!(
                "{BIN_VAR}={} is not an absolute path",
                bin.display()
            ));
        }
        return match std::fs::metadata(&bin) {
            Ok(meta) if meta.is_file() => Ok(bin),
            Ok(_) => Err(format!("{BIN_VAR}={} is not a regular file", bin.display())),
            Err(error) => Err(format!("{BIN_VAR}={}: {error}", bin.display())),
        };
    }
    for dir in std::env::split_paths(&path.unwrap_or_default()) {
        let candidate = dir.join("ty");
        if is_executable_file(&candidate) {
            return std::path::absolute(&candidate)
                .map_err(|error| format!("{}: {error}", candidate.display()));
        }
    }
    Err(format!(
        "no ty binary: set {BIN_VAR} or put a ty advertising {} on PATH",
        REQUIRED_CAPABILITIES.join(", ")
    ))
}

fn is_executable_file(path: &Path) -> bool {
    let Ok(meta) = std::fs::metadata(path) else {
        return false;
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        meta.is_file() && meta.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        meta.is_file()
    }
}
