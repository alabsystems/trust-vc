// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Serialized process-environment mutation — THE blessed choke point for
//! `std::env::set_var` / `std::env::remove_var` across the trust-vc workspace.
//!
//! `std::env::set_var` / `remove_var` mutate process-global state: unserialized
//! use races parallel test threads and any env-gated reader that consults the
//! environment mid-flight (and concurrent writes are UB on most platforms). The
//! Trust toolchain's deny-by-default `env_mutation` lint therefore forbids
//! calling them directly; every mutation in this workspace routes through this
//! module, which
//! (a) funnels every raw call through the single `write_env` primitive, the
//!     ONE `env_mutation`-blessed site in the crate, and
//! (b) serializes mutation behind one process-wide lock and restores the
//!     previous value on scope exit, even on panic.
//!
//! Every consumer crate reaches this through its normal `trust-vc-core`
//! dependency (`trust_vc_core::env`); the merge-contract crate is a dependency
//! leaf below core and keeps its own equivalent lock-scoped choke point.
//!
//! Patterns:
//! - whole-scope fixed values:
//!   [`with_serialized_env_vars`](crate::env::with_serialized_env_vars) /
//!   [`with_serialized_env_vars_removed`](crate::env::with_serialized_env_vars_removed)
//! - set/remove sequences probing a knob's parser:
//!   [`with_env_edits`](crate::env::with_env_edits)
//! - guard style inside an existing serialization scope:
//!   [`lock_env`](crate::env::lock_env) +
//!   [`ScopedEnvVar::set`](crate::env::ScopedEnvVar::set) /
//!   [`ScopedEnvVar::unset`](crate::env::ScopedEnvVar::unset)
//! - single-`#[test]` harnesses that must LEAVE a var set for a later child
//!   process:
//!   [`set_persistent_env_var`](crate::env::set_persistent_env_var)

use std::ffi::{OsStr, OsString};
use std::sync::{Mutex, MutexGuard, OnceLock};

/// One process-wide lock for all environment mutation in a binary.
fn env_mutex() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

/// Acquire the process-wide environment lock explicitly.
///
/// For code that needs guard-style scoping ([`ScopedEnvVar`]) across a whole
/// scope. Hold the returned guard for as long as the mutated environment must
/// stay in place. A poisoned lock (a previous holder panicked) is recovered:
/// the guards below restore state on unwind, so the environment is consistent
/// even after a panic.
pub fn lock_env() -> MutexGuard<'static, ()> {
    env_mutex().lock().unwrap_or_else(|e| e.into_inner())
}

/// THE single raw environment write for the crate. Every set/remove routes
/// through this one function; it is the ONLY sanctioned `env_mutation` site.
///
/// Callers must already hold [`lock_env`] (directly or via a `with_*` helper /
/// an outer serialization scope) so the mutation is serialized against every
/// other reader and writer in the process.
///
/// `env_mutation` is the Trust toolchain's deny-by-default env wall; stock
/// rustc does not know the lint name, hence `unknown_lints`.
#[allow(unknown_lints, env_mutation)]
fn write_env(key: &OsStr, value: Option<&OsStr>) {
    match value {
        Some(value) => std::env::set_var(key, value),
        None => std::env::remove_var(key),
    }
}

/// RAII guard: sets or removes one env var, restoring the previous state on
/// drop (also on panic).
///
/// Does NOT itself take [`lock_env`] — compose with [`lock_env`] (or an outer
/// serialization scope) or use the `with_*` helpers below, which do. (Taking
/// the lock per-guard would deadlock the multi-guard helpers.)
pub struct ScopedEnvVar {
    key: OsString,
    previous: Option<OsString>,
}

impl ScopedEnvVar {
    /// Set `key=value` for the guard's lifetime.
    pub fn set(key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> Self {
        let key = key.as_ref().to_owned();
        let previous = std::env::var_os(&key);
        write_env(&key, Some(value.as_ref()));
        Self { key, previous }
    }

    /// Remove `key` for the guard's lifetime.
    pub fn unset(key: impl AsRef<OsStr>) -> Self {
        let key = key.as_ref().to_owned();
        let previous = std::env::var_os(&key);
        write_env(&key, None);
        Self { key, previous }
    }
}

impl Drop for ScopedEnvVar {
    fn drop(&mut self) {
        write_env(&self.key, self.previous.as_deref());
    }
}

/// Run `f` with `vars` set, serialized behind the process-wide env lock;
/// previous values are restored afterwards (also on panic).
pub fn with_serialized_env_vars<T>(vars: &[(&str, &str)], f: impl FnOnce() -> T) -> T {
    let _env_lock = lock_env();
    let _guards: Vec<_> = vars
        .iter()
        .map(|(key, value)| ScopedEnvVar::set(key, value))
        .collect();
    f()
}

/// Run `f` with `vars` removed from the environment, serialized behind the
/// process-wide env lock; previous values are restored afterwards.
pub fn with_serialized_env_vars_removed<T>(vars: &[&str], f: impl FnOnce() -> T) -> T {
    let _env_lock = lock_env();
    let _guards: Vec<_> = vars.iter().map(|key| ScopedEnvVar::unset(key)).collect();
    f()
}

/// Set `key=value` for the remainder of the process, serialized behind the env
/// lock. Unlike [`with_serialized_env_vars`], the value is NOT restored: for
/// single-`#[test]` harnesses (e.g. a trybuild driver) that must LEAVE the
/// variable in place for a child process launched after this returns.
pub fn set_persistent_env_var(key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
    let _env_lock = lock_env();
    write_env(key.as_ref(), Some(value.as_ref()));
}

/// Scoped editor for code that walks a knob through several set/remove states
/// (e.g. probing an env parser's `"0"` / `"1"` / unset behavior).
///
/// Every key touched through the editor is captured once on first touch and
/// restored when the [`with_env_edits`] scope ends (also on panic).
pub struct EnvEditor {
    saved: Vec<(OsString, Option<OsString>)>,
}

impl EnvEditor {
    fn save_once(&mut self, key: &OsStr) {
        if !self.saved.iter().any(|(saved_key, _)| saved_key == key) {
            self.saved.push((key.to_owned(), std::env::var_os(key)));
        }
    }

    /// Set `key=value` until the end of the [`with_env_edits`] scope or the
    /// next edit of `key`.
    pub fn set(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
        let key = key.as_ref();
        self.save_once(key);
        write_env(key, Some(value.as_ref()));
    }

    /// Remove `key` until the end of the [`with_env_edits`] scope or the next
    /// edit of `key`.
    pub fn remove(&mut self, key: impl AsRef<OsStr>) {
        let key = key.as_ref();
        self.save_once(key);
        write_env(key, None);
    }
}

impl Drop for EnvEditor {
    fn drop(&mut self) {
        // Restore in reverse touch order (first-touched wins last).
        for (key, previous) in self.saved.drain(..).rev() {
            write_env(&key, previous.as_deref());
        }
    }
}

/// Run `f` with exclusive, restore-on-exit access to the process environment
/// via an [`EnvEditor`].
pub fn with_env_edits<T>(f: impl FnOnce(&mut EnvEditor) -> T) -> T {
    let _env_lock = lock_env();
    let mut editor = EnvEditor { saved: Vec::new() };
    f(&mut editor)
    // editor drops (restores) before _env_lock releases.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scoped_set_and_unset_restore_previous_state() {
        let _lock = lock_env();
        let key = "TRUST_VC_CORE_ENV_SCOPED";
        assert!(std::env::var(key).is_err());
        {
            let _g = ScopedEnvVar::set(key, "a");
            assert_eq!(std::env::var(key).as_deref(), Ok("a"));
            {
                let _h = ScopedEnvVar::unset(key);
                assert!(std::env::var(key).is_err());
            }
            assert_eq!(std::env::var(key).as_deref(), Ok("a"));
        }
        assert!(std::env::var(key).is_err());
    }

    #[test]
    fn env_edits_restore_all_touched_keys() {
        let key = "TRUST_VC_CORE_ENV_EDITS";
        with_env_edits(|env| {
            env.set(key, "0");
            assert_eq!(std::env::var(key).as_deref(), Ok("0"));
            env.set(key, "1");
            assert_eq!(std::env::var(key).as_deref(), Ok("1"));
            env.remove(key);
            assert!(std::env::var(key).is_err());
        });
        assert!(std::env::var(key).is_err());
    }

    #[test]
    fn serialized_vars_visible_inside_scope_only() {
        let key = "TRUST_VC_CORE_ENV_SERIALIZED";
        with_serialized_env_vars(&[(key, "42")], || {
            assert_eq!(std::env::var(key).as_deref(), Ok("42"));
        });
        assert!(std::env::var(key).is_err());
        with_serialized_env_vars_removed(&[key], || {
            assert!(std::env::var(key).is_err());
        });
    }
}
