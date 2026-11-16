// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The original semantic values of the two request output variables.
//!
//! These values are not rebased output paths. `env!` must see the original
//! relative value, empty string, or absence supplied by the caller.
//!
//! Installed compiler 20882 has string-valued `Options::logical_env` overrides,
//! followed by a process-environment fallback. It has no unset/tombstone. A
//! coordinator using this module must therefore start with both variables
//! absent, before its producer and worker threads, and exclude every concurrent
//! or callback environment writer, including proc macros. Check absence before
//! and after compiler calls. Those checks observe moments; they do not establish
//! the no-writers contract between them. Unknown plugins cannot be admitted by
//! this module. Cargo and every other environment/cohort dimension require
//! separate representation before ordinary coordinator activation.
//!
//! This module changes compiler options and child-command data only. It never
//! changes this process's environment or grants resource, SDK or import custody.

extern crate rustc_data_structures;

use rustc_data_structures::fx::FxIndexMap;
use rustc_session::config::Options;
use std::ffi::OsStr;
use std::io;
use std::process::Command;

const KEYS: [&str; 2] = ["TRUST_VC_VERDICT_DIR", "TRUST_VC_DUMP_VCIR"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OutputEnvironment {
    values: [Option<String>; 2],
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

impl OutputEnvironment {
    /// Preserve original values, including an explicitly present empty string.
    /// Non-Unicode paths remain valid ordinary output data, but cannot be
    /// represented by the installed in-process compiler's logical environment.
    /// Refuse that request instead of treating it as an absent variable.
    pub(crate) fn from_raw(
        verdict_dir: Option<&OsStr>,
        dump_vcir: Option<&OsStr>,
    ) -> io::Result<Self> {
        fn value(input: Option<&OsStr>) -> io::Result<Option<String>> {
            input
                .map(|raw| {
                    let text = raw.to_str().ok_or_else(|| {
                        invalid("non-Unicode output environment is not representable")
                    })?;
                    if text.as_bytes().contains(&0) {
                        return Err(invalid("NUL in output environment"));
                    }
                    Ok(text.to_owned())
                })
                .transpose()
        }
        Ok(Self {
            values: [value(verdict_dir)?, value(dump_vcir)?],
        })
    }

    /// A point-in-time observation, not a token proving future absence. The
    /// dedicated-process startup and no-environment-writers contract above is
    /// required for absence to remain faithful during expansion.
    pub(crate) fn require_absent_process() -> io::Result<()> {
        if KEYS.iter().any(|key| std::env::var_os(key).is_some()) {
            return Err(invalid("coordinator output environment must be absent"));
        }
        Ok(())
    }

    /// The complete supported logical environment. The map deliberately has no
    /// binding for absence; an empty string remains a present binding.
    pub(crate) fn logical_env(&self) -> FxIndexMap<String, String> {
        KEYS.iter()
            .zip(&self.values)
            .filter_map(|(key, value)| value.as_ref().map(|value| ((*key).into(), value.clone())))
            .collect()
    }

    /// Apply only under the dedicated-process contract. No unknown logical
    /// bindings are discarded or silently classified as absent.
    pub(crate) fn apply_to_options(&self, options: &mut Options) -> io::Result<()> {
        Self::require_absent_process()?;
        self.replace_logical_env(options)
    }

    fn replace_logical_env(&self, options: &mut Options) -> io::Result<()> {
        if options
            .logical_env
            .keys()
            .any(|key| !KEYS.contains(&key.as_str()))
        {
            return Err(invalid("unrepresented compiler logical environment"));
        }
        options.logical_env = self.logical_env();
        Ok(())
    }

    /// Bind the actual native map before a caller accounts for this one tracked
    /// field in its producer baseline. The caller must retain the residual
    /// tracking comparison and every other native/source/Cargo check.
    pub(crate) fn check_options(&self, options: &Options) -> io::Result<()> {
        Self::require_absent_process()?;
        self.check_logical_env(&options.logical_env)
    }

    /// The output component represents only these two environment keys. The
    /// compiler context composes it with its explicitly typed macro inputs.
    /// Bind the compiler's actual env!/option_env! dependency before reading
    /// or verification, including an observed absence. An unrelated key must
    /// not silently use the coordinator's ambient value. This does not observe
    /// arbitrary proc-macro std::env reads; those require the closed audited
    /// macro cohort described above.
    pub(crate) fn check_dependency(&self, key: &str, actual: Option<&str>) -> io::Result<()> {
        let index = KEYS
            .iter()
            .position(|known| *known == key)
            .ok_or_else(|| invalid("unrepresented compiler environment dependency"))?;
        if self.values[index].as_deref() != actual {
            return Err(invalid(
                "compiler environment dependency differs from its request",
            ));
        }
        Ok(())
    }

    fn check_logical_env(&self, actual: &FxIndexMap<String, String>) -> io::Result<()> {
        if actual != &self.logical_env() {
            return Err(invalid(
                "actual compiler logical environment differs from its request",
            ));
        }
        Ok(())
    }

    /// Mirror the same original values and absence in an erasure child. Other
    /// command environment entries and all descriptor/resource handling belong
    /// to their existing callers and are left untouched here.
    pub(crate) fn configure_child(&self, command: &mut Command) {
        for (key, value) in KEYS.iter().zip(&self.values) {
            if let Some(value) = value {
                command.env(key, value);
            } else {
                command.env_remove(key);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn observed_dependencies_bind_absence_empty_and_refuse_unrepresented_keys() {
        let env = OutputEnvironment::from_raw(Some(OsStr::new("")), None).unwrap();
        env.check_dependency(KEYS[0], Some("")).unwrap();
        env.check_dependency(KEYS[1], None).unwrap();
        assert!(env.check_dependency(KEYS[0], None).is_err());
        assert!(env.check_dependency(KEYS[1], Some("")).is_err());
        for value in [None, Some(""), Some("synthetic")] {
            assert!(env
                .check_dependency("UNREPRESENTED_COHORT_KEY", value)
                .is_err());
        }
    }

    #[test]
    fn raw_relative_empty_and_absent_values_are_distinct() {
        let env =
            OutputEnvironment::from_raw(Some(OsStr::new("relative/records")), Some(OsStr::new("")))
                .unwrap();
        let map = env.logical_env();
        assert_eq!(
            map.get(KEYS[0]).map(String::as_str),
            Some("relative/records")
        );
        assert_eq!(map.get(KEYS[1]).map(String::as_str), Some(""));
        let absent = OutputEnvironment::from_raw(None, None).unwrap();
        assert!(absent.logical_env().is_empty());
        assert_ne!(env, absent);
    }

    #[test]
    fn nul_is_refused_instead_of_becoming_absent() {
        assert!(OutputEnvironment::from_raw(Some(OsStr::new("bad\0path")), None).is_err());
        assert!(OutputEnvironment::from_raw(None, Some(OsStr::new("bad\0path"))).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn non_unicode_is_refused_instead_of_becoming_absent() {
        use std::os::unix::ffi::OsStrExt;
        let bad = OsStr::from_bytes(b"bad-\xff");
        assert!(OutputEnvironment::from_raw(Some(bad), None).is_err());
        assert!(OutputEnvironment::from_raw(None, Some(bad)).is_err());
    }

    #[test]
    fn actual_map_requires_every_original_value_and_absence() {
        let env = OutputEnvironment::from_raw(Some(OsStr::new("records")), None).unwrap();
        let mut actual = env.logical_env();
        env.check_logical_env(&actual).unwrap();
        actual.insert(KEYS[0].into(), "different".into());
        assert!(env.check_logical_env(&actual).is_err());
        actual = env.logical_env();
        actual.insert(KEYS[1].into(), "".into());
        assert!(env.check_logical_env(&actual).is_err());
        actual = env.logical_env();
        actual.insert("UNREPRESENTED_COHORT_KEY".into(), "synthetic".into());
        assert!(env.check_logical_env(&actual).is_err());
    }

    #[test]
    fn replacing_request_values_cannot_discard_unknown_logical_bindings() {
        let env = OutputEnvironment::from_raw(None, None).unwrap();
        let mut options = Options::default();
        options
            .logical_env
            .insert("UNREPRESENTED_COHORT_KEY".into(), "synthetic".into());
        let before = options.logical_env.clone();
        assert!(env.replace_logical_env(&mut options).is_err());
        assert_eq!(options.logical_env, before);
    }

    #[test]
    fn tracked_options_retain_every_dimension_beyond_the_exact_logical_map() {
        let original = Options::default();
        let mut options = original.clone();
        let env = OutputEnvironment::from_raw(Some(OsStr::new("records")), None).unwrap();
        env.replace_logical_env(&mut options).unwrap();
        assert_ne!(
            options.dep_tracking_hash(false),
            original.dep_tracking_hash(false)
        );
        options.logical_env = original.logical_env.clone();
        assert_eq!(
            options.dep_tracking_hash(false),
            original.dep_tracking_hash(false)
        );
        options.test = !options.test;
        assert_ne!(
            options.dep_tracking_hash(false),
            original.dep_tracking_hash(false)
        );
    }

    #[test]
    fn child_commands_mirror_values_and_explicit_removal_without_other_changes() {
        let env = OutputEnvironment::from_raw(Some(OsStr::new("relative/records")), None).unwrap();
        let mut child = Command::new("unused-compiler");
        child
            .env(KEYS[0], "old")
            .env(KEYS[1], "old")
            .env("UNRELATED_COHORT_KEY", "synthetic");
        env.configure_child(&mut child);
        let map = child
            .get_envs()
            .map(|(key, value)| (key.to_owned(), value.map(OsStr::to_owned)))
            .collect::<std::collections::BTreeMap<_, _>>();
        assert_eq!(
            map[OsStr::new(KEYS[0])].as_deref(),
            Some(OsStr::new("relative/records"))
        );
        assert_eq!(map[OsStr::new(KEYS[1])], None);
        assert_eq!(
            map[OsStr::new("UNRELATED_COHORT_KEY")].as_deref(),
            Some(OsStr::new("synthetic"))
        );
    }
}
