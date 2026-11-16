// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit request environment for the audited SDK macro cohort.
//!
//! VERUSDOC uses proc_macro::tracked::env_var, whose exact installed bridge
//! consults logical_env before its process fallback. It has no macro cache.
//! Keep its raw presence/value separate from the two output destinations.
//! All three base variables must be absent before producer/worker startup;
//! the dedicated serial caller must exclude process environment writers.
//! VSTD_KIND remains the independently owned one-way Imported context.

extern crate rustc_data_structures;

use crate::output_environment::OutputEnvironment;
use rustc_data_structures::fx::FxIndexMap;
use rustc_session::config::Options;
use std::ffi::OsStr;
use std::io;
use std::process::Command;

const VERUSDOC: &str = "VERUSDOC";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CompilerEnvironment {
    outputs: OutputEnvironment,
    verusdoc: Option<String>,
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

impl CompilerEnvironment {
    pub(crate) fn from_raw(
        verdict_dir: Option<&OsStr>,
        dump_vcir: Option<&OsStr>,
        verusdoc: Option<&OsStr>,
    ) -> io::Result<Self> {
        let verusdoc = verusdoc
            .map(|value| {
                let text = value
                    .to_str()
                    .ok_or_else(|| invalid("non-Unicode VERUSDOC is not representable"))?;
                if text.as_bytes().contains(&0) {
                    return Err(invalid("NUL in VERUSDOC"));
                }
                Ok(text.to_owned())
            })
            .transpose()?;
        Ok(Self {
            outputs: OutputEnvironment::from_raw(verdict_dir, dump_vcir)?,
            verusdoc,
        })
    }

    pub(crate) fn require_absent_process() -> io::Result<()> {
        OutputEnvironment::require_absent_process()?;
        if std::env::var_os(VERUSDOC).is_some() {
            return Err(invalid("coordinator VERUSDOC must be absent"));
        }
        Ok(())
    }

    fn logical_env(&self) -> FxIndexMap<String, String> {
        let mut map = self.outputs.logical_env();
        if let Some(value) = &self.verusdoc {
            map.insert(VERUSDOC.into(), value.clone());
        }
        map
    }

    pub(crate) fn apply_to_options(&self, options: &mut Options) -> io::Result<()> {
        Self::require_absent_process()?;
        self.replace_logical_env(options)
    }

    fn replace_logical_env(&self, options: &mut Options) -> io::Result<()> {
        if options.logical_env.keys().any(|key| {
            !matches!(
                key.as_str(),
                "TRUST_VC_VERDICT_DIR" | "TRUST_VC_DUMP_VCIR" | "VERUSDOC"
            )
        }) {
            return Err(invalid("unrepresented compiler logical environment"));
        }
        options.logical_env = self.logical_env();
        Ok(())
    }

    pub(crate) fn check_options(&self, options: &Options) -> io::Result<()> {
        Self::require_absent_process()?;
        if options.logical_env != self.logical_env() {
            return Err(invalid(
                "actual compiler logical environment differs from its request",
            ));
        }
        Ok(())
    }

    pub(crate) fn check_dependency(&self, key: &str, actual: Option<&str>) -> io::Result<()> {
        if key != VERUSDOC {
            return self.outputs.check_dependency(key, actual);
        }
        if actual != self.verusdoc.as_deref() {
            return Err(invalid(
                "actual VERUSDOC dependency differs from its request",
            ));
        }
        Ok(())
    }

    pub(crate) fn configure_child(&self, command: &mut Command) {
        self.outputs.configure_child(command);
        if let Some(value) = &self.verusdoc {
            command.env(VERUSDOC, value);
        } else {
            command.env_remove(VERUSDOC);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn documentation_values_presence_and_unknown_dependencies_are_bound() {
        for value in [None, Some(""), Some("1"), Some("0")] {
            let env = CompilerEnvironment::from_raw(None, None, value.map(OsStr::new)).unwrap();
            env.check_dependency(VERUSDOC, value).unwrap();
            assert_eq!(env.logical_env().get(VERUSDOC).map(String::as_str), value);
            assert!(env
                .check_dependency("UNREPRESENTED_COHORT_KEY", None)
                .is_err());
            assert!(env.check_dependency(VERUSDOC, Some("different")).is_err());
        }
        let absent = CompilerEnvironment::from_raw(None, None, None).unwrap();
        assert!(absent.check_dependency(VERUSDOC, Some("")).is_err());
        assert!(CompilerEnvironment::from_raw(None, None, Some(OsStr::new("bad\0value"))).is_err());
    }

    #[test]
    fn child_carries_the_exact_third_value_or_removal() {
        for value in [None, Some(""), Some("1")] {
            let env = CompilerEnvironment::from_raw(None, None, value.map(OsStr::new)).unwrap();
            let mut command = Command::new("unused");
            command.env(VERUSDOC, "parent-poison");
            env.configure_child(&mut command);
            assert_eq!(
                command
                    .get_envs()
                    .find(|(key, _)| *key == VERUSDOC)
                    .unwrap()
                    .1,
                value.map(OsStr::new)
            );
        }
    }

    #[test]
    fn complete_union_cannot_drop_unknown_options_or_other_tracking_fields() {
        let env = CompilerEnvironment::from_raw(
            Some(OsStr::new("relative")),
            None,
            Some(OsStr::new("1")),
        )
        .unwrap();
        let original = Options::default();
        let mut options = original.clone();
        env.replace_logical_env(&mut options).unwrap();
        assert_eq!(
            options.logical_env.get("VERUSDOC").map(String::as_str),
            Some("1")
        );
        assert_eq!(
            options
                .logical_env
                .get("TRUST_VC_VERDICT_DIR")
                .map(String::as_str),
            Some("relative")
        );
        assert_ne!(
            options.dep_tracking_hash(false),
            original.dep_tracking_hash(false)
        );
        options.logical_env = original.logical_env.clone();
        assert_eq!(
            options.dep_tracking_hash(false),
            original.dep_tracking_hash(false)
        );
        options.test = !original.test;
        assert_ne!(
            options.dep_tracking_hash(false),
            original.dep_tracking_hash(false)
        );
        options
            .logical_env
            .insert("UNREPRESENTED_COHORT_KEY".into(), "synthetic".into());
        let before = options.logical_env.clone();
        assert!(env.replace_logical_env(&mut options).is_err());
        assert_eq!(options.logical_env, before);
    }

    #[cfg(unix)]
    #[test]
    fn non_unicode_documentation_value_is_not_treated_as_absent() {
        use std::os::unix::ffi::OsStrExt;
        assert!(
            CompilerEnvironment::from_raw(None, None, Some(OsStr::from_bytes(b"doc-\xff")))
                .is_err()
        );
    }
}
