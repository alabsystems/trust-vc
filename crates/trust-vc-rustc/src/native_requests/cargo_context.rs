// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The Cargo protocol's actual environment reads are request data only.
//! They never carry VSTD_KIND, compiler selection or scheduler custody.

use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CargoContext {
    pub(crate) values: BTreeMap<String, Option<OsString>>,
}

impl Default for CargoContext {
    fn default() -> Self {
        Self {
            values: BTreeMap::from([(crate::cargo::VIA_CARGO.to_owned(), None)]),
        }
    }
}

fn allowed(key: &str) -> bool {
    if key.as_bytes().iter().any(|b| *b == 0 || *b == b'=') {
        return false;
    }
    matches!(
        key,
        crate::cargo::VIA_CARGO
            | crate::cargo::DRIVER_ARGS
            | "CARGO_CRATE_NAME"
            | "CARGO_PKG_NAME"
            | "CARGO_PKG_VERSION"
            | "CARGO_MANIFEST_DIR"
            | "CARGO_PRIMARY_PACKAGE"
    ) || [
        crate::cargo::DRIVER_ARGS_FOR,
        crate::cargo::VERIFY,
        crate::cargo::IS_BUILTIN,
        crate::cargo::IS_BUILTIN_MACROS,
    ]
    .iter()
    .any(|prefix| {
        key.strip_prefix(*prefix)
            .is_some_and(|tail| !tail.is_empty() && !tail.as_bytes().contains(&0))
    })
}

impl CargoContext {
    pub(crate) fn capture(argv: &[OsString], macro_package_name: Option<&std::ffi::OsStr>) -> Self {
        let Some(argv) = argv
            .iter()
            .map(|s| s.to_str().map(str::to_owned))
            .collect::<Option<Vec<_>>>()
        else {
            // The original raw argv still travels byte-for-byte. The native
            // coordinator refuses non-Unicode compiler argv before using this.
            return Self {
                values: BTreeMap::new(),
            };
        };
        let mut values = BTreeMap::new();
        let _ = crate::cargo::prepare(&argv, |key| {
            let value = if key == "CARGO_PKG_NAME" {
                macro_package_name.map(std::ffi::OsStr::to_os_string)
            } else {
                std::env::var_os(key)
            };
            values.insert(key.to_owned(), value.clone());
            value
                .map(|v| {
                    v.into_string().map_err(|_| {
                        format!("Cargo environment variable {key} is not valid Unicode")
                    })
                })
                .transpose()
        });
        Self { values }
    }

    pub(crate) fn read(&self, key: &str) -> Result<Option<String>, String> {
        if !allowed(key) {
            return Err("an unrepresented Cargo environment key was requested".into());
        }
        self.values
            .get(key)
            .ok_or_else(|| format!("the actual Cargo read {key} was not captured"))?
            .as_ref()
            .map(|value| {
                value
                    .to_str()
                    .map(str::to_owned)
                    .ok_or_else(|| format!("Cargo environment variable {key} is not valid Unicode"))
            })
            .transpose()
    }

    pub(crate) fn check_macro_package(
        &self,
        snapshot: Option<&std::ffi::OsStr>,
    ) -> Result<(), String> {
        if self
            .values
            .get("CARGO_PKG_NAME")
            .is_some_and(|value| value.as_deref() != snapshot)
        {
            return Err("Cargo and macro package snapshots differ".into());
        }
        Ok(())
    }
    pub(crate) fn validate(&self, argv: &[String]) -> Result<(), String> {
        if self.values.keys().any(|key| !allowed(key)) {
            return Err("unrepresented Cargo request environment".into());
        }
        let mut used = BTreeSet::new();
        // Even a malformed native Cargo request must retain the exact reads
        // made before its ordinary argument error, rather than invent values.
        let _ = crate::cargo::prepare(argv, |key| {
            used.insert(key.to_owned());
            self.read(key)
        });
        if used.len() != self.values.len() || self.values.keys().any(|key| !used.contains(key)) {
            return Err("the Cargo request environment has missing or unused reads".into());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn standalone_absence_is_retained_and_global_keys_never_enter() {
        let argv = vec![
            "compiler".into(),
            "--internal-test-mode".into(),
            "input.rs".into(),
        ];
        let context = CargoContext::default();
        context.validate(&argv).unwrap();
        assert_eq!(context.read(crate::cargo::VIA_CARGO).unwrap(), None);
        for key in [
            "VSTD_KIND",
            "RUSTC",
            "CARGO_MAKEFLAGS",
            "BUILD_SLOT_HELD",
            "TRUST_VC_NATIVE_REQUEST_FD",
            "CARGO_ENCODED_RUSTFLAGS",
        ] {
            let forged = CargoContext {
                values: BTreeMap::from([(key.to_owned(), Some("1".into()))]),
            };
            assert!(forged.validate(&argv).is_err());
        }
        assert!(CargoContext {
            values: BTreeMap::new()
        }
        .validate(&argv)
        .is_err());
    }
    #[test]
    fn cargo_reads_keep_empty_absent_and_nonunicode_distinct() {
        let context = CargoContext {
            values: BTreeMap::from([
                ("CARGO_PRIMARY_PACKAGE".into(), Some("".into())),
                (crate::cargo::VIA_CARGO.into(), None),
                (
                    "CARGO_PKG_NAME".into(),
                    Some(OsString::from_vec(vec![0xff])),
                ),
            ]),
        };
        assert_eq!(
            context.read("CARGO_PRIMARY_PACKAGE").unwrap(),
            Some("".into())
        );
        assert_eq!(context.read(crate::cargo::VIA_CARGO).unwrap(), None);
        assert!(context
            .read("CARGO_PKG_NAME")
            .unwrap_err()
            .contains("not valid Unicode"));
        assert!(context.read("CARGO_PKG_VERSION").is_err());
    }
}
