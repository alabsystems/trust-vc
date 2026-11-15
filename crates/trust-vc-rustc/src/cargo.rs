//! The native driver's Cargo wrapper protocol.
//!
//! Cargo's leading compiler argument selects the calling convention, never a
//! program to execute. Both routes use this binary's linked Trust compiler.
//! Package selection requests verification; it supplies no proof or imported
//! contract. The protocol follows pinned Verus's `cargo_verus.rs`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
#[cfg(feature = "rustc")]
use std::sync::atomic::{AtomicU64, Ordering};

use sha2::{Digest, Sha256};

pub const VIA_CARGO: &str = "__VERUS_DRIVER_VIA_CARGO__";
pub const DRIVER_ARGS: &str = " __VERUS_DRIVER_ARGS__";
pub const DRIVER_ARGS_FOR: &str = " __VERUS_DRIVER_ARGS_FOR_";
pub const DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
pub const VERIFY: &str = "__VERUS_DRIVER_VERIFY_";
pub const IS_BUILTIN: &str = " __VERUS_DRIVER_IS_BUILTIN_";
pub const IS_BUILTIN_MACROS: &str = " __VERUS_DRIVER_IS_BUILTIN_MACROS_";

/// Values actually consulted, including absent values. The direct route does
/// not depend on unrelated forwarded verification options.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Inputs(pub BTreeMap<String, Option<String>>);

impl Inputs {
    fn get(
        &mut self,
        key: &str,
        read: &mut impl FnMut(&str) -> Result<Option<String>, String>,
    ) -> Result<Option<String>, String> {
        let value = read(key)?;
        self.0.insert(key.to_string(), value.clone());
        Ok(value)
    }

    /// Chain environment dependencies into the compiler's real dep-info.
    #[cfg(feature = "rustc")]
    pub(crate) fn install(&self, config: &mut rustc_interface::interface::Config) {
        use rustc_span::symbol::Symbol;
        if self.0.is_empty() {
            return;
        }
        let previous = config.track_state.take();
        let values = self.0.clone();
        config.track_state = Some(Box::new(move |session| {
            if let Some(previous) = previous {
                previous(session);
            }
            let mut dependencies = session.env_depinfo.lock();
            for (key, value) in values {
                dependencies.insert((Symbol::intern(&key), value.as_deref().map(Symbol::intern)));
            }
        }));
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Invocation {
    Standalone,
    Direct {
        args: Vec<String>,
        inputs: Inputs,
        bootstrap: bool,
    },
    Verify {
        args: Vec<String>,
        options: Options,
        inputs: Inputs,
    },
}

/// Cargo controls compilation separately for roots and dependencies. Presence
/// of CARGO_PRIMARY_PACKAGE counts even when its value is empty.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Options {
    pub compile: bool,
    pub import_deps: BTreeSet<String>,
}

/// The manifest spelling is the one Cargo hashes, without canonicalizing it.
#[must_use]
pub fn package_id(name: &str, version: &str, manifest_path: &str) -> String {
    let digest = Sha256::digest(manifest_path.as_bytes());
    let short: String = digest[..6]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    format!("{name}-{version}-{short}")
}

fn compiler_argument(value: &str) -> bool {
    matches!(
        Path::new(value).file_name().and_then(|name| name.to_str()),
        Some("rustc" | "trustc" | "rustc.exe" | "trustc.exe")
    )
}

fn option_value<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    for (index, argument) in args.iter().enumerate() {
        if argument == name {
            return args.get(index + 1).map(String::as_str);
        }
        if let Some(value) = argument
            .strip_prefix(name)
            .and_then(|tail| tail.strip_prefix('='))
        {
            return Some(value);
        }
    }
    None
}

fn unpack(value: &str) -> impl Iterator<Item = String> + '_ {
    value.split(DRIVER_ARGS_SEP).skip(1).map(str::to_string)
}

/// Pure protocol interpretation, with explicit environment reads for testing
/// and for the compiler's dependency tracker.
pub fn prepare(
    argv: &[String],
    mut read: impl FnMut(&str) -> Result<Option<String>, String>,
) -> Result<Invocation, String> {
    let mut inputs = Inputs::default();
    let via_cargo = inputs.get(VIA_CARGO, &mut read)?.as_deref() == Some("1");
    let leading_compiler = argv.get(1).is_some_and(|arg| compiler_argument(arg));
    if via_cargo != leading_compiler {
        return Err(format!(
            "{VIA_CARGO} must be 1 if and only if a rustc or trustc compiler path is the first argument"
        ));
    }
    if !via_cargo {
        return Ok(Invocation::Standalone);
    }
    let mut args = argv.get(2..).unwrap_or_default().to_vec();
    if option_value(&args, "--crate-name") == Some("___")
        || inputs
            .get("CARGO_CRATE_NAME", &mut read)?
            .is_some_and(|name| name.starts_with("build_script_"))
    {
        return Ok(Invocation::Direct {
            args,
            inputs,
            bootstrap: false,
        });
    }
    let name = inputs.get("CARGO_PKG_NAME", &mut read)?;
    let version = inputs.get("CARGO_PKG_VERSION", &mut read)?;
    let directory = inputs.get("CARGO_MANIFEST_DIR", &mut read)?;
    let id = match (&name, version, directory) {
        (Some(name), Some(version), Some(directory)) => Some(package_id(
            name,
            &version,
            &format!("{directory}{}Cargo.toml", std::path::MAIN_SEPARATOR),
        )),
        _ => None,
    };
    let selected = match &id {
        Some(id) => inputs.get(&format!("{VERIFY}{id}"), &mut read)?.as_deref() == Some("1"),
        None => false,
    };
    if !selected {
        let mut bootstrap = false;
        if option_value(&args, "--crate-name") == Some("proc_macro2") {
            args.extend(
                ["--cfg", "proc_macro_span", "--cfg", "span_locations"].map(str::to_string),
            );
            bootstrap = true;
        }
        if let Some(id) = id {
            let builtin = inputs.get(&format!("{IS_BUILTIN}{id}"), &mut read)?;
            let macros = inputs.get(&format!("{IS_BUILTIN_MACROS}{id}"), &mut read)?;
            if builtin.as_deref() == Some("1") || macros.as_deref() == Some("1") {
                args.extend(
                    ["--cfg", "verus_only", "--cfg", "verus_keep_ghost"].map(str::to_string),
                );
                bootstrap = true;
            }
        }
        return Ok(Invocation::Direct {
            args,
            inputs,
            bootstrap,
        });
    }
    if let Some(value) = inputs.get(DRIVER_ARGS, &mut read)? {
        args.extend(unpack(&value));
    }
    if let Some(value) = inputs.get(&format!("{DRIVER_ARGS_FOR}{}", id.unwrap()), &mut read)? {
        args.extend(unpack(&value));
    }
    let cfgs = if name.as_deref() == Some("vstd") {
        "cfg(verus_keep_ghost, verus_keep_ghost_body, verus_verify_core, verus_no_vstd)"
    } else {
        "cfg(verus_keep_ghost, verus_keep_ghost_body, verus_verify_core, verus_no_vstd, verus_only)"
    };
    args.extend(["--check-cfg".to_string(), cfgs.to_string()]);
    let primary = inputs.get("CARGO_PRIMARY_PACKAGE", &mut read)?.is_some();
    let options = take_options(&mut args, primary)?;
    Ok(Invocation::Verify {
        args,
        options,
        inputs,
    })
}

fn take_options(args: &mut Vec<String>, primary: bool) -> Result<Options, String> {
    let mut options = Options::default();
    let mut output = Vec::with_capacity(args.len());
    let mut arguments = args.iter();
    while let Some(argument) = arguments.next() {
        if argument != "--VIA-CARGO" {
            output.push(argument.clone());
            continue;
        }
        let option = arguments
            .next()
            .ok_or("expected an option after --VIA-CARGO")?;
        match option.as_str() {
            "compile-when-primary-package" => options.compile |= primary,
            "compile-when-not-primary-package" => options.compile |= !primary,
            _ => {
                let Some(dependency) = option.strip_prefix("import-dep-if-present=") else {
                    return Err(format!("unexpected --VIA-CARGO {option}"));
                };
                if dependency.is_empty() || dependency.contains('=') {
                    return Err("expected --VIA-CARGO import-dep-if-present=DEP_NAME".to_string());
                }
                options.import_deps.insert(dependency.to_string());
            }
        }
    }
    *args = output;
    Ok(options)
}

/// Requested imports that actually occur in this target's --extern list.
/// The returned paths are native compiler inputs, not an authenticated VcIR
/// contract. The shim still requires its ordinary import implementation.
pub fn imports(args: &[String], options: &Options) -> Result<Vec<(String, PathBuf)>, String> {
    let mut files: BTreeMap<String, Vec<PathBuf>> = BTreeMap::new();
    let mut arguments = args.iter();
    while let Some(argument) = arguments.next() {
        let value = if argument == "--extern" {
            arguments.next().map(String::as_str)
        } else {
            argument.strip_prefix("--extern=")
        };
        let Some((name, path)) = value.and_then(|value| value.split_once('=')) else {
            continue;
        };
        let name = name.rsplit(':').next().unwrap_or(name);
        files
            .entry(name.to_string())
            .or_default()
            .push(PathBuf::from(path));
    }
    let mut imports = Vec::new();
    for name in &options.import_deps {
        let Some(paths) = files.get(name) else {
            continue;
        };
        let Some(path) = paths
            .iter()
            .map(|path| path.with_extension("vir"))
            .find(|path| path.is_file())
        else {
            return Err(format!("could not find .vir file for '{name}'"));
        };
        imports.push((name.clone(), path));
    }
    Ok(imports)
}

#[cfg(feature = "rustc")]
pub(crate) struct Scratch(PathBuf);

#[cfg(feature = "rustc")]
impl Scratch {
    pub(crate) fn new() -> std::io::Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        for _ in 0..100 {
            let path = std::env::temp_dir().join(format!(
                "trust-vc-cargo-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let mut builder = std::fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                builder.mode(0o700);
            }
            match builder.create(&path) {
                Ok(()) => {
                    let scratch = Self(path);
                    std::fs::create_dir(scratch.0.join("verify"))?;
                    std::fs::create_dir(scratch.0.join("erase"))?;
                    return Ok(scratch);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => return Err(error),
            }
        }
        Err(std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "could not create private Cargo outputs",
        ))
    }

    pub(crate) fn path(&self) -> &Path {
        &self.0
    }
}

#[cfg(feature = "rustc")]
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| value.to_string()).collect()
    }

    fn plan(args: &[&str], variables: &[(&str, &str)]) -> Result<Invocation, String> {
        let variables: BTreeMap<_, _> = variables
            .iter()
            .map(|(key, value)| (key.to_string(), value.to_string()))
            .collect();
        prepare(&strings(args), |key| Ok(variables.get(key).cloned()))
    }

    fn selected(extra: &[(&str, &str)]) -> Vec<(String, String)> {
        let mut values = vec![
            (VIA_CARGO.to_string(), "1".to_string()),
            ("CARGO_PKG_NAME".to_string(), "example".to_string()),
            ("CARGO_PKG_VERSION".to_string(), "1.0.0".to_string()),
            ("CARGO_MANIFEST_DIR".to_string(), "/example".to_string()),
            (
                format!(
                    "{VERIFY}{}",
                    package_id("example", "1.0.0", "/example/Cargo.toml")
                ),
                "1".to_string(),
            ),
        ];
        values.extend(
            extra
                .iter()
                .map(|(key, value)| (key.to_string(), value.to_string())),
        );
        values
    }

    fn selected_plan(args: &[&str], extra: &[(&str, &str)]) -> Invocation {
        let values = selected(extra);
        let references: Vec<_> = values
            .iter()
            .map(|(key, value)| (key.as_str(), value.as_str()))
            .collect();
        plan(args, &references).unwrap()
    }

    #[test]
    fn convention_is_explicit_and_accepts_the_trust_compiler() {
        assert_eq!(
            plan(&["driver", "--internal-test-mode", "source.rs"], &[]).unwrap(),
            Invocation::Standalone
        );
        assert!(plan(&["driver", "/tool/bin/trustc", "source.rs"], &[]).is_err());
        assert!(plan(&["driver", "source.rs"], &[(VIA_CARGO, "1")]).is_err());
        assert!(matches!(
            plan(&["driver", "/tool/bin/trustc", "-vV"], &[(VIA_CARGO, "1")]).unwrap(),
            Invocation::Direct { .. }
        ));
    }

    #[test]
    fn package_identity_uses_the_exact_manifest_spelling() {
        assert_eq!(package_id("p", "1", ""), "p-1-e3b0c44298fc");
        assert_ne!(
            package_id("p", "1", "/a/Cargo.toml"),
            package_id("p", "1", "/a/./Cargo.toml")
        );
    }

    #[test]
    fn selected_package_receives_global_then_package_options() {
        let key = format!(
            "{DRIVER_ARGS_FOR}{}",
            package_id("example", "1.0.0", "/example/Cargo.toml")
        );
        let global = format!("{DRIVER_ARGS_SEP}--rlimit{DRIVER_ARGS_SEP}10");
        let local = format!("{DRIVER_ARGS_SEP}--no-verify{DRIVER_ARGS_SEP}--VIA-CARGO{DRIVER_ARGS_SEP}compile-when-primary-package");
        let Invocation::Verify {
            args,
            options,
            inputs,
        } = selected_plan(
            &["driver", "/tool/bin/trustc", "source.rs"],
            &[
                (DRIVER_ARGS, &global),
                (&key, &local),
                ("CARGO_PRIMARY_PACKAGE", ""),
            ],
        )
        else {
            panic!("selected package did not use the verifier")
        };
        assert_eq!(
            &args[..4],
            &strings(&["source.rs", "--rlimit", "10", "--no-verify"])
        );
        assert!(options.compile);
        assert!(!args.iter().any(|arg| arg == "--VIA-CARGO"));
        assert_eq!(inputs.0["CARGO_PRIMARY_PACKAGE"].as_deref(), Some(""));
    }

    #[test]
    fn primary_and_dependency_compilation_are_independent() {
        let key = format!(
            "{DRIVER_ARGS_FOR}{}",
            package_id("example", "1.0.0", "/example/Cargo.toml")
        );
        let value = format!(
            "{DRIVER_ARGS_SEP}--VIA-CARGO{DRIVER_ARGS_SEP}compile-when-not-primary-package"
        );
        for (primary, compile) in [(false, true), (true, false)] {
            let mut extra = vec![(key.as_str(), value.as_str())];
            if primary {
                extra.push(("CARGO_PRIMARY_PACKAGE", "1"));
            }
            let Invocation::Verify { options, .. } =
                selected_plan(&["driver", "trustc", "source.rs"], &extra)
            else {
                panic!()
            };
            assert_eq!(options.compile, compile);
        }
    }

    #[test]
    fn probes_and_build_scripts_do_not_read_package_verification_options() {
        for (args, extra) in [
            (
                vec!["driver", "trustc", "--crate-name", "___", "--print", "cfg"],
                vec![],
            ),
            (
                vec!["driver", "trustc", "build.rs"],
                vec![("CARGO_CRATE_NAME", "build_script_build")],
            ),
        ] {
            let Invocation::Direct { inputs, .. } = selected_plan(&args, &extra) else {
                panic!()
            };
            assert!(!inputs.0.contains_key(DRIVER_ARGS));
            assert!(!inputs.0.contains_key("CARGO_PKG_NAME"));
        }
    }

    #[test]
    fn unrelated_dependencies_ignore_forwarded_verification_arguments() {
        let Invocation::Direct {
            args,
            inputs,
            bootstrap,
        } = plan(
            &["driver", "trustc", "--crate-name=proc_macro2", "source.rs"],
            &[
                (VIA_CARGO, "1"),
                (DRIVER_ARGS, "malformed unrelated options"),
            ],
        )
        .unwrap()
        else {
            panic!()
        };
        assert!(args.ends_with(&strings(&[
            "--cfg",
            "proc_macro_span",
            "--cfg",
            "span_locations"
        ])));
        assert!(!inputs.0.contains_key(DRIVER_ARGS));
        assert!(bootstrap);
        let Invocation::Direct {
            args, bootstrap, ..
        } = plan(
            &["driver", "trustc", "--crate-name", "ordinary", "source.rs"],
            &[(VIA_CARGO, "1")],
        )
        .unwrap()
        else {
            panic!()
        };
        assert!(!bootstrap);
        assert_eq!(args, strings(&["--crate-name", "ordinary", "source.rs"]));
    }

    #[test]
    fn builtin_package_flags_do_not_select_verification() {
        let id = package_id("builtin", "1", "/builtin/Cargo.toml");
        let key = format!("{IS_BUILTIN}{id}");
        let Invocation::Direct {
            args,
            inputs,
            bootstrap,
        } = plan(
            &["driver", "trustc", "source.rs"],
            &[
                (VIA_CARGO, "1"),
                ("CARGO_PKG_NAME", "builtin"),
                ("CARGO_PKG_VERSION", "1"),
                ("CARGO_MANIFEST_DIR", "/builtin"),
                (&key, "1"),
            ],
        )
        .unwrap()
        else {
            panic!()
        };
        assert!(args.ends_with(&strings(&[
            "--cfg",
            "verus_only",
            "--cfg",
            "verus_keep_ghost"
        ])));
        assert_eq!(inputs.0[&key].as_deref(), Some("1"));
        assert!(!inputs.0.contains_key(DRIVER_ARGS));
        assert!(bootstrap);
    }

    #[test]
    fn malformed_cargo_control_cannot_reach_rustc_or_be_silently_dropped() {
        for values in [
            vec!["--VIA-CARGO"],
            vec!["--VIA-CARGO", "unknown"],
            vec!["--VIA-CARGO", "import-dep-if-present="],
        ] {
            assert!(take_options(&mut strings(&values), true).is_err());
        }
    }

    #[test]
    fn self_import_absent_from_externs_does_not_invent_a_dependency() {
        let options = Options {
            compile: false,
            import_deps: ["own_lib".to_string()].into_iter().collect(),
        };
        assert!(imports(
            &strings(&["source.rs", "--extern", "other=/deps/libother.rlib"]),
            &options
        )
        .unwrap()
        .is_empty());
        assert!(imports(
            &strings(&["source.rs", "--extern", "own_lib=/absent/libown.rlib"]),
            &options
        )
        .is_err());
    }
}
