// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Request operands compared with actual native facts, not an argv hash.

use super::*;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_session::config::{ErrorOutputType, OutputType};
use rustc_session::search_paths::PathKind;
use rustc_span::source_map::FilePathMapping;
use rustc_span::RealFileName;
use std::collections::BTreeMap;

mod untracked;

pub(in crate::reader::declaration_staging) struct NormalNativeRequest {
    crate_name: String,
    crate_type: String,
    edition: String,
    cfg: BTreeSet<(String, Option<String>)>,
    externs: BTreeMap<String, (PathBuf, bool)>,
    search: Vec<(PathKind, PathBuf)>,
    output: PathBuf,
    emit: OutputType,
    lints: Vec<(String, String)>,
    cap_lints: Option<String>,
    attrs: Vec<String>,
    unstable_options: bool,
    write_long_types: bool,
    working_dir: RealFileName,
    compiler_environment: Option<crate::compiler_environment::CompilerEnvironment>,
}

fn cfg_value(text: &str) -> Result<(String, Option<String>), String> {
    let (name, value) = match text.split_once('=') {
        Some((name, value)) => (
            name,
            Some(
                serde_json::from_str::<String>(value)
                    .map_err(|_| "this owned cfg string is not represented")?,
            ),
        ),
        None => (text, None),
    };
    if name.is_empty()
        || name.as_bytes()[0].is_ascii_digit()
        || !name.bytes().all(|b| b == b'_' || b.is_ascii_alphanumeric())
    {
        return Err("this owned cfg identifier is not represented".into());
    }
    Ok((name.to_string(), value))
}

fn value<'a>(args: &'a [String], at: usize, name: &str) -> Result<Option<&'a str>, String> {
    if args[at] == name {
        return args
            .get(at + 1)
            .map(|s| Some(s.as_str()))
            .ok_or_else(|| "incomplete normal native option".into());
    }
    Ok(args[at]
        .strip_prefix(name)
        .and_then(|s| s.strip_prefix('=')))
}

fn cfgs(args: &[String]) -> Result<BTreeSet<(String, Option<String>)>, String> {
    let mut out = BTreeSet::new();
    for at in 1..args.len() {
        if let Some(text) = value(args, at, "--cfg")? {
            out.insert(cfg_value(text)?);
        }
    }
    Ok(out)
}

impl NormalNativeRequest {
    pub(in crate::reader::declaration_staging) fn check_cfg(text: &str) -> Result<(), String> {
        cfg_value(text).map(|_| ())
    }

    pub(in crate::reader::declaration_staging) fn capture(args: &[String]) -> Result<Self, String> {
        let (mut name, mut kind, mut edition, mut output, mut emit) =
            (None, None, None, None, None);
        let mut externs = BTreeMap::new();
        let (mut search, mut lints, mut attrs) = (Vec::new(), Vec::new(), Vec::new());
        let (mut cap_lints, mut unstable_options, mut write_long_types) = (None, false, true);
        for at in 1..args.len() {
            for (flag, target) in [
                ("--crate-name", &mut name),
                ("--crate-type", &mut kind),
                ("--edition", &mut edition),
            ] {
                if let Some(text) = value(args, at, flag)? {
                    if target.replace(text.to_string()).is_some() {
                        return Err("ambiguous normal crate/edition request".into());
                    }
                }
            }
            let out = if args[at] == "-o" {
                args.get(at + 1).map(String::as_str)
            } else {
                args[at].strip_prefix("-o").filter(|s| !s.is_empty())
            };
            if let Some(text) = out {
                if output.replace(PathBuf::from(text)).is_some() {
                    return Err("ambiguous normal output request".into());
                }
            }
            if let Some(text) = value(args, at, "--emit")? {
                let requested = match text {
                    "metadata" => OutputType::Metadata,
                    "link" => OutputType::Exe,
                    _ => {
                        return Err(
                            "explicit or multiple native emit destinations are not represented"
                                .into(),
                        )
                    }
                };
                if emit.replace(requested).is_some() {
                    return Err("ambiguous normal emit request".into());
                }
            }
            if let Some(text) = value(args, at, "--extern")? {
                let (alias, file) = text
                    .split_once('=')
                    .ok_or("normal extern has no exact file")?;
                let force = alias.starts_with("force:");
                let alias = alias.strip_prefix("force:").unwrap_or(alias);
                if alias.is_empty()
                    || alias.contains(':')
                    || externs
                        .insert(alias.to_string(), (PathBuf::from(file), force))
                        .is_some()
                {
                    return Err("normal extern options/duplicates are not represented".into());
                }
            }
            let directory = if args[at] == "-L" {
                args.get(at + 1).map(String::as_str)
            } else {
                args[at].strip_prefix("-L").filter(|s| !s.is_empty())
            };
            if let Some(text) = directory {
                let (kind, path) = match text.strip_prefix("dependency=") {
                    Some(path) => (PathKind::Dependency, path),
                    None => (PathKind::All, text),
                };
                search.push((kind, PathBuf::from(path)));
            }
            for (short, long, level) in [
                ("-A", "--allow", "allow"),
                ("-W", "--warn", "warn"),
                ("-D", "--deny", "deny"),
                ("-F", "--forbid", "forbid"),
            ] {
                let text = if args[at] == short {
                    args.get(at + 1).map(String::as_str)
                } else {
                    args[at].strip_prefix(short).filter(|s| !s.is_empty())
                };
                let text = text.or(value(args, at, long)?);
                if let Some(text) = text {
                    lints.push((text.replace('-', "_"), level.to_string()));
                }
            }
            if let Some(text) = value(args, at, "--cap-lints")? {
                if cap_lints.replace(text.to_string()).is_some() {
                    return Err("ambiguous native lint cap".into());
                }
            }
            let unstable = if args[at] == "-Z" {
                args.get(at + 1).map(String::as_str)
            } else {
                args[at].strip_prefix("-Z").filter(|s| !s.is_empty())
            };
            if let Some(text) = unstable {
                if let Some(attr) = text.strip_prefix("crate-attr=") {
                    attrs.push(attr.to_string());
                }
                if text == "unstable-options" {
                    unstable_options = true;
                }
                if text == "write_long_types_to_disk=no" {
                    write_long_types = false;
                }
            }
        }
        let crate_type = match kind
            .ok_or("normal request needs an explicit crate type")?
            .as_str()
        {
            "lib" | "rlib" => "rlib".to_string(),
            _ => {
                return Err(
                    "this owned native recipe only represents its library metadata crate type"
                        .into(),
                )
            }
        };
        Ok(Self {
            crate_name: name.ok_or("normal request needs an explicit crate name")?,
            crate_type,
            edition: edition.ok_or("normal request needs an explicit edition")?,
            cfg: cfgs(args)?,
            externs,
            search,
            output: output.ok_or("normal request needs one output")?,
            emit: emit.unwrap_or(OutputType::Exe),
            lints,
            cap_lints,
            attrs,
            unstable_options,
            write_long_types,
            working_dir: working_directory(
                &std::env::current_dir()
                    .and_then(|path| path.canonicalize())
                    .map_err(|error| {
                        format!("cannot bind the actual request working directory: {error}")
                    })?,
            ),
            compiler_environment: None,
        })
    }

    pub(in crate::reader::declaration_staging) fn bind_compiler_environment(
        &mut self,
        environment: crate::compiler_environment::CompilerEnvironment,
    ) {
        self.compiler_environment = Some(environment);
    }

    fn check_working_dir(&self, actual: &RealFileName) -> Result<(), String> {
        if actual != &self.working_dir {
            return Err(
                "the actual native working directory differs from its captured request".into(),
            );
        }
        Ok(())
    }
}

fn working_directory(path: &std::path::Path) -> RealFileName {
    FilePathMapping::empty().to_real_filename(&RealFileName::empty(), path)
}

impl Invocation {
    pub(in crate::reader::declaration_staging) fn check_normal_client(
        &self,
        tcx: TyCtxt<'_>,
        request: &NormalNativeRequest,
    ) -> Result<(), String> {
        let actual = Self::capture_client(tcx, &[])?;
        if !actual.same_target(self)
            || tcx.crate_name(LOCAL_CRATE).as_str() != request.crate_name
            || tcx
                .crate_types()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                != vec![request.crate_type.clone()]
            || tcx.sess.opts.edition.as_str() != request.edition
        {
            return Err(
                "the actual normal crate/edition/target/sysroot differs from its plan".into(),
            );
        }
        // Use the genuine producer's observed automatic configuration as the
        // baseline. Different native configurations are unsupported, not
        // silently synthesized from the current client's own actual cfg.
        let producer_explicit = cfgs(&self.argv)?;
        if !producer_explicit.is_subset(&self.cfg) {
            return Err("the native producer cfg baseline is unavailable".into());
        }
        let mut expected_cfg = self
            .cfg
            .difference(&producer_explicit)
            .cloned()
            .collect::<BTreeSet<_>>();
        expected_cfg.extend(request.cfg.iter().cloned());
        if actual.cfg != expected_cfg {
            return Err(
                "the actual normal effective cfg differs from the represented native plan".into(),
            );
        }
        let search = tcx
            .sess
            .opts
            .search_paths
            .iter()
            .map(|s| (s.kind, s.dir.as_ref().to_path_buf()))
            .collect::<Vec<_>>();
        if search != request.search {
            return Err("the actual normal search selection differs from its plan".into());
        }
        let mut externs = BTreeMap::new();
        for (alias, entry) in tcx.sess.opts.externs.iter() {
            let files = entry
                .files()
                .ok_or("a normal extern uses an unrepresented native search lookup")?
                .collect::<Vec<_>>();
            if files.len() != 1 || entry.is_private_dep || !entry.add_prelude || entry.nounused_dep
            {
                return Err("the actual normal extern flags/files differ from its plan".into());
            }
            externs.insert(alias.clone(), (files[0].original().clone(), entry.force));
        }
        if externs != request.externs {
            return Err("the actual normal extern selection differs from its plan".into());
        }
        if tcx.sess.io.output_dir.is_some()
            || tcx.sess.io.output_file.as_ref().map(|p| p.as_path())
                != Some(request.output.as_path())
            || tcx.sess.opts.output_types.len() != 1
            || !tcx
                .sess
                .opts
                .output_types
                .keys()
                .any(|kind| *kind == request.emit)
            || tcx.sess.opts.output_types.values().any(Option::is_some)
        {
            return Err("the actual normal output selection differs from its plan".into());
        }
        let lints = tcx
            .sess
            .opts
            .lint_opts
            .iter()
            .map(|(name, level)| (name.clone(), level.as_str().to_string()))
            .collect::<Vec<_>>();
        if lints != request.lints
            || tcx
                .sess
                .opts
                .lint_cap
                .map(|level| level.as_str().to_string())
                != request.cap_lints
            || tcx.sess.opts.error_format
                != (ErrorOutputType::Json {
                    pretty: false,
                    json_rendered: rustc_errors::emitter::HumanReadableErrorType {
                        short: false,
                        unicode: false,
                    },
                    color_config: rustc_errors::ColorConfig::Never,
                })
            || tcx.sess.opts.unstable_opts.crate_attr != request.attrs
            || tcx.sess.opts.unstable_opts.unstable_options != request.unstable_options
            || tcx.sess.opts.unstable_opts.write_long_types_to_disk != request.write_long_types
        {
            return Err(
                "the actual normal diagnostic/attribute options differ from its plan".into(),
            );
        }
        // Dependency tracking deliberately omits native semantic and output
        // selectors. Account for every untracked field with typed native facts
        // before using the existing tracking comparison as a supplementary check.
        untracked::check(&self.options, &tcx.sess.opts)?;
        // A coordinator executes each original request in that request's cwd.
        // Bind the actual native SourceMap path before accounting for this
        // represented dimension in the producer's tracking baseline. Remapped
        // paths and a post-capture cwd change are not silently normalized.
        request.check_working_dir(tcx.sess.source_map().working_dir())?;
        if let Some(environment) = &request.compiler_environment {
            environment
                .check_options(&tcx.sess.opts)
                .map_err(|error| error.to_string())?;
        }
        // Retain the existing Invocation native tracking comparison for all
        // other tracked options. Normalize only the request dimensions just
        // compared independently above; this is never an argv-equality hash
        // or an imported proof/success fact. Unknown native configurations
        // conservatively refuse this owner recipe.
        let mut baseline = self.options.clone();
        baseline.crate_name = Some(request.crate_name.clone());
        baseline.edition = tcx.sess.opts.edition;
        baseline.output_types = tcx.sess.opts.output_types.clone();
        baseline.lint_opts = tcx.sess.opts.lint_opts.clone();
        baseline.lint_cap = tcx.sess.opts.lint_cap;
        baseline.unstable_opts.crate_attr = tcx.sess.opts.unstable_opts.crate_attr.clone();
        baseline.unstable_opts.unstable_options = request.unstable_options;
        baseline.unstable_opts.write_long_types_to_disk = request.write_long_types;
        baseline.working_dir = request.working_dir.clone();
        if request.compiler_environment.is_some() {
            // The exact map, including missing keys, was independently bound
            // above. Every other tracked dimension retains its comparison.
            baseline.logical_env = tcx.sess.opts.logical_env.clone();
        }
        if baseline.dep_tracking_hash(false) != tcx.sess.opts.dep_tracking_hash(false) {
            return Err(
                "the remaining actual native options are outside this represented owner recipe"
                    .into(),
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod working_directory_tests {
    use super::*;

    #[test]
    fn cwd_binding_keeps_wrong_directories_and_other_tracked_options_refused() {
        let request = NormalNativeRequest::capture(&[
            "actual-request".into(),
            "--crate-name=original".into(),
            "--crate-type=lib".into(),
            "--edition=2021".into(),
            "-o".into(),
            "original.rmeta".into(),
        ])
        .unwrap();
        let native = Options::default();
        assert!(request.check_working_dir(&native.working_dir).is_ok());
        let mut changed = native.clone();
        changed.working_dir = working_directory(
            &std::env::current_dir()
                .unwrap()
                .join("different-native-cwd"),
        );
        assert!(request.check_working_dir(&changed.working_dir).is_err());
        assert!(request
            .check_working_dir(&RealFileName::from_virtual_path(
                request.working_dir.local_path().unwrap()
            ))
            .is_err());
        assert_ne!(
            native.dep_tracking_hash(false),
            changed.dep_tracking_hash(false)
        );
        changed.working_dir = request.working_dir.clone();
        assert_eq!(
            native.dep_tracking_hash(false),
            changed.dep_tracking_hash(false)
        );
        changed.test = !native.test;
        assert_ne!(
            native.dep_tracking_hash(false),
            changed.dep_tracking_hash(false)
        );
    }
}
