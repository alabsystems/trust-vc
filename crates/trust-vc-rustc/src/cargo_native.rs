//! Private frontend outputs after the linked compiler parsed the original CLI.
//!
//! Fields are bound to Trust 29ebb's rustc_session options/configuration. No
//! Trust authority control is changed: its embedded-frontend boundary already
//! rejects nondefault evidence sinks and deauthorizes official proof output.

use std::path::Path;

use rustc_interface::interface::Config;
use rustc_session::config::{Options, OutFileName, OutputType, OutputTypes, SwitchWithOptPath};

pub(crate) fn configure(config: &mut Config, directory: &Path) {
    // This producer uses RUST_DEP_GRAPH instead of a typed path. Supporting it
    // needs a separate process/environment port; accepting it here would let
    // speculative frontend work write outside its private directory.
    if config.opts.unstable_opts.dump_dep_graph {
        rustc_session::EarlyDiagCtxt::new(config.opts.error_format).early_fatal(
            crate::verdict::refusal_message("cargo-output", "private Cargo frontend passes do not yet support environment-named dependency-graph dumps"),
        );
    }

    config.output_dir = Some(directory.to_path_buf());
    config.output_file = None;
    config.ice_file = Some(directory.join("compiler-ice.txt"));
    configure_options(&mut config.opts, directory);
}

fn configure_options(options: &mut Options, directory: &Path) {
    options.incremental = None;
    // Type checking, const evaluation and borrow checking still run. LLVM and
    // the linker run only in the final, original requested compile, after
    // verification succeeds. A speculative metadata file is no final output.
    options.output_types = OutputTypes::new(&[
        (
            OutputType::Metadata,
            Some(OutFileName::Real(directory.join("check.rmeta"))),
        ),
        (
            OutputType::DepInfo,
            Some(OutFileName::Real(directory.join("check.d"))),
        ),
    ]);

    let options = &mut options.unstable_opts;
    options.dump_mir_dir = directory.join("mir").to_string_lossy().into_owned();
    options.nll_facts_dir = directory.join("nll").to_string_lossy().into_owned();
    for (path, name) in [
        (&mut options.metrics_dir, "metrics"),
        (&mut options.remark_dir, "remarks"),
        (&mut options.split_dwarf_out_dir, "dwarf"),
    ] {
        if path.is_some() {
            *path = Some(directory.join(name));
        }
    }
    if options.temps_dir.is_some() {
        options.temps_dir = Some(directory.to_string_lossy().into_owned());
    }
    if options.print_codegen_stats_json.is_some() {
        options.print_codegen_stats_json = Some(
            directory
                .join("codegen-stats.json")
                .to_string_lossy()
                .into_owned(),
        );
    }
    if options.self_profile.enabled() {
        options.self_profile = SwitchWithOptPath::Enabled(Some(directory.to_path_buf()));
    }
    if options.dump_mono_stats.enabled() {
        options.dump_mono_stats = SwitchWithOptPath::Enabled(Some(directory.to_path_buf()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_session::config::TrustFrontendAuthoritySnapshot;

    #[test]
    fn parsed_frontend_outputs_are_private_without_changing_trust_authority() {
        let mut options = Options::default();
        options.incremental = Some("/public/incremental".into());
        options.output_types = OutputTypes::new(&[(
            OutputType::Exe,
            Some(OutFileName::Real("/public/program".into())),
        )]);
        options.unstable_opts.metrics_dir = Some("/public/metrics".into());
        options.unstable_opts.remark_dir = Some("/public/remarks".into());
        options.unstable_opts.split_dwarf_out_dir = Some("/public/dwarf".into());
        options.unstable_opts.temps_dir = Some("/public/temps".to_string());
        options.unstable_opts.print_codegen_stats_json = Some("/public/stats".to_string());
        options.unstable_opts.self_profile =
            SwitchWithOptPath::Enabled(Some("/public/profile".into()));
        options.unstable_opts.dump_mono_stats = SwitchWithOptPath::Enabled(None);
        let authority = TrustFrontendAuthoritySnapshot::capture(&options);
        configure_options(&mut options, Path::new("/private"));
        assert!(authority.changed_option(&options).is_none());
        assert!(options.incremental.is_none());
        assert_eq!(options.output_types.len(), 2);
        assert!(options.output_types.contains_key(&OutputType::Metadata));
        assert!(options.output_types.contains_key(&OutputType::DepInfo));
        for (_, output) in options.output_types.iter() {
            assert!(
                matches!(output, Some(OutFileName::Real(path)) if path.starts_with("/private"))
            );
        }
        let unstable = &options.unstable_opts;
        assert!(Path::new(&unstable.dump_mir_dir).starts_with("/private"));
        assert!(Path::new(&unstable.nll_facts_dir).starts_with("/private"));
        for path in [
            &unstable.metrics_dir,
            &unstable.remark_dir,
            &unstable.split_dwarf_out_dir,
        ] {
            assert!(path.as_ref().unwrap().starts_with("/private"));
        }
        assert!(Path::new(unstable.temps_dir.as_ref().unwrap()).starts_with("/private"));
        assert!(
            Path::new(unstable.print_codegen_stats_json.as_ref().unwrap()).starts_with("/private")
        );
        assert!(
            matches!(&unstable.self_profile, SwitchWithOptPath::Enabled(Some(path)) if path.starts_with("/private"))
        );
        assert!(
            matches!(&unstable.dump_mono_stats, SwitchWithOptPath::Enabled(Some(path)) if path.starts_with("/private"))
        );
    }
}
