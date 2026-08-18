// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The one-word `trust-vc` command.
//!
//! This module is a FRONT END, not a verifier. It owns exactly three things:
//!
//!   1. a friendlier argv shape — `trust-vc <FILE.rs>` / `trust-vc <DIR>` with
//!      no subcommand, plus an `example` verb — which it translates into the
//!      argv [`crate::run_cargo_cli`] already understands (`check …`);
//!   2. `--version` / `--help` that answer with NOTHING installed (no sysroot,
//!      no solver, no network, no filesystem access);
//!   3. loud, actionable errors: an unsupported flag names itself and the flag
//!      to use instead, and a target that cannot hold Rust sources says so
//!      rather than reporting "0 functions found" and exiting 0.
//!
//! Everything past the translation is the existing pipeline: `scan` parses the
//! sources with `syn`, `trust_vc_core` extracts the verification conditions and
//! discharges them on the pure-Rust `ay` solver, in this process. No cargo, no
//! rustc, no sysroot, no external solver.

use clap::CommandFactory;
use std::path::Path;

/// The command's name in its own help, usage and error output — including
/// clap's, so a typo'd flag is answered with `Usage: trust-vc …` and not with
/// the cargo subcommand's spelling.
const ONE_WORD_NAME: &str = "trust-vc";

/// Short git head stamped in by `build.rs`, when it could read one.
const BUILD_GIT_HEAD: Option<&str> = option_env!("TVC_BUILD_GIT_HEAD");

/// Verbs handed to the cargo dispatch verbatim. Each already owns its own
/// `--help` and its own "install X first" diagnostics, so wrapping them would
/// only add a layer that can drift.
const FORWARDED_VERBS: &[&str] = &["new", "suggest", "evidence", "gate", "fuzz"];

/// Verbs that exist on the cargo subcommand but drive a CARGO BUILD of a
/// workspace. `trust-vc` deliberately does not: it is the command you can run
/// with no toolchain present, so it points at the cargo surface instead of
/// half-working.
const CARGO_ONLY_VERBS: &[&str] = &["build", "focus", "verus-compat"];

/// Flags that take a separate value, needed to tell a flag's value apart from
/// the positional target.
const VALUE_FLAGS: &[&str] = &["--function", "--filter", "--timeout", "--jobs", "-j"];

/// Flags this command REFUSES, each with the thing to use instead.
///
/// Two families, both fail-loud (never silently ignored):
///   * cargo/workspace selection — real features, but they belong to the cargo
///     subcommand, which is where a cargo-driven run should start;
///   * spellings a user arrives with from another Rust contract verifier —
///     mapped onto the flag that does the same job here.
const UNSUPPORTED_FLAGS: &[(&str, &str)] = &[
    // --- cargo / workspace selection -------------------------------------
    (
        "--manifest-path",
        "cargo-driven runs live on the cargo subcommand: `cargo trust-vc check --manifest-path <PATH>`",
    ),
    (
        "--package",
        "verify a package by path instead (`trust-vc <DIR>`), or use `cargo trust-vc check --package <NAME>`",
    ),
    (
        "-p",
        "verify a package by path instead (`trust-vc <DIR>`), or use `cargo trust-vc check -p <NAME>`",
    ),
    (
        "--workspace",
        "verify each crate by path, or use `cargo trust-vc check --workspace`",
    ),
    (
        "--exclude",
        "use `cargo trust-vc check --exclude <NAME>`; `trust-vc` selects by path",
    ),
    (
        "--features",
        "features are a build concept; `trust-vc` reads sources directly. Use `cargo trust-vc check --features <LIST>`",
    ),
    (
        "-F",
        "features are a build concept; `trust-vc` reads sources directly. Use `cargo trust-vc check -F <LIST>`",
    ),
    (
        "--all-features",
        "features are a build concept; `trust-vc` reads sources directly. Use `cargo trust-vc check --all-features`",
    ),
    (
        "--no-default-features",
        "features are a build concept; `trust-vc` reads sources directly. Use `cargo trust-vc check --no-default-features`",
    ),
    (
        "--target",
        "`trust-vc` does not compile, so there is no target to select",
    ),
    (
        "--target-dir",
        "`trust-vc` writes no build artifacts; `--emit-certificate` / `--emit-hints` write beside the sources",
    ),
    (
        "--config",
        "use `cargo trust-vc check --config <KEY=VALUE>` for cargo configuration",
    ),
    (
        "--release",
        "`trust-vc` does not compile, so there is no profile to pick",
    ),
    (
        "--offline",
        "`trust-vc` never touches the network, so this is already the case",
    ),
    (
        "--locked",
        "`trust-vc` resolves no dependencies, so there is no lockfile to honor",
    ),
    (
        "--frozen",
        "`trust-vc` resolves no dependencies, so there is no lockfile to honor",
    ),
    (
        "-Z",
        "cargo's unstable flags belong to the cargo subcommand: `cargo trust-vc check -Z <FLAG>`",
    ),
    (
        "--frontend",
        "front-end selection is part of the cargo-driven path: `cargo trust-vc check --frontend <NAME>`",
    ),
    (
        "--fwd-verus-args-to",
        "argument forwarding is part of the cargo-driven path: `cargo trust-vc check --fwd-verus-args-to <SELECTOR>`",
    ),
    // --- spellings from other Rust contract verifiers ---------------------
    ("--verify-function", "use `--function <NAME>`"),
    ("--verify-only-module", "use `--filter <PATTERN>`"),
    ("--verify-module", "use `--filter <PATTERN>`"),
    (
        "--rlimit",
        "use `--timeout <SECONDS>` — a per-function wall-clock budget",
    ),
    ("--num-threads", "use `-j <JOBS>`"),
    (
        "--solver",
        "obligations are discharged in-process on the built-in `ay` solver; there is no external solver to select",
    ),
    (
        "--smt-solver",
        "obligations are discharged in-process on the built-in `ay` solver; there is no external solver to select",
    ),
    (
        "--no-verify",
        "`trust-vc` only verifies — there is nothing to skip. Use `cargo build` to build",
    ),
    (
        "--compile",
        "`trust-vc` does not build code. Use `cargo build`, then `trust-vc <PATH>` to verify",
    ),
    (
        "--crate-type",
        "`trust-vc` does not build code. Use `cargo build`, then `trust-vc <PATH>` to verify",
    ),
    (
        "--expand-errors",
        "use `--localize` to surface the first failing proof step",
    ),
    ("--profile", "use `-v` (repeatable) for timing on stderr"),
    (
        "--record",
        "use `--emit-certificate` to write a machine-checkable proof certificate",
    ),
];

/// Run the one-word CLI. Returns the process exit code.
pub(crate) fn run(argv: &[String]) -> i32 {
    let program = argv.first().map_or("trust-vc", String::as_str).to_string();
    let args: Vec<String> = argv.iter().skip(1).cloned().collect();

    // Answered before anything touches the filesystem: `--help` and `--version`
    // must work on a machine with nothing installed.
    match args.first().map(String::as_str) {
        None | Some("help" | "-h" | "--help") => {
            print!("{}", help_text());
            return 0;
        }
        Some("version" | "-V" | "--version") => {
            println!("{}", version_line());
            return 0;
        }
        Some("example") => return run_example(&args[1..]),
        _ => {}
    }

    let verb = args[0].as_str();
    if FORWARDED_VERBS.contains(&verb) {
        let mut forwarded = Vec::with_capacity(args.len() + 1);
        forwarded.push(program);
        forwarded.extend(args.iter().cloned());
        crate::run_cli(&forwarded, Some(ONE_WORD_NAME));
        return 0;
    }
    if CARGO_ONLY_VERBS.contains(&verb) {
        eprintln!(
            "error: `{verb}` drives a cargo build of a workspace, which `trust-vc` does not do"
        );
        eprintln!("note: run it on the cargo subcommand instead: `cargo trust-vc {verb} …`");
        eprintln!(
            "note: `trust-vc <PATH>` verifies sources directly — no cargo, no rustc, no sysroot"
        );
        return 2;
    }

    // Everything else is the default verb: verify.
    let rest: &[String] = if matches!(verb, "verify" | "check") {
        &args[1..]
    } else {
        &args[..]
    };
    run_verify(&program, rest)
}

/// Translate verify arguments and hand them to the shared `check` dispatch.
fn run_verify(program: &str, args: &[String]) -> i32 {
    if args.iter().any(|arg| arg == "-h" || arg == "--help") {
        print_verify_help();
        return 0;
    }
    if args.iter().any(|arg| arg == "-V" || arg == "--version") {
        println!("{}", version_line());
        return 0;
    }
    if let Some(code) = reject_unsupported_flags(args) {
        return code;
    }
    // A flag we do not recognize at all is CLAP's to report — it names the flag
    // and suggests the nearest match. Validating the target first would answer a
    // typo'd flag with a confusing "no `src/` directory" instead, so the target
    // check runs only when every flag is one this command defines. Unrecognized
    // spellings of OUR flags (`-vv`, `-j4`) simply skip the check, which is the
    // safe direction: clap still parses them.
    if args
        .iter()
        .filter(|arg| arg.starts_with('-') && arg.as_str() != "--")
        .all(|arg| is_known_flag(arg.split('=').next().unwrap_or(arg)))
    {
        if let Err(code) = validate_target(positional_target(args).unwrap_or(".")) {
            return code;
        }
    }

    // `check` + the untouched tail: one parser, one flag set, one behavior for
    // both commands.
    let mut forwarded = Vec::with_capacity(args.len() + 2);
    forwarded.push(program.to_string());
    forwarded.push("check".to_string());
    forwarded.extend(args.iter().cloned());
    crate::run_cli(&forwarded, Some(ONE_WORD_NAME));
    0
}

/// `trust-vc example` — a sample that this tool verifies as-is.
fn run_example(rest: &[String]) -> i32 {
    match rest.first().map(String::as_str) {
        None => {
            print!("{}", example_source());
            0
        }
        Some("-h" | "--help") => {
            print!("{}", example_help());
            0
        }
        Some(other) => {
            eprintln!("error: `example` takes no arguments, but got `{other}`");
            eprintln!(
                "note: it prints the sample to stdout — redirect it: `trust-vc example > demo.rs`"
            );
            2
        }
    }
}

/// The sample source.
///
/// The body is the SAME text `trust-vc new --bin` scaffolds, so the promise
/// "this verifies" is carried by the scaffold's existing integration coverage
/// rather than by a second, untested copy of a contract.
fn example_source() -> String {
    let mut out = String::new();
    out.push_str("// Written by `trust-vc example`.\n");
    out.push_str("//\n");
    out.push_str("// Verify it:\n");
    out.push_str("//     trust-vc demo.rs\n");
    out.push_str("//\n");
    out.push_str("// Nothing else is needed — the contract below is read from this source and\n");
    out.push_str("// discharged on the built-in `ay` solver. No cargo, no rustc, no sysroot.\n");
    out.push_str("//\n");
    out.push_str("// Things to try:\n");
    out.push_str("//   * delete the `requires(...)` line — the proof fails and you get a\n");
    out.push_str("//     counterexample (`x = 4294967295`), because `x + 1` can overflow;\n");
    out.push_str("//   * `trust-vc demo.rs --json` for machine-readable results;\n");
    out.push_str("//   * `trust-vc new --bin myproj` for a full crate wired the same way.\n");
    out.push_str(crate::cargo_trust_vc_new_bin_template());
    out
}

fn example_help() -> String {
    let mut out = String::new();
    out.push_str("trust-vc example — print a tiny annotated program that verifies as-is\n\n");
    out.push_str("Usage:\n  trust-vc example > demo.rs\n  trust-vc demo.rs\n\n");
    out.push_str("The sample is written to stdout and takes no arguments.\n");
    out.push_str("It is the same source `trust-vc new --bin <NAME>` scaffolds.\n");
    out
}

/// `trust-vc --version`: version, and the build's git head when stamped.
fn version_line() -> String {
    match BUILD_GIT_HEAD.and_then(|head| head.get(..8)) {
        Some(head) if head != "unknown" => {
            format!("trust-vc {} ({head})", env!("CARGO_PKG_VERSION"))
        }
        _ => format!("trust-vc {}", env!("CARGO_PKG_VERSION")),
    }
}

/// Full option list for the verify path, rendered from the SAME clap definition
/// the parser uses, so it can never drift from the accepted flags.
fn print_verify_help() {
    let mut command = crate::CliArgs::command()
        .name(ONE_WORD_NAME)
        .bin_name(ONE_WORD_NAME);
    let mut stdout = std::io::stdout();
    let _ = command.write_long_help(&mut stdout);
    println!();
}

/// The first positional argument — the verification target — skipping flags and
/// the values they consume.
fn positional_target(args: &[String]) -> Option<&str> {
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        if arg == "--" {
            return args.get(index + 1).map(String::as_str);
        }
        if VALUE_FLAGS.contains(&arg) {
            index += 2;
            continue;
        }
        if arg.starts_with('-') {
            index += 1;
            continue;
        }
        return Some(arg);
    }
    None
}

/// Refuse an unsupported flag by NAME, with the alternative. Returns the exit
/// code when one is found; `None` when every flag is supported.
fn reject_unsupported_flags(args: &[String]) -> Option<i32> {
    for arg in args {
        if arg == "--" {
            break;
        }
        if !arg.starts_with('-') {
            continue;
        }
        let name = arg.split('=').next().unwrap_or(arg.as_str());
        let hit = UNSUPPORTED_FLAGS
            .iter()
            .find(|(flag, _)| name == *flag || is_bundled_short(name, flag));
        if let Some((flag, note)) = hit {
            eprintln!("error: unsupported flag `{flag}`");
            eprintln!("note: {note}");
            eprintln!("note: `trust-vc verify --help` lists every flag this command accepts");
            return Some(2);
        }
    }
    None
}

/// Whether `name` is a flag the shared check parser defines.
///
/// Read off the SAME clap definition the parser uses, so this cannot drift as
/// flags are added or renamed.
fn is_known_flag(name: &str) -> bool {
    crate::CliArgs::command().get_arguments().any(|arg| {
        if let Some(long) = name.strip_prefix("--") {
            return arg.get_long().is_some_and(|defined| long == defined);
        }
        match name.strip_prefix('-') {
            // A single short flag; `-vv` / `-j4` deliberately do not match.
            Some(short) if short.len() == 1 => arg
                .get_short()
                .is_some_and(|defined| short.starts_with(defined)),
            _ => false,
        }
    })
}

/// True for a short flag written with its value attached (`-pfoo` for `-p`).
fn is_bundled_short(name: &str, flag: &str) -> bool {
    flag.len() == 2 && !flag.starts_with("--") && name.len() > 2 && name.starts_with(flag)
}

/// Fail before verification when the target cannot hold Rust sources, so a
/// first run never ends in a silent "0 functions found".
fn validate_target(raw: &str) -> Result<(), i32> {
    let path = Path::new(raw);
    if !path.exists() {
        eprintln!("error: no such file or directory: {raw}");
        eprintln!("note: `trust-vc <FILE.rs>` verifies one file; `trust-vc <DIR>` verifies a crate through its `src/` tree");
        eprintln!("note: nothing needs installing first — try `trust-vc example > demo.rs && trust-vc demo.rs`");
        return Err(2);
    }
    if path.is_file() {
        if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
            eprintln!("error: not a Rust source file: {raw}");
            eprintln!(
                "note: pass a `.rs` file, or a directory whose `src/` tree holds the sources"
            );
            return Err(2);
        }
        return Ok(());
    }
    if !path.join("src").is_dir() {
        let shown = if raw == "." {
            "the current directory".to_string()
        } else {
            format!("`{raw}`")
        };
        eprintln!("error: nothing to verify in {shown}: it has no `src/` directory");
        eprintln!(
            "note: a crate directory is verified through `src/`; a single file is passed by name"
        );
        eprintln!("note: try `trust-vc example > demo.rs && trust-vc demo.rs`");
        return Err(2);
    }
    Ok(())
}

/// The top-level help. Pure string building — no filesystem, no subprocess.
fn help_text() -> String {
    let mut out = String::new();
    out.push_str(&version_line());
    out.push_str(" — deductive verifier for annotated Rust\n\n");
    out.push_str(
        "Annotate a function with `requires` / `ensures`; trust-vc extracts the proof\n\
         obligations and discharges them on the pure-Rust `ay` SMT solver, in this\n\
         process. No cargo, no rustc, no sysroot, no external solver, no network.\n\n\
         Verb and flag spellings are deliberately familiar to users of other Rust\n\
         contract verifiers. trust-vc is an ALab tool: not affiliated with, and not a\n\
         distribution of, any of them.\n\n",
    );
    out.push_str("Start here:\n");
    out.push_str("  trust-vc example > demo.rs && trust-vc demo.rs\n\n");
    out.push_str("Usage:\n");
    out.push_str(
        "  trust-vc [OPTIONS] <PATH>       Verify a .rs file, or a crate through its src/ tree\n",
    );
    out.push_str("  trust-vc <COMMAND> [ARGS]\n\n");
    out.push_str("Commands:\n");
    out.push_str(
        "  verify <PATH>   Verify a file or crate — the default, so the verb may be omitted\n",
    );
    out.push_str(
        "  example         Print a tiny annotated program that verifies as-is, to stdout\n",
    );
    out.push_str(
        "  new             Scaffold a crate wired for verification, --bin / --lib <NAME> (needs git)\n",
    );
    out.push_str("  suggest <FILE>  Suggest annotations for an unannotated function\n");
    out.push_str("  evidence        Generate replacement-parity evidence reports\n");
    out.push_str("  gate            Run the full local gate (needs cargo, rustfmt, clippy)\n");
    out.push_str("  fuzz            Run the libfuzzer targets (needs cargo-fuzz)\n\n");
    out.push_str("Common options (`trust-vc verify --help` lists all of them):\n");
    out.push_str("  --function <NAME>    Verify one function, by exact name\n");
    out.push_str("  --filter <PATTERN>   Verify functions whose name contains PATTERN\n");
    out.push_str("  --json               Machine-readable results on stdout\n");
    out.push_str("  --ci                 Deterministic output; non-zero exit on any failure\n");
    out.push_str("  --diff               Only functions in git-changed files\n");
    out.push_str("  --localize           Show the first failing proof step\n");
    out.push_str("  --no-cheating        Reject assume/admit/external_body before verifying\n");
    out.push_str("  --timeout <SECONDS>  Per-function wall-clock budget\n");
    out.push_str("  -j, --jobs <JOBS>    Parallel verification jobs\n");
    out.push_str("  --emit-certificate   Write .trust_vc/proof-certificate.json\n");
    out.push_str("  --watch              Re-verify on change\n");
    out.push_str("  -v                   More detail on stderr (repeatable)\n");
    out.push_str("  -V, --version        Print the version and exit\n\n");
    out.push_str("Exit codes:\n");
    out.push_str("  0  Everything verified (or nothing to verify)\n");
    out.push_str("  1  A failure, counterexample, or unknown\n");
    out.push_str("  2  CLI error\n\n");
    out.push_str(
        "Cargo-driven runs (--package, --manifest-path, --features, …) live on the cargo\n\
         subcommand: `cargo trust-vc check …`. A path that collides with a command name\n\
         still works: `trust-vc verify example`.\n",
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn help_and_version_need_nothing_installed() {
        // Both are pure string builders: no filesystem, no subprocess, no env
        // beyond the compiled-in version stamp.
        let help = help_text();
        assert!(help.contains("trust-vc example > demo.rs && trust-vc demo.rs"));
        assert!(help.contains("verify <PATH>"));
        assert!(help.contains("Exit codes:"));
        assert!(version_line().starts_with("trust-vc "));
    }

    #[test]
    fn example_source_carries_a_contract_and_a_verifiable_function() {
        let source = example_source();
        assert!(source.contains("trust_vc::contract"), "{source}");
        assert!(source.contains("requires("), "{source}");
        assert!(source.contains("ensures("), "{source}");
        // The sample is the scaffold's own template, not a second copy.
        assert!(
            source.contains(crate::cargo_trust_vc_new_bin_template()),
            "{source}"
        );
    }

    #[test]
    fn positional_target_skips_flags_and_their_values() {
        let args: Vec<String> = ["--function", "increment", "-j", "2", "demo.rs"]
            .iter()
            .map(|arg| (*arg).to_string())
            .collect();
        assert_eq!(positional_target(&args), Some("demo.rs"));

        let flags_only: Vec<String> = ["--json"].iter().map(|arg| (*arg).to_string()).collect();
        assert_eq!(positional_target(&flags_only), None);

        let after_sep: Vec<String> = ["--", "demo.rs"]
            .iter()
            .map(|arg| (*arg).to_string())
            .collect();
        assert_eq!(positional_target(&after_sep), Some("demo.rs"));
    }

    #[test]
    fn unsupported_flags_are_refused_not_ignored() {
        for flag in ["--rlimit", "--manifest-path", "--num-threads=4", "-pdemo"] {
            let args = vec![flag.to_string(), "demo.rs".to_string()];
            assert_eq!(
                reject_unsupported_flags(&args),
                Some(2),
                "`{flag}` must fail loudly"
            );
        }
    }

    #[test]
    fn supported_flags_are_not_refused() {
        let args: Vec<String> = [
            "--json",
            "--ci",
            "--diff",
            "--localize",
            "--no-cheating",
            "--emit-certificate",
            "--emit-hints=stdout",
            "--function",
            "increment",
            "--filter",
            "incr",
            "--timeout",
            "10",
            "-j",
            "2",
            "-vv",
            "--check",
            "demo.rs",
        ]
        .iter()
        .map(|arg| (*arg).to_string())
        .collect();
        assert_eq!(reject_unsupported_flags(&args), None);
    }

    #[test]
    fn every_unsupported_flag_names_an_alternative() {
        for (flag, note) in UNSUPPORTED_FLAGS {
            assert!(flag.starts_with('-'), "`{flag}` should be a flag");
            assert!(!note.is_empty(), "`{flag}` must say what to use instead");
        }
    }
}
