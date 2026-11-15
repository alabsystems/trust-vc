//! The `rust_verify` command line: Verus options versus rustc arguments.
//!
//! Upstream's test harness (`rust_verify_test/tests/common/mod.rs`, `run_verus`)
//! starts `target-verus/<profile>/rust_verify` with one argv that mixes Verus's
//! own options with ordinary rustc arguments. Verus separates them with
//! getopts' `parse_partial` over the option table in `rust_verify/src/config.rs`
//! (`parse_args_with_imports`), and hands whatever getopts did not match to
//! rustc.
//!
//! This module reproduces that split. Every Verus option is consumed and never
//! forwarded: rustc reads `-V` as `--version`, so a forwarded `-V new-mut-ref`
//! would make the compiler print its version and exit 0 having compiled
//! nothing, which the harness would score as a pass.

/// How many values a Verus option takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Arity {
    Flag,
    Value,
}

/// Long options from `rust_verify/src/config.rs`, with their getopts arity.
/// `optflag` options are `Flag`; `optopt` and `optmulti` options are `Value`.
const LONG_OPTIONS: &[(&str, Arity)] = &[
    ("version", Arity::Flag),
    ("export", Arity::Value),
    ("import", Arity::Value),
    ("verify-root", Arity::Flag),
    ("verify-module", Arity::Value),
    ("verify-only-module", Arity::Value),
    ("verify-function", Arity::Value),
    ("no-external-by-default", Arity::Flag),
    ("no-verify", Arity::Flag),
    ("no-lifetime", Arity::Flag),
    ("no-erasure-check", Arity::Flag),
    ("no-auto-recommends-check", Arity::Flag),
    ("no-cheating", Arity::Flag),
    ("time", Arity::Flag),
    ("time-expanded", Arity::Flag),
    ("output-json", Arity::Flag),
    ("rlimit", Arity::Value),
    ("smt-option", Arity::Value),
    ("multiple-errors", Arity::Value),
    ("no-vstd", Arity::Flag),
    ("is-vstd", Arity::Flag),
    ("is-core", Arity::Flag),
    ("is-stdlib-outside-of-core", Arity::Flag),
    ("expand-errors", Arity::Flag),
    ("log-dir", Arity::Value),
    ("log-all", Arity::Flag),
    ("log", Arity::Value),
    ("triggers", Arity::Flag),
    ("triggers-mode", Arity::Value),
    ("profile", Arity::Flag),
    ("profile-all", Arity::Flag),
    ("compile", Arity::Flag),
    ("record", Arity::Flag),
    ("num-threads", Arity::Value),
    ("trace", Arity::Flag),
    ("no-report-long-running", Arity::Flag),
    ("help", Arity::Flag),
];

/// One Verus option as it appeared on the command line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerusOption {
    /// The option name without dashes: `no-lifetime`, or `V` for `-V`.
    pub name: String,
    /// The option's value, for options that take one.
    pub value: Option<String>,
}

/// The harness argv, split.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SplitArgs {
    /// `argv[1]` was `--internal-test-mode` (the harness's build-test mode).
    pub internal_test_mode: bool,
    /// Verus options, in command-line order.
    pub verus: Vec<VerusOption>,
    /// Everything else, in order, without `argv[0]`. These go to rustc.
    pub rustc: Vec<String>,
}

impl SplitArgs {
    /// True when the Verus option `name` is present.
    pub fn has(&self, name: &str) -> bool {
        self.verus.iter().any(|o| o.name == name)
    }

    /// The value of the last occurrence of the Verus option `name`.
    pub fn value(&self, name: &str) -> Option<&str> {
        self.verus
            .iter()
            .rev()
            .find(|o| o.name == name)
            .and_then(|o| o.value.as_deref())
    }

    /// Values of every `-V` option (`new-mut-ref`, `no-solver-version-check`, ...).
    pub fn extended(&self) -> Vec<&str> {
        self.verus
            .iter()
            .filter(|o| o.name == "V")
            .filter_map(|o| o.value.as_deref())
            .collect()
    }

    /// The input file: the one rustc argument that names a `.rs` file and is
    /// not the value of a rustc option. The harness always passes exactly one.
    pub fn entry_file(&self) -> Option<&str> {
        let mut prev_takes_value = false;
        let mut found = None;
        for a in &self.rustc {
            if prev_takes_value {
                prev_takes_value = false;
                continue;
            }
            if rustc_option_takes_separate_value(a) {
                prev_takes_value = true;
                continue;
            }
            if !a.starts_with('-') && a.ends_with(".rs") {
                found = Some(a.as_str());
            }
        }
        found
    }

    /// The value of rustc's `-o` (the last one, as rustc takes it). The
    /// harness always passes `-o <test dir>/libtest_crate.rmeta` (or
    /// `libtest.rlib` with `--compile`), where the test dir is the one it
    /// made for this test.
    pub fn output_file(&self) -> Option<&str> {
        let mut found = None;
        let mut args = self.rustc.iter();
        while let Some(a) = args.next() {
            if a == "-o" {
                found = args.next().map(String::as_str);
            } else if let Some(v) = a.strip_prefix("-o").filter(|v| !v.is_empty()) {
                found = Some(v);
            } else if rustc_option_takes_separate_value(a) {
                args.next();
            }
        }
        found
    }
}

/// An argument error: a Verus option that is missing its value, or that has a
/// value it does not take.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgError(pub String);

impl std::fmt::Display for ArgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Split `args` (without `argv[0]`) into Verus options and rustc arguments.
pub fn split(args: &[String]) -> Result<SplitArgs, ArgError> {
    let mut out = SplitArgs::default();
    let mut rest = args;
    if rest.first().map(String::as_str) == Some("--internal-test-mode") {
        out.internal_test_mode = true;
        rest = &rest[1..];
    }

    let mut i = 0;
    while i < rest.len() {
        let a = &rest[i];

        // A rustc option whose value is the next argument: forward both, so a
        // value that happens to look like a Verus option is never consumed.
        if rustc_option_takes_separate_value(a) {
            out.rustc.push(a.clone());
            if let Some(v) = rest.get(i + 1) {
                out.rustc.push(v.clone());
            }
            i += 2;
            continue;
        }

        // `-V value` or `-Vvalue`.
        if a == "-V" {
            let v = rest
                .get(i + 1)
                .ok_or_else(|| ArgError("-V needs a value".to_string()))?;
            out.verus.push(VerusOption {
                name: "V".to_string(),
                value: Some(v.clone()),
            });
            i += 2;
            continue;
        }
        if let Some(v) = a.strip_prefix("-V") {
            out.verus.push(VerusOption {
                name: "V".to_string(),
                value: Some(v.to_string()),
            });
            i += 1;
            continue;
        }

        // `--name`, `--name value` or `--name=value`, for Verus's long options.
        if let Some(body) = a.strip_prefix("--") {
            let (name, inline) = match body.split_once('=') {
                Some((n, v)) => (n, Some(v.to_string())),
                None => (body, None),
            };
            if let Some(&(_, arity)) = LONG_OPTIONS.iter().find(|(n, _)| *n == name) {
                match (arity, inline) {
                    (Arity::Flag, None) => {
                        out.verus.push(VerusOption {
                            name: name.to_string(),
                            value: None,
                        });
                        i += 1;
                    }
                    (Arity::Flag, Some(_)) => {
                        return Err(ArgError(format!("option --{name} does not take a value")));
                    }
                    (Arity::Value, Some(v)) => {
                        out.verus.push(VerusOption {
                            name: name.to_string(),
                            value: Some(v),
                        });
                        i += 1;
                    }
                    (Arity::Value, None) => {
                        let v = rest
                            .get(i + 1)
                            .ok_or_else(|| ArgError(format!("option --{name} needs a value")))?;
                        out.verus.push(VerusOption {
                            name: name.to_string(),
                            value: Some(v.clone()),
                        });
                        i += 2;
                    }
                }
                continue;
            }
        }

        out.rustc.push(a.clone());
        i += 1;
    }
    Ok(out)
}

/// rustc options that take their value as the following argument. The list
/// covers what the harness and rust_verify pass, plus the other common ones.
fn rustc_option_takes_separate_value(a: &str) -> bool {
    matches!(
        a,
        "--crate-name"
            | "--crate-type"
            | "--extern"
            | "-L"
            | "-o"
            | "--out-dir"
            | "--cfg"
            | "--check-cfg"
            | "--edition"
            | "--emit"
            | "--error-format"
            | "--json"
            | "--target"
            | "--sysroot"
            | "--cap-lints"
            | "--print"
            | "-A"
            | "-W"
            | "-D"
            | "-F"
            | "-C"
            | "-Z"
            | "-l"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(args: &[&str]) -> Vec<String> {
        args.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn harness_argv_splits() {
        let args = v(&[
            "--internal-test-mode",
            "--expand-errors",
            "--multiple-errors",
            "2",
            "-V",
            "new-mut-ref",
            "--no-lifetime",
            "--crate-name",
            "test_crate",
            "--crate-type",
            "lib",
            "--extern",
            "verus_builtin=/x/libverus_builtin.rlib",
            "-L",
            "dependency=/x",
            "-Z",
            "write_long_types_to_disk=no",
            "-A",
            "non_snake_case",
            "-o",
            "/t/libtest_crate.rmeta",
            "--emit=metadata",
            "--error-format=json",
            "-V",
            "no-solver-version-check",
            "/t/test.rs",
            "--cfg",
            "verus_no_vstd",
        ]);
        let s = split(&args).unwrap();
        assert!(s.internal_test_mode);
        assert!(s.has("expand-errors"));
        assert!(s.has("no-lifetime"));
        assert_eq!(s.extended(), vec!["new-mut-ref", "no-solver-version-check"]);
        assert_eq!(
            s.verus
                .iter()
                .find(|o| o.name == "multiple-errors")
                .unwrap()
                .value
                .as_deref(),
            Some("2")
        );
        assert!(!s.rustc.iter().any(|a| a == "-V" || a == "new-mut-ref"));
        assert_eq!(s.entry_file(), Some("/t/test.rs"));
        assert_eq!(s.output_file(), Some("/t/libtest_crate.rmeta"));
        assert_eq!(s.rustc.first().map(String::as_str), Some("--crate-name"));
        assert_eq!(s.rustc.last().map(String::as_str), Some("verus_no_vstd"));
    }

    #[test]
    fn import_is_consumed_with_value() {
        let args = v(&[
            "--cfg",
            "vstd_todo",
            "--extern",
            "vstd=/x/libvstd.rlib",
            "--import",
            "vstd=/x/vstd.vir",
            "t.rs",
        ]);
        let s = split(&args).unwrap();
        assert_eq!(s.verus.len(), 1);
        assert_eq!(s.verus[0].name, "import");
        assert_eq!(s.verus[0].value.as_deref(), Some("vstd=/x/vstd.vir"));
        assert_eq!(
            s.rustc,
            v(&[
                "--cfg",
                "vstd_todo",
                "--extern",
                "vstd=/x/libvstd.rlib",
                "t.rs"
            ])
        );
    }

    #[test]
    fn glued_v_and_equals_forms() {
        let s = split(&v(&["-Vnew-mut-ref", "--rlimit=5", "a.rs"])).unwrap();
        assert_eq!(s.extended(), vec!["new-mut-ref"]);
        assert_eq!(s.verus[1].value.as_deref(), Some("5"));
        assert_eq!(s.rustc, v(&["a.rs"]));
    }

    #[test]
    fn missing_value_is_an_error() {
        assert!(split(&v(&["a.rs", "-V"])).is_err());
        assert!(split(&v(&["a.rs", "--multiple-errors"])).is_err());
        assert!(split(&v(&["--compile=1", "a.rs"])).is_err());
    }

    #[test]
    fn output_file_skips_option_values() {
        // examples.rs passes an entry outside the test dir; the test dir is
        // still the directory of `-o`.
        let s = split(&v(&[
            "--cfg",
            "-o",
            "-o",
            "/t/example-a/libtest_crate.rmeta",
            "../../examples/a.rs",
        ]))
        .unwrap();
        assert_eq!(s.output_file(), Some("/t/example-a/libtest_crate.rmeta"));
        assert_eq!(s.entry_file(), Some("../../examples/a.rs"));
        let glued = split(&v(&["-o/t/x/lib.rmeta", "a.rs"])).unwrap();
        assert_eq!(glued.output_file(), Some("/t/x/lib.rmeta"));
        assert_eq!(split(&v(&["a.rs"])).unwrap().output_file(), None);
    }

    #[test]
    fn rustc_values_are_not_taken_as_verus_options() {
        // A --cfg value spelled like a Verus flag stays with rustc.
        let s = split(&v(&["--cfg", "--compile", "a.rs"])).unwrap();
        assert!(s.verus.is_empty());
        assert_eq!(s.rustc, v(&["--cfg", "--compile", "a.rs"]));
    }
}
