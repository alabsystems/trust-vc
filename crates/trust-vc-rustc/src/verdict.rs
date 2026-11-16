//! Verdict records and refusal diagnostics.
//!
//! Every `rust_verify` run writes one verdict record: a single JSON line that
//! names every function it saw and what it concluded about each. The harness
//! only sees diagnostics and an exit code, so the record is what lets the
//! runner tell a real pass from a harness pass over code trust-vc never
//! checked.
//!
//! The record is appended to two places:
//!   * `trust-vc-verdict.jsonl` in the test directory (the harness deletes
//!     that directory when a test passes, so this copy is for failures);
//!   * `$TRUST_VC_VERDICT_DIR/<test dir name>.jsonl`, when that variable is
//!     set, so the runner can join records to libtest results.
//!
//! The test directory is the directory of rustc's `-o` output, which the
//! harness makes for each test: `<test binary>-<test name>` for the
//! `test_verify_one_file!` cases, `example-<file stem>` for examples.rs. The
//! entry file's directory is used only when there is no `-o`. examples.rs
//! passes an entry file inside the Verus checkout, and nothing is ever
//! written there.
//!
//! A refusal is an error diagnostic whose message starts with
//! `trust-vc refused: <tag>`, where `<tag>` is a lowercase word with dashes.
//! Any test that carries one counts as refused, whatever the harness says.
//!
//! Each function gets one [`Verdict`]; the run as a whole gets one
//! [`Outcome`]. Only `refused` and `skipped` functions mean "trust-vc did not
//! do the work"; `rejected` means the program was refused by the compiler or
//! by a Verus rule that the reader checked, which is also Verus's outcome for
//! it, so no verification claim is made or needed.

use std::io::Write;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

/// Schema name written into every record.
pub const SCHEMA: &str = "trust-vc.verdict@1";

/// Prefix of every refusal message.
pub const REFUSAL_PREFIX: &str = "trust-vc refused: ";

/// Environment variable naming the directory that collects records.
pub const VERDICT_DIR_ENV: &str = "TRUST_VC_VERDICT_DIR";

/// Output destinations for one invocation. These paths carry no verification,
/// import, compiler or resource permission.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OutputSinks {
    verdict_dir: Option<PathBuf>,
    dump_vcir: Option<PathBuf>,
    request_cwd: Option<PathBuf>,
}

impl OutputSinks {
    /// Output paths for an ordinary invocation in the current directory.
    /// The caller captures its environment; this constructor never reads it.
    pub fn new(verdict_dir: Option<PathBuf>, dump_vcir: Option<PathBuf>) -> Self {
        Self {
            verdict_dir,
            dump_vcir,
            request_cwd: None,
        }
    }

    /// Interpret a request's output paths in its original working directory,
    /// without changing the coordinator's working directory or environment.
    /// Absolute paths remain absolute; relative paths retain their lexical
    /// components beneath `cwd`. No filesystem or source permission is granted.
    pub fn for_request(
        cwd: &Path,
        verdict_dir: Option<PathBuf>,
        dump_vcir: Option<PathBuf>,
    ) -> std::io::Result<Self> {
        if !cwd.is_absolute() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "the request output directory must be absolute",
            ));
        }
        Ok(Self {
            verdict_dir: verdict_dir.map(|path| cwd.join(path)),
            dump_vcir: dump_vcir.map(|path| cwd.join(path)),
            request_cwd: Some(cwd.to_path_buf()),
        })
    }

    pub(crate) fn wants_vcir_dump(&self) -> bool {
        self.dump_vcir.is_some()
    }

    fn local_verdict_path(&self, directory: &Path) -> PathBuf {
        let directory = match &self.request_cwd {
            Some(cwd) => cwd.join(directory),
            None => directory.to_path_buf(),
        };
        directory.join("trust-vc-verdict.jsonl")
    }

    /// Write only the requested debug output. Failure loses the dump and does
    /// not change a verification result.
    pub(crate) fn write_vcir(&self, text: &str) -> std::io::Result<()> {
        match &self.dump_vcir {
            Some(path) => std::fs::write(path, text),
            None => Ok(()),
        }
    }
}

/// Build the message of a refusal diagnostic.
pub fn refusal_message(tag: &str, detail: &str) -> String {
    if detail.is_empty() {
        format!("{REFUSAL_PREFIX}{tag}")
    } else {
        format!("{REFUSAL_PREFIX}{tag}: {detail}")
    }
}

/// The tag of a refusal message, or `None` when `message` is not a refusal.
pub fn refusal_tag(message: &str) -> Option<&str> {
    let rest = message.strip_prefix(REFUSAL_PREFIX)?;
    // The tag is the first run of tag characters. `split` yields it as a
    // subslice, so no byte index is computed here and no slice bound can be
    // out of range or off a char boundary (the earlier `&rest[..end]` was a
    // bounds check the verifier could not discharge across the `find` call).
    let tag = rest
        .split(|c: char| !(c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-'))
        .next()?;
    (!tag.is_empty()).then_some(tag)
}

/// A refusal that has no source span, rendered as one line of rustc's JSON
/// diagnostic format. Used when the compiler stopped before any function could
/// be looked at (a fatal parse error, an internal error).
pub fn crate_refusal_json(tag: &str, detail: &str) -> String {
    let message = refusal_message(tag, detail);
    json!({
        "$message_type": "diagnostic",
        "message": message,
        "code": null,
        "level": "error",
        "spans": [],
        "children": [],
        "rendered": format!("error: {message}\n\n"),
    })
    .to_string()
}

/// What happened to one function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// Every site was proved.
    Verified,
    /// Some site was not proved; the failures were reported.
    Failed,
    /// trust-vc could not read or check the function; a refusal was reported.
    Refused,
    /// The function was not checked because an option asked for that
    /// (`--no-verify`). Counts as a refusal.
    Skipped,
    /// The crate was rejected (by rustc, or by a Verus rule the reader
    /// checks) before verification, as Verus would reject it.
    Rejected,
    /// Not a Verus item (outside `verus!`), so neither Verus nor trust-vc
    /// verifies it.
    External,
    /// `#[verifier::external_body]`: the body is not checked (by Verus
    /// either) and callers trust the contract.
    Trusted,
    /// A trait method declaration without a body: nothing to check. Its
    /// `requires` are checked at every call and its `ensures` in every
    /// implementation, whose verdicts say how that went.
    Declared,
}

impl Verdict {
    /// The name written into the record.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
            Self::Refused => "refused",
            Self::Skipped => "skipped",
            Self::Rejected => "rejected",
            Self::External => "external",
            Self::Trusted => "trusted",
            Self::Declared => "declared",
        }
    }

    /// True when trust-vc did not do the work it was asked for.
    #[must_use]
    pub const fn is_refusal(self) -> bool {
        matches!(self, Self::Refused | Self::Skipped)
    }
}

/// How a whole run ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// rustc reported errors before the reader ran (parse, expansion, name
    /// resolution, type checking).
    FrontEndRejected,
    /// A Verus rule or native ownership check rejected the program before
    /// verification.
    VerusRejected,
    /// The erase run (rustc with ghost code erased, through borrow checking)
    /// reported errors.
    EraseRejected,
    /// Something was refused.
    Refused,
    /// Every function was read and checked, and some check failed; the
    /// failures were reported as Verus errors.
    VerificationFailed,
    /// Every function was read and checked, and every check was proved.
    Checked,
    /// Cargo explicitly requested --no-verify. Its compiler work succeeded,
    /// but no verification result is claimed and functions remain skipped.
    VerificationSkipped,
}

impl Outcome {
    /// The name written into the record.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FrontEndRejected => "front-end-rejected",
            Self::VerusRejected => "verus-rejected",
            Self::EraseRejected => "erase-rejected",
            Self::Refused => "refused",
            Self::VerificationFailed => "verification-failed",
            Self::Checked => "checked",
            Self::VerificationSkipped => "verification-skipped",
        }
    }
}

/// One function's line in the record.
#[derive(Clone, Debug)]
pub struct FnVerdict {
    /// `tcx.def_path_str` of the function.
    pub def_path: String,
    /// rustc's `DefKind`, as text.
    pub kind: String,
    /// What happened to it.
    pub verdict: Verdict,
    /// The refusal tag, for refused and skipped functions.
    pub tag: Option<String>,
    /// Where the whole item is: file and first and last line (1-based).
    /// The runner uses it to match the reference run's errors to
    /// functions.
    pub lines: Option<(String, usize, usize)>,
    /// Checked sites: how many were proved and how many failed, when the
    /// function was verified.
    pub sites: Option<SiteCounts>,
}

/// Per-function site counts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SiteCounts {
    /// Sites proved.
    pub proved: usize,
    /// Sites refuted (reported as Verus errors, or not reported because
    /// Verus would stop at `--multiple-errors`).
    pub failed: usize,
}

/// One run's record.
#[derive(Clone, Debug, Default)]
pub struct Record {
    pub entry_file: Option<PathBuf>,
    /// rustc's `-o` output file; its directory is the test directory.
    pub output_file: Option<PathBuf>,
    pub argv: Vec<String>,
    pub verus_options: Vec<(String, Option<String>)>,
    pub functions: Vec<FnVerdict>,
    /// Every refusal message printed. A function's own refusal is also
    /// recorded on the function.
    pub crate_refusals: Vec<String>,
    /// How the run ended, once known.
    pub outcome: Option<Outcome>,
    /// Exit status of the erase run, when it ran.
    pub erase_exit: Option<i32>,
    pub exit_code: Option<i32>,
}

impl Record {
    /// True when anything in this run was refused.
    pub fn any_refused(&self) -> bool {
        self.outcome == Some(Outcome::VerificationSkipped)
            || !self.crate_refusals.is_empty()
            || self.functions.iter().any(|f| f.verdict.is_refusal())
    }

    pub fn to_json(&self) -> Value {
        json!({
            "schema": SCHEMA,
            "compiler_commit": env!("VC_SHIM_COMPILER_COMMIT"),
            "entry_file": self.entry_file.as_ref().map(|p| p.display().to_string()),
            "output_file": self.output_file.as_ref().map(|p| p.display().to_string()),
            "test_dir": self.test_dir_name(),
            "argv": self.argv,
            "verus_options": self.verus_options.iter().map(|(n, v)| json!({"name": n, "value": v})).collect::<Vec<_>>(),
            "functions": self.functions.iter().map(|f| json!({
                "def_path": f.def_path,
                "kind": f.kind,
                "verdict": f.verdict.as_str(),
                "tag": f.tag,
                "file": f.lines.as_ref().map(|(file, _, _)| file),
                "lines": f.lines.as_ref().map(|(_, lo, hi)| [lo, hi]),
                "sites_proved": f.sites.map(|s| s.proved),
                "sites_failed": f.sites.map(|s| s.failed),
            })).collect::<Vec<_>>(),
            "crate_refusals": self.crate_refusals,
            "outcome": self.outcome.map(Outcome::as_str),
            "erase_exit": self.erase_exit,
            "refused": self.any_refused(),
            "exit_code": self.exit_code,
        })
    }

    /// The test directory: the directory of the `-o` output, else the
    /// directory of the entry file.
    pub fn test_dir(&self) -> Option<&Path> {
        self.output_file
            .as_ref()
            .or(self.entry_file.as_ref())
            .and_then(|p| p.parent())
    }

    /// Name of the test directory (`<binary>-<test>` under the harness).
    pub fn test_dir_name(&self) -> Option<String> {
        self.test_dir()
            .and_then(Path::file_name)
            .map(|n| n.to_string_lossy().into_owned())
    }

    /// Append this record to its two destinations, and return the ones that
    /// could not be written. A write failure does not change the exit code:
    /// the runner treats a harness pass without a record as a false pass, so a
    /// lost record can only lower the score.
    pub fn write_to(&self, outputs: &OutputSinks) -> Vec<String> {
        // One write call per record: tests run concurrently and two of them
        // can share a file (examples with the same file stem), and an
        // O_APPEND write of the whole line keeps lines from interleaving.
        let line = format!("{}\n", self.to_json());
        let mut problems = Vec::new();
        let mut targets = Vec::new();
        if let Some(dir) = self.output_file.as_ref().and_then(|p| p.parent()) {
            targets.push(outputs.local_verdict_path(dir));
        }
        if let (Some(dir), Some(name)) = (&outputs.verdict_dir, self.test_dir_name()) {
            if let Err(e) = std::fs::create_dir_all(dir) {
                problems.push(format!("{}: {e}", dir.display()));
            }
            targets.push(dir.join(format!("{name}.jsonl")));
        }
        for t in targets {
            let res = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&t)
                .and_then(|mut f| f.write_all(line.as_bytes()));
            if let Err(e) = res {
                problems.push(format!("{}: {e}", t.display()));
            }
        }
        problems
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tags_parse() {
        assert_eq!(
            refusal_tag("trust-vc refused: no-engine: fn `f`"),
            Some("no-engine")
        );
        assert_eq!(
            refusal_tag("trust-vc refused: no-engine"),
            Some("no-engine")
        );
        assert_eq!(refusal_tag("trust-vc refused: "), None);
        assert_eq!(refusal_tag("assertion failed"), None);
        assert_eq!(
            refusal_tag(&refusal_message("parse-error", "")),
            Some("parse-error")
        );
    }

    /// Pins the boundaries of the tag scan rewritten from `find` + slice to
    /// `split`: the tag ends at the first non-tag char, wherever and however
    /// wide that char is, and an empty run is no tag.
    #[test]
    fn tag_boundaries_after_split_rewrite() {
        // Multi-byte char right after the tag: tag ends before it.
        assert_eq!(
            refusal_tag("trust-vc refused: no-engine\u{e9}x"),
            Some("no-engine")
        );
        // Multi-byte char first: no tag.
        assert_eq!(refusal_tag("trust-vc refused: \u{e9}no-engine"), None);
        // Uppercase and space end the tag; digits and dashes do not.
        assert_eq!(refusal_tag("trust-vc refused: abc-12Def"), Some("abc-12"));
        assert_eq!(refusal_tag("trust-vc refused: x y"), Some("x"));
        assert_eq!(refusal_tag("trust-vc refused: Upper"), None);
        // Prefix must match exactly.
        assert_eq!(refusal_tag("trust-vc refused:no-engine"), None);
        // The tag may run to the end of the message.
        assert_eq!(refusal_tag("trust-vc refused: -"), Some("-"));
    }

    #[test]
    fn crate_refusal_is_harness_json() {
        let line = crate_refusal_json("internal-error", "boom");
        let v: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(v["level"], "error");
        assert!(v["spans"].as_array().unwrap().is_empty());
        assert_eq!(
            refusal_tag(v["message"].as_str().unwrap()),
            Some("internal-error")
        );
        assert!(v["rendered"].is_string());
        assert!(!line.contains('\n'));
    }

    #[test]
    fn record_knows_its_test_dir() {
        let r = Record {
            entry_file: Some(PathBuf::from("/s/test_inputs/basic-test1/test.rs")),
            ..Record::default()
        };
        assert_eq!(r.test_dir_name().as_deref(), Some("basic-test1"));
        assert!(!r.any_refused());
    }

    #[test]
    fn test_dir_is_the_output_dir_when_there_is_one() {
        // examples.rs: the entry is the example in the Verus checkout, the
        // output goes to the test dir the harness made.
        let r = Record {
            entry_file: Some(PathBuf::from("../../examples/guide/integers.rs")),
            output_file: Some(PathBuf::from(
                "/s/test_inputs/example-integers/libtest_crate.rmeta",
            )),
            ..Record::default()
        };
        assert_eq!(r.test_dir_name().as_deref(), Some("example-integers"));
        assert_eq!(
            r.test_dir(),
            Some(Path::new("/s/test_inputs/example-integers"))
        );
        assert_eq!(
            r.to_json()["output_file"],
            "/s/test_inputs/example-integers/libtest_crate.rmeta"
        );
    }

    #[test]
    fn records_are_written_whole_and_never_beside_the_entry() {
        let tmp = std::env::temp_dir().join(format!("trust-vc-verdict-{}", std::process::id()));
        let entry_dir = tmp.join("examples");
        let test_dir = tmp.join("test_inputs/example-a");
        std::fs::create_dir_all(&entry_dir).unwrap();
        std::fs::create_dir_all(&test_dir).unwrap();
        let r = Record {
            entry_file: Some(entry_dir.join("a.rs")),
            output_file: Some(test_dir.join("libtest_crate.rmeta")),
            ..Record::default()
        };
        assert!(r.write_to(&OutputSinks::default()).is_empty());
        assert!(r.write_to(&OutputSinks::default()).is_empty());
        assert!(!entry_dir.join("trust-vc-verdict.jsonl").exists());
        let text = std::fs::read_to_string(test_dir.join("trust-vc-verdict.jsonl")).unwrap();
        assert_eq!(text.lines().count(), 2);
        for line in text.lines() {
            let v: Value = serde_json::from_str(line).unwrap();
            assert_eq!(v["test_dir"], "example-a");
        }
        std::fs::remove_dir_all(&tmp).unwrap();
    }

    #[test]
    fn only_refused_and_skipped_functions_are_refusals() {
        let f = |verdict| FnVerdict {
            def_path: "f".to_string(),
            kind: "Fn".to_string(),
            verdict,
            tag: None,
            lines: None,
            sites: None,
        };
        for (verdict, refusal) in [
            (Verdict::Verified, false),
            (Verdict::Failed, false),
            (Verdict::Rejected, false),
            (Verdict::External, false),
            (Verdict::Trusted, false),
            (Verdict::Declared, false),
            (Verdict::Refused, true),
            (Verdict::Skipped, true),
        ] {
            let r = Record {
                functions: vec![f(verdict)],
                ..Record::default()
            };
            assert_eq!(r.any_refused(), refusal, "{verdict:?}");
            let json = r.to_json();
            assert_eq!(json["functions"][0]["verdict"], verdict.as_str());
        }
    }

    #[test]
    fn successful_cargo_skip_remains_non_verification_evidence() {
        let record = Record {
            outcome: Some(Outcome::VerificationSkipped),
            exit_code: Some(0),
            functions: vec![FnVerdict {
                def_path: "p".to_string(),
                kind: "Fn".to_string(),
                verdict: Verdict::Skipped,
                tag: Some("no-verify".to_string()),
                lines: None,
                sites: None,
            }],
            ..Record::default()
        };
        let json = record.to_json();
        assert_eq!(json["outcome"], "verification-skipped");
        assert_eq!(json["exit_code"], 0);
        assert_eq!(json["refused"], true);
        assert!(json["functions"][0]["sites_proved"].is_null());
        let empty = Record {
            outcome: Some(Outcome::VerificationSkipped),
            exit_code: Some(0),
            ..Record::default()
        };
        assert_eq!(
            empty.to_json()["refused"],
            true,
            "an empty skipped crate is still no verification evidence"
        );
    }
}

#[cfg(test)]
mod output_tests;
