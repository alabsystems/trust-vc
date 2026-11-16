//! The `rust_verify` entry point that upstream Verus's test harness runs.
//!
//! Flow, for one harness case (the order follows Verus's
//! `rust_verify/src/driver.rs`, `run`, and `verifier.rs`):
//!
//! 1. Split the argv into Verus options and rustc arguments
//!    ([`crate::args`]). Options whose effect this binary cannot produce
//!    (vstd import, `--expand-errors`, ...) refuse the whole case here.
//! 2. Verify run: rustc in process, with the cfgs, lint allowances and crate
//!    attributes `rust_verify` adds, through expansion and type checking
//!    (`rustc_hir_analysis::check_crate`). Front-end errors end the run: they
//!    are rustc's own diagnostics, as under Verus.
//! 3. Read the crate into VcIR ([`crate::reader`]). Refusals and Verus
//!    errors are reported; Verus errors are reported by phase, earliest
//!    phase only, as Verus stops after the first phase that fails.
//! 4. Erase run: a second rustc, with ghost code erased by the macros,
//!    through borrow checking, in a child process
//!    ([`ERASE_RUN_FLAG`]). Verus borrow-checks its functions (all but the
//!    `external_body` and external ones) before verifying, stops there on
//!    ownership errors, and compiles the whole crate only once verification
//!    and everything else succeeded. The erase run stands in for both: its
//!    errors inside the functions the first check covers end the run as
//!    Verus's lifetime check would; errors only elsewhere are held and
//!    reported only if the run gets as far as Verus's compile. The erase
//!    run's crate must have the impls of the verify run's, which Verus's
//!    lifetime check sees, and the crate's source must not name the cfg
//!    only the verify run sets; otherwise the case is refused.
//! 5. Verification ([`crate::verify`]): trust-vc-vcir's VC generator turns
//!    every function into per-site queries, the solver answers them, and
//!    failures are reported with Verus's messages and spans. Anything not
//!    decided is refused with a tag.
//! 6. Write the verdict record ([`crate::verdict`]).
//!
//! stderr carries only rustc JSON diagnostics: the harness fails a case on
//! any stderr line it cannot parse as one.

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_hir_analysis;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use std::collections::HashSet;
use std::path::PathBuf;
use std::process::{Command, ExitCode, Stdio};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LOCAL_CRATE;
use rustc_span::{BytePos, FileName, RelativeBytePos, Span};

use trust_vc_vcir::{check_crate_for_diagnostics, Block, Body, FnDecl, FnId, StmtKind, WfClass};

use crate::args::{self, SplitArgs};
use crate::cargo::{self, Inputs as CargoInputs, Invocation as CargoInvocation};
use crate::compiler_environment::CompilerEnvironment;
use crate::messages::{self, Phase};
use crate::reader::{self, CrateRead, FnStatus, ReadOptions, Refusal, UserError};
use crate::verdict::{self, FnVerdict, Outcome, OutputSinks, Record, SiteCounts, Verdict};
use crate::verify::{self, Report, VerifyOptions};

/// Environment variable naming a file that receives a debug dump of the VcIR
/// the reader produced. Never stderr: the harness reads stderr as JSON.
pub const DUMP_VCIR_ENV: &str = "TRUST_VC_DUMP_VCIR";

/// Tag for a read function the verifier returned no result for (a bug).
pub const TAG_VCGEN_MISSING: &str = "vcgen-missing";
/// Tag for functions not checked because something else in the crate was
/// refused.
pub const TAG_CRATE_REFUSED: &str = "crate-refused";
/// Tag for VcIR the checker rejected as malformed: a reader bug.
pub const TAG_VCIR_MALFORMED: &str = "vcir-malformed";
/// Tag for an exec assignment the reader expected rustc to reject, which
/// the erase run accepted.
pub const TAG_BORROWCK_EXPECTED: &str = "borrowck-expected";
/// Tag for a run that stopped before the reader could run.
pub const TAG_FRONT_END_ERROR: &str = "front-end-error";
/// Tag for a type error inside a `reveal`/`hide` helper function, which
/// Verus never type-checks.
pub const TAG_REVEAL_TYPECK: &str = "reveal-typeck";
const REVEAL_TYPECK_DETAIL: &str =
    "type checking failed in a reveal/hide path; Verus resolves these paths without type checking";
/// Tag for a function not verified because of `--no-verify`.
pub const TAG_NO_VERIFY: &str = "no-verify";
/// Tag for an error Verus reports in one module of several while it
/// verifies the others.
pub const TAG_SST_MODULES: &str = "sst-modules";
/// Tag for a compiler panic.
pub const TAG_INTERNAL_ERROR: &str = "internal-error";
/// Tag for a command line this binary cannot interpret.
pub const TAG_BAD_ARGUMENTS: &str = "bad-arguments";
/// Tag for an erase run that could not be started.
pub const TAG_ERASE_RUN: &str = "erase-run";
/// Tag for an erase run whose crate does not have the impls of the verify
/// run's crate, which Verus's lifetime check sees.
pub const TAG_ERASE_IMPLS: &str = "erase-impls";

/// Tag for a crate whose own source names the one cfg the verify run sets
/// and the erase run does not.
pub const TAG_ERASE_CFG: &str = "erase-cfg";

/// The cfg `rust_verify` sets for its verify run only ([`VERIFY_RUN_CFGS`],
/// [`ERASE_RUN_CFGS`]).
const KEEP_GHOST_BODY_CFG: &str = "verus_keep_ghost_body";

/// The `$message_type` of the stderr line on which the erase run lists the
/// impls of its crate ([`impl_keys`]). The parent reads it and prints it
/// nowhere.
const ERASE_IMPLS_MESSAGE: &str = "trust-vc-erase-impls";

/// First argument of the child process that performs the erase run.
pub const ERASE_RUN_FLAG: &str = "--trust-vc-erase-run";
const ERASE_INPUTS_PREFIX: &str = "--trust-vc-erase-cargo-state=";
const ERASE_COMPILER_ENVIRONMENT_FLAG: &str = "--trust-vc-erase-compiler-environment";
const ERASE_ENVIRONMENT_REFUSAL_MESSAGE: &str = "trust-vc-erase-environment-refusal";

/// The rustc flags `rust_verify` adds to every run in which `verus!` has been
/// expanded (`enable_default_features_and_verus_attr` with `syntax_macro`
/// set), suppressing unused and stable feature warnings: the compiler and
/// the upstream harness enable features that have since stabilized, and
/// the resulting warnings would fail otherwise warning-free cases.
const VERIFY_RUN_ALLOWS: &[&str] = &[
    "unused_parens",
    "unused_braces",
    "unconditional_panic",
    "arithmetic_overflow",
    "irrefutable_let_patterns",
    "unused_imports",
    "unused_mut",
    "unused_features",
    "stable_features",
];

fn verus_rustc_flags() -> Vec<String> {
    let mut f = Vec::new();
    for allow in VERIFY_RUN_ALLOWS {
        f.push("-A".to_string());
        f.push(allow.to_string());
    }
    f.push("-Zcrate-attr=allow(internal_features)".to_string());
    for feature in [
        "stmt_expr_attributes",
        "negative_impls",
        "rustc_attrs",
        "unboxed_closures",
        "register_tool",
        "tuple_trait",
        "custom_inner_attributes",
        "try_trait_v2",
    ] {
        f.push(format!("-Zcrate-attr=feature({feature})"));
    }
    for tool in ["verus", "verifier", "verusfmt"] {
        f.push(format!("-Zcrate-attr=register_tool({tool})"));
    }
    f
}

/// The cfgs of `rust_verify`'s verification run (`driver.rs`, `run`).
const VERIFY_RUN_CFGS: [&str; 3] = ["verus_only", "verus_keep_ghost", "verus_keep_ghost_body"];

/// The cfgs of the erase run (`driver.rs`, `run_with_erase_macro_compile`):
/// without `verus_keep_ghost_body`, `verus!` erases ghost code.
const ERASE_RUN_CFGS: [&str; 2] = ["verus_only", "verus_keep_ghost"];

/// Lints the erase run allows (`run_with_erase_macro_compile`): erased code
/// leaves unused variables and dead code behind.
const ERASE_RUN_ALLOWS: [&str; 12] = [
    "unused_imports",
    "unused_variables",
    "unused_assignments",
    "unreachable_patterns",
    "unused_parens",
    "unused_braces",
    "dead_code",
    "unreachable_code",
    "unused_mut",
    "unused_labels",
    "unused_attributes",
    "non_shorthand_field_patterns",
];

/// What the Verus options ask of this run.
#[derive(Debug, Clone, Default)]
struct RunOptions {
    read: ReadOptions,
    no_cheating: bool,
    no_verify: bool,
    verify: VerifyOptions,
    /// The erase run's full argv (child program name first), or `None` when
    /// Verus runs neither its lifetime check nor its erase compile.
    erase_args: Option<Vec<String>>,
    /// Verus runs its lifetime check before verifying (not under
    /// `--no-lifetime`); the erase run stands in for it.
    lifetime_check: bool,
    /// Verus runs its erase compile once verification succeeded
    /// (`driver.rs`): not under `--no-erasure-check` or `--no-lifetime`,
    /// unless `--compile` asks for it.
    erase_compile: bool,
    /// Cargo --no-verify is an explicit skip, rather than a proof success.
    cargo: bool,
    cargo_inputs: CargoInputs,
    private_output: Option<PathBuf>,
    compiler_environment: Option<CompilerEnvironment>,
}

impl RunOptions {
    fn from_split(split: &SplitArgs, erase_args: Vec<String>) -> Result<Self, String> {
        let parsed_verify = verify_options(split)?;
        let no_lifetime = split.has("no-lifetime");
        let lifetime_check = !no_lifetime;
        let erase_compile = split.has("compile") || !(no_lifetime || split.has("no-erasure-check"));
        Ok(Self {
            read: ReadOptions {
                new_mut_ref: split.extended().contains(&"new-mut-ref"),
                no_external_by_default: split.has("no-external-by-default"),
                no_bv_simplify: split.extended().contains(&"no-bv-simplify"),
            },
            no_cheating: split.has("no-cheating"),
            no_verify: split.has("no-verify"),
            verify: VerifyOptions {
                auto_recommends: !split.has("no-auto-recommends-check"),
                ..parsed_verify
            },
            erase_args: (lifetime_check || erase_compile).then_some(erase_args),
            lifetime_check,
            erase_compile,
            cargo: false,
            cargo_inputs: CargoInputs::default(),
            private_output: None,
            compiler_environment: None,
        })
    }
}

/// The verification options on the command line, or why they cannot be
/// read (Verus rejects the same values).
fn verify_options(split: &SplitArgs) -> Result<VerifyOptions, String> {
    let mut opts = VerifyOptions::default();
    if let Some(value) = split.value("rlimit") {
        opts.rlimit = Some(match value {
            "infinity" => None,
            _ => match value.parse::<f32>() {
                Ok(secs) if secs > 0.0 && secs.is_finite() => Some(secs),
                _ => {
                    return Err(format!(
                        "expected a positive number or `infinity` after --rlimit, found `{value}`"
                    ))
                }
            },
        });
    }
    if let Some(value) = split.value("multiple-errors") {
        opts.multiple_errors = value
            .parse()
            .map_err(|_| format!("expected an integer after --multiple-errors, found `{value}`"))?;
    }
    Ok(opts)
}

/// The option combinations and values Verus rejects while it reads its
/// command line (`config.rs`, `parse_args_with_imports`), before compiling
/// anything.
fn argument_error(split: &SplitArgs) -> Option<String> {
    const TRIGGERS_MODES: [&str; 5] = [
        "silent",
        "selective",
        "all-modules",
        "verbose",
        "verbose-all-modules",
    ];
    if split.has("triggers") && split.has("triggers-mode") {
        return Some("--triggers and --triggers-mode are mutually exclusive".to_string());
    }
    if let Some(mode) = split.value("triggers-mode") {
        if !TRIGGERS_MODES.contains(&mode) {
            return Some(format!("invalid --triggers-mode {mode}"));
        }
    }
    let capture_profiles = split.extended().contains(&"capture-profiles");
    if split.has("profile") && (split.has("profile-all") || capture_profiles) {
        return Some(
            "--profile is mutually exclusive with --profile-all and --capture-profiles".to_string(),
        );
    }
    if split.has("profile-all") && !(split.has("verify-only-module") || split.has("verify-root")) {
        return Some(
            "Must pass --verify-only-module or --verify-root when using profile-all".to_string(),
        );
    }
    if let Some(threads) = split.value("num-threads") {
        if threads.parse::<usize>().is_err() {
            return Some("expected integer after num_threads".to_string());
        }
    }
    if split.has("compile") && split.has("no-erasure-check") {
        return Some("--compile and --no-erasure-check are mutually exclusive".to_string());
    }
    None
}

/// A Verus option or rustc argument whose effect this binary cannot produce;
/// the case is refused before compiling.
fn unsupported_request(split: &SplitArgs, via_cargo: bool) -> Option<(&'static str, String)> {
    if let Some(problem) = argument_error(split) {
        return Some(("bad-arguments", problem));
    }
    if let Err(problem) = verify_options(split) {
        return Some(("bad-arguments", problem));
    }
    for (option, tag) in [
        // Solver options change Z3's behaviour, which trust-vc cannot mirror.
        ("smt-option", "smt-option"),
        ("import", "vstd"),
        ("export", "export"),
        ("is-vstd", "vstd"),
        ("is-core", "is-core"),
        ("expand-errors", "expand-errors"),
        ("output-json", "output-json"),
        ("verify-function", "verify-subset"),
        ("verify-module", "verify-subset"),
        ("verify-only-module", "verify-subset"),
        ("verify-root", "verify-subset"),
    ] {
        if split.has(option) {
            return Some((
                tag,
                format!("the Verus option --{option} is not supported yet"),
            ));
        }
    }
    if !split.internal_test_mode && !via_cargo {
        // Outside the test mode rust_verify supplies vstd and the builtin
        // crates from its own installation.
        return Some((
            "test-mode",
            "runs without --internal-test-mode are not supported yet".to_string(),
        ));
    }
    for extended in split.extended() {
        match extended {
            // Handled.
            "new-mut-ref" | "no-bv-simplify" => {}
            // Only change what the reader refuses anyway (`inline_air_stmt`)
            // or how the solver is driven, not which programs verify.
            "allow-inline-air" | "no-solver-version-check" => {}
            "check-api-safety" => {
                return Some((
                    "check-api-safety",
                    "the Verus option -V check-api-safety is not supported yet".to_string(),
                ))
            }
            other => {
                return Some((
                    "verus-option",
                    format!("the Verus option -V {other} is not supported yet"),
                ))
            }
        }
    }
    let mut prev = "";
    for arg in &split.rustc {
        if prev == "--extern" && arg.starts_with("vstd=") {
            return Some((
                "vstd",
                "programs that use vstd are not supported yet".to_string(),
            ));
        }
        prev = arg;
    }
    None
}

/// The verify run's callbacks: read after type checking, report, stop.
struct VerifyRun {
    opts: RunOptions,
    outputs: OutputSinks,
    /// Set once the callback ran; if it never ran the compiler stopped early.
    reached: bool,
    /// Set while trust-vc reads, checks and reports the crate (after rustc's
    /// own type checking). A fatal compiler error in this window comes from a
    /// query trust-vc made, not from the program as Verus would see it.
    reading: bool,
    functions: Vec<FnVerdict>,
    crate_refusals: Vec<String>,
    outcome: Option<Outcome>,
    erase_exit: Option<i32>,
    /// A failure the compiler's own status does not show (the erase run
    /// reported errors in another process).
    failed_elsewhere: bool,
}

impl Callbacks for VerifyRun {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        crate::diagnostic_compat::configure(config);
        self.opts.cargo_inputs.install(config);
        if let Some(environment) = &self.opts.compiler_environment {
            if let Err(error) = environment.apply_to_options(&mut config.opts) {
                rustc_session::EarlyDiagCtxt::new(config.opts.error_format)
                    .early_fatal(error.to_string());
            }
        }
        if let Some(directory) = &self.opts.private_output {
            crate::cargo_native::configure(config, directory);
        }
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if !self.prepare_read(tcx) {
            return Compilation::Stop;
        }
        let read = reader::read_crate(tcx, self.opts.read);
        self.decide(tcx, &read);
        self.reading = false;
        Compilation::Stop
    }
}

impl VerifyRun {
    fn prepare_read(&mut self, tcx: TyCtxt<'_>) -> bool {
        self.reached = true;
        if let Some(environment) = &self.opts.compiler_environment {
            let checked = environment
                .check_options(&tcx.sess.opts)
                .and_then(|()| check_environment_dependencies(environment, tcx.sess));
            if let Err(error) = checked {
                self.refuse(
                    tcx,
                    rustc_span::DUMMY_SP,
                    "request-environment",
                    &error.to_string(),
                );
                self.outcome = Some(Outcome::Refused);
                return false;
            }
        }
        // Use the actual tracked macro read, including ordinary CLI requests
        // whose logical environment need not be virtualized. Checking only a
        // process snapshot would miss an injected compiler value.
        let documentation_expansion = tcx.sess.env_depinfo.lock().iter().any(|(key, value)| {
            key.as_str() == "VERUSDOC" && value.is_some_and(|value| value.as_str() == "1")
        });
        if documentation_expansion {
            let constant = tcx.hir_body_owners().find(|owner| {
                let definition = owner.to_def_id();
                matches!(tcx.def_kind(definition), DefKind::Fn | DefKind::AssocFn)
                    && matches!(
                        tcx.constness(definition),
                        rustc_hir::Constness::Const { .. }
                    )
            });
            if let Some(owner) = constant {
                self.refuse(tcx, tcx.def_span(owner), "documentation-const",
                    "VERUSDOC=1 omits const-function contracts in this macro cohort; verification of that expansion is not represented");
                self.outcome = Some(Outcome::Refused);
                return false;
            }
        }
        if tcx.dcx().has_errors().is_some() {
            self.outcome = Some(Outcome::FrontEndRejected);
            return false;
        }
        rustc_hir_analysis::check_crate(tcx);
        if tcx.dcx().has_errors().is_some() {
            self.outcome = Some(Outcome::FrontEndRejected);
            let reveal_errors = reader::reveal_helpers_with_type_errors(tcx);
            if !reveal_errors.is_empty() {
                // Some of these type errors would not exist under Verus,
                // which rewrites reveal helpers before type checking.
                for span in reveal_errors {
                    self.refuse(tcx, span, TAG_REVEAL_TYPECK, REVEAL_TYPECK_DETAIL);
                }
                self.outcome = Some(Outcome::Refused);
            }
            return false;
        }
        self.reading = true;
        if !reader::builtin_loaded(tcx) {
            // Verus's first check once the crate is type-checked
            // (`verifier.rs`, `construct_vir_crate`).
            let mut error = UserError::new(
                Phase::RustToVir,
                tcx.hir_root_module().spans.inner_span,
                messages::NO_BUILTIN,
            );
            error.help = Some(messages::NO_BUILTIN_HELP.to_string());
            emit_user_error(tcx, &error);
            self.outcome = Some(Outcome::VerusRejected);
            self.reading = false;
            return false;
        }
        true
    }

    fn new(opts: RunOptions, outputs: OutputSinks) -> Self {
        Self {
            opts,
            outputs,
            reached: false,
            reading: false,
            functions: Vec::new(),
            crate_refusals: Vec::new(),
            outcome: None,
            erase_exit: None,
            failed_elsewhere: false,
        }
    }

    fn dump_vcir(&self, read: &CrateRead) {
        if !self.outputs.wants_vcir_dump() {
            return;
        }
        let statuses: Vec<String> = read
            .fns
            .iter()
            .map(|f| format!("{}: {:?}", f.def_path, f.status))
            .collect();
        let text = format!(
            "{}-- statuses --\n{}\n",
            trust_vc_vcir::pretty::crate_to_string(&read.krate),
            statuses.join("\n")
        );
        // A dump that cannot be written only loses the dump.
        let _ = self.outputs.write_vcir(&text);
    }

    /// Record every function; `read_verdict` (with `read_tag`) is the
    /// verdict of the functions that were read completely.
    fn record_functions(
        &mut self,
        tcx: TyCtxt<'_>,
        read: &CrateRead,
        read_verdict: Verdict,
        read_tag: Option<&str>,
    ) {
        self.record_functions_with(tcx, read, &|_| {
            (read_verdict, read_tag.map(str::to_string), None)
        });
    }

    /// Record every function; `read_outcome` gives the verdict, tag and site
    /// counts of a function that was read completely.
    fn record_functions_with(
        &mut self,
        tcx: TyCtxt<'_>,
        read: &CrateRead,
        read_outcome: &dyn Fn(FnId) -> (Verdict, Option<String>, Option<SiteCounts>),
    ) {
        for f in &read.fns {
            let (verdict, tag, sites) = match &f.status {
                FnStatus::Read(id) => read_outcome(*id),
                FnStatus::Rejected | FnStatus::Deferred(_) => (Verdict::Rejected, None, None),
                FnStatus::Refused(r) => (Verdict::Refused, Some(r.tag.to_string()), None),
                FnStatus::External => (Verdict::External, None, None),
            };
            self.functions.push(FnVerdict {
                def_path: f.def_path.clone(),
                kind: f.kind.clone(),
                verdict,
                tag,
                lines: item_lines(tcx, f.def_id),
                sites,
            });
        }
    }

    /// Decide the fate of the crate from what the reader found; see the
    /// module documentation for the order.
    fn decide(&mut self, tcx: TyCtxt<'_>, read: &CrateRead) {
        self.decide_with_owner(tcx, read, None);
    }

    fn decide_with_owner<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        read: &CrateRead,
        owner: Option<&reader::declaration_staging::LiveNormalClientRead<'_, '_, '_, 'tcx>>,
    ) {
        self.dump_vcir(read);
        let refusals: Vec<&Refusal> = read.refusals().collect();
        let first_phase: Vec<&UserError> = read
            .errors
            .iter()
            .filter(|e| e.phase == Phase::RustToVir)
            .collect();

        // Refusals: the case is refused. Verus errors from the first phase
        // are shown too, since they are Verus's own verdict on this code.
        if !refusals.is_empty() {
            for r in refusals {
                self.refuse(tcx, r.span, r.tag, &r.detail);
            }
            for e in first_phase {
                emit_user_error(tcx, e);
            }
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            return;
        }

        if !first_phase.is_empty() {
            for e in first_phase {
                emit_user_error(tcx, e);
            }
            self.outcome = Some(Outcome::VerusRejected);
            self.record_functions(tcx, read, Verdict::Rejected, None);
            return;
        }

        // Refusals that only a first-phase rejection could override.
        if !read.pending_item_refusals.is_empty() {
            for r in &read.pending_item_refusals {
                self.refuse(tcx, r.span, r.tag, &r.detail);
            }
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            return;
        }

        // The VcIR checker: malformed IR is a reader bug and refused; user
        // errors join the reader's later-phase errors.
        let mut later: Vec<UserError> = read.errors.clone();
        let mut malformed = false;
        let diagnostics = check_crate_for_diagnostics(&read.krate);
        let incomplete_binder = diagnostics.incomplete_binders.first().copied();
        for problem in diagnostics.errors {
            let span = read.span(problem.span).unwrap_or(rustc_span::DUMMY_SP);
            match problem.class {
                WfClass::Malformed => {
                    malformed = true;
                    self.refuse(tcx, span, TAG_VCIR_MALFORMED, &problem.message);
                }
                WfClass::User => {
                    let mut error =
                        UserError::new(wf_phase(&problem.message), span, problem.message);
                    error.function = problem
                        .function
                        .and_then(|id| read.fn_defs.get(&id).copied());
                    later.push(error);
                }
            }
        }
        if malformed {
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            return;
        }
        // Errors of the phases before Verus's lifetime check (VIR building,
        // modes and well-formedness) end the run. Verus reports the
        // warnings of its well-formedness check once that check passes.
        let first_later = later.iter().map(|e| e.phase).min();
        if first_later.is_none_or(|phase| phase > Phase::WellFormed) {
            for warning in &read.warnings {
                emit_warning(tcx, warning);
            }
        }
        if let Some(phase) = first_later.filter(|phase| *phase < Phase::Simplify) {
            for e in reported(read, &later, phase) {
                emit_user_error(tcx, e);
            }
            self.outcome = Some(Outcome::VerusRejected);
            self.record_functions(tcx, read, Verdict::Rejected, None);
            return;
        }

        // `--no-cheating`: every assume, and every function with a trusted
        // body (`external_body`, which `verus!` also puts on an `uninterp`
        // spec function), is an error. Verus's well-formedness check finds
        // them without stopping and defers them: they are reported after
        // verification (or after the error that ends it), in its function
        // order, and never when the lifetime check fails.
        let mut cheating_errors: Vec<UserError> = Vec::new();
        let mut cheating_fns: HashSet<FnId> = HashSet::new();
        if self.opts.no_cheating {
            for decl in &read.krate.fns {
                let function = read.fn_defs.get(&decl.id).copied();
                let mut found = Vec::new();
                // `check_function` finds `assume_termination` before the
                // assumes of the body.
                if let Some(def) = function {
                    let attrs = crate::reader::attrs::item_attrs(
                        tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)),
                    );
                    if attrs.assume_termination {
                        found.push(UserError::new(
                            Phase::Modes,
                            tcx.def_span(def),
                            messages::NO_CHEATING_ASSUME_TERMINATION,
                        ));
                    }
                }
                for_each_assume(decl, &mut |span, attrs| {
                    let span = read.span(span).unwrap_or(rustc_span::DUMMY_SP);
                    let mut error =
                        UserError::new(Phase::Modes, span, messages::NO_CHEATING_ASSUME);
                    if let Some(text) = attrs.custom_errs.first() {
                        error.message = text.clone();
                    } else if let Some(text) = attrs.proof_notes.first() {
                        error.primary_label = Some(messages::proof_note_label(text));
                    }
                    found.push(error);
                });
                if decl.attrs.external_body {
                    let span = read.span(decl.span).unwrap_or(rustc_span::DUMMY_SP);
                    found.push(UserError::new(
                        Phase::Modes,
                        span,
                        messages::NO_CHEATING_EXTERNAL_BODY,
                    ));
                }
                if !found.is_empty() {
                    cheating_fns.insert(decl.id);
                }
                for mut error in found {
                    error.function = function;
                    cheating_errors.push(error);
                }
            }
            // Stable: a function's errors keep the order they were found in.
            cheating_errors.sort_by_key(|e| read.verus_order(e.function));
        }
        let cheating = !cheating_errors.is_empty();

        // Proof bodies in the closed tracked-only fragment retain every
        // ownership use in the original compiler MIR. Check those roots
        // natively: the macro erase run removes their bodies entirely.
        if !self.owned_boundary(tcx, read, owner, OwnedBoundary::RetainedInputs) {
            return;
        }
        let mut native_ownership_failed = false;
        if !read.native_ownership.is_empty() {
            if !self.opts.lifetime_check {
                self.refuse(
                    tcx,
                    tcx.hir_root_module().spans.inner_span,
                    "ownership",
                    "tracked proof values require native ownership checking",
                );
                self.outcome = Some(Outcome::Refused);
                self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
                return;
            }
            for function in &read.fns {
                if read.native_ownership.contains(&function.def_id)
                    && matches!(function.status, FnStatus::Read(_))
                {
                    tcx.ensure_ok().mir_borrowck(function.def_id);
                }
            }
            native_ownership_failed = tcx.dcx().has_errors().is_some();
        }

        // The remaining lifetime check stops the run on exec ownership
        // errors; the erase run's borrow checker stands in for it.
        // It runs whatever else the crate holds: before simplification
        // errors are reported, and before the deferred `--no-cheating`
        // errors, which a failed lifetime check leaves unreported. A
        // function holding an exec assignment to an immutable local, which
        // only rustc reports, needs it to fail.
        let deferred: Vec<Span> = read
            .fns
            .iter()
            .filter_map(|f| match f.status {
                FnStatus::Deferred(span) => Some(span),
                _ => None,
            })
            .collect();
        let mut compile_errors: Option<Vec<String>> = None;
        if !self.owned_boundary(tcx, read, owner, OwnedBoundary::RetainedInputs) {
            return;
        }
        let erase_result = self.erase_run(tcx, read, owner);
        if native_ownership_failed {
            // The lifetime phase reports ownership errors in proof and exec
            // bodies alike. Keep running the exec check after a proof error,
            // but never publish verification or deferred compile errors.
            if matches!(&erase_result, EraseResult::Failed) {
                self.outcome = Some(Outcome::Refused);
                self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            } else {
                self.outcome = Some(Outcome::VerusRejected);
                self.record_functions(tcx, read, Verdict::Rejected, None);
            }
            return;
        }
        match erase_result {
            EraseResult::Rejected => {
                self.outcome = Some(Outcome::EraseRejected);
                self.record_functions(tcx, read, Verdict::Rejected, None);
                return;
            }
            EraseResult::Failed => {
                self.outcome = Some(Outcome::Refused);
                self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
                return;
            }
            EraseResult::Clean | EraseResult::Skipped | EraseResult::CompileOnly(_)
                if !deferred.is_empty() =>
            {
                for span in deferred {
                    self.refuse(
                        tcx,
                        span,
                        TAG_BORROWCK_EXPECTED,
                        "an exec assignment to an immutable variable that was not reported by rustc",
                    );
                }
                self.outcome = Some(Outcome::Refused);
                self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
                return;
            }
            EraseResult::CompileOnly(lines) => compile_errors = Some(lines),
            EraseResult::Clean | EraseResult::Skipped => {}
        }

        // Simplification errors, then errors Verus finds as it turns each
        // module's functions into SST before verifying that module. With
        // more than one module Verus verifies the others as well, which is
        // not reproduced. The deferred `--no-cheating` errors follow.
        if let Some(phase) = first_later {
            if phase.is_sst() && read.fn_modules.len() > 1 {
                // Each module reports the first error of its own; when
                // every module has one, nothing else is verified.
                if let Some(firsts) = first_error_per_module(tcx, read, &later) {
                    for e in firsts {
                        emit_user_error(tcx, e);
                    }
                    for e in &cheating_errors {
                        emit_user_error(tcx, e);
                    }
                    self.outcome = Some(Outcome::VerusRejected);
                    self.record_functions(tcx, read, Verdict::Rejected, None);
                    return;
                }
                for e in reported(read, &later, phase) {
                    self.refuse(
                        tcx,
                        e.span,
                        TAG_SST_MODULES,
                        "an error Verus reports while it verifies a crate's modules one by one",
                    );
                }
                self.outcome = Some(Outcome::Refused);
                self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
                return;
            }
            for e in reported(read, &later, phase) {
                emit_user_error(tcx, e);
            }
            for e in &cheating_errors {
                emit_user_error(tcx, e);
            }
            self.outcome = Some(Outcome::VerusRejected);
            self.record_functions(tcx, read, Verdict::Rejected, None);
            return;
        }

        // Diagnostic binders preserve real typed source structure but never
        // license VC generation. Even if a future change loses their source
        // error, incomplete construction cannot become a successful read.
        if let Some((_, span)) = incomplete_binder {
            self.refuse(
                tcx,
                read.span(span).unwrap_or(rustc_span::DUMMY_SP),
                "source-construction",
                "a source binder without a reported trigger error",
            );
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            return;
        }

        // What only verification needed to refuse stands now that Verus
        // would verify.
        if !read.verify_refusals.is_empty() {
            for r in &read.verify_refusals {
                self.refuse(tcx, r.span, r.tag, &r.detail);
            }
            for e in &cheating_errors {
                emit_user_error(tcx, e);
            }
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            return;
        }

        // `--no-verify`: nothing is verified, and each function that would
        // have been is refused, so that the run is never taken for a
        // verified one.
        if self.opts.no_verify {
            if self.opts.cargo {
                for e in &cheating_errors {
                    emit_user_error(tcx, e);
                }
                if cheating {
                    self.outcome = Some(Outcome::VerusRejected);
                    self.record_functions(tcx, read, Verdict::Rejected, None);
                } else if let Some(lines) = compile_errors {
                    print_lines(&lines);
                    self.failed_elsewhere = true;
                    self.outcome = Some(Outcome::EraseRejected);
                    self.record_functions(tcx, read, Verdict::Rejected, None);
                } else {
                    self.outcome = Some(Outcome::VerificationSkipped);
                    self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_NO_VERIFY));
                }
                return;
            }
            for f in &read.fns {
                if let FnStatus::Read(_) = f.status {
                    let detail = format!("`{}` is not verified under --no-verify", f.def_path);
                    self.refuse(tcx, tcx.def_span(f.def_id), TAG_NO_VERIFY, &detail);
                }
            }
            for e in &cheating_errors {
                emit_user_error(tcx, e);
            }
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_NO_VERIFY));
            return;
        }

        // Verification.
        if !self.owned_boundary(tcx, read, owner, OwnedBoundary::PositiveVerification) {
            return;
        }
        if let Some(environment) = &self.opts.compiler_environment {
            let checked = environment
                .check_options(&tcx.sess.opts)
                .and_then(|()| check_environment_dependencies(environment, tcx.sess));
            if let Err(error) = checked {
                self.refuse(
                    tcx,
                    rustc_span::DUMMY_SP,
                    "request-environment",
                    &error.to_string(),
                );
                self.outcome = Some(Outcome::Refused);
                self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
                return;
            }
        }
        let verification = verify::verify(read, self.opts.verify);
        if !self.owned_boundary(tcx, read, owner, OwnedBoundary::PositiveVerification) {
            return;
        }
        if owner.is_some()
            && read
                .krate
                .fns
                .iter()
                .filter(|f| f.role == trust_vc_vcir::FnRole::Imported)
                .any(|f| {
                    verification.fns.get(&f.id).is_none_or(|result| {
                        result.verdict != Verdict::Declared || result.sites.is_some()
                    })
                })
        {
            self.refuse(
                tcx,
                tcx.hir_root_module().spans.inner_span,
                "owned-import",
                "a normal imported signature was not kept bodyless and unscored",
            );
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            return;
        }
        for report in &verification.reports {
            match report {
                Report::Failure(failure) => verify::emit_failure(tcx, failure),
                Report::Recommendation(failure) => verify::emit_recommendation(tcx, failure),
                Report::Refusal { span, tag, detail } => self.refuse(tcx, *span, tag, detail),
                Report::Note { span, message } => verify::emit_note(tcx, *span, message),
            }
        }
        for e in &cheating_errors {
            emit_user_error(tcx, e);
        }
        let outcome_of = |id: FnId| match verification.fns.get(&id) {
            // Verus reported an error in this function (an assume or a
            // trusted body under `--no-cheating`), so it is not verified or
            // trusted whatever its checks say.
            Some(outcome)
                if matches!(outcome.verdict, Verdict::Verified | Verdict::Trusted)
                    && cheating_fns.contains(&id) =>
            {
                (Verdict::Rejected, None, outcome.sites)
            }
            Some(outcome) => (outcome.verdict, outcome.tag.clone(), outcome.sites),
            // Every read function is in the VcIR crate, so the generator
            // saw it; a missing entry is a bug and never a verification.
            None => (Verdict::Refused, Some(TAG_VCGEN_MISSING.to_string()), None),
        };
        self.record_functions_with(tcx, read, &outcome_of);
        let any_refused = !self.crate_refusals.is_empty()
            || self.functions.iter().any(|f| f.verdict.is_refusal());
        let any_failed = self.functions.iter().any(|f| f.verdict == Verdict::Failed);
        if any_refused {
            if self.crate_refusals.is_empty() {
                // A function was refused without a diagnostic: say so, so the
                // case carries a tag.
                self.refuse(
                    tcx,
                    rustc_span::DUMMY_SP,
                    TAG_VCGEN_MISSING,
                    "a function has no verification result",
                );
            }
            self.outcome = Some(Outcome::Refused);
        } else if any_failed {
            self.outcome = Some(Outcome::VerificationFailed);
        } else if cheating {
            self.outcome = Some(Outcome::VerusRejected);
        } else if let Some(lines) = compile_errors {
            // Verification found nothing, so Verus runs its compile, which
            // reports the errors the lifetime check skipped.
            print_lines(&lines);
            self.failed_elsewhere = true;
            self.outcome = Some(Outcome::EraseRejected);
            self.functions.clear();
            self.record_functions(tcx, read, Verdict::Rejected, None);
        } else {
            self.outcome = Some(Outcome::Checked);
        }
    }

    fn owned_boundary<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        read: &CrateRead,
        owner: Option<&reader::declaration_staging::LiveNormalClientRead<'_, '_, '_, 'tcx>>,
        boundary: OwnedBoundary,
    ) -> bool {
        let Some(owner) = owner else {
            return true;
        };
        let checked = match boundary {
            OwnedBoundary::RetainedInputs => owner.check_retained_inputs(tcx),
            OwnedBoundary::PositiveVerification => owner.ready_for_solver(tcx),
        };
        if let Err(reason) = checked {
            self.refuse(
                tcx,
                tcx.hir_root_module().spans.inner_span,
                "owned-inputs",
                &reason,
            );
            self.outcome = Some(Outcome::Refused);
            self.record_functions(tcx, read, Verdict::Skipped, Some(TAG_CRATE_REFUSED));
            return false;
        }
        true
    }

    /// Report a refusal as an error diagnostic and record it.
    fn refuse(&mut self, tcx: TyCtxt<'_>, span: Span, tag: &str, detail: &str) {
        let message = verdict::refusal_message(tag, detail);
        if span == rustc_span::DUMMY_SP {
            tcx.dcx().struct_err(message.clone()).emit();
        } else {
            tcx.dcx().struct_span_err(span, message.clone()).emit();
        }
        self.crate_refusals.push(message);
    }

    /// Run the erase compile if the options ask for it. Its diagnostics
    /// are printed, except errors that lie wholly inside functions Verus's
    /// lifetime check skips, which are held when they are all it reported.
    ///
    /// The erase run stands in for Verus's lifetime check only when its
    /// crate has the items the verify run's crate has: an impl that ghost
    /// code produces (a macro called in a proof block) changes what the
    /// lifetime check allows (a `Drop` or `Copy` impl), and the erase run
    /// does not see it; nor does it see an item under
    /// `cfg(verus_keep_ghost_body)`.
    fn erase_run<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        read: &CrateRead,
        owner: Option<&reader::declaration_staging::LiveNormalClientRead<'_, '_, '_, 'tcx>>,
    ) -> EraseResult {
        let Some(args) = self.opts.erase_args.clone() else {
            return EraseResult::Skipped;
        };
        // Code the crate puts under that cfg (a function, a method, a
        // field's type, a type alias, a macro, a bound) is in the verify
        // run's crate and not in the erase run's, or the other way round,
        // and Verus's lifetime check sees the verify run's.
        if self.opts.lifetime_check {
            if let Some(span) = names_keep_ghost_body(tcx) {
                self.refuse(
                    tcx,
                    span,
                    TAG_ERASE_CFG,
                    "the crate names `verus_keep_ghost_body`, which the erase run does not set",
                );
                return EraseResult::Failed;
            }
        }
        if !self.owned_boundary(tcx, read, owner, OwnedBoundary::RetainedInputs) {
            return EraseResult::Failed;
        }
        let private_output = self
            .opts
            .private_output
            .as_ref()
            .map(|directory| directory.with_file_name("erase"));
        let child = match run_erase_child(
            &args,
            &self.opts.cargo_inputs,
            private_output.as_deref(),
            self.opts.compiler_environment.as_ref(),
        ) {
            Ok(child) => child,
            Err(problem) => {
                // Without the erase run nothing may be called checked.
                self.refuse(tcx, rustc_span::DUMMY_SP, TAG_ERASE_RUN, &problem);
                return EraseResult::Failed;
            }
        };
        if !self.owned_boundary(tcx, read, owner, OwnedBoundary::RetainedInputs) {
            return EraseResult::Failed;
        }
        self.erase_exit = Some(child.code);
        if let Some(problem) = &child.environment_refusal {
            print_lines(&child.lines);
            self.refuse(tcx, rustc_span::DUMMY_SP, "request-environment", problem);
            return EraseResult::Failed;
        }
        if self.opts.lifetime_check {
            let problem = match &child.impls {
                Some(erased) => impl_difference(&impls(tcx), erased),
                None => Some((
                    "the erase run stopped before its impls were known".to_string(),
                    rustc_span::DUMMY_SP,
                )),
            };
            if let Some((detail, span)) = problem {
                self.refuse(tcx, span, TAG_ERASE_IMPLS, &detail);
                return EraseResult::Failed;
            }
        }
        let lines = child.lines;
        if child.code == 0 {
            if self.opts.erase_compile {
                if self.opts.cargo {
                    // These files live in scratch space and are not Cargo
                    // outputs. Final compilation reports the real artifacts.
                    let diagnostics: Vec<_> = lines
                        .into_iter()
                        .filter(|line| {
                            serde_json::from_str::<serde_json::Value>(line)
                                .map_or(true, |value| value["$message_type"] != "artifact")
                        })
                        .collect();
                    print_lines(&diagnostics);
                } else {
                    print_lines(&lines);
                }
            }
            return EraseResult::Clean;
        }
        // Exit 1 is rustc's for errors it reported; anything else (a panic)
        // is printed as it came. Without the lifetime check every error is
        // one of the erase compile.
        let scope = LifetimeScope::new(tcx, read);
        let kinds: Vec<Option<bool>> = lines
            .iter()
            .map(|line| match (child.code, self.opts.lifetime_check) {
                (1, true) => scope.classify(line),
                (1, false) => scope.classify(line).map(|_| true),
                _ => Some(false),
            })
            .collect();
        let any_error = kinds.iter().any(Option::is_some);
        if any_error && kinds.iter().all(|k| *k != Some(false)) {
            // Errors only the erase compile reports, which Verus does not
            // run under `--no-erasure-check`.
            if !self.opts.erase_compile {
                return EraseResult::Clean;
            }
            return EraseResult::CompileOnly(lines);
        }
        let shown: Vec<String> = lines
            .into_iter()
            .zip(&kinds)
            .filter(|(_, kind)| **kind != Some(true))
            .map(|(line, _)| line)
            .collect();
        print_lines(&shown);
        self.failed_elsewhere = true;
        EraseResult::Rejected
    }
}

enum OwnedBoundary {
    RetainedInputs,
    PositiveVerification,
}

mod normal_invocation;
mod owned;
pub(crate) use normal_invocation::NormalInvocation;
pub(crate) use owned::{NormalReadBinding, NormalReadScope, OwnedNormalVerifier};

pub(crate) fn normal_client_lints(verify: &mut Vec<String>, erase: &mut Vec<String>) {
    for allow in VERIFY_RUN_ALLOWS {
        verify.extend(["-A".to_string(), (*allow).to_string()]);
        erase.extend(["-A".to_string(), (*allow).to_string()]);
    }
    for allow in ERASE_RUN_ALLOWS {
        erase.extend(["-A".to_string(), allow.to_string()]);
    }
}

/// How the erase run went.
enum EraseResult {
    /// Verus runs neither its lifetime check nor its erase compile
    /// (`--no-lifetime` without `--compile`).
    Skipped,
    /// It compiled without errors.
    Clean,
    /// rustc reported errors Verus's lifetime check reports as well; they
    /// are on stderr.
    Rejected,
    /// rustc reported errors only inside functions Verus's lifetime check
    /// skips (`external_body` and external ones). Verus reports those from
    /// the compile it runs once nothing else failed; the erase run's stderr
    /// lines are held until the run is known to get that far.
    CompileOnly(Vec<String>),
    /// It could not be run; a refusal was reported.
    Failed,
}

/// Where Verus's lifetime check looks: `rust_verify/src/verifier.rs`,
/// `run_lifetime_checks_on_verus_aware_items`, borrow-checks every Verus
/// function except `external_body` ones, and no external item. Line ranges,
/// by file, of the functions it checks and of those it skips.
///
/// A function a macro produced is written in the macro's definition and
/// placed in the crate at the macro's call; it covers both ranges.
struct LifetimeScope {
    checked: Vec<LineRange>,
    skipped: Vec<LineRange>,
}

/// A file and a first and last line.
type LineRange = (String, usize, usize);

impl LifetimeScope {
    fn new(tcx: TyCtxt<'_>, read: &CrateRead) -> Self {
        let external_body: HashSet<rustc_span::def_id::LocalDefId> = read
            .krate
            .fns
            .iter()
            .filter(|decl| decl.attrs.external_body)
            .filter_map(|decl| read.fn_defs.get(&decl.id).copied())
            .collect();
        let mut scope = Self {
            checked: Vec::new(),
            skipped: Vec::new(),
        };
        for f in &read.fns {
            let Some(lines) = item_lines(tcx, f.def_id) else {
                continue;
            };
            let ranges =
                if matches!(f.status, FnStatus::External) || external_body.contains(&f.def_id) {
                    &mut scope.skipped
                } else {
                    &mut scope.checked
                };
            ranges.push(lines);
            let span = tcx.source_span(f.def_id);
            if span.from_expansion() {
                ranges.push(span_lines(tcx, span.source_callsite()));
            }
        }
        scope
    }

    /// For one line of the erase run's stderr: `None` if it is not an error
    /// diagnostic, `Some(true)` if it is one whose every primary span lies
    /// inside a skipped function and outside every checked one, and
    /// `Some(false)` for any other error, or a line that cannot be read.
    ///
    /// Code a macro produced is placed in the crate at the outermost call
    /// site on its span's expansion chain, while rustc gives the span's own
    /// location in the macro's definition, which may lie inside a skipped
    /// function while the macro is called in a checked one, whose lifetime
    /// check Verus runs. So a primary span is inside a skipped function when
    /// its outermost call site is, and it touches a checked function when
    /// any span on its chain does.
    fn classify(&self, line: &str) -> Option<bool> {
        let Ok(diag) = serde_json::from_str::<serde_json::Value>(line) else {
            return Some(false);
        };
        if diag["level"] != "error"
            || diag["message"]
                .as_str()
                .is_some_and(|m| m.starts_with("aborting due to"))
        {
            return None;
        }
        let primary: Vec<&serde_json::Value> = diag["spans"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|s| s["is_primary"].as_bool() == Some(true))
            .collect();
        let placed = |span: &&serde_json::Value| {
            let Some(chain) = expansion_chain(span) else {
                return false;
            };
            let Some((file, lo, hi)) = chain.last().copied().and_then(json_span_lines) else {
                return false;
            };
            let inside = self
                .skipped
                .iter()
                .any(|(f, a, b)| *f == file && *a <= lo && hi <= *b);
            let touches_checked = chain.iter().any(|span| match json_span_lines(span) {
                Some((file, lo, hi)) => self
                    .checked
                    .iter()
                    .any(|(f, a, b)| *f == file && *a <= hi && lo <= *b),
                None => true,
            });
            inside && !touches_checked
        };
        Some(!primary.is_empty() && primary.iter().all(placed))
    }
}

/// A JSON span followed by the call sites on its expansion chain
/// (`expansion`, then that expansion's call-site `span`, and so on),
/// outermost last. `None` if the chain cannot be followed.
fn expansion_chain(span: &serde_json::Value) -> Option<Vec<&serde_json::Value>> {
    let mut chain = vec![span];
    let mut current = span;
    loop {
        match current.get("expansion") {
            None | Some(serde_json::Value::Null) => return Some(chain),
            Some(expansion) => match expansion.get("span") {
                Some(call_site) if call_site.is_object() => {
                    chain.push(call_site);
                    current = call_site;
                }
                _ => return None,
            },
        }
    }
}

/// The file and first and last line of a JSON span.
fn json_span_lines(span: &serde_json::Value) -> Option<LineRange> {
    Some((
        span["file_name"].as_str()?.to_string(),
        usize::try_from(span["line_start"].as_u64()?).ok()?,
        usize::try_from(span["line_end"].as_u64()?).ok()?,
    ))
}

/// Print lines to stderr as they came.
fn print_lines(lines: &[String]) {
    for line in lines {
        eprintln!("{line}");
    }
}

/// The errors Verus reports for `phase` out of `errors`: every error of the
/// phase that builds VIR (one per item), and only the first error, in
/// Verus's function order, of any later phase, which stops there.
///
/// Within a function, the mode checker walks the body in source order: an
/// assignment's target before its value, a call before its arguments. The
/// reader emits the effects of a value before the statement that uses it, so
/// mode errors are put in source order. Other phases keep the order they were
/// found in.
fn reported<'a>(read: &CrateRead, errors: &'a [UserError], phase: Phase) -> Vec<&'a UserError> {
    let mut of_phase: Vec<&UserError> = errors.iter().filter(|e| e.phase == phase).collect();
    if phase != Phase::RustToVir {
        if phase == Phase::Modes {
            of_phase.sort_by_key(|e| (read.verus_order(e.function), e.span.lo()));
        } else if phase == Phase::Simplify {
            // Verus's trait cycle check runs before simplification.
            of_phase.sort_by_key(|e| {
                (
                    e.message != messages::TRAIT_CYCLE,
                    read.verus_order(e.function),
                )
            });
        } else {
            // Stable: a function's errors keep the order they were found in.
            of_phase.sort_by_key(|e| read.verus_order(e.function));
        }
        of_phase.truncate(1);
    }
    of_phase
}

/// The first `Sst` error of each module, in Verus's order, when every
/// module with functions has one (Verus turns each module into SST just
/// before verifying it, and a module stops at its first error).
fn first_error_per_module<'a>(
    tcx: TyCtxt<'_>,
    read: &CrateRead,
    errors: &'a [UserError],
) -> Option<Vec<&'a UserError>> {
    let mut of_phase: Vec<&UserError> = errors.iter().filter(|e| e.phase.is_sst()).collect();
    // SST construction of all functions precedes trigger elaboration within
    // each module. Compare stages before source order when choosing its error.
    of_phase.sort_by_key(|e| (e.phase, read.verus_order(e.function)));
    let mut firsts: Vec<&UserError> = Vec::new();
    let mut seen: HashSet<rustc_hir::def_id::LocalDefId> = HashSet::new();
    for e in of_phase {
        let module = tcx.parent_module_from_def_id(e.function?).to_local_def_id();
        if seen.insert(module) {
            firsts.push(e);
        }
    }
    firsts.sort_by_key(|e| read.verus_order(e.function));
    (read.fn_modules.iter().all(|m| seen.contains(m))).then_some(firsts)
}

/// The Verus phase of a VcIR checker user error, by its message.
fn wf_phase(message: &str) -> Phase {
    use trust_vc_vcir::wf::{MSG_DUPLICATE_NOTE, MSG_MUT_SPEC_PARAM};
    if message == MSG_DUPLICATE_NOTE || message == MSG_MUT_SPEC_PARAM {
        Phase::RustToVir
    } else if message.ends_with("is not marked mutable") {
        Phase::Simplify
    } else {
        Phase::Modes
    }
}

/// Call `f` with the span and attributes of every `assume` in `decl`.
fn for_each_assume(
    decl: &FnDecl,
    f: &mut dyn FnMut(trust_vc_vcir::SpanId, &trust_vc_vcir::ClauseAttrs),
) {
    fn walk(block: &Block, f: &mut dyn FnMut(trust_vc_vcir::SpanId, &trust_vc_vcir::ClauseAttrs)) {
        for stmt in &block.stmts {
            match &stmt.kind {
                StmtKind::Assume { attrs, .. } => f(stmt.span, attrs),
                StmtKind::If {
                    then_block,
                    else_block,
                    ..
                } => {
                    walk(then_block, f);
                    walk(else_block, f);
                }
                StmtKind::Ghost(inner) | StmtKind::Block(inner) => walk(inner, f),
                StmtKind::GhostTail { block, tail } => {
                    walk(block, f);
                    walk_expression(tail, f);
                }
                StmtKind::Loop(lp) => {
                    if let Some(cond) = &lp.cond {
                        walk(&cond.block, f);
                    }
                    walk(&lp.body, f);
                }
                _ => {}
            }
        }
    }
    fn walk_expression(
        expr: &trust_vc_vcir::Expr,
        f: &mut dyn FnMut(trust_vc_vcir::SpanId, &trust_vc_vcir::ClauseAttrs),
    ) {
        match &expr.kind {
            trust_vc_vcir::ExprKind::ProofInSpec(block)
            | trust_vc_vcir::ExprKind::ProofInSpecTail { block, .. } => walk(block, f),
            _ => {}
        }
        expr.for_each_child(&mut |child| walk_expression(child, f));
    }
    if let Body::Stmts(block) = &decl.body {
        walk(block, f);
    }
}

/// File and first and last line of a whole item, body included.
fn item_lines(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::LocalDefId) -> Option<LineRange> {
    Some(span_lines(tcx, tcx.source_span(def_id)))
}

/// File and first and last line of a span.
fn span_lines(tcx: TyCtxt<'_>, span: Span) -> LineRange {
    let source_map = tcx.sess.source_map();
    let lo = source_map.lookup_char_pos(span.lo());
    let hi = source_map.lookup_char_pos(span.hi());
    (
        lo.file.name.prefer_local_unconditionally().to_string(),
        lo.line,
        hi.line,
    )
}

/// Report a Verus error the way Verus lays it out.
fn emit_warning(tcx: TyCtxt<'_>, warning: &UserError) {
    tcx.dcx()
        .struct_span_warn(warning.span, warning.message.clone())
        .emit();
}

fn emit_user_error(tcx: TyCtxt<'_>, error: &UserError) {
    let mut diag = tcx.dcx().struct_span_err(error.span, error.message.clone());
    if let Some(label) = &error.primary_label {
        diag.span_label(error.span, label.clone());
    }
    for (span, label) in &error.labels {
        diag.span_label(*span, label.clone());
    }
    if let Some(help) = &error.help {
        diag.help(help.clone());
    }
    diag.emit();
}

/// What the erase run's child process gave back.
struct EraseChild {
    code: i32,
    /// Its stderr lines (JSON diagnostics), which the caller prints or holds.
    lines: Vec<String>,
    /// The impls of its crate ([`impl_keys`]), if it got that far.
    impls: Option<Vec<String>>,
    environment_refusal: Option<String>,
}

/// Start the erase run as a child process of this binary and wait for it.
fn run_erase_child(
    args: &[String],
    inputs: &CargoInputs,
    private_output: Option<&std::path::Path>,
    compiler_environment: Option<&CompilerEnvironment>,
) -> Result<EraseChild, String> {
    let exe = std::env::current_exe().map_err(|e| format!("cannot find this binary: {e}"))?;
    let mut command = Command::new(exe);
    command.arg(ERASE_RUN_FLAG);
    if let Some(environment) = compiler_environment {
        // This selects only the child's restricted dependency checks. It is
        // plain launch data and constructs no import or compiler ownership.
        command.arg(ERASE_COMPILER_ENVIRONMENT_FLAG);
        environment.configure_child(&mut command);
    }
    if !inputs.0.is_empty() || private_output.is_some() {
        let values = serde_json::to_string(&(&inputs.0, private_output))
            .map_err(|error| format!("cannot encode Cargo environment dependencies: {error}"))?;
        command.arg(format!("{ERASE_INPUTS_PREFIX}{values}"));
    }
    let child = command
        .args(args.get(1..).unwrap_or(&[]))
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot start the erase run: {e}"))?;
    let output = child
        .wait_with_output()
        .map_err(|e| format!("cannot read the erase run's output: {e}"))?;
    let mut lines = Vec::new();
    let mut impls = None;
    let mut environment_refusal = None;
    for line in String::from_utf8_lossy(&output.stderr).lines() {
        if let Ok(value) = serde_json::from_str::<serde_json::Value>(line) {
            if value["$message_type"] == ERASE_ENVIRONMENT_REFUSAL_MESSAGE {
                environment_refusal = Some("the erase compiler read an unrepresented or mismatched request environment dependency".to_owned());
                continue;
            }
            if value["$message_type"] == ERASE_IMPLS_MESSAGE {
                impls = serde_json::from_value(value["impls"].clone()).ok();
                continue;
            }
        }
        lines.push(line.to_string());
    }
    Ok(EraseChild {
        code: output.status.code().unwrap_or(101),
        lines,
        impls,
        environment_refusal,
    })
}

fn check_environment_dependencies(
    environment: &CompilerEnvironment,
    session: &rustc_session::Session,
) -> std::io::Result<()> {
    session
        .env_depinfo
        .lock()
        .iter()
        .try_for_each(|(key, value)| {
            environment.check_dependency(key.as_str(), value.as_ref().map(|value| value.as_str()))
        })
}

/// Callbacks of the erase run: a plain compile that lists its crate's
/// impls on stderr once macros are expanded.
struct EraseRun {
    cargo_inputs: CargoInputs,
    private_output: Option<PathBuf>,
    compiler_environment: Option<CompilerEnvironment>,
}

impl Callbacks for EraseRun {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        crate::diagnostic_compat::configure(config);
        self.cargo_inputs.install(config);
        if let Some(directory) = &self.private_output {
            crate::cargo_native::configure(config, directory);
        }
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if let Some(environment) = &self.compiler_environment {
            if let Err(error) = check_environment_dependencies(environment, tcx.sess) {
                eprintln!(
                    "{}",
                    serde_json::json!({
                        "$message_type": ERASE_ENVIRONMENT_REFUSAL_MESSAGE,
                        "permission_from_report": false,
                    })
                );
                tcx.dcx()
                    .struct_err(format!("request environment refused: {error}"))
                    .emit();
                return Compilation::Stop;
            }
        }
        let line = serde_json::json!({
            "$message_type": ERASE_IMPLS_MESSAGE,
            "impls": impl_keys(tcx),
        });
        eprintln!("{line}");
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if let Some(environment) = &self.compiler_environment {
            if let Err(error) = check_environment_dependencies(environment, tcx.sess) {
                eprintln!(
                    "{}",
                    serde_json::json!({
                        "$message_type": ERASE_ENVIRONMENT_REFUSAL_MESSAGE,
                        "permission_from_report": false,
                    })
                );
                tcx.dcx()
                    .struct_err(format!("request environment refused: {error}"))
                    .emit();
                return Compilation::Stop;
            }
        }
        Compilation::Continue
    }
}

/// One impl of a crate, as the two compiles can compare it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ImplKey {
    /// Its trait (or `inherent`) and where it is written: the line and
    /// column of its header and of the outermost macro call that produced
    /// it. The same source compiled twice gives the same text.
    what: String,
    /// The file the header and the call are in.
    file: String,
}

impl ImplKey {
    fn text(&self) -> String {
        format!("{} in {}", self.what, self.file)
    }
}

/// Every impl of the crate ([`ImplKey`]), with its header's span, sorted by
/// key.
fn impls(tcx: TyCtxt<'_>) -> Vec<(ImplKey, Span)> {
    let place = |span: Span| {
        let (file, lo_line, lo_col, _, _) = tcx.sess.source_map().span_to_location_info(span);
        let name = file.map_or_else(
            || "no-location".to_string(),
            |f| f.name.prefer_local_unconditionally().to_string(),
        );
        (format!("{lo_line}:{lo_col}"), name)
    };
    let mut impls: Vec<(ImplKey, Span)> = tcx
        .hir_crate_items(())
        .definitions()
        .filter(|def_id| matches!(tcx.def_kind(*def_id), DefKind::Impl { .. }))
        .map(|def_id| {
            let of_trait = match tcx.hir_expect_item(def_id).kind {
                rustc_hir::ItemKind::Impl(imp) => imp.of_trait,
                _ => None,
            };
            let trait_name = of_trait
                .and_then(|header| header.trait_ref.path.res.opt_def_id())
                .map_or_else(
                    || "an inherent".to_string(),
                    |d| format!("a `{}`", tcx.def_path_str(d)),
                );
            let span = tcx.def_span(def_id);
            let (at, file) = place(span);
            let (from, call_file) = place(span.source_callsite());
            let key = ImplKey {
                what: format!("{trait_name} impl at {at} (made at {from})"),
                file: format!("{file} ({call_file})"),
            };
            (key, span)
        })
        .collect();
    impls.sort_by_key(|(key, _)| key.text());
    impls
}

/// [`impls`] as the erase run lists them.
fn impl_keys(tcx: TyCtxt<'_>) -> Vec<String> {
    impls(tcx).into_iter().map(|(key, _)| key.text()).collect()
}

/// Where the crate's own source first names [`KEEP_GHOST_BODY_CFG`]
/// (in a `cfg`, a `cfg_attr`, a `cfg!` or anywhere else): the source text
/// of every file the crate was read from, before any macro expansion.
fn names_keep_ghost_body(tcx: TyCtxt<'_>) -> Option<Span> {
    let files = tcx.sess.source_map().files();
    files.iter().find_map(|file| {
        if file.cnum != LOCAL_CRATE
            || !matches!(
                file.name,
                FileName::Real(_) | FileName::Anon(_) | FileName::Custom(_)
            )
        {
            return None;
        }
        // A file of the crate whose text is not at hand counts as naming it.
        let Some(src) = file.src.as_ref() else {
            return Some(Span::with_root_ctxt(file.start_pos, file.start_pos));
        };
        let at = src.find(KEEP_GHOST_BODY_CFG)?;
        let lo = file.absolute_position(RelativeBytePos(u32::try_from(at).unwrap_or(0)));
        let len = u32::try_from(KEEP_GHOST_BODY_CFG.len()).unwrap_or(0);
        Some(Span::with_root_ctxt(lo, lo + BytePos(len)))
    })
}

/// The first impl the verify run has more often than the erase run, as a
/// refusal detail at its span, or else the first the erase run has more
/// often, at no span.
fn impl_difference(verified: &[(ImplKey, Span)], erased: &[String]) -> Option<(String, Span)> {
    let mut only_erased: Vec<&String> = erased.iter().collect();
    for (key, span) in verified {
        let text = key.text();
        match only_erased.iter().position(|k| **k == text) {
            Some(i) => {
                only_erased.remove(i);
            }
            None => {
                return Some((
                    format!(
                        "{} is not in the erase run's crate, and Verus's lifetime check sees it",
                        key.what
                    ),
                    *span,
                ))
            }
        }
    }
    only_erased.first().map(|text| {
        let what = text.split(" in ").next().unwrap_or(text);
        (
            format!("{what} is only in the erase run's crate, and Verus's lifetime check does not see it"),
            rustc_span::DUMMY_SP,
        )
    })
}

/// The child process's entry: compile `argv[2..]` as rustc arguments.
fn erase_child_main(argv: &[String]) -> ExitCode {
    let mut rustc_args = vec![argv
        .first()
        .cloned()
        .unwrap_or_else(|| "rust_verify".to_string())];
    let mut remaining = argv.get(2..).unwrap_or(&[]);
    let compiler_environment =
        if remaining.first().map(String::as_str) == Some(ERASE_COMPILER_ENVIRONMENT_FLAG) {
            remaining = &remaining[1..];
            // The real child has the original three values/removals installed by
            // Command. Do not apply the coordinator's absent-process guard here.
            let verdict = std::env::var_os(verdict::VERDICT_DIR_ENV);
            let dump = std::env::var_os(DUMP_VCIR_ENV);
            let verusdoc = std::env::var_os("VERUSDOC");
            match CompilerEnvironment::from_raw(
                verdict.as_deref(),
                dump.as_deref(),
                verusdoc.as_deref(),
            ) {
                Ok(environment) => Some(environment),
                Err(error) => {
                    eprintln!(
                        "{}",
                        serde_json::json!({
                            "$message_type": ERASE_ENVIRONMENT_REFUSAL_MESSAGE,
                            "permission_from_report": false,
                        })
                    );
                    eprintln!(
                        "{}",
                        verdict::crate_refusal_json("request-environment", &error.to_string())
                    );
                    return ExitCode::from(1);
                }
            }
        } else {
            None
        };
    let mut cargo_inputs = CargoInputs::default();
    let mut private_output = None;
    if let Some(values) = remaining
        .first()
        .and_then(|arg| arg.strip_prefix(ERASE_INPUTS_PREFIX))
    {
        match serde_json::from_str(values) {
            Ok((values, output)) => {
                cargo_inputs = CargoInputs(values);
                private_output = output;
            }
            Err(error) => {
                eprintln!(
                    "{}",
                    verdict::crate_refusal_json(
                        TAG_BAD_ARGUMENTS,
                        &format!("invalid erase Cargo inputs: {error}")
                    )
                );
                return ExitCode::from(1);
            }
        }
        remaining = &remaining[1..];
    }
    rustc_args.extend(remaining.iter().cloned());
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(
                &rustc_args,
                &mut EraseRun {
                    cargo_inputs,
                    private_output,
                    compiler_environment,
                },
            )
        })
    }));
    match outcome {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(_)) => ExitCode::from(1),
        Err(_) => ExitCode::from(101),
    }
}

/// Print one crate-level refusal as a JSON diagnostic line on stderr and
/// record it.
fn refuse_crate(record: &mut Record, tag: &str, detail: &str) {
    eprintln!("{}", verdict::crate_refusal_json(tag, detail));
    record
        .crate_refusals
        .push(verdict::refusal_message(tag, detail));
}

/// Print a note as a JSON diagnostic line on stderr. Notes do not affect the
/// harness's assertions.
fn note_json(message: &str) {
    let line = serde_json::json!({
        "$message_type": "diagnostic",
        "message": message,
        "code": null,
        "level": "note",
        "spans": [],
        "children": [],
        "rendered": format!("note: {message}\n\n"),
    });
    eprintln!("{line}");
}

/// Entry point of the `rust_verify` binary.
pub fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().collect();
    if argv.get(1).map(String::as_str) == Some(ERASE_RUN_FLAG) {
        return erase_child_main(&argv);
    }
    // Capture ordinary CLI output data once, before compiler callbacks. Live
    // coordinator requests pass their own OutputSinks instead of reading or
    // changing this process's environment.
    let outputs = OutputSinks::new(
        std::env::var_os(verdict::VERDICT_DIR_ENV).map(PathBuf::from),
        std::env::var_os(DUMP_VCIR_ENV).map(PathBuf::from),
    );
    ExitCode::from(run_with_context(argv, outputs, |key| {
        match std::env::var(key) {
            Ok(value) => Ok(Some(value)),
            Err(std::env::VarError::NotPresent) => Ok(None),
            Err(std::env::VarError::NotUnicode(_)) => Err(format!(
                "Cargo environment variable {key} is not valid Unicode"
            )),
        }
    }))
}

fn run_with_context(
    argv: Vec<String>,
    outputs: OutputSinks,
    environment: impl FnMut(&str) -> Result<Option<String>, String>,
) -> u8 {
    let mut record = Record {
        argv: argv.clone(),
        ..Record::default()
    };
    let invocation = cargo::prepare(&argv, environment);
    let (arguments, cargo_options, cargo_inputs) = match invocation {
        Ok(CargoInvocation::Standalone) => (
            argv.get(1..).unwrap_or(&[]).to_vec(),
            None,
            CargoInputs::default(),
        ),
        Ok(CargoInvocation::Direct {
            args,
            inputs,
            bootstrap,
        }) => return direct_cargo_compile(&argv, args, inputs, bootstrap),
        Ok(CargoInvocation::Verify {
            args,
            options,
            inputs,
        }) => (args, Some(options), inputs),
        Err(problem) => {
            refuse_crate(&mut record, TAG_BAD_ARGUMENTS, &problem);
            record.outcome = Some(Outcome::Refused);
            return finish(record, 1, &outputs);
        }
    };
    let mut split = match args::split(&arguments) {
        Ok(s) => s,
        Err(e) => {
            refuse_crate(&mut record, TAG_BAD_ARGUMENTS, &e.to_string());
            return finish(record, 1, &outputs);
        }
    };
    record.entry_file = split.entry_file().map(PathBuf::from);
    record.output_file = split.output_file().map(PathBuf::from);
    if let Some(options) = &cargo_options {
        let imports = match cargo::imports(&split.rustc, options) {
            Ok(imports) => imports,
            Err(problem) => {
                refuse_crate(&mut record, "cargo-import", &problem);
                record.outcome = Some(Outcome::Refused);
                return finish(record, 1, &outputs);
            }
        };
        for (name, path) in imports {
            // A real sidecar is still subject to the native import gate. Its
            // presence alone never authorizes a contract or a proof.
            split.verus.push(args::VerusOption {
                name: "import".to_string(),
                value: Some(format!("{name}={}", path.display())),
            });
        }
        enable_cargo_bootstrap();
    }
    record.verus_options = split
        .verus
        .iter()
        .map(|o| (o.name.clone(), o.value.clone()))
        .collect();

    if let Some((tag, detail)) = unsupported_request(&split, cargo_options.is_some()) {
        refuse_crate(&mut record, tag, &detail);
        record.outcome = Some(Outcome::Refused);
        return finish(record, 1, &outputs);
    }

    let program = argv
        .first()
        .cloned()
        .unwrap_or_else(|| "rust_verify".to_string());
    let cargo_compile = cargo_options
        .as_ref()
        .is_some_and(|options| options.compile || split.has("compile"));
    let invocation = match NormalInvocation::derive(program, split) {
        Ok(invocation) => invocation,
        Err(reason) => {
            refuse_crate(&mut record, TAG_BAD_ARGUMENTS, &reason);
            record.outcome = Some(Outcome::Refused);
            return finish(record, 1, &outputs);
        }
    };
    let mut opts = invocation.options();
    let mut scratch = None;
    if cargo_options.is_some() {
        opts.cargo = true;
        opts.cargo_inputs = cargo_inputs.clone();
        opts.erase_compile = cargo_compile;
        {
            let private = match cargo::Scratch::new() {
                Ok(private) => private,
                Err(error) => {
                    refuse_crate(
                        &mut record,
                        TAG_ERASE_RUN,
                        &format!("cannot create private Cargo outputs: {error}"),
                    );
                    record.outcome = Some(Outcome::Refused);
                    return finish(record, 1, &outputs);
                }
            };
            opts.private_output = Some(private.path().join("verify"));
            scratch = Some(private);
        }
    }
    let mut callbacks = VerifyRun::new(opts, outputs.clone());
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(invocation.verify(), &mut callbacks)
        })
    }));

    record.functions = std::mem::take(&mut callbacks.functions);
    record
        .crate_refusals
        .extend(std::mem::take(&mut callbacks.crate_refusals));
    record.erase_exit = callbacks.erase_exit;
    record.outcome = callbacks.outcome;

    let mut code = match outcome {
        Err(_) => {
            refuse_crate(&mut record, TAG_INTERNAL_ERROR, "the compiler panicked");
            record.outcome = Some(Outcome::Refused);
            101
        }
        Ok(result) => {
            if !callbacks.reached {
                refuse_crate(
                    &mut record,
                    TAG_FRONT_END_ERROR,
                    "the compiler stopped before macro expansion finished",
                );
                record.outcome = Some(Outcome::Refused);
            } else if result.is_err() && callbacks.reading {
                // A fatal error raised by one of trust-vc's own queries: what
                // was left unread is not a rejection of the program.
                refuse_crate(
                    &mut record,
                    TAG_INTERNAL_ERROR,
                    "the compiler stopped with a fatal error while trust-vc read the crate",
                );
                record.outcome = Some(Outcome::Refused);
            } else if result.is_err() && record.outcome.is_none() {
                // A fatal error in rustc's own checking (a query cycle, for
                // one): the program is rejected, as it is under Verus.
                record.outcome = Some(Outcome::FrontEndRejected);
            }
            // Refusals are errors, so a run that refused anything has already
            // failed; the check on `any_refused` keeps that true if a refusal
            // is ever reported some other way.
            // A successful explicit Cargo skip remains a non-verification in
            // the record. This exception never covers another refusal, an
            // unread function, or a native compiler/ownership/mode error.
            let explicit_cargo_skip = cargo_options.is_some()
                && record.outcome == Some(Outcome::VerificationSkipped)
                && record.crate_refusals.is_empty()
                && record
                    .functions
                    .iter()
                    .all(|function| match function.verdict {
                        Verdict::Skipped => function.tag.as_deref() == Some(TAG_NO_VERIFY),
                        Verdict::External | Verdict::Declared => true,
                        _ => false,
                    });
            if result.is_ok()
                && !callbacks.failed_elsewhere
                && (!record.any_refused() || explicit_cargo_skip)
            {
                0
            } else {
                1
            }
        }
    };
    if code == 0 && cargo_compile {
        // The earlier erase compile was speculative and private. Only a
        // completed verification (or explicit recorded --no-verify skip)
        // can now emit Cargo's requested public artifacts.
        match run_erase_child(invocation.erase(), &cargo_inputs, None, None) {
            Ok(child) => {
                print_lines(&child.lines);
                if child.code != 0 {
                    code = if child.code == 101 { 101 } else { 1 };
                    record.outcome = Some(Outcome::EraseRejected);
                    for function in &mut record.functions {
                        if function.verdict != Verdict::External {
                            function.verdict = Verdict::Rejected;
                            function.tag = None;
                            function.sites = None;
                        }
                    }
                }
            }
            Err(problem) => {
                refuse_crate(&mut record, TAG_ERASE_RUN, &problem);
                record.outcome = Some(Outcome::Refused);
                code = 1;
            }
        }
    }
    drop(scratch);
    finish(record, code, &outputs)
}

/// Called at the single-threaded binary entry, before starting rustc's worker
/// threads. Verus's builtin/proc-macro crates require these unstable features.
fn enable_cargo_bootstrap() {
    // SAFETY: no compiler or other worker thread has been started by main.
    unsafe { std::env::set_var("RUSTC_BOOTSTRAP", "1") };
}

fn direct_cargo_compile(
    argv: &[String],
    args: Vec<String>,
    inputs: CargoInputs,
    bootstrap: bool,
) -> u8 {
    struct DirectRun(CargoInputs);
    impl Callbacks for DirectRun {
        fn config(&mut self, config: &mut rustc_interface::interface::Config) {
            self.0.install(config);
        }
    }
    if bootstrap {
        enable_cargo_bootstrap();
    }
    let mut compiler_args = vec![argv
        .first()
        .cloned()
        .unwrap_or_else(|| "rust_verify".to_string())];
    compiler_args.extend(args);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        rustc_driver::catch_fatal_errors(|| {
            rustc_driver::run_compiler(&compiler_args, &mut DirectRun(inputs))
        })
    }));
    // This is ordinary compiler work, not a verification. Do not write a
    // proof-success record for a probe, build script or unselected dependency.
    match outcome {
        Ok(Ok(())) => 0,
        Ok(Err(_)) => 1,
        Err(_) => 101,
    }
}

/// Write the verdict record and retain the actual numeric exit status.
fn finish(mut record: Record, code: u8, outputs: &OutputSinks) -> u8 {
    record.exit_code = Some(i32::from(code));
    for problem in record.write_to(outputs) {
        note_json(&format!(
            "trust-vc: could not write verdict record: {problem}"
        ));
    }
    code
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `e` (lines 21-24) is skipped, `f` (line 27) is checked.
    fn scope() -> LifetimeScope {
        LifetimeScope {
            checked: vec![("t.rs".to_string(), 27, 27)],
            skipped: vec![("t.rs".to_string(), 21, 24)],
        }
    }

    /// A JSON span at `line`, produced by macro calls at `calls` (innermost
    /// first).
    fn span(line: u64, calls: &[u64]) -> serde_json::Value {
        let mut expansion = serde_json::Value::Null;
        for call in calls.iter().rev() {
            expansion = serde_json::json!({
                "span": { "file_name": "t.rs", "line_start": call, "line_end": call,
                          "expansion": expansion },
                "macro_decl_name": "mk!",
            });
        }
        serde_json::json!({
            "file_name": "t.rs", "line_start": line, "line_end": line,
            "is_primary": true, "expansion": expansion,
        })
    }

    fn error(spans: Vec<serde_json::Value>) -> String {
        serde_json::json!({ "level": "error", "message": "use of moved value: `s`", "spans": spans })
            .to_string()
    }

    #[test]
    fn plain_error_inside_a_skipped_function_is_held() {
        assert_eq!(scope().classify(&error(vec![span(23, &[])])), Some(true));
        assert_eq!(scope().classify(&error(vec![span(27, &[])])), Some(false));
    }

    #[test]
    fn macro_error_is_placed_at_its_outermost_call() {
        // Written in `e`, called in `f`: Verus's lifetime check reports it.
        assert_eq!(scope().classify(&error(vec![span(23, &[27])])), Some(false));
        // Written in `e`, called in `e`.
        assert_eq!(scope().classify(&error(vec![span(23, &[22])])), Some(true));
        // Written outside every function, called in `e`, or in `f`.
        assert_eq!(scope().classify(&error(vec![span(10, &[22])])), Some(true));
        assert_eq!(scope().classify(&error(vec![span(10, &[27])])), Some(false));
        // Two macros: the outer one called in `f`, or in `e`.
        assert_eq!(
            scope().classify(&error(vec![span(23, &[24, 27])])),
            Some(false)
        );
        assert_eq!(
            scope().classify(&error(vec![span(23, &[10, 22])])),
            Some(true)
        );
    }

    #[test]
    fn a_chain_touching_a_checked_function_is_not_held() {
        // Written on `f`'s line, called in `e`.
        assert_eq!(scope().classify(&error(vec![span(27, &[22])])), Some(false));
        // Passing through a macro written on `f`'s line.
        assert_eq!(
            scope().classify(&error(vec![span(23, &[27, 22])])),
            Some(false)
        );
    }

    #[test]
    fn an_unreadable_chain_or_line_is_not_held() {
        let mut broken = span(23, &[]);
        broken["expansion"] = serde_json::json!({ "macro_decl_name": "mk!" });
        assert_eq!(scope().classify(&error(vec![broken])), Some(false));
        let mut no_line = span(23, &[22]);
        no_line["expansion"]["span"]["line_start"] = serde_json::Value::Null;
        assert_eq!(scope().classify(&error(vec![no_line])), Some(false));
        assert_eq!(scope().classify("not json"), Some(false));
        assert_eq!(scope().classify(&error(vec![])), Some(false));
    }

    #[test]
    fn every_primary_span_must_be_held() {
        let two = error(vec![span(23, &[]), span(23, &[27])]);
        assert_eq!(scope().classify(&two), Some(false));
        let two = error(vec![span(23, &[]), span(22, &[])]);
        assert_eq!(scope().classify(&two), Some(true));
    }

    #[test]
    fn warnings_and_the_summary_are_not_errors() {
        let warning = serde_json::json!({ "level": "warning", "message": "w", "spans": [] });
        assert_eq!(scope().classify(&warning.to_string()), None);
        let summary = serde_json::json!({
            "level": "error", "message": "aborting due to 1 previous error", "spans": [],
        });
        assert_eq!(scope().classify(&summary.to_string()), None);
    }

    fn split(args: &[&str]) -> SplitArgs {
        let mut argv: Vec<String> = vec!["--internal-test-mode".to_string()];
        argv.extend(args.iter().map(|a| (*a).to_string()));
        argv.push("test.rs".to_string());
        args::split(&argv).expect("argv")
    }

    #[test]
    fn verus_argument_errors_are_found() {
        for bad in [
            &["--compile", "--no-erasure-check"][..],
            &["--triggers", "--triggers-mode", "silent"],
            &["--triggers-mode", "loud"],
            &["--profile", "--profile-all", "--verify-root"],
            &["--profile", "-V", "capture-profiles"],
            &["--profile-all"],
            &["--num-threads", "abc"],
        ] {
            assert!(argument_error(&split(bad)).is_some(), "{bad:?}");
        }
        for good in [
            &["--compile"][..],
            &["--no-erasure-check"],
            &["--triggers-mode", "verbose-all-modules"],
            &["--profile"],
            &["--profile-all", "--verify-root"],
            &["--num-threads", "4"],
        ] {
            assert!(argument_error(&split(good)).is_none(), "{good:?}");
        }
    }

    #[test]
    fn erasure_options_choose_the_checks() {
        let opts = |args: &[&str]| {
            let o = RunOptions::from_split(&split(args), vec!["rust_verify".to_string()]).unwrap();
            (o.erase_args.is_some(), o.lifetime_check, o.erase_compile)
        };
        assert_eq!(opts(&[]), (true, true, true));
        assert_eq!(opts(&["--no-erasure-check"]), (true, true, false));
        assert_eq!(opts(&["--no-lifetime"]), (false, false, false));
        assert_eq!(opts(&["--no-lifetime", "--compile"]), (true, false, true));
    }

    fn key(what: &str) -> (ImplKey, Span) {
        let key = ImplKey {
            what: what.to_string(),
            file: "t.rs (t.rs)".to_string(),
        };
        (key, rustc_span::DUMMY_SP)
    }

    #[test]
    fn impls_of_one_compile_only_are_found() {
        let both = [key("a `Drop` impl at 3:1 (made at 3:1)")];
        let listed =
            |keys: &[(ImplKey, Span)]| keys.iter().map(|(k, _)| k.text()).collect::<Vec<_>>();
        assert!(impl_difference(&both, &listed(&both)).is_none());
        let verified = [
            key("a `Drop` impl at 3:1 (made at 3:1)"),
            key("an inherent impl at 9:1 (made at 9:1)"),
        ];
        let (detail, _) = impl_difference(&verified, &listed(&both)).expect("verify run only");
        assert!(detail.starts_with("an inherent impl at 9:1"), "{detail}");
        let (detail, _) = impl_difference(&both, &listed(&verified)).expect("erase run only");
        assert!(detail.starts_with("an inherent impl at 9:1"), "{detail}");
        // The same impl twice (one macro called twice) must be there twice.
        let twice = [
            key("a `Drop` impl at 3:1 (made at 3:1)"),
            key("a `Drop` impl at 3:1 (made at 3:1)"),
        ];
        assert!(impl_difference(&twice, &listed(&both)).is_some());
        assert!(impl_difference(&both, &listed(&twice)).is_some());
    }
}
