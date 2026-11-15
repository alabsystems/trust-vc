// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Each ignored control owns one exact standalone test process and a fresh
//! genuine producer. No fake read, compiler context or successful receipt.

use super::*;
use crate::args;
use crate::reader::FnStatus;
use crate::shim::NormalInvocation;

fn dedicated(name: &str) {
    let module = module_path!().split_once("::").unwrap().1;
    let expected = format!("{module}::{name}");
    let argv = std::env::args().skip(1).collect::<Vec<_>>();
    for required in [
        expected.as_str(),
        "--exact",
        "--ignored",
        "--test-threads=1",
    ] {
        assert_eq!(argv.iter().filter(|s| s.as_str() == required).count(), 1);
    }
    assert!(argv.iter().all(|s| [
        expected.as_str(),
        "--exact",
        "--ignored",
        "--test-threads=1",
        "--nocapture"
    ]
    .contains(&s.as_str())));
    assert_eq!(std::env::var("VSTD_KIND").as_deref(), Ok("IsVstd"));
}

fn with_owner(name: &str, action: impl FnOnce(&StandaloneImported<'_>, &Path)) {
    dedicated(name);
    let template = std::path::PathBuf::from(
        std::env::var_os("TRUST_VC_NORMAL_OPTIONS_REQUEST")
            .expect("fresh genuine @2 request template"),
    );
    let mut request: Value = serde_json::from_slice(&std::fs::read(template).unwrap()).unwrap();
    assert_eq!(
        request["schema"],
        "trust-vc.native-declaration-staging-request@2"
    );
    assert!(request.get("builtin").is_none() && request.get("macros").is_none());
    let root = std::env::temp_dir().join(format!(
        "trust-vc-normal-options-{}-{name}",
        std::process::id()
    ));
    std::fs::create_dir(&root).unwrap();
    let root = root.canonicalize().unwrap();
    request["output"] = json!(root.join("staging"));
    let path = root.join("request.json");
    std::fs::write(&path, serde_json::to_vec_pretty(&request).unwrap()).unwrap();
    let library = produce(&path).unwrap();
    library.write_observation().unwrap();
    // SAFETY: dedicated exact process; this is its only test, every genuine
    // producer compiler has returned/joined, and no engine work has started.
    // This one-way transition remains Imported through process termination.
    let owner = unsafe { StandaloneImported::enter(&library).unwrap() };
    action(&owner, &root);
    owner.check_retained_inputs().unwrap();
}

fn client_source(root: &Path, name: &str, body: &str) -> ClientSource {
    let path = root.join(format!("{name}.rs"));
    let text = format!("#![feature(sized_hierarchy)]\nuse verus_builtin::*;\nuse verus_builtin_macros::*;\nextern crate vstd;\n{body}\n");
    std::fs::write(&path, text).unwrap();
    ClientSource::read(&path).unwrap()
}

fn request(
    owner: &StandaloneImported<'_>,
    source: &ClientSource,
    output: &Path,
    options: &[&str],
) -> NormalInvocation {
    let mut argv = vec![
        "--crate-type=lib".to_string(),
        "--crate-name=owned_option_client".to_string(),
        "--emit=metadata".to_string(),
        "--error-format=json".to_string(),
        "-Zunstable-options".to_string(),
    ];
    let library = owner.library();
    argv.extend([
        "--sysroot".into(),
        library
            .prepared
            .erase
            .invocation
            .sysroot()
            .display()
            .to_string(),
    ]);
    for directory in owner.native_dependency_directories().unwrap() {
        argv.extend(["-L".into(), format!("dependency={}", directory.display())]);
    }
    argv.extend([
        "--extern".into(),
        format!("vstd={}", library.prepared.erase.file.path.display()),
    ]);
    argv.extend([
        "--extern".into(),
        format!(
            "force:verus_builtin={}",
            library.inputs.builtin.path.display()
        ),
    ]);
    for file in owner.macro_files() {
        let name = file
            .path
            .file_stem()
            .unwrap()
            .to_str()
            .unwrap()
            .strip_prefix("lib")
            .unwrap();
        argv.extend([
            "--extern".into(),
            format!("force:{name}={}", file.path.display()),
        ]);
    }
    argv.extend([
        "-o".into(),
        output.display().to_string(),
        source.file().path.display().to_string(),
    ]);
    argv.extend(options.iter().map(|s| s.to_string()));
    NormalInvocation::derive("owned-option-client".into(), args::split(&argv).unwrap()).unwrap()
}

const IMPORTED: &str =
    "proof fn imported_control<A>(s: vstd::set::Set<A>) { assert(s.len() as int >= 0); }";

#[derive(Default)]
struct ReadSummary {
    external: bool,
    outside: bool,
    old_mut: bool,
    new_mut: bool,
    imported: usize,
}
struct ReadClient<'a> {
    owner: &'a StandaloneImported<'a>,
    source: &'a ClientSource,
    plan: &'a macro_context::NormalClientPlan<'a>,
    verifier: OwnedNormalVerifier<'a, 'a>,
    summary: Option<ReadSummary>,
}
impl Callbacks for ReadClient<'_> {
    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let preparation = self
            .verifier
            .after_expansion(tcx)
            .expect("genuine normal HIR preparation");
        let imports = self.owner.for_client(tcx, self.plan.verify()).unwrap();
        let live = imports
            .read_for_normal_verification(&preparation, self.source)
            .unwrap();
        self.summary = Some(live.with_read(|_, read| {
            ReadSummary {
                external: read.fns.iter().any(|f| {
                    f.def_path.ends_with("outside") && matches!(f.status, FnStatus::External)
                }),
                outside: read
                    .pending_item_refusals
                    .iter()
                    .any(|r| r.tag == "external-by-default"),
                old_mut: read
                    .errors
                    .iter()
                    .any(|e| e.message == crate::messages::MUT_REF_PARAM_SPEC_FN),
                new_mut: read
                    .fns
                    .iter()
                    .any(|f| matches!(&f.status, FnStatus::Refused(r) if r.tag == "new-mut-ref")),
                imported: read
                    .krate
                    .fns
                    .iter()
                    .filter(|f| f.role == trust_vc_vcir::FnRole::Imported)
                    .count(),
            }
        }));
        Compilation::Stop
    }
}

fn observe(
    owner: &StandaloneImported<'_>,
    source: &ClientSource,
    root: &Path,
    name: &str,
    flags: &[&str],
) -> ReadSummary {
    let invocation = request(owner, source, &root.join(format!("{name}.rmeta")), flags);
    let plan = macro_context::NormalClientPlan::from_invocation(owner, source, invocation).unwrap();
    let mut callback = ReadClient {
        owner,
        source,
        plan: &plan,
        verifier: OwnedNormalVerifier::new(&plan),
        summary: None,
    };
    let result = run_compiler(plan.verify(), &mut callback);
    record_phase(
        &owner.library().inputs,
        name,
        &result,
        callback
            .summary
            .as_ref()
            .map(|_| Ok::<_, String>(()))
            .as_ref(),
    )
    .unwrap();
    result.unwrap();
    owner.check_retained_inputs().unwrap();
    callback.summary.unwrap()
}

#[test]
#[ignore = "requires a dedicated exact process and a fresh genuine @2 producer"]
fn actual_owned_reader_uses_the_invocations_nondefault_options() {
    with_owner(
        "actual_owned_reader_uses_the_invocations_nondefault_options",
        |owner, root| {
            let outside = client_source(
                root,
                "outside",
                &format!("fn outside() {{}}\nverus! {{ {IMPORTED} }}"),
            );
            let default = observe(owner, &outside, root, "DefaultRead", &[]);
            let enabled = observe(
                owner,
                &outside,
                root,
                "NoExternalRead",
                &["--no-external-by-default"],
            );
            assert!(default.external && !default.outside && default.imported > 0);
            assert!(!enabled.external && enabled.outside && enabled.imported == default.imported);
            let mutable = client_source(root, "mutable", &format!("verus! {{ {IMPORTED}\nspec fn reference_option(x: &mut u8) -> bool {{ true }} }}"));
            let default = observe(owner, &mutable, root, "OldMutRead", &[]);
            let enabled = observe(owner, &mutable, root, "NewMutRead", &["-V", "new-mut-ref"]);
            assert!(default.old_mut && !default.new_mut);
            assert!(enabled.new_mut && !enabled.old_mut && enabled.imported > 0);
        },
    );
}

struct ScopeClient<'a> {
    owner: &'a StandaloneImported<'a>,
    source: &'a ClientSource,
    first: &'a macro_context::NormalClientPlan<'a>,
    second: &'a macro_context::NormalClientPlan<'a>,
    checked: bool,
}
impl Callbacks for ScopeClient<'_> {
    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut first = OwnedNormalVerifier::new(self.first);
        let mut different_options = OwnedNormalVerifier::new(self.second);
        let mut same_plan = OwnedNormalVerifier::new(self.first);
        let preparation = first.after_expansion(tcx).unwrap();
        let mut other = different_options.after_expansion(tcx).unwrap();
        let mut duplicate = same_plan.after_expansion(tcx).unwrap();
        let imports = self.owner.for_client(tcx, self.first.verify()).unwrap();
        let live = imports
            .read_for_normal_verification(&preparation, self.source)
            .unwrap();
        assert!(!live.matches_preparation(tcx, other.binding()));
        assert!(!live.matches_preparation(tcx, duplicate.binding()));
        assert!(other
            .decide(&live)
            .unwrap_err()
            .contains("another invocation or verifier preparation"));
        assert!(duplicate
            .decide(&live)
            .unwrap_err()
            .contains("another invocation or verifier preparation"));
        assert!(live.matches_preparation(tcx, preparation.binding()));
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
#[ignore = "requires a dedicated exact process and a fresh genuine @2 producer"]
fn actual_same_context_reads_cannot_cross_options_or_verifier_identity() {
    with_owner(
        "actual_same_context_reads_cannot_cross_options_or_verifier_identity",
        |owner, root| {
            let source = client_source(root, "identity", &format!("verus! {{ {IMPORTED} }}"));
            let first = macro_context::NormalClientPlan::from_invocation(
                owner,
                &source,
                request(owner, &source, &root.join("first.rmeta"), &[]),
            )
            .unwrap();
            let second = macro_context::NormalClientPlan::from_invocation(
                owner,
                &source,
                request(owner, &source, &root.join("first.rmeta"), &["--no-verify"]),
            )
            .unwrap();
            let mut callback = ScopeClient {
                owner,
                source: &source,
                first: &first,
                second: &second,
                checked: false,
            };
            run_compiler(first.verify(), &mut callback).unwrap();
            assert!(callback.checked);
            let mismatched = macro_context::NormalClientPlan::from_invocation(
                owner,
                &source,
                request(
                    owner,
                    &source,
                    &root.join("first.rmeta"),
                    &["--cfg", "native_option_probe"],
                ),
            )
            .unwrap();
            let mut mismatch = NativeMismatchClient {
                plan: &mismatched,
                verifier: OwnedNormalVerifier::new(&mismatched),
                checked: false,
                reason: None,
            };
            let result = run_compiler(first.verify(), &mut mismatch);
            let rejection = mismatch.reason.clone().map(Err::<(), String>);
            record_phase(
                &owner.library().inputs,
                "ActualNativeCfgMismatch",
                &result,
                rejection.as_ref(),
            )
            .unwrap();
            assert!(result.is_err() && mismatch.checked);
            let record = mismatch.verifier.into_record(root.join("mismatch.rmeta"));
            assert_eq!(record.outcome, Some(Outcome::Refused));
            assert!(record
                .crate_refusals
                .iter()
                .any(|r| r.contains("owned-native-invocation") && r.contains("cfg")));
        },
    );
}

struct NativeMismatchClient<'a> {
    plan: &'a macro_context::NormalClientPlan<'a>,
    verifier: OwnedNormalVerifier<'a, 'a>,
    checked: bool,
    reason: Option<String>,
}
impl Callbacks for NativeMismatchClient<'_> {
    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        rustc_hir_analysis::check_crate(tcx);
        assert!(tcx.dcx().has_errors().is_none());
        let reason = self.plan.check_native_context(tcx).unwrap_err();
        assert!(reason.contains("cfg"));
        self.reason = Some(reason);
        assert!(self.verifier.after_expansion(tcx).is_none());
        self.checked = true;
        Compilation::Stop
    }
}

struct NativeOptionsMatchClient<'a> {
    plan: &'a macro_context::NormalClientPlan<'a>,
    checked: bool,
}
impl Callbacks for NativeOptionsMatchClient<'_> {
    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        rustc_hir_analysis::check_crate(tcx);
        assert!(tcx.dcx().has_errors().is_none());
        assert!(!tcx.sess.opts.unstable_opts.no_leak_check);
        self.plan.check_native_context(tcx).unwrap();
        self.checked = true;
        Compilation::Stop
    }
}

struct NativeNoLeakCheckClient<'a> {
    plan: &'a macro_context::NormalClientPlan<'a>,
    verifier: OwnedNormalVerifier<'a, 'a>,
    checked: bool,
    reason: Option<String>,
}
impl Callbacks for NativeNoLeakCheckClient<'_> {
    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        rustc_hir_analysis::check_crate(tcx);
        assert!(tcx.dcx().has_errors().is_none());
        assert!(tcx.sess.opts.unstable_opts.no_leak_check);
        let reason = self.plan.check_native_context(tcx).unwrap_err();
        assert!(reason.contains("unstable_opts.no_leak_check"));
        self.reason = Some(reason);
        assert!(self.verifier.after_expansion(tcx).is_none());
        self.checked = true;
        Compilation::Stop
    }
}

#[test]
#[ignore = "requires a dedicated exact process and a fresh genuine @2 producer"]
fn actual_same_source_native_no_leak_check_cannot_match_the_owned_plan() {
    with_owner(
        "actual_same_source_native_no_leak_check_cannot_match_the_owned_plan",
        |owner, root| {
            let source = client_source(root, "native_options", &format!("verus! {{ {IMPORTED} }}"));
            let plan = macro_context::NormalClientPlan::from_invocation(
                owner,
                &source,
                request(owner, &source, &root.join("native_options.rmeta"), &[]),
            )
            .unwrap();
            let mut matched = NativeOptionsMatchClient {
                plan: &plan,
                checked: false,
            };
            run_compiler(plan.verify(), &mut matched).unwrap();
            assert!(matched.checked);
            // The sealed owned request does not support this option. Deliberately
            // perturb the *actual* compiler session while preserving that same
            // plan, source, native entry, cfg, output and CStore/image ownership.
            let mut split = plan.invocation().original().unwrap().clone();
            split.rustc.push("-Zno-leak-check".into());
            let unsupported =
                NormalInvocation::derive("owned-option-client".into(), split).unwrap();
            assert!(
                macro_context::NormalClientPlan::from_invocation(owner, &source, unsupported)
                    .is_err()
            );
            let mut actual_args = plan.verify().to_vec();
            actual_args.push("-Zno-leak-check".into());
            let mut mismatch = NativeNoLeakCheckClient {
                plan: &plan,
                verifier: OwnedNormalVerifier::new(&plan),
                checked: false,
                reason: None,
            };
            let result = run_compiler(&actual_args, &mut mismatch);
            let rejection = mismatch.reason.clone().map(Err::<(), String>);
            record_phase(
                &owner.library().inputs,
                "ActualNativeNoLeakCheckMismatch",
                &result,
                rejection.as_ref(),
            )
            .unwrap();
            assert!(result.is_err() && mismatch.checked);
            let record = mismatch
                .verifier
                .into_record(root.join("native_options_rejected.rmeta"));
            assert_eq!(record.outcome, Some(Outcome::Refused));
            assert!(record
                .crate_refusals
                .iter()
                .any(|r| r.contains("owned-native-invocation")
                    && r.contains("unstable_opts.no_leak_check")));
        },
    );
}

#[test]
#[ignore = "requires a dedicated exact process and a fresh genuine @2 producer"]
fn actual_request_binding_and_lifetime_options_keep_the_normal_gates() {
    with_owner(
        "actual_request_binding_and_lifetime_options_keep_the_normal_gates",
        |owner, root| {
            let source = client_source(
                root,
                "lifetime",
                &format!("verus! {{ {IMPORTED}\nproof fn local_control() {{ assert(true); }} }}"),
            );
            let original = request(owner, &source, &root.join("bad.rmeta"), &[]);
            let mut wrong = original.original().unwrap().clone();
            let extern_arg = wrong
                .rustc
                .iter_mut()
                .find(|s| s.starts_with("vstd="))
                .unwrap();
            *extern_arg = format!("vstd={}", root.join("unowned.rmeta").display());
            let wrong = NormalInvocation::derive("owned-option-client".into(), wrong).unwrap();
            assert!(
                macro_context::NormalClientPlan::from_invocation(owner, &source, wrong).is_err()
            );
            let response = root.join("unretained.args");
            std::fs::write(
                &response,
                "--cfg hidden_native_flag\n--emit=metadata=unowned.rmeta\n",
            )
            .unwrap();
            for hidden in [
                vec![format!("--emit=metadata={}", source.file().path.display())],
                vec![format!("@{}", response.display())],
                vec!["-A".to_string(), format!("@{}", response.display())],
                vec![format!("--out-dir={}", root.display())],
                vec!["--unknown-native-output-option=unowned".to_string()],
            ] {
                let original = request(owner, &source, &root.join("hidden.rmeta"), &[]);
                let mut split = original.original().unwrap().clone();
                split.rustc.extend(hidden);
                let hidden = NormalInvocation::derive("owned-option-client".into(), split).unwrap();
                assert!(
                    macro_context::NormalClientPlan::from_invocation(owner, &source, hidden)
                        .is_err()
                );
                source.file().read().unwrap();
            }
            let other = client_source(root, "other-source", &format!("verus! {{ {IMPORTED} }}"));
            assert!(macro_context::NormalClientPlan::from_invocation(
                owner,
                &other,
                request(owner, &source, &root.join("wrong-source.rmeta"), &[])
            )
            .is_err());
            let output = root.join("no-lifetime.rmeta");
            let plan = macro_context::NormalClientPlan::from_invocation(
                owner,
                &source,
                request(owner, &source, &output, &["--no-lifetime"]),
            )
            .unwrap();
            assert!(verify_plan(owner, &source, "NoLifetime", &plan, output).unwrap());
            let output = root.join("no-verify.rmeta");
            let plan = macro_context::NormalClientPlan::from_invocation(
                owner,
                &source,
                request(owner, &source, &output, &["--no-verify"]),
            )
            .unwrap();
            assert!(!verify_plan(owner, &source, "NoVerify", &plan, output).unwrap());
            let report: Value = serde_json::from_slice(
                &std::fs::read(owner.library().inputs.output.join("NoVerify.json")).unwrap(),
            )
            .unwrap();
            assert!(report["normal_verdict"]["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|f| f["verdict"] != "verified"));
            assert_eq!(report["publication"], "NoSuccessfulPublication");
            assert_eq!(report["imported_verified_functions"], 0);
            let tracked = client_source(root, "tracked", &format!("verus! {{ {IMPORTED}\nproof fn consume<A>(tracked a: A) {{}}\nproof fn check<A>(tracked a: A) {{ consume(a); }} }}"));
            let output = root.join("tracked-no-lifetime.rmeta");
            let plan = macro_context::NormalClientPlan::from_invocation(
                owner,
                &tracked,
                request(owner, &tracked, &output, &["--no-lifetime"]),
            )
            .unwrap();
            assert!(!verify_plan(owner, &tracked, "TrackedNoLifetime", &plan, output).unwrap());
            let report: Value = serde_json::from_slice(
                &std::fs::read(owner.library().inputs.output.join("TrackedNoLifetime.json"))
                    .unwrap(),
            )
            .unwrap();
            assert!(report["original_native_ownership_roots"].as_u64().unwrap() > 0);
            assert_eq!(report["publication"], "NoSuccessfulPublication");
            assert!(report["normal_verdict"]["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|f| f["verdict"] != "verified"));
        },
    );
}
