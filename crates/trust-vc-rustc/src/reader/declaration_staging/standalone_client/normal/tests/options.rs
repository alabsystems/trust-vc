// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Genuine option-sensitive reads, with separate logical and runtime references.

use super::*;
use crate::reader::FnStatus;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use trust_vc_vcir::{Body, FnRole, Mode, Ty};

fn named_local(tcx: TyCtxt<'_>, name: &str) -> Option<LocalDefId> {
    let items = tcx.hir_crate_items(());
    let mut matches = items.owners().filter_map(|owner| {
        (matches!(tcx.def_kind(owner.def_id), DefKind::Fn | DefKind::AssocFn)
            && tcx.item_name(owner.def_id.to_def_id()).as_str() == name)
            .then_some(owner.def_id)
    });
    let result = matches.next();
    assert!(
        matches.next().is_none(),
        "fixture declaration {name} must be unique"
    );
    result
}

fn logical_reference_is_read(tcx: TyCtxt<'_>, read: &crate::reader::CrateRead) -> bool {
    let Some(original) = named_local(tcx, "reference_option") else {
        return false;
    };
    read.fns.iter().any(|function| {
        if function.def_id != original {
            return false;
        }
        let FnStatus::Read(id) = &function.status else {
            return false;
        };
        let Some(declaration) = read
            .krate
            .fns
            .iter()
            .find(|declaration| declaration.id == *id)
        else {
            return false;
        };
        let [parameter] = declaration.params.as_slice() else {
            return false;
        };
        declaration.role == FnRole::Item
            && declaration.mode == Mode::Spec
            && declaration
                .locals
                .get(parameter.index())
                .is_some_and(|local| {
                    local.mode == Mode::Spec && local.ty == Ty::MutRef(Box::new(Ty::uint(8)))
                })
            && matches!(&declaration.body, Body::Spec(value) if value.ty == Ty::Bool)
    })
}

#[derive(Debug, Default)]
struct ReadSummary {
    external: bool,
    outside: bool,
    old_mut: bool,
    new_mut: bool,
    logical_reference: bool,
    imported: usize,
    records: String,
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
                new_mut: read.fns.iter().any(|f| {
                    Some(f.def_id) == named_local(tcx, "runtime_reference_option")
                        && matches!(&f.status, FnStatus::Refused(r) if r.tag == "new-mut-ref")
                }),
                logical_reference: logical_reference_is_read(tcx, read),
                imported: read
                    .krate
                    .fns
                    .iter()
                    .filter(|f| f.role == trust_vc_vcir::FnRole::Imported)
                    .count(),
                records: read
                    .fns
                    .iter()
                    .map(|function| {
                        format!(
                            "{:?}: {} => {:?}",
                            function.def_id, function.def_path, function.status
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n"),
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

pub(super) fn nondefault_options() {
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
            let mutable = client_source(root, "mutable", &format!("verus! {{ {IMPORTED}\nspec fn reference_option(x: &mut u8) -> bool {{ true }}\nfn runtime_reference_option(_x: &mut u8) {{}} }}"));
            let default = observe(owner, &mutable, root, "OldMutRead", &[]);
            let enabled = observe(owner, &mutable, root, "NewMutRead", &["-V", "new-mut-ref"]);
            assert!(
                default.old_mut && !default.new_mut,
                "{default:?}\n{}",
                default.records
            );
            assert!(
                !default.logical_reference,
                "{default:?}\n{}",
                default.records
            );
            assert!(
                enabled.new_mut && !enabled.old_mut && enabled.imported > 0,
                "{enabled:?}\n{}",
                enabled.records
            );
            assert!(
                enabled.logical_reference,
                "{enabled:?}\n{}",
                enabled.records
            );
        },
    );
}
