//! Atomic admission after a successful actual helper transaction.

use super::*;
use rustc_hir::def::DefKind;
use rustc_middle::ty;

pub(super) fn prepare<'facts, 'tcx>(
    tcx: TyCtxt<'tcx>,
    closed: &'facts nominal_helpers::ClosedScope<'facts, 'tcx>,
    facts: capability::facts::NominalInputs<'facts>,
    meanings: &'facts meaning::ScalarBindings,
    selections: &'facts BTreeMap<NativeKey, Vec<builtins::Selection>>,
    owners: &BTreeMap<NativeKey, rustc_hir::def_id::LocalDefId>,
    modes: &declaration_modes::DeclarationModes<'tcx>,
    bytes: &factory::ByteInputs<'_>,
    compared: &factory::ComparedViews<'_>,
    pairs: &spec_graph::Pairs,
    functions: &mut Vec<CheckedFunctionInputs>,
    observations: &mut Vec<Value>,
) -> Result<BTreeMap<NativeKey, spec_graph::OwnedSourceFamily>, String> {
    let mut families = BTreeMap::new();
    let intrinsic = spec_graph::Intrinsics::capture(tcx, facts.inputs, facts.common)?;
    let mut work = spec_graph::Work::new();
    for owner in owners.values().copied() {
        let attrs =
            crate::reader::attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)));
        if !attrs.inline
            || !attrs.open
            || attrs.mode != Some(trust_vc_vcir::Mode::Spec)
            || !tcx.visibility(owner).is_public()
            || tcx.def_kind(owner) != DefKind::AssocFn
        {
            continue;
        }
        let root = declaration_native::key(tcx, owner.to_def_id());
        let result = (|| {
            let parent = tcx.local_parent(owner);
            if tcx.def_kind(parent) != (DefKind::Impl { of_trait: false }) {
                return Err(
                    "a source forwarding root requires its actual inherent implementation".into(),
                );
            }
            let self_type = tcx
                .try_normalize_erasing_regions(
                    ty::TypingEnv::non_body_analysis(tcx, parent.to_def_id()),
                    tcx.type_of(parent).instantiate_identity(),
                )
                .map_err(|_| "the source forwarding self type cannot be normalized")?;
            let ty::Adt(adt, _) = self_type.kind() else {
                return Err("the source forwarding impl has no native nominal self type".into());
            };
            if !adt.did().is_local() {
                return Err("the source forwarding carrier is not original local source".into());
            }
            let nominal = SourceNominals::capture(
                tcx,
                closed,
                facts,
                meanings,
                selections,
                owners,
                declaration_native::key(tcx, adt.did()),
            )?;
            let graph = spec_graph::capture_forwarding(tcx, owner, &intrinsic, pairs, &mut work)?;
            let read = graph.read_source(&nominal, &mut work)?;
            let mut pending = Vec::new();
            for function in read.required_owners()? {
                let key = declaration_native::key(tcx, function.to_def_id());
                if functions
                    .iter()
                    .any(|packet| packet.native.keep_key() == key)
                {
                    return Err(
                        "source semantics cannot replace an already retained native function"
                            .into(),
                    );
                }
                let candidate = facts
                    .candidates
                    .matches
                    .iter()
                    .find(|candidate| candidate.keep == key)
                    .ok_or("a required source function lacks native correspondence")?;
                if facts.erase.roundtrip_unknown.contains_key(&candidate.erase) {
                    return Err("a required source function lacks actual metadata roundtrip".into());
                }
                let checked = declaration_policy::check(tcx, function.to_def_id());
                let policy = checked
                    .owned_for(tcx, function.to_def_id())
                    .ok_or("a required source function lacks complete native generic policy")?;
                let evidence = read.function(tcx, function)?;
                let correspondence = factory::prepare_correspondence(bytes, compared, candidate)?;
                let native = factory::prepare_source_function(
                    tcx,
                    function,
                    modes,
                    evidence,
                    correspondence,
                )
                .map_err(|error| match error {
                    factory::PreparationError::Refused(reason) => reason,
                    factory::PreparationError::ModeRejected(error) => {
                        format!("native source mode rejection: {}", error.message)
                    }
                    factory::PreparationError::ModeUnknown(reason) => {
                        format!("native source mode Unknown: {}", reason.detail)
                    }
                })?
                .into_owned(tcx)?;
                pending.push(CheckedFunctionInputs { native, policy });
            }
            let family = read.into_owned_family(&mut work)?;
            // Validate the full three-member signature inventory before either
            // required member is moved into the handoff.
            family.validate_functions(functions.iter().chain(&pending))?;
            nominal.revalidate(tcx)?;
            Ok::<_, String>((family, pending))
        })();
        match result {
            Ok((family, pending)) => {
                if families.contains_key(&root) { return Err("duplicate atomic source family".into()); }
                functions.extend(pending);
                family.validate_functions(functions.iter())?;
                families.insert(root, family);
                observations.push(json!({"root_hash": root.def_path_hash.to_string(), "display_path": tcx.def_path_str(owner).chars().take(512).collect::<String>(), "state": "CheckedOriginalSourceFamily", "native_owner_retained": true, "permission_from_observation": false}));
            }
            Err(reason) => observations.push(json!({"root_hash": root.def_path_hash.to_string(), "display_path": tcx.def_path_str(owner).chars().take(512).collect::<String>(), "state": "Unknown", "reason": reason, "body_import_authorized": false})),
        }
    }
    intrinsic.revalidate()?;
    closed.revalidate(tcx, facts.inputs, facts.common, facts.helpers)?;
    diagnostics(tcx)?;
    Ok(families)
}
