//! Compiler-owned foreign declaration observations, not an import authority.
//!
//! An empty Rust client resolves `InspectSet` to the genuine external type.
//! The callback runs after ordinary compiler analysis and records metadata;
//! it never lowers a carrier, reads private representations/MIR, imports an
//! axiom, resolves erased parameter modes or declares any function verified.
//! A later Keep-body producer must supply the missing mode/header facts.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_driver;

use std::path::PathBuf;
use std::process::ExitCode;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{self, Ty, TyCtxt};
use serde_json::{json, Value};

const EXPECTED_COMPILER: &str = "29ebb403de7a102850d6cb10a62d5cc3baf723ed";

fn crate_record(tcx: TyCtxt<'_>, krate: CrateNum) -> Value {
    let source = tcx.used_crate_source(krate);
    let path = |p: &Option<PathBuf>| p.as_ref().map(|p| p.display().to_string());
    json!({
        "crate_num_debug": format!("{krate:?}"),
        "name": tcx.crate_name(krate).to_string(),
        "stable_crate_id": format!("{:016x}", tcx.stable_crate_id(krate).as_u64()),
        "svh": tcx.crate_hash(krate).to_string(),
        "sources": {
            "rmeta": path(&source.rmeta),
            "rlib": path(&source.rlib),
            "dylib": path(&source.dylib),
            "sdylib_interface": path(&source.sdylib_interface),
        },
    })
}

fn definition(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let (high, low) = tcx.def_path_hash(def).0.split();
    let kind = tcx.def_kind(def);
    let visibility = match kind {
        DefKind::Struct | DefKind::AssocFn => Some(format!("{:?}", tcx.visibility(def))),
        _ => None,
    };
    json!({
        "def_id_debug": format!("{def:?}"),
        "path_display_only": tcx.def_path_str(def),
        "kind": format!("{kind:?}"),
        "def_path_hash": format!("{:016x}{:016x}", high.as_u64(), low.as_u64()),
        "stable_crate_id": format!("{:016x}", tcx.stable_crate_id(def.krate).as_u64()),
        "crate_svh": tcx.crate_hash(def.krate).to_string(),
        "visibility_debug": visibility,
    })
}

// Tool attrs are unparsed; the exact compiler explicitly permits this use of
// get_all_attrs. Debug strings preserve observation order but are not a wire
// representation or an authenticated interpretation of Verus directives.
#[allow(deprecated)]
fn attributes(tcx: TyCtxt<'_>, def: DefId) -> Vec<String> {
    tcx.get_all_attrs(def)
        .iter()
        .map(|attr| format!("{attr:#?}"))
        .collect()
}

fn type_record<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Value {
    let adt = match ty.kind() {
        ty::Adt(adt, _) => Some(definition(tcx, adt.did())),
        _ => None,
    };
    json!({"display": ty.to_string(), "kind_debug": format!("{:?}", ty.kind()), "adt": adt})
}

fn unknown(reason: &str) -> Value {
    json!({"state": "Unknown", "reason": reason})
}

fn instantiated_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    implementation: DefId,
    len: DefId,
    concrete: Ty<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> Result<Value, String> {
    let generics = tcx.generics_of(len);
    if !generics.own_params.is_empty()
        || generics.count() != args.len()
        || tcx.generics_of(implementation).count() != args.len()
        || !matches!(
            tcx.associated_item(len).container,
            ty::AssocContainer::InherentImpl
        )
    {
        return Err(
            "prototype cannot instantiate this method's actual generic/container shape".into(),
        );
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let self_type = tcx
        .try_normalize_erasing_regions(env, tcx.type_of(implementation).instantiate(tcx, args))
        .map_err(|error| format!("impl self-type normalization failed: {error:?}"))?;
    if self_type != concrete {
        return Err(
            "the normalized impl self type did not match the normalized client type".into(),
        );
    }
    let unnormalized = tcx.fn_sig(len).instantiate(tcx, args);
    let before_normalization = format!("{unnormalized:?}");
    let signature = tcx
        .try_normalize_erasing_regions(env, unnormalized)
        .map_err(|error| format!("method signature normalization failed: {error:?}"))?;
    let bare = signature.skip_binder();
    Ok(json!({
        "state": "ObservedCompilerSignature",
        "unnormalized_binder_debug": before_normalization,
        "binder_debug": format!("{signature:?}"),
        "normalization": "try_normalize_erasing_regions in fully_monomorphized environment",
        "regions_erased": true,
        "impl_self_type": type_record(tcx, self_type),
        "input_types_display": bare.inputs().iter().map(|ty| ty.to_string()).collect::<Vec<_>>(),
        "output_type": type_record(tcx, bare.output()),
    }))
}

fn len_record<'tcx>(
    tcx: TyCtxt<'tcx>,
    implementation: DefId,
    len: DefId,
    concrete: Ty<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> Value {
    let generics = tcx.generics_of(len);
    let impl_generics = tcx.generics_of(implementation);
    let instantiated = instantiated_signature(tcx, implementation, len, concrete, args)
        .unwrap_or_else(|reason| unknown(&reason));
    let erased = "macro Erase metadata retains no authoritative HIR parameter/header bodies";
    json!({
        "definition": definition(tcx, len),
        "impl_definition": definition(tcx, implementation),
        "container_debug": format!("{:?}", tcx.associated_item(len).container),
        "declaration_signature_unnormalized_debug": format!("{:?}", tcx.fn_sig(len).instantiate_identity()),
        "generics_debug": format!("{generics:?}"),
        "impl_generics_debug": format!("{impl_generics:?}"),
        "explicit_clauses_debug": format!("{:?}", tcx.explicit_clauses_of(len)),
        "raw_item_attrs_debug": attributes(tcx, len),
        "instantiated_signature": instantiated,
        "parameter_modes": unknown(erased),
        "return_mode": unknown("surviving attrs are recorded, not authenticated as resolved mode facts"),
        "requires": unknown(erased),
        "recommends": unknown(erased),
        "ensures": unknown(erased),
        "unsupported_headers": unknown(erased),
        "body_verification": unknown("original Keep-body analysis/verification was not performed"),
    })
}

fn observe(tcx: TyCtxt<'_>, whole_inventory: bool) -> Result<Value, String> {
    let aliases: Vec<_> = tcx
        .hir_crate_items(())
        .owners()
        .filter(|owner| {
            tcx.def_kind(owner.def_id) == DefKind::TyAlias
                && tcx.item_name(owner.def_id.to_def_id()).as_str() == "InspectSet"
        })
        .collect();
    if aliases.len() != 1 {
        return Err("the checked client must have exactly one InspectSet type alias".into());
    }
    let alias = aliases[0].def_id;
    if tcx.generics_of(alias).count() != 0 {
        return Err("Unknown: prototype requires a non-generic inspection alias".into());
    }
    let concrete = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            tcx.type_of(alias).instantiate_identity(),
        )
        .map_err(|error| format!("Unknown: client type normalization failed: {error:?}"))?;
    let (adt, args) = match concrete.kind() {
        ty::Adt(adt, args) => (*adt, *args),
        _ => return Err("InspectSet did not resolve to an external ADT".into()),
    };
    let set = adt.did();
    if set.is_local() {
        return Err("InspectSet resolved to a local type".into());
    }

    if whole_inventory {
        return Ok(json!({
            "schema": "trust-vc.foreign-declaration-inventory@1",
            "compiler_commit": env!("VC_SHIM_COMPILER_COMMIT"),
            "compiler_sysroot": env!("VC_SHIM_COMPILER_SYSROOT"),
            "target_crate": crate_record(tcx, set.krate),
            "loaded_crates": tcx.crates(()).iter().map(|krate| crate_record(tcx, *krate)).collect::<Vec<_>>(),
            "declarations": crate::reader::declaration_facts::observe_foreign(tcx, set.krate)?,
            "authority": "whole selected crate declaration observations only",
            "import_authorized": false, "verified_functions": null,
            "private_representation_or_axioms_read": false,
        }));
    }

    // `len` is only the prototype's discovery filter. Its spelling grants no
    // source, mode, library, proof or import authority; the report records the
    // actual compiler DefId/hash and the wrapper checks the selected artifact.
    let mut candidates = Vec::new();
    let mut inherent_items = Vec::new();
    for &implementation in tcx.inherent_impls(set) {
        let mut items = Vec::new();
        for &item in tcx.associated_item_def_ids(implementation) {
            items.push(json!({
                "name": tcx.item_name(item).to_string(),
                "definition": definition(tcx, item),
                "raw_item_attrs_debug": attributes(tcx, item),
            }));
            if tcx.def_kind(item) == DefKind::AssocFn && tcx.item_name(item).as_str() == "len" {
                candidates.push((implementation, item));
            }
        }
        inherent_items.push(json!({
            "definition": definition(tcx, implementation),
            "self_type_declaration_unnormalized_debug": format!("{:?}", tcx.type_of(implementation).instantiate_identity()),
            "generics_debug": format!("{:?}", tcx.generics_of(implementation)),
            "items": items,
        }));
    }
    let len = match candidates.as_slice() {
        [(implementation, method)] => len_record(tcx, *implementation, *method, concrete, args),
        _ => unknown(&format!(
            "no unique inherent len declaration; observed {} candidates; see actual item inventory",
            candidates.len()
        )),
    };
    Ok(json!({
        "schema": "trust-vc.foreign-metadata-observation@1",
        "compiler_commit": env!("VC_SHIM_COMPILER_COMMIT"),
        "compiler_sysroot": env!("VC_SHIM_COMPILER_SYSROOT"),
        "compiler_analysis_completed": true,
        "authority": "metadata observation only",
        "import_authorized": false,
        "verified_functions": null,
        "private_representation_or_axioms_read": false,
        "keep_body_declaration_key_alignment": unknown("a separate Keep-body producer view has not been inspected"),
        "inherent_items_metadata_only": inherent_items,
        "loaded_crates": tcx.crates(()).iter().map(|krate| crate_record(tcx, *krate)).collect::<Vec<_>>(),
        "target_crate": crate_record(tcx, set.krate),
        "set": {
            "definition": definition(tcx, set),
            "declaration_type": {
                "state": "UnnormalizedCompilerDeclaration",
                "debug": format!("{:?}", tcx.type_of(set).instantiate_identity()),
            },
            "concrete_client_type": type_record(tcx, concrete),
            "concrete_arguments_debug": format!("{args:?}"),
            "generics_debug": format!("{:?}", tcx.generics_of(set)),
            "explicit_clauses_debug": format!("{:?}", tcx.explicit_clauses_of(set)),
            "raw_item_attrs_debug": attributes(tcx, set),
            "logical_carrier": unknown("no VcIR carrier is constructed by inspection"),
        },
        "len": len,
    }))
}

#[derive(Default)]
struct Inspect {
    result: Option<Result<Value, String>>,
    whole_inventory: bool,
}

impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some(if tcx.dcx().has_errors().is_some() {
            Err("ordinary compiler analysis rejected the client".into())
        } else {
            let report = observe(tcx, self.whole_inventory);
            if tcx.dcx().has_errors().is_some() {
                Err("foreign declaration observation emitted compiler errors".into())
            } else {
                report
            }
        });
        Compilation::Stop
    }
}

/// Run the analysis-only inspection tool. It never enters the verifier shim.
pub fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("vstd_metadata_inspect: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    if env!("VC_SHIM_COMPILER_COMMIT") != EXPECTED_COMPILER {
        return Err("this prototype requires the recorded Trust29ebb compiler".into());
    }
    let mut args = std::env::args();
    let program = args.next().ok_or("missing program name")?;
    let first = args
        .next()
        .ok_or("usage: vstd_metadata_inspect [--inventory] REPORT -- RUSTC_ARGS")?;
    let whole_inventory = first == "--inventory";
    let output = PathBuf::from(if whole_inventory {
        args.next().ok_or("--inventory requires a report path")?
    } else {
        first
    });
    if args.next().as_deref() != Some("--") {
        return Err("expected -- before compiler arguments".into());
    }
    let mut compiler_args = vec![program];
    compiler_args.extend(args);
    if compiler_args
        .iter()
        .any(|arg| arg == "--sysroot" || arg.starts_with("--sysroot="))
    {
        return Err("the compiler sysroot is pinned by the helper build".into());
    }
    compiler_args.extend(["--sysroot".into(), env!("VC_SHIM_COMPILER_SYSROOT").into()]);
    let mut callbacks = Inspect {
        whole_inventory,
        ..Inspect::default()
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&compiler_args, &mut callbacks))
        .map_err(|_| "compiler rejected the inspection client".to_string())?;
    let report = callbacks
        .result
        .ok_or("compiler analysis callback was not reached")??;
    let serialized = serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?;
    std::fs::write(&output, serialized).map_err(|error| format!("{}: {error}", output.display()))
}
