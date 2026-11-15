// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Structured observations of an actual owned client read. No value here can
//! construct native imports, meanings, ownership or a verification result.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};
use trust_vc_vcir::{FnDecl, FnId, FnRole};

use super::super::{diagnostics, ClientImports};
use super::ClientSource;
use crate::reader::{declaration_modes, declaration_native, CrateRead, FnStatus};

mod native;
mod vcir;

fn key(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let key = declaration_native::key(tcx, def);
    json!({"stable_crate_id": format!("{:016x}", key.stable_crate_id),
        "def_path_hash": format!("{:032x}", key.def_path_hash)})
}

fn matches_key(tcx: TyCtxt<'_>, def: DefId, id: FnId) -> bool {
    let key = declaration_native::key(tcx, def);
    id.0.hi == (key.def_path_hash >> 64) as u64 && id.0.lo == key.def_path_hash as u64
}

/// Ordinary correspondence data, not native IDs or an authority constructor.
fn unique_match<K: Eq>(
    keys: &[K],
    wanted: &K,
    used: &mut BTreeSet<usize>,
    budget: &mut vcir::Budget,
) -> Result<usize, String> {
    budget.charge(keys.len(), 0, 0)?;
    let mut found = None;
    for (index, key) in keys.iter().enumerate() {
        if key != wanted {
            continue;
        }
        if found.replace(index).is_some() {
            return Err("client footprint native correspondence is ambiguous".into());
        }
    }
    let index = found.ok_or("client footprint has no exact native correspondence")?;
    if !used.insert(index) {
        return Err("client footprint reused a native occurrence".into());
    }
    Ok(index)
}

fn declarations<'a>(
    read: &'a CrateRead,
    budget: &mut vcir::Budget,
) -> Result<BTreeMap<FnId, &'a FnDecl>, String> {
    budget.charge(read.krate.fns.len(), 0, 0)?;
    budget.charge(read.fns.len(), 0, 0)?;
    budget.charge(read.fn_defs.len(), 0, 0)?;
    let mut declarations = BTreeMap::new();
    for declaration in &read.krate.fns {
        if declarations.insert(declaration.id, declaration).is_some() {
            return Err("client footprint declaration IDs collide".into());
        }
    }
    Ok(declarations)
}

fn imported<'tcx>(
    tcx: TyCtxt<'tcx>,
    imports: &ClientImports<'_, 'tcx>,
    declarations: &BTreeMap<FnId, &FnDecl>,
    budget: &mut vcir::Budget,
) -> Result<HashMap<DefId, FnId>, String> {
    let (_, functions) = imports.declarations(tcx)?;
    budget.charge(functions.len(), 0, 0)?;
    let mut native = HashMap::new();
    for function in functions {
        let declaration = declarations
            .get(&function.id())
            .ok_or("licensed imported function was not installed")?;
        if function.definition().is_local()
            || declaration.role != FnRole::Imported
            || !matches_key(tcx, function.definition(), function.id())
            || native
                .insert(function.definition(), function.id())
                .is_some()
        {
            return Err("client footprint imported identity correspondence changed".into());
        }
    }
    let installed = declarations
        .values()
        .filter(|decl| decl.role == FnRole::Imported)
        .count();
    if installed != native.len() {
        return Err("client footprint has an unlicensed imported declaration".into());
    }
    Ok(native)
}

fn calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    read: &CrateRead,
    imports: &ClientImports<'_, 'tcx>,
    walked: Vec<vcir::Call>,
    actual: Vec<native::Call>,
    declarations: &BTreeMap<FnId, &FnDecl>,
    budget: &mut vcir::Budget,
) -> Result<Vec<Value>, String> {
    let keys = actual
        .iter()
        .map(|call| (call.callee, call.span))
        .collect::<Vec<_>>();
    let mut used = BTreeSet::new();
    let mut output = Vec::new();
    for mut call in walked {
        if declarations[&call.callee].role == FnRole::Imported {
            let span = read
                .span(call.span)
                .ok_or("an imported call has no native source span")?;
            let index = unique_match(&keys, &(call.callee, span), &mut used, budget)?;
            let current = &actual[index];
            if call.value["type_arguments"].as_array().map(Vec::len)
                != Some(current.type_argument_count)
                || call.value["value_arguments"].as_array().map(Vec::len)
                    != Some(current.value_argument_count)
            {
                return Err("native and VcIR complete call argument inventories differ".into());
            }
            call.value["native"] = current.value.clone();
        } else {
            call.value["native"] =
                json!({"state": "LocalCall; imported-call census does not claim a native match"});
        }
        output.push(call.value);
    }
    if used.len() != actual.len() {
        return Err("a native imported call disappeared from the VcIR footprint".into());
    }
    // Recheck every called imported declaration against this exact owned
    // registry, rather than accepting a matching signature or name alone.
    for native in actual {
        let definition = native.definition;
        let imported = imports
            .function(tcx, definition)
            .ok_or("called native import was revoked")?;
        let declaration = declarations[&native.callee];
        if *declaration != imported.declaration(declaration.span) {
            return Err(
                "the installed called signature differs from the owned native import".into(),
            );
        }
    }
    Ok(output)
}

fn assertions(
    read: &CrateRead,
    values: Vec<Value>,
    actual: Vec<native::Assertion>,
    budget: &mut vcir::Budget,
) -> Result<Vec<Value>, String> {
    let keys = actual
        .iter()
        .map(|assertion| assertion.span)
        .collect::<Vec<_>>();
    let mut used = BTreeSet::new();
    let mut output = Vec::new();
    for mut value in values {
        let index = value["span"]
            .as_u64()
            .and_then(|index| u32::try_from(index).ok())
            .ok_or("assertion footprint has no bounded span index")?;
        let span = read
            .span(trust_vc_vcir::SpanId(index))
            .ok_or("an assertion has no native source span")?;
        let index = unique_match(&keys, &span, &mut used, budget)?;
        value["native"] = actual[index].value.clone();
        output.push(value);
    }
    if used.len() != actual.len() {
        return Err("a native assertion disappeared from the VcIR footprint".into());
    }
    Ok(output)
}

pub(in crate::reader::declaration_staging) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    read: &CrateRead,
    imports: &ClientImports<'_, 'tcx>,
    source: &ClientSource,
) -> Result<Value, String> {
    diagnostics(tcx)?;
    imports.revalidate(tcx)?;
    let mut budget = vcir::Budget::new();
    let source_bytes = source.file().read()?;
    budget.charge(0, source_bytes.len(), 0)?;
    let source = native::Source {
        file: source.file(),
        bytes: &source_bytes,
    };
    let declarations = declarations(read, &mut budget)?;
    let native_imports = imported(tcx, imports, &declarations, &mut budget)?;
    let mut records = Vec::new();
    let mut functions = Vec::new();
    let mut seen = BTreeSet::new();
    for record in &read.fns {
        let definition = record.def_id.to_def_id();
        let mut row = json!({"native": key(tcx, definition),
            "path_display_only": budget.text(&record.def_path)?, "status": match &record.status {
                FnStatus::Read(_) => "Read", FnStatus::External => "External", FnStatus::Rejected => "Rejected",
                FnStatus::Refused(_) => "Refused", FnStatus::Deferred(_) => "Deferred" }});
        if let FnStatus::Read(id) = &record.status {
            let id = *id;
            if !seen.insert(id)
                || read.fn_defs.get(&id) != Some(&record.def_id)
                || !matches_key(tcx, definition, id)
                || !declaration_modes::original_body_available(tcx, record.def_id)
            {
                return Err("a local read lacks its unique original native body/identity".into());
            }
            let declaration = declarations
                .get(&id)
                .copied()
                .ok_or("a local Read record has no VcIR declaration")?;
            if declaration.role != FnRole::Item {
                return Err(
                    "client footprint does not yet represent local instance/trait roles".into(),
                );
            }
            let mut walk = vcir::Walk::new(declaration, &declarations);
            let body = walk.body(&mut budget)?;
            let actual = native::calls(tcx, record.def_id, &native_imports, &source, &mut budget)?;
            let assertions = assertions(read, walk.assertions, actual.assertions, &mut budget)?;
            let calls = calls(
                tcx,
                read,
                imports,
                walk.calls,
                actual.calls,
                &declarations,
                &mut budget,
            )?;
            row["id"] = vcir::id(id);
            functions.push(json!({"id": vcir::id(id), "native": key(tcx, definition),
                "source": source.anchor(tcx, tcx.def_span(definition), &mut budget)?,
                "native_original_body_present": true, "signature": vcir::signature(declaration, &mut budget)?,
                "native_signature": native::signature(tcx, definition, &mut budget)?,
                "native_parameters": native::parameters(tcx, record.def_id, declaration, &mut budget)?,
                "body": body, "assertions": assertions, "calls": calls}));
        }
        records.push(row);
    }
    if declarations
        .values()
        .filter(|decl| decl.role != FnRole::Imported)
        .count()
        != seen.len()
        || read.fn_defs.len() != seen.len()
    {
        return Err("a local VcIR declaration has no exact original Read record".into());
    }
    let result = json!({"schema": "trust-vc.current-client-footprint@1", "state": "ObservedCurrentClientRead",
        "function_records": records, "local_functions": functions,
        "native_authority_from_observation": false, "ownership_checked": false,
        "solver_executed": false, "verified_functions": null});
    if serde_json::to_vec(&result)
        .map_err(|e| e.to_string())?
        .len()
        > 1_048_576
    {
        return Err("the structured client footprint exceeded its output bound".into());
    }
    imports.revalidate(tcx)?;
    source.file.read()?;
    diagnostics(tcx)?;
    Ok(result)
}

#[cfg(test)]
mod tests;
