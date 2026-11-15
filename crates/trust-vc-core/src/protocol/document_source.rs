//! Rule 5 of [`super`]: what `ty` read (`source`) is what was written.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json::Value;
use sha2::{Digest, Sha256};

use super::{refuse, strings, Expected, Refusal};
use crate::protocol::ProtocolShape;

/// One unit of the module `ty` checked.
struct Unit<'a> {
    kind: &'a str,
    name: Option<&'a str>,
    arity: u64,
    local: bool,
}

/// The standard modules a spec may extend. Their operators have their TLA+
/// meaning; `TLC`'s do not (`RandomElement` is one seeded pick, `TLCGet` and
/// `TLCSet` read and write the checker's state), and the other standard and
/// community modules are not reviewed for this use.
const ADMITTED_STANDARD_MODULES: [&str; 4] = ["Naturals", "Integers", "Sequences", "FiniteSets"];

pub(super) fn source(document: &Value, expected: &Expected<'_>) -> Result<(), Refusal> {
    let bad = |detail: String| refuse("source refused", detail);
    let source = &document["source"];
    if !source.is_object() {
        return Err(bad("the document has no `source` block".to_string()));
    }
    let digest: String = Sha256::digest(expected.spec.as_bytes())
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    if source["sha256"] != digest.as_str() || source["bytes"] != expected.spec.len() {
        return Err(bad(format!(
            "ty read {} byte(s) with sha256 {}, not the {} byte(s) written ({digest})",
            source["bytes"],
            source["sha256"],
            expected.spec.len()
        )));
    }
    let range = &source["root_module_bytes"];
    let (Some(start), Some(end)) = (range["start"].as_u64(), range["end"].as_u64()) else {
        return Err(bad("the document has no `root_module_bytes`".to_string()));
    };
    let outside = usize::try_from(start)
        .ok()
        .zip(usize::try_from(end).ok())
        .filter(|(start, end)| start <= end && *end <= expected.spec.len())
        .and_then(|(start, end)| Some((expected.spec.get(..start)?, expected.spec.get(end..)?)));
    match outside {
        Some((before, after)) if before.trim().is_empty() && after.trim().is_empty() => {}
        _ => {
            return Err(bad(format!(
                "ty checked bytes {start}..{end} of the {} written; text outside the module was \
                 not checked",
                expected.spec.len()
            )))
        }
    }
    let modules = strings(&source["modules_in_file"]);
    if modules.len() != 1 {
        return Err(bad(format!(
            "{} modules in the spec ({}) where exactly one is checked",
            modules.len(),
            modules.join(", ")
        )));
    }
    let loaded: Vec<(&str, &str)> = source["loaded_modules"]
        .as_array()
        .map(|list| {
            list.iter()
                .map(|m| {
                    (
                        m["name"].as_str().unwrap_or(""),
                        m["kind"].as_str().unwrap_or(""),
                    )
                })
                .collect()
        })
        .unwrap_or_default();
    match loaded.first() {
        Some((name, "root")) if Some(*name) == source["root_module"].as_str() => {}
        _ => {
            return Err(bad(
                "`loaded_modules` does not start with the root".to_string()
            ))
        }
    }
    if let Some((name, kind)) = loaded[1..].iter().find(|(_, kind)| *kind != "standard") {
        return Err(bad(format!(
            "the spec loads module {name} from {kind} source; only ty's standard modules may be \
             loaded"
        )));
    }
    if let Some((name, _)) = loaded[1..]
        .iter()
        .find(|(name, _)| !ADMITTED_STANDARD_MODULES.contains(name))
    {
        return Err(bad(format!(
            "the spec loads standard module {name}; only {} are admitted",
            ADMITTED_STANDARD_MODULES.join(", ")
        )));
    }
    let units = units(&source["units"]).ok_or_else(|| bad("`units` is malformed".to_string()))?;
    let mut seen = std::collections::BTreeSet::new();
    for unit in &units {
        // `RECURSIVE R(_)` is followed by `R`'s definition.
        if let (Some(name), false) = (unit.name, unit.kind == "recursive") {
            if !seen.insert(name) {
                return Err(bad(format!(
                    "'{name}' is declared or defined more than once"
                )));
            }
        }
    }
    for name in expected.request.names() {
        let defined = units.iter().any(|unit| {
            unit.kind == "operator" && unit.name == Some(name) && unit.arity == 0 && !unit.local
        });
        if !defined {
            return Err(refuse(
                "config refused",
                format!("`{name}` is not an operator the module defines without parameters"),
            ));
        }
    }
    if let Some(shape) = expected.shape {
        generated_shape(shape, &units, loaded.len())?;
    }
    Ok(())
}

/// A `#[protocol]` module declares exactly the emitted variables, in order,
/// and defines exactly the emitted operators, each without parameters and
/// not `LOCAL`, and holds nothing else: no text placed in it (a liveness
/// property's TLA+ text) added, removed or replaced a definition.
fn generated_shape(
    shape: &ProtocolShape,
    units: &[Unit<'_>],
    loaded: usize,
) -> Result<(), Refusal> {
    let mut declared = Vec::new();
    let mut defined = Vec::new();
    for unit in units {
        match (unit.kind, unit.name) {
            ("variable", Some(name)) => declared.push(name),
            ("operator", Some(name)) if unit.arity == 0 && !unit.local => defined.push(name),
            _ => {
                return Err(refuse(
                    "source refused",
                    "the generated module holds a unit it did not emit",
                ))
            }
        }
    }
    let mut expected: Vec<&str> = shape.operators.iter().map(String::as_str).collect();
    expected.sort_unstable();
    defined.sort_unstable();
    if loaded != 1 || declared != shape.variables || defined != expected {
        return Err(refuse(
            "source refused",
            format!(
                "the generated module is not what was emitted: variables {declared:?}, \
                 operators {defined:?}, {loaded} module(s) loaded"
            ),
        ));
    }
    Ok(())
}

fn units(value: &Value) -> Option<Vec<Unit<'_>>> {
    value
        .as_array()?
        .iter()
        .map(|unit| {
            Some(Unit {
                kind: unit["kind"].as_str()?,
                name: unit["name"].as_str(),
                arity: unit["arity"].as_u64()?,
                local: unit["local"].as_bool()?,
            })
        })
        .collect()
}
