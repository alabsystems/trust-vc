//! Decode actual declaration observations into structural join candidates.
//!
//! This codec does not authenticate a producer or authorize an import. The
//! staging owner separately binds source coordinates to approved bytes and
//! external declarations to selected artifacts. Neither a JSON assertion nor
//! a successful candidate match supplies mode, header, body or proof authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};

use serde_json::Value;

use super::{
    AuthoredSpan, CommonInputs, Declaration, DeclarationShape, DeclarationType, Digest,
    ExternalType, FunctionOrigin, GenericScope, IntegerWidth, NativeKey, NominalKind, Observation,
    SourceAnchor, TypeParameter, View,
};

/// Stable machine classification emitted from an actual compiler DefKind.
/// Rust's Debug spelling is retained separately for diagnostics only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeDeclarationKind {
    Function,
    AssociatedFunction,
    Struct,
    Enum,
    Union,
    InherentImplementation,
    TraitImplementation,
    Module,
    Trait,
    Other,
}

impl NativeDeclarationKind {
    pub const fn machine_name(self) -> &'static str {
        match self {
            Self::Function => "Function",
            Self::AssociatedFunction => "AssociatedFunction",
            Self::Struct => "Struct",
            Self::Enum => "Enum",
            Self::Union => "Union",
            Self::InherentImplementation => "InherentImplementation",
            Self::TraitImplementation => "TraitImplementation",
            Self::Module => "Module",
            Self::Trait => "Trait",
            Self::Other => "Other",
        }
    }
}

fn declaration_kind(value: &Value) -> Result<NativeDeclarationKind, String> {
    Ok(match text(value, "declaration_kind")? {
        "Function" => NativeDeclarationKind::Function,
        "AssociatedFunction" => NativeDeclarationKind::AssociatedFunction,
        "Struct" => NativeDeclarationKind::Struct,
        "Enum" => NativeDeclarationKind::Enum,
        "Union" => NativeDeclarationKind::Union,
        "InherentImplementation" => NativeDeclarationKind::InherentImplementation,
        "TraitImplementation" => NativeDeclarationKind::TraitImplementation,
        "Module" => NativeDeclarationKind::Module,
        "Trait" => NativeDeclarationKind::Trait,
        "Other" => NativeDeclarationKind::Other,
        _ => return Err("unsupported native declaration kind machine value".into()),
    })
}

fn nominal_kind(value: &Value) -> Result<NominalKind, String> {
    match declaration_kind(value)? {
        NativeDeclarationKind::Struct => Ok(NominalKind::Struct),
        NativeDeclarationKind::Enum => Ok(NominalKind::Enum),
        NativeDeclarationKind::Union => Ok(NominalKind::Union),
        _ => Err("a nominal observation does not name a native nominal declaration".into()),
    }
}

/// Compiler-reported coordinates, before any source authentication. The
/// compiler source-file ID and Debug/display strings are deliberately absent.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ObservedAnchor {
    pub local_path: String,
    pub compiler_source_hash: String,
    pub original_file_len: u32,
    pub bytes: (u32, u32),
}

/// Explicit inputs supplied by the staging owner. These are observations, not
/// capabilities: a caller constructing this context cannot authorize imports.
pub struct Context {
    pub common: CommonInputs,
    pub cfg_sha256: Digest,
    pub stable_crate_id: u64,
    pub selected_rmeta_sha256: Option<Digest>,
    /// Only entries whose actual files/hash/ranges were bound to the approved
    /// source manifest belong here. Missing, virtual and foreign spans stay
    /// Unknown; matching a path string alone must not populate this table.
    pub source_anchors: BTreeMap<ObservedAnchor, AuthoredSpan>,
    /// Actual native external declaration binders and selected artifact
    /// identities. An argument count observed at one use is not a substitute
    /// for the declaration's generic parameter facts.
    pub external_nominals: BTreeMap<NativeKey, ExternalType>,
}

/// Collect native external binder observations from the structural codec.
/// `selected_artifacts` must describe the actual loaded metadata cohort;
/// names, source paths and argument-list lengths cannot populate that map.
/// The result still grants only candidate-comparison data, never authority.
pub fn external_nominals(
    value: &Value,
    local_crate: u64,
    selected_artifacts: &BTreeMap<u64, Digest>,
) -> Result<BTreeMap<NativeKey, ExternalType>, String> {
    fn visit(
        value: &Value,
        local_crate: u64,
        selected_artifacts: &BTreeMap<u64, Digest>,
        result: &mut BTreeMap<NativeKey, ExternalType>,
        depth: usize,
    ) -> Result<(), String> {
        if depth > 256 {
            return Err("declaration observation nesting exceeded its bound".into());
        }
        match value {
            Value::Object(fields) => {
                if fields.get("kind").and_then(Value::as_str) == Some("Adt") {
                    nominal_kind(&value["definition"])?;
                    let declaration = key(&value["definition"])?;
                    let count = number(value, "native_type_parameter_count")?;
                    if usize::try_from(count).ok() != Some(array(value, "type_arguments")?.len()) {
                        return Err("nominal arguments differ from the native binder count".into());
                    }
                    if declaration.stable_crate_id != local_crate {
                        let artifact = selected_artifacts
                            .get(&declaration.stable_crate_id)
                            .ok_or("external nominal crate has no selected metadata artifact")?;
                        let observed = ExternalType {
                            artifact_sha256: *artifact,
                            key: declaration,
                            type_parameters: count,
                        };
                        if let Some(previous) = result.insert(declaration, observed.clone()) {
                            if previous != observed {
                                return Err("external nominal binder observations disagree".into());
                            }
                        }
                    }
                }
                for child in fields.values() {
                    visit(child, local_crate, selected_artifacts, result, depth + 1)?;
                }
            }
            Value::Array(values) => {
                for child in values {
                    visit(child, local_crate, selected_artifacts, result, depth + 1)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    let mut result = BTreeMap::new();
    visit(value, local_crate, selected_artifacts, &mut result, 0)?;
    Ok(result)
}

fn array<'a>(value: &'a Value, field: &str) -> Result<&'a [Value], String> {
    value[field]
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| format!("missing {field} array"))
}

fn text<'a>(value: &'a Value, field: &str) -> Result<&'a str, String> {
    value[field]
        .as_str()
        .ok_or_else(|| format!("missing {field} string"))
}

fn number(value: &Value, field: &str) -> Result<u32, String> {
    value[field]
        .as_u64()
        .and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| format!("missing or overflowing {field} index"))
}

fn boolean(value: &Value, field: &str) -> Result<bool, String> {
    value[field]
        .as_bool()
        .ok_or_else(|| format!("missing {field} boolean"))
}

fn hexadecimal(value: &Value, field: &str, width: usize) -> Result<u128, String> {
    let value = text(value, field)?;
    if value.len() != width || !value.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("invalid {field} width or encoding"));
    }
    u128::from_str_radix(value, 16).map_err(|_| format!("invalid {field}"))
}

fn key(definition: &Value) -> Result<NativeKey, String> {
    let result = NativeKey {
        stable_crate_id: u64::try_from(hexadecimal(definition, "stable_crate_id", 16)?)
            .map_err(|_| "overflowing stable crate ID")?,
        def_path_hash: hexadecimal(definition, "def_path_hash", 32)?,
    };
    if !result.is_well_formed() {
        return Err("definition hash is outside its recorded stable crate".into());
    }
    Ok(result)
}

fn observed(value: &Value, expected: &str) -> Result<(), String> {
    if value["state"] == expected {
        Ok(())
    } else if value["state"] == "Unknown" {
        Err(value["reason"]
            .as_str()
            .unwrap_or("unknown observation")
            .into())
    } else {
        Err(format!("missing or unsupported {expected} observation"))
    }
}

fn source_span(context: &Context, value: &Value) -> Result<AuthoredSpan, String> {
    observed(value, "ObservedRealSourceAnchor")?;
    let coordinates = ObservedAnchor {
        local_path: text(value, "local_path")?.into(),
        compiler_source_hash: text(value, "compiler_source_hash")?.into(),
        original_file_len: number(value, "original_file_len")?,
        bytes: (number(value, "original_lo")?, number(value, "original_hi")?),
    };
    let bound = context
        .source_anchors
        .get(&coordinates)
        .ok_or("compiler coordinates have no approved source-byte binding")?;
    if !bound.is_well_formed()
        || bound.original_file_len != coordinates.original_file_len
        || bound.bytes != coordinates.bytes
    {
        return Err("the supplied source-byte binding changes compiler coordinates".into());
    }
    Ok(bound.clone())
}

fn source(context: &Context, row: &Value) -> Result<SourceAnchor, String> {
    let scopes = &row["authored_scope_anchors"];
    observed(scopes, "ObservedAuthoredScopeCandidates")?;
    let enclosing = array(scopes, "scopes")?;
    if enclosing.len() > 64 {
        return Err("authored scope depth exceeded its bound".into());
    }
    let enclosing_declarations = enclosing
        .iter()
        .map(|scope| source_span(context, &scope["definition_anchor"]))
        .collect::<Result<_, _>>()?;
    Ok(SourceAnchor {
        identifier: source_span(context, &row["definition"]["identifier_anchor"])?,
        enclosing_declarations,
    })
}

fn generics(value: &Value, owner: NativeKey) -> Result<Vec<GenericScope>, String> {
    let scopes = array(value, "generic_scopes")?;
    if scopes.is_empty() || scopes.len() > 64 {
        return Err("missing or excessive generic scope depth".into());
    }
    let mut result = Vec::new();
    let mut expected = Some(owner);
    for scope in scopes {
        let current = key(&scope["definition"])?;
        if Some(current) != expected || current.stable_crate_id != owner.stable_crate_id {
            return Err("generic scope owner/parent identity does not match".into());
        }
        let generic = &scope["generics"];
        let parent = generic
            .get("parent")
            .ok_or("missing generic parent observation")?;
        expected = if parent.is_null() {
            None
        } else {
            Some(key(parent)?)
        };
        let parameters = array(generic, "own_parameters")?
            .iter()
            .map(|parameter| {
                if parameter["kind"] != "Type" {
                    return Err("non-type generic parameter is not represented".into());
                }
                let result = TypeParameter {
                    index: number(parameter, "index")?,
                    has_default: boolean(parameter, "has_default")?,
                    synthetic: boolean(parameter, "synthetic")?,
                    pure_wrt_drop: boolean(parameter, "pure_wrt_drop")?,
                };
                if result.has_default || result.synthetic {
                    return Err("default or synthetic generic parameter is not represented".into());
                }
                Ok(result)
            })
            .collect::<Result<_, String>>()?;
        result.push(GenericScope {
            parent_count: number(generic, "parent_count")?,
            own_type_parameters: parameters,
            has_self: boolean(generic, "has_self")?,
        });
    }
    if expected.is_some() || super::generic_count(&result).is_none() {
        return Err("generic parent chain or flattened indices are incomplete".into());
    }
    Ok(result)
}

fn ty(context: &Context, value: &Value, depth: usize) -> Result<DeclarationType, String> {
    if depth > 64 {
        return Err("structural type nesting exceeded its bound".into());
    }
    Ok(match text(value, "kind")? {
        "Bool" => DeclarationType::Bool,
        kind @ ("Int" | "Uint") => {
            let width = match text(value, "width")? {
                "pointer" => IntegerWidth::Pointer,
                "8" => IntegerWidth::Fixed(8),
                "16" => IntegerWidth::Fixed(16),
                "32" => IntegerWidth::Fixed(32),
                "64" => IntegerWidth::Fixed(64),
                "128" => IntegerWidth::Fixed(128),
                _ => return Err("unsupported integer width".into()),
            };
            DeclarationType::Integer {
                signed: kind == "Int",
                width,
            }
        }
        "TypeParameter" => DeclarationType::Parameter(number(value, "index")?),
        "Tuple" => DeclarationType::Tuple(
            array(value, "elements")?
                .iter()
                .map(|value| ty(context, value, depth + 1))
                .collect::<Result<_, _>>()?,
        ),
        "Adt" => {
            nominal_kind(&value["definition"])?;
            let declaration = key(&value["definition"])?;
            let arguments = array(value, "type_arguments")?
                .iter()
                .map(|value| ty(context, value, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            if usize::try_from(number(value, "native_type_parameter_count")?).ok()
                != Some(arguments.len())
            {
                return Err(
                    "nominal arguments differ from the native declaration binder count".into(),
                );
            }
            if declaration.stable_crate_id == context.stable_crate_id {
                DeclarationType::LocalNominal {
                    declaration,
                    arguments,
                }
            } else {
                let external = context.external_nominals.get(&declaration).ok_or(
                    "external nominal declaration has no selected-artifact/binder observation",
                )?;
                if external.key != declaration
                    || !context
                        .common
                        .dependency_artifacts
                        .contains(&external.artifact_sha256)
                    || usize::try_from(external.type_parameters).ok() != Some(arguments.len())
                {
                    return Err(
                        "external nominal artifact, key or generic arity does not match".into(),
                    );
                }
                DeclarationType::ExternalNominal {
                    declaration: external.clone(),
                    arguments,
                }
            }
        }
        _ => return Err("unsupported structural type; no Debug/string fallback".into()),
    })
}

fn nominal(context: &Context, row: &Value, owner: NativeKey) -> Result<DeclarationShape, String> {
    let value = &row["structural_nominal_type"];
    observed(value, "ObservedStructuralNominalType")?;
    let scopes = generics(value, owner)?;
    let count = super::generic_count(&scopes).ok_or("invalid nominal generic scopes")?;
    let DeclarationType::LocalNominal {
        declaration,
        arguments,
    } = ty(context, &value["type"], 0)?
    else {
        return Err("nominal declaration did not retain its actual ADT identity".into());
    };
    if declaration != owner
        || arguments
            != (0..count)
                .map(DeclarationType::Parameter)
                .collect::<Vec<_>>()
    {
        return Err(
            "nominal declaration identity arguments do not match its native binders".into(),
        );
    }
    let kind = nominal_kind(&row["definition"])?;
    Ok(DeclarationShape::Nominal { kind })
}

fn function(context: &Context, row: &Value) -> Result<DeclarationShape, String> {
    let signature = &row["structural_signature"];
    observed(signature, "ObservedStructuralSignature")?;
    if signature["abi"] != "Rust"
        || signature["safety"] != "Safe"
        || signature["c_variadic"] != false
        || signature["splatted"] != false
    {
        return Err("unsupported native function signature flags".into());
    }
    let owner = key(&row["definition"])?;
    let scopes = generics(signature, owner)?;
    let native_scopes = array(signature, "generic_scopes")?;
    let generic_parent = &native_scopes[0]["generics"]["parent"];
    let container = &row["function_container"];
    let origin = match container["state"].as_str() {
        Some("ObservedFreeFunction")
            if declaration_kind(&row["definition"])? == NativeDeclarationKind::Function
                && declaration_kind(&container["parent"])? == NativeDeclarationKind::Module
                && key(&container["parent"])?.stable_crate_id == owner.stable_crate_id
                && generic_parent.is_null() =>
        {
            FunctionOrigin::Free
        }
        Some("ObservedInherentDeclaration")
            if declaration_kind(&row["definition"])?
                == NativeDeclarationKind::AssociatedFunction =>
        {
            let self_type = &container["structural_self_type"];
            observed(self_type, "ObservedStructuralNominalType")?;
            // Check the actual generic impl identity/chain before discarding
            // declaration keys from the structural scope representation.
            let parent = key(&container["parent"])?;
            let self_scopes = generics(self_type, parent)?;
            if declaration_kind(&container["parent"])?
                != NativeDeclarationKind::InherentImplementation
                || parent.stable_crate_id != owner.stable_crate_id
                || key(generic_parent)? != parent
                || scopes.get(1..) != Some(self_scopes.as_slice())
            {
                return Err("method and inherent Self have different native parent binders".into());
            }
            FunctionOrigin::Inherent {
                self_type: ty(context, &self_type["type"], 0)?,
            }
        }
        _ => return Err("trait/default/inherited or unknown function container".into()),
    };
    Ok(DeclarationShape::Function {
        origin,
        inputs: array(signature, "inputs")?
            .iter()
            .map(|value| ty(context, value, 0))
            .collect::<Result<_, _>>()?,
        output: Box::new(ty(context, &signature["output"], 0)?),
    })
}

fn observation<T>(value: Result<T, String>) -> Observation<T> {
    match value {
        Ok(value) => Observation::Observed(value),
        Err(reason) => Observation::Unknown(reason),
    }
}

/// Decode either actual observation schema. Every declaration remains in the
/// inventory even if its source/type/container is Unknown. Malformed native
/// keys or a mismatched view are errors, never silently filtered rows.
pub fn decode(context: Context, value: &Value) -> Result<View, String> {
    match value["schema"].as_str() {
        Some("trust-vc.keep-declaration-observation@2")
            if context.selected_rmeta_sha256.is_none() => {}
        Some("trust-vc.erase-declaration-observation@2")
            if context.selected_rmeta_sha256.is_some() =>
        {
            if u64::try_from(hexadecimal(value, "stable_crate_id", 16)?).ok()
                != Some(context.stable_crate_id)
            {
                return Err("Erase inventory belongs to a different native crate".into());
            }
        }
        _ => return Err("unsupported or mismatched Keep/Erase observation schema".into()),
    }
    if value["import_authorized"] != false || value.get("verified_functions") != Some(&Value::Null)
    {
        return Err(
            "a declaration observation must not claim import or verification authority".into(),
        );
    }
    let mut declarations = Vec::new();
    let mut keys = BTreeSet::new();
    for (field, is_nominal) in [("types", true), ("rows", false)] {
        for row in array(value, field)? {
            let owner = key(&row["definition"])?;
            if owner.stable_crate_id != context.stable_crate_id || !keys.insert(owner) {
                return Err(
                    "a declaration key is duplicated or belongs to another native crate".into(),
                );
            }
            let structural = if is_nominal {
                &row["structural_nominal_type"]
            } else {
                &row["structural_signature"]
            };
            let expected = if is_nominal {
                "ObservedStructuralNominalType"
            } else {
                "ObservedStructuralSignature"
            };
            let generic = observed(structural, expected).and_then(|()| generics(structural, owner));
            declarations.push(Declaration {
                key: owner,
                source: observation(source(&context, row)),
                generics: observation(generic),
                shape: observation(if is_nominal {
                    nominal(&context, row, owner)
                } else {
                    function(&context, row)
                }),
            });
        }
    }
    Ok(View {
        common: context.common,
        cfg_sha256: context.cfg_sha256,
        stable_crate_id: context.stable_crate_id,
        selected_rmeta_sha256: context.selected_rmeta_sha256,
        declarations,
    })
}

#[cfg(test)]
mod tests;
