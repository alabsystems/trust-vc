// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Minimal cargo path-dependency spec import.
//!
//! This imports public `#[trust_vc::spec]` signatures from directly referenced
//! local path dependencies. It also imports a narrow body axiom for public,
//! non-opaque, non-generic spec functions whose bodies are call-free expressions
//! the verifier can lower. It declares a narrow subset of public dependency
//! concrete function signatures for direct calls and may require call-site
//! preconditions, but it does not assume dependency concrete postconditions
//! without a semantic proof artifact. Unsupported dependency
//! contracts/recommendations and dependency concrete bodies remain blocked.

use proc_macro2::Span;
use quote::{quote, ToTokens};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use syn::parse::{Parse, ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::visit::{self, Visit};
use syn::visit_mut::VisitMut;
use syn::{Expr, ItemFn, Token};
use trust_vc_core::{
    ir::TrustVcType,
    vc::{ProofObligation, VerificationContext},
};

const TRUST_VC_DEPENDENCY_FACTS_ENV: &str = "__TRUST_VC_DEPENDENCY_FACTS__";
const TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND: &str = "trust-vc-semantic-facts-v1";

#[derive(Debug, Clone, PartialEq, Eq)]
struct PathDependency {
    alias: String,
    manifest_path: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DependencySpecSignature {
    name: String,
    return_ty: TrustVcType,
    params: Vec<(String, TrustVcType)>,
    body_axiom: Option<DependencySpecBodyAxiom>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DependencySpecBodyAxiom {
    condition: String,
    trigger: String,
    bound_vars: Vec<(String, TrustVcType)>,
    /// `true` when the source spec function is `#[trust_vc::opaque]`. An opaque
    /// body axiom is imported but registered *suppressed-until-reveal*: the
    /// encoder hides it (the call stays an uninterpreted symbol of the right
    /// arity/sort) unless a `reveal!` in the verified body discloses it — exactly
    /// as for an in-crate opaque spec. Importing the (true) definitional axiom in
    /// suppressed form can never make a false goal provable; it only lets a
    /// `reveal!` later expose the same body cross-file/in-crate opacity already
    /// exposes. Part of #2778.
    is_opaque: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DependencyConcreteSignature {
    name: String,
    return_ty: TrustVcType,
    params: Vec<(String, TrustVcType)>,
    contract: DependencyConcreteContract,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DependencyConcreteContract {
    return_binding: String,
    return_binding_set: bool,
    requires: Vec<String>,
    ensures: Vec<String>,
    referenced_calls: BTreeSet<String>,
}

impl DependencyConcreteContract {
    fn has_clauses(&self) -> bool {
        !self.requires.is_empty() || !self.ensures.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DependencyCallSite {
    callee: String,
    args: Vec<String>,
    call_expr: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
struct DependencySemanticArtifact {
    crate_name: String,
    package_name: String,
    package_version: String,
    package_env_id: String,
    manifest_path: String,
    source_path: Option<String>,
    source_len: Option<u64>,
    source_sha256: Option<String>,
    semantic_payload: DependencySemanticPayload,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
struct DependencySemanticPayload {
    kind: String,
    proof_facts_exported: bool,
    #[serde(default)]
    concrete_functions: Vec<DependencyConcreteFact>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
struct DependencyConcreteFact {
    name: String,
    return_type: String,
    params: Vec<DependencyConcreteParamFact>,
    return_binding: String,
    requires: Vec<String>,
    ensures: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
struct DependencyConcreteParamFact {
    name: String,
    ty: String,
}

pub(super) fn import_dependency_spec_signatures(
    file_path: &Path,
    func: &ItemFn,
    ctx: &mut VerificationContext,
) -> Result<(), String> {
    let referenced_body_calls = referenced_body_call_paths(func);
    let referenced_contract_calls = referenced_contract_call_paths(func);
    let referenced_calls = referenced_call_paths(func);
    if referenced_calls.is_empty() {
        return Ok(());
    }

    let Some(package_manifest) = find_package_manifest(file_path) else {
        return Ok(());
    };
    let deps = read_path_dependencies(&package_manifest)?;
    for dep in deps {
        if !references_alias(&referenced_calls, &dep.alias) {
            continue;
        }
        import_dependency_specs(
            &dep,
            &referenced_calls,
            &referenced_body_calls,
            &referenced_contract_calls,
            func,
            ctx,
        )?;
    }
    Ok(())
}

fn import_dependency_specs(
    dep: &PathDependency,
    referenced_calls: &BTreeSet<String>,
    referenced_body_calls: &BTreeSet<String>,
    referenced_contract_calls: &BTreeSet<String>,
    target_func: &ItemFn,
    ctx: &mut VerificationContext,
) -> Result<(), String> {
    let lib_path = dependency_lib_path(&dep.manifest_path)?;
    if !lib_path.exists() {
        return Ok(());
    }

    let source = fs::read_to_string(&lib_path).map_err(|err| {
        format!(
            "failed to read dependency spec source {}: {err}",
            lib_path.display()
        )
    })?;
    let file = trust_vc_core::parse_file_allow_tracked(&source).map_err(|err| {
        format!(
            "failed to parse dependency spec source {}: {err}",
            lib_path.display()
        )
    })?;

    let public_functions = collect_public_function_map(&file.items);
    let public_reexports = collect_public_reexports(&file.items);
    let mut public_callables =
        public_dependency_callables(&dep.alias, &public_functions, &public_reexports);
    extend_with_transitive_public_spec_callables(dep, &mut public_callables)?;
    let concrete_signatures = collect_public_concrete_signatures(
        &dep.alias,
        referenced_calls,
        &public_functions,
        &public_reexports,
        &public_callables,
    )?;
    let semantic_artifacts = dependency_semantic_artifacts_from_env()?;

    for concrete in &concrete_signatures {
        ensure_dependency_concrete_contract_import_supported(
            dep,
            concrete,
            referenced_body_calls,
            referenced_contract_calls,
            &semantic_artifacts,
        )?;
    }

    let mut spec_referenced_calls = referenced_calls.clone();
    for concrete in &concrete_signatures {
        spec_referenced_calls.extend(concrete.contract.referenced_calls.iter().cloned());
    }

    let mut used_bound_names = ctx
        .variables()
        .iter()
        .map(|variable| variable.name().to_string())
        .collect::<BTreeSet<_>>();
    let lib_dir = lib_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));
    for spec in collect_public_spec_signatures(
        &file.items,
        &lib_dir,
        &dep.alias,
        "",
        &spec_referenced_calls,
        &mut used_bound_names,
    )? {
        ctx.declare_helper_function_typed(&spec.name, spec.return_ty, spec.params);
        if let Some(body_axiom) = spec.body_axiom {
            import_body_axiom(&spec.name, body_axiom, ctx);
        }
    }
    for spec in collect_transitive_public_spec_signatures(
        dep,
        &spec_referenced_calls,
        &mut used_bound_names,
    )? {
        ctx.declare_helper_function_typed(&spec.name, spec.return_ty, spec.params);
        if let Some(body_axiom) = spec.body_axiom {
            import_body_axiom(&spec.name, body_axiom, ctx);
        }
    }

    let body_call_sites = dependency_body_call_sites(target_func, &dep.alias);
    for concrete in concrete_signatures {
        ctx.declare_helper_function_typed(
            &concrete.name,
            concrete.return_ty.clone(),
            concrete.params.clone(),
        );
        if referenced_body_calls.contains(&concrete.name) {
            import_concrete_call_contracts(&concrete, &body_call_sites, ctx)?;
        }
    }

    Ok(())
}

fn ensure_dependency_concrete_contract_import_supported(
    dep: &PathDependency,
    concrete: &DependencyConcreteSignature,
    referenced_body_calls: &BTreeSet<String>,
    referenced_contract_calls: &BTreeSet<String>,
    semantic_artifacts: &[DependencySemanticArtifact],
) -> Result<(), String> {
    if referenced_contract_calls.contains(&concrete.name) && concrete.contract.has_clauses() {
        return Err(format!(
            "dependency concrete function `{}` is called from the target contract, but TrustVc only imports dependency concrete call contracts for target function bodies",
            concrete.name
        ));
    }
    if referenced_body_calls.contains(&concrete.name)
        && !concrete.contract.ensures.is_empty()
        && !has_matching_dependency_concrete_fact(dep, concrete, semantic_artifacts)?
    {
        return Err(format!(
            "dependency concrete function `{}` has postconditions, but TrustVc cannot import dependency concrete postconditions without matching semantic proof artifacts",
            concrete.name
        ));
    }
    Ok(())
}

fn has_matching_dependency_concrete_fact(
    dep: &PathDependency,
    concrete: &DependencyConcreteSignature,
    semantic_artifacts: &[DependencySemanticArtifact],
) -> Result<bool, String> {
    let Some(artifact) = matching_dependency_semantic_artifact(dep, semantic_artifacts)? else {
        return Ok(false);
    };
    if artifact.semantic_payload.kind != TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND
        || !artifact.semantic_payload.proof_facts_exported
    {
        return Ok(false);
    }
    validate_dependency_semantic_artifact_source_binding(dep, artifact)?;

    let Some(local_name) = concrete
        .name
        .strip_prefix(&format!("{}::", dep.alias))
        .map(str::to_string)
    else {
        return Ok(false);
    };
    let expected_requires = dequalify_dependency_contract_clauses(&concrete.contract.requires, dep);
    let expected_ensures = dequalify_dependency_contract_clauses(&concrete.contract.ensures, dep);
    let expected_params = concrete
        .params
        .iter()
        .map(|(name, ty)| DependencyConcreteParamFact {
            name: name.clone(),
            ty: ty.to_type_string(),
        })
        .collect::<Vec<_>>();

    Ok(artifact
        .semantic_payload
        .concrete_functions
        .iter()
        .any(|fact| {
            fact.name == local_name
                && fact.return_type == concrete.return_ty.to_type_string()
                && fact.params == expected_params
                && fact.return_binding == concrete.contract.return_binding
                && fact.requires == expected_requires
                && fact.ensures == expected_ensures
        }))
}

fn matching_dependency_semantic_artifact<'a>(
    dep: &PathDependency,
    semantic_artifacts: &'a [DependencySemanticArtifact],
) -> Result<Option<&'a DependencySemanticArtifact>, String> {
    let Some(identity) = read_package_manifest_identity(&dep.manifest_path)? else {
        return Ok(None);
    };
    let expected_manifest_path = canonical_manifest_path_for_hash(&dep.manifest_path);
    Ok(semantic_artifacts.iter().find(|artifact| {
        artifact.package_name == identity.name
            && artifact.package_version == identity.version
            && artifact.package_env_id == identity.package_env_id
            && artifact.manifest_path == expected_manifest_path
    }))
}

fn validate_dependency_semantic_artifact_source_binding(
    dep: &PathDependency,
    artifact: &DependencySemanticArtifact,
) -> Result<(), String> {
    let (Some(source_path), Some(source_len), Some(source_sha256)) = (
        artifact.source_path.as_deref(),
        artifact.source_len,
        artifact.source_sha256.as_deref(),
    ) else {
        return Err(format!(
            "dependency semantic artifact for `{}` is missing dependency source binding metadata",
            dep.alias
        ));
    };
    if source_path.is_empty() || source_sha256.is_empty() {
        return Err(format!(
            "dependency semantic artifact for `{}` has incomplete dependency source binding metadata",
            dep.alias
        ));
    }

    let expected_source_path = dependency_lib_path(&dep.manifest_path)?;
    let expected_source_path = canonical_manifest_path_for_hash(&expected_source_path);
    if source_path != expected_source_path {
        return Err(format!(
            "dependency semantic artifact for `{}` source path mismatch for {}",
            dep.alias, expected_source_path
        ));
    }

    let (actual_source_len, actual_source_sha256) =
        dependency_source_digest(Path::new(&expected_source_path))?;
    if source_len != actual_source_len {
        return Err(format!(
            "dependency semantic artifact for `{}` source length mismatch for {}",
            dep.alias, expected_source_path
        ));
    }
    if source_sha256 != actual_source_sha256 {
        return Err(format!(
            "dependency semantic artifact for `{}` source hash mismatch for {}",
            dep.alias, expected_source_path
        ));
    }

    Ok(())
}

fn dequalify_dependency_contract_clauses(clauses: &[String], dep: &PathDependency) -> Vec<String> {
    let prefix = format!("{} :: ", dep.alias);
    clauses
        .iter()
        .map(|clause| clause.replace(&prefix, ""))
        .collect()
}

fn import_body_axiom(
    spec_name: &str,
    body_axiom: DependencySpecBodyAxiom,
    ctx: &mut VerificationContext,
) {
    for (bound_name, ty) in &body_axiom.bound_vars {
        if ctx.get_variable_type(bound_name).is_none() {
            ctx.declare_var_typed(bound_name, ty.clone());
        }
    }

    let axiom_name = format!("__body_axiom_{}_dependency_spec", sanitize_ident(spec_name));
    if ctx
        .obligations()
        .iter()
        .any(|obligation| obligation.name() == axiom_name)
    {
        return;
    }

    // `with_opaque(true)` registers an opaque dependency spec's body axiom in
    // suppressed-until-reveal form: the encoder's broadcast-setup reveal gate
    // (setup_broadcasts.rs / invariants) drops it unless the function is named by
    // a `reveal!` obligation. The `__body_axiom_` prefix is what marks it as a
    // body axiom for that gate, and the trigger carries the fully-qualified
    // dependency name (e.g. `trust_vc_std::arithmetic::mul`) so a bare
    // `reveal!(mul)` matches it by trigger-head leaf. Part of #2778.
    ctx.push_obligation(
        ProofObligation::broadcast_assume(axiom_name, body_axiom.condition)
            .with_bound_vars(
                body_axiom
                    .bound_vars
                    .into_iter()
                    .map(|(name, _)| name)
                    .collect(),
            )
            .with_trigger_patterns(vec![vec![body_axiom.trigger]])
            .with_opaque(body_axiom.is_opaque),
    );
}

fn import_concrete_call_contracts(
    concrete: &DependencyConcreteSignature,
    body_call_sites: &[DependencyCallSite],
    ctx: &mut VerificationContext,
) -> Result<(), String> {
    for (call_index, call_site) in body_call_sites
        .iter()
        .filter(|call_site| call_site.callee == concrete.name)
        .enumerate()
    {
        if call_site.args.len() != concrete.params.len() {
            return Err(format!(
                "Call to dependency concrete function `{}` has {} argument(s), but its contract has {} parameter(s)",
                concrete.name,
                call_site.args.len(),
                concrete.params.len()
            ));
        }

        let mut substitutions = BTreeMap::new();
        for ((param_name, _), arg) in concrete.params.iter().zip(&call_site.args) {
            let arg_expr = parse_dependency_contract_expr(&concrete.name, arg, "call argument")?;
            substitutions.insert(param_name.clone(), arg_expr);
        }
        substitutions.insert(
            concrete.contract.return_binding.clone(),
            parse_dependency_contract_expr(&concrete.name, &call_site.call_expr, "call result")?,
        );

        let requires = concrete
            .contract
            .requires
            .iter()
            .map(|clause| {
                substitute_dependency_contract_clause(&concrete.name, clause, &substitutions)
            })
            .collect::<Result<Vec<_>, _>>()?;

        for (index, condition) in requires.iter().enumerate() {
            let name = format!(
                "__call_requires_{}_dependency_concrete_{}_{}",
                sanitize_ident(&concrete.name),
                call_index,
                index
            );
            ctx.push_obligation(ProofObligation::assert(name, condition.clone()));
        }

        let ensures = concrete
            .contract
            .ensures
            .iter()
            .map(|clause| {
                substitute_dependency_contract_clause(&concrete.name, clause, &substitutions)
            })
            .collect::<Result<Vec<_>, _>>()?;

        for (index, condition) in ensures.iter().enumerate() {
            let name = format!(
                "__call_ensures_{}_dependency_concrete_{}_{}",
                sanitize_ident(&concrete.name),
                call_index,
                index
            );
            ctx.push_obligation(ProofObligation::assume(name, condition.clone()));
        }
    }

    Ok(())
}

fn parse_dependency_contract_expr(
    function_name: &str,
    source: &str,
    context: &str,
) -> Result<Expr, String> {
    syn::parse_str::<Expr>(source).map_err(|err| {
        format!("failed to parse dependency concrete function `{function_name}` {context}: {err}")
    })
}

fn substitute_dependency_contract_clause(
    function_name: &str,
    clause: &str,
    substitutions: &BTreeMap<String, Expr>,
) -> Result<String, String> {
    let mut expr = parse_dependency_contract_expr(function_name, clause, "contract clause")?;
    DependencyContractSubstituter { substitutions }.visit_expr_mut(&mut expr);
    Ok(expr.to_token_stream().to_string())
}

struct DependencyContractSubstituter<'a> {
    substitutions: &'a BTreeMap<String, Expr>,
}

impl VisitMut for DependencyContractSubstituter<'_> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let Expr::Path(path) = expr else {
            syn::visit_mut::visit_expr_mut(self, expr);
            return;
        };
        if path.qself.is_none() && path.path.segments.len() == 1 {
            if let Some(segment) = path.path.segments.first() {
                if let Some(replacement) = self.substitutions.get(&segment.ident.to_string()) {
                    *expr = replacement.clone();
                    return;
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

fn references_alias(referenced_calls: &BTreeSet<String>, alias: &str) -> bool {
    let prefix = format!("{alias}::");
    referenced_calls
        .iter()
        .any(|call| call.starts_with(&prefix))
}

fn find_package_manifest(file_path: &Path) -> Option<PathBuf> {
    let mut dir = file_path.parent()?;
    loop {
        let manifest = dir.join("Cargo.toml");
        if manifest.is_file() {
            return Some(manifest);
        }
        dir = dir.parent()?;
    }
}

fn dependency_lib_path(manifest_path: &Path) -> Result<PathBuf, String> {
    let root = manifest_path.parent().ok_or_else(|| {
        format!(
            "dependency manifest has no parent: {}",
            manifest_path.display()
        )
    })?;
    let source = fs::read_to_string(manifest_path).map_err(|err| {
        format!(
            "failed to read dependency manifest {}: {err}",
            manifest_path.display()
        )
    })?;
    if let Some(path) = read_lib_path_from_manifest(&source) {
        Ok(root.join(path))
    } else {
        Ok(root.join("src/lib.rs"))
    }
}

fn read_path_dependencies(manifest_path: &Path) -> Result<Vec<PathDependency>, String> {
    let root = manifest_path.parent().ok_or_else(|| {
        format!(
            "package manifest has no parent: {}",
            manifest_path.display()
        )
    })?;
    let source = fs::read_to_string(manifest_path).map_err(|err| {
        format!(
            "failed to read package manifest {}: {err}",
            manifest_path.display()
        )
    })?;

    let mut deps = Vec::new();
    let mut table = ManifestTable::Other;

    for raw_line in source.lines() {
        let stripped = strip_toml_comment(raw_line);
        let line = stripped.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = table_header(line) {
            table = manifest_table(header);
            continue;
        }

        match &table {
            ManifestTable::Dependencies => {
                if let Some((alias, value)) = line.split_once('=') {
                    if let Some(path) = toml_string_field(value, "path") {
                        deps.push(PathDependency {
                            alias: rust_crate_name(alias.trim()),
                            manifest_path: root.join(path).join("Cargo.toml"),
                        });
                    }
                }
            }
            ManifestTable::DependencyDetail(alias) => {
                if let Some((key, value)) = line.split_once('=') {
                    if key.trim() == "path" {
                        if let Some(path) = toml_string_value(value) {
                            deps.push(PathDependency {
                                alias: alias.clone(),
                                manifest_path: root.join(path).join("Cargo.toml"),
                            });
                        }
                    }
                }
            }
            ManifestTable::Other | ManifestTable::Lib => {}
        }
    }

    deps.sort_by(|left, right| left.alias.cmp(&right.alias));
    deps.dedup_by(|left, right| left.alias == right.alias);
    Ok(deps)
}

fn dependency_semantic_artifacts_from_env() -> Result<Vec<DependencySemanticArtifact>, String> {
    let Ok(value) = std::env::var(TRUST_VC_DEPENDENCY_FACTS_ENV) else {
        return Ok(Vec::new());
    };
    if value.trim().is_empty() {
        return Ok(Vec::new());
    }
    serde_json::from_str(&value).map_err(|err| {
        format!(
            "failed to parse cargo-trust-vc dependency semantic facts from {TRUST_VC_DEPENDENCY_FACTS_ENV}: {err}"
        )
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PackageManifestIdentity {
    name: String,
    version: String,
    package_env_id: String,
}

fn read_package_manifest_identity(
    manifest_path: &Path,
) -> Result<Option<PackageManifestIdentity>, String> {
    let source = fs::read_to_string(manifest_path).map_err(|err| {
        format!(
            "failed to read dependency manifest {}: {err}",
            manifest_path.display()
        )
    })?;
    let mut in_package_table = false;
    let mut name = None;
    let mut version = None;
    for raw_line in source.lines() {
        let stripped = strip_toml_comment(raw_line);
        let line = stripped.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = table_header(line) {
            in_package_table = header.trim() == "package";
            continue;
        }
        if !in_package_table {
            continue;
        }
        if let Some((key, value)) = line.split_once('=') {
            match key.trim() {
                "name" => name = toml_string_value(value).map(|path| path.display().to_string()),
                "version" => {
                    version = toml_string_value(value).map(|path| path.display().to_string())
                }
                _ => {}
            }
        }
    }
    let (Some(name), Some(version)) = (name, version) else {
        return Ok(None);
    };
    let package_env_id = package_env_id_from_manifest_path(&name, &version, manifest_path);
    Ok(Some(PackageManifestIdentity {
        name,
        version,
        package_env_id,
    }))
}

fn package_env_id_from_manifest_path(
    package_name: &str,
    package_version: &str,
    manifest_path: &Path,
) -> String {
    let digest = Sha256::digest(canonical_manifest_path_for_hash(manifest_path).as_bytes());
    let mut manifest_path_hash = String::with_capacity(12);
    for byte in &digest[..6] {
        manifest_path_hash.push_str(&format!("{byte:02x}"));
    }
    format!("{package_name}-{package_version}-{manifest_path_hash}")
}

fn canonical_manifest_path_for_hash(manifest_path: &Path) -> String {
    manifest_path
        .canonicalize()
        .unwrap_or_else(|_| manifest_path.to_path_buf())
        .to_string_lossy()
        .into_owned()
}

fn dependency_source_digest(path: &Path) -> Result<(u64, String), String> {
    let bytes = fs::read(path).map_err(|err| {
        format!(
            "failed to read dependency source {} for semantic artifact validation: {err}",
            path.display()
        )
    })?;
    Ok((bytes.len() as u64, format!("sha256:{}", sha256_hex(&bytes))))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        hex.push_str(&format!("{byte:02x}"));
    }
    hex
}

fn read_lib_path_from_manifest(source: &str) -> Option<PathBuf> {
    let mut table = ManifestTable::Other;
    for raw_line in source.lines() {
        let stripped = strip_toml_comment(raw_line);
        let line = stripped.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = table_header(line) {
            table = manifest_table(header);
            continue;
        }
        if table == ManifestTable::Lib {
            if let Some((key, value)) = line.split_once('=') {
                if key.trim() == "path" {
                    return toml_string_value(value);
                }
            }
        }
    }
    None
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ManifestTable {
    Dependencies,
    DependencyDetail(String),
    Lib,
    Other,
}

fn manifest_table(header: &str) -> ManifestTable {
    match header.trim() {
        "dependencies" => ManifestTable::Dependencies,
        "lib" => ManifestTable::Lib,
        header if header.starts_with("dependencies.") => {
            let alias = header.trim_start_matches("dependencies.");
            ManifestTable::DependencyDetail(rust_crate_name(alias))
        }
        _ => ManifestTable::Other,
    }
}

fn table_header(line: &str) -> Option<&str> {
    line.strip_prefix('[')?.strip_suffix(']')
}

fn rust_crate_name(raw: &str) -> String {
    raw.trim()
        .trim_matches('"')
        .trim_matches('\'')
        .replace('-', "_")
}

fn strip_toml_comment(line: &str) -> String {
    let mut out = String::new();
    let mut in_string = false;
    let mut escaped = false;
    for ch in line.chars() {
        if escaped {
            out.push(ch);
            escaped = false;
            continue;
        }
        if in_string && ch == '\\' {
            out.push(ch);
            escaped = true;
            continue;
        }
        if ch == '"' {
            in_string = !in_string;
            out.push(ch);
            continue;
        }
        if ch == '#' && !in_string {
            break;
        }
        out.push(ch);
    }
    out
}

fn toml_string_field(value: &str, field: &str) -> Option<PathBuf> {
    let offset = value.find(field)?;
    let rest = &value[offset + field.len()..];
    let after_equals = rest.trim_start().strip_prefix('=')?.trim_start();
    toml_string_value(after_equals)
}

fn toml_string_value(value: &str) -> Option<PathBuf> {
    let value = value.trim_start();
    let after_quote = value.strip_prefix('"')?;
    let end = after_quote.find('"')?;
    Some(PathBuf::from(&after_quote[..end]))
}

fn collect_public_spec_signatures(
    items: &[syn::Item],
    module_dir: &Path,
    alias: &str,
    module_path: &str,
    referenced_calls: &BTreeSet<String>,
    used_bound_names: &mut BTreeSet<String>,
) -> Result<Vec<DependencySpecSignature>, String> {
    let mut specs = Vec::new();
    for item in items {
        match item {
            syn::Item::Fn(item_fn) if is_public(&item_fn.vis) && has_spec_attr(&item_fn.attrs) => {
                let local_name = qualified_name(module_path, &item_fn.sig.ident.to_string());
                let qualified = format!("{alias}::{local_name}");
                if referenced_calls.contains(&qualified) {
                    specs.push(signature_from_spec(
                        alias,
                        &local_name,
                        item_fn,
                        used_bound_names,
                    )?);
                }
            }
            syn::Item::Mod(module) if is_public(&module.vis) => {
                let path = qualified_name(module_path, &module.ident.to_string());
                if let Some((_, items)) = &module.content {
                    // Inline module: recurse directly (directory unchanged).
                    specs.extend(collect_public_spec_signatures(
                        items,
                        module_dir,
                        alias,
                        &path,
                        referenced_calls,
                        used_bound_names,
                    )?);
                } else if let Some(module_file) = resolve_dependency_module_file(module, module_dir)
                {
                    // Out-of-line (file) module — e.g. `pub mod arithmetic;` whose
                    // body lives in a sibling source file. Resolve, parse, and
                    // recurse so a referenced spec like `trust_vc_std::arithmetic::mul`
                    // is found. Fail closed: an unreadable / unparseable module file
                    // is skipped, leaving any call into it an uninterpreted symbol.
                    // Part of #2778.
                    if let Ok(source) = fs::read_to_string(&module_file) {
                        if let Ok(parsed) = trust_vc_core::parse_file_allow_tracked(&source) {
                            let child_dir = module_file
                                .parent()
                                .map(Path::to_path_buf)
                                .unwrap_or_else(|| module_dir.to_path_buf());
                            specs.extend(collect_public_spec_signatures(
                                &parsed.items,
                                &child_dir,
                                alias,
                                &path,
                                referenced_calls,
                                used_bound_names,
                            )?);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Ok(specs)
}

/// Resolves an out-of-line (`mod name;`) dependency module to its source file,
/// mirroring rustc's resolution: an explicit `#[path = "..."]`, else
/// `<dir>/name.rs`, else `<dir>/name/mod.rs`. Returns `None` when no candidate
/// exists (the caller then skips it — fail closed). Part of #2778.
fn resolve_dependency_module_file(module: &syn::ItemMod, module_dir: &Path) -> Option<PathBuf> {
    let explicit = module.attrs.iter().find_map(|attr| {
        if !attr.path().is_ident("path") {
            return None;
        }
        match &attr.meta {
            syn::Meta::NameValue(nv) => match &nv.value {
                Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(value),
                    ..
                }) => Some(value.value()),
                _ => None,
            },
            _ => None,
        }
    });
    if let Some(explicit) = explicit {
        let candidate = module_dir.join(explicit);
        return candidate.exists().then_some(candidate);
    }

    let mod_name = module.ident.to_string();
    let direct = module_dir.join(format!("{mod_name}.rs"));
    if direct.exists() {
        return Some(direct);
    }
    let nested = module_dir.join(&mod_name).join("mod.rs");
    nested.exists().then_some(nested)
}

fn collect_public_function_map(items: &[syn::Item]) -> BTreeMap<String, &ItemFn> {
    let mut functions = BTreeMap::new();
    collect_public_function_map_inner(items, "", &mut functions);
    functions
}

fn collect_public_function_map_inner<'a>(
    items: &'a [syn::Item],
    module_path: &str,
    functions: &mut BTreeMap<String, &'a ItemFn>,
) {
    for item in items {
        match item {
            syn::Item::Fn(item_fn) if is_public(&item_fn.vis) => {
                let local_name = qualified_name(module_path, &item_fn.sig.ident.to_string());
                functions.insert(local_name, item_fn);
            }
            syn::Item::Mod(module) if is_public(&module.vis) => {
                if let Some((_, items)) = &module.content {
                    let path = qualified_name(module_path, &module.ident.to_string());
                    collect_public_function_map_inner(items, &path, functions);
                }
            }
            _ => {}
        }
    }
}

fn collect_public_reexports(items: &[syn::Item]) -> BTreeMap<String, String> {
    let mut reexports = BTreeMap::new();
    collect_public_reexports_inner(items, "", &mut reexports);
    reexports
}

fn collect_public_reexports_inner(
    items: &[syn::Item],
    module_path: &str,
    reexports: &mut BTreeMap<String, String>,
) {
    for item in items {
        match item {
            syn::Item::Use(item_use) if is_public(&item_use.vis) => {
                collect_public_reexport_tree(
                    module_path,
                    &mut Vec::new(),
                    &item_use.tree,
                    reexports,
                );
            }
            syn::Item::Mod(module) if is_public(&module.vis) => {
                if let Some((_, items)) = &module.content {
                    let path = qualified_name(module_path, &module.ident.to_string());
                    collect_public_reexports_inner(items, &path, reexports);
                }
            }
            _ => {}
        }
    }
}

fn collect_public_reexport_tree(
    module_path: &str,
    prefix: &mut Vec<String>,
    tree: &syn::UseTree,
    reexports: &mut BTreeMap<String, String>,
) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            collect_public_reexport_tree(module_path, prefix, &path.tree, reexports);
            prefix.pop();
        }
        syn::UseTree::Name(name) => {
            let exported = qualified_name(module_path, &name.ident.to_string());
            if let Some(source) = reexport_source_path(module_path, prefix, &name.ident.to_string())
            {
                reexports.insert(exported, source);
            }
        }
        syn::UseTree::Rename(rename) => {
            let exported = qualified_name(module_path, &rename.rename.to_string());
            if let Some(source) =
                reexport_source_path(module_path, prefix, &rename.ident.to_string())
            {
                reexports.insert(exported, source);
            }
        }
        syn::UseTree::Group(group) => {
            for tree in &group.items {
                collect_public_reexport_tree(module_path, prefix, tree, reexports);
            }
        }
        syn::UseTree::Glob(_) => {}
    }
}

fn reexport_source_path(module_path: &str, prefix: &[String], leaf: &str) -> Option<String> {
    let mut path = prefix.to_vec();
    path.push(leaf.to_string());
    if path.iter().any(|segment| segment == "super") {
        return None;
    }

    let crate_absolute = path.first().is_some_and(|segment| segment == "crate");
    if crate_absolute || path.first().is_some_and(|segment| segment == "self") {
        path.remove(0);
    }
    if path.is_empty() {
        return None;
    }

    let local = path.join("::");
    if crate_absolute || module_path.is_empty() {
        Some(local)
    } else {
        Some(qualified_name(module_path, &local))
    }
}

fn public_dependency_callables(
    alias: &str,
    functions: &BTreeMap<String, &ItemFn>,
    reexports: &BTreeMap<String, String>,
) -> BTreeMap<String, String> {
    let mut callables = BTreeMap::new();
    for local_name in functions.keys() {
        callables.insert(local_name.clone(), format!("{alias}::{local_name}"));
    }
    for exported_name in reexports.keys() {
        callables.insert(exported_name.clone(), format!("{alias}::{exported_name}"));
    }
    callables
}

fn extend_with_transitive_public_spec_callables(
    dep: &PathDependency,
    callables: &mut BTreeMap<String, String>,
) -> Result<(), String> {
    for transitive_dep in read_path_dependencies(&dep.manifest_path)? {
        let Some(file) = parse_dependency_lib_file(&transitive_dep)? else {
            continue;
        };
        let public_functions = collect_public_function_map(&file.items);
        for (local_name, item_fn) in public_functions {
            if !has_spec_attr(&item_fn.attrs) {
                continue;
            }
            let qualified = format!("{}::{local_name}", transitive_dep.alias);
            callables.entry(qualified.clone()).or_insert(qualified);
        }
    }
    Ok(())
}

fn collect_transitive_public_spec_signatures(
    dep: &PathDependency,
    referenced_calls: &BTreeSet<String>,
    used_bound_names: &mut BTreeSet<String>,
) -> Result<Vec<DependencySpecSignature>, String> {
    let mut specs = Vec::new();
    for transitive_dep in read_path_dependencies(&dep.manifest_path)? {
        if !references_alias(referenced_calls, &transitive_dep.alias) {
            continue;
        }
        let Some(file) = parse_dependency_lib_file(&transitive_dep)? else {
            continue;
        };
        let transitive_lib_dir = dependency_lib_path(&transitive_dep.manifest_path)?
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."));
        specs.extend(collect_public_spec_signatures(
            &file.items,
            &transitive_lib_dir,
            &transitive_dep.alias,
            "",
            referenced_calls,
            used_bound_names,
        )?);
    }
    Ok(specs)
}

fn parse_dependency_lib_file(dep: &PathDependency) -> Result<Option<syn::File>, String> {
    let lib_path = dependency_lib_path(&dep.manifest_path)?;
    if !lib_path.exists() {
        return Ok(None);
    }

    let source = fs::read_to_string(&lib_path).map_err(|err| {
        format!(
            "failed to read dependency spec source {}: {err}",
            lib_path.display()
        )
    })?;
    trust_vc_core::parse_file_allow_tracked(&source)
        .map(Some)
        .map_err(|err| {
            format!(
                "failed to parse dependency spec source {}: {err}",
                lib_path.display()
            )
        })
}

fn collect_public_concrete_signatures(
    alias: &str,
    referenced_calls: &BTreeSet<String>,
    functions: &BTreeMap<String, &ItemFn>,
    reexports: &BTreeMap<String, String>,
    public_callables: &BTreeMap<String, String>,
) -> Result<Vec<DependencyConcreteSignature>, String> {
    let mut signatures = Vec::new();
    let mut seen = BTreeSet::new();
    let prefix = format!("{alias}::");

    for referenced in referenced_calls {
        let Some(exported_local_name) = referenced.strip_prefix(&prefix) else {
            continue;
        };
        let Some(item_fn) = functions.get(exported_local_name).or_else(|| {
            reexports
                .get(exported_local_name)
                .and_then(|target| functions.get(target))
        }) else {
            continue;
        };
        if has_spec_attr(&item_fn.attrs) {
            continue;
        }
        let imported_name = format!("{alias}::{exported_local_name}");
        if !seen.insert(imported_name.clone()) {
            continue;
        }

        signatures.push(signature_from_concrete(
            alias,
            exported_local_name,
            item_fn,
            public_callables,
        )?);
    }

    Ok(signatures)
}

fn signature_from_spec(
    alias: &str,
    local_name: &str,
    item_fn: &ItemFn,
    used_bound_names: &mut BTreeSet<String>,
) -> Result<DependencySpecSignature, String> {
    if has_dependency_contract_attr(&item_fn.attrs) {
        return Err(format!(
            "dependency spec function `{alias}::{local_name}` has contract or recommendation attributes, but TrustVc does not import dependency spec contracts"
        ));
    }

    let return_ty = match &item_fn.sig.output {
        syn::ReturnType::Type(_, ty) => type_from_syn(ty),
        syn::ReturnType::Default => {
            return Err(format!(
                "dependency spec function `{alias}::{local_name}` has no return type"
            ))
        }
    };
    if return_ty.contains_opaque() {
        return Err(format!(
            "dependency spec function `{alias}::{local_name}` has unsupported return type `{}`",
            return_ty.to_type_string()
        ));
    }

    let mut params = Vec::new();
    for input in &item_fn.sig.inputs {
        let syn::FnArg::Typed(pat_type) = input else {
            return Err(format!(
                "dependency spec function `{alias}::{local_name}` must not take self"
            ));
        };
        let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
            return Err(format!(
                "dependency spec function `{alias}::{local_name}` has unsupported parameter pattern"
            ));
        };
        let ty = type_from_syn(&pat_type.ty);
        if ty.contains_opaque() {
            return Err(format!(
                "dependency spec function `{alias}::{local_name}` has unsupported parameter type `{}` for `{}`",
                ty.to_type_string(),
                pat_ident.ident
            ));
        }
        params.push((pat_ident.ident.to_string(), ty));
    }

    let body_axiom = body_axiom_from_spec(
        alias,
        local_name,
        item_fn,
        &return_ty,
        &params,
        used_bound_names,
    )?;

    Ok(DependencySpecSignature {
        name: format!("{alias}::{local_name}"),
        return_ty,
        params,
        body_axiom,
    })
}

fn signature_from_concrete(
    alias: &str,
    local_name: &str,
    item_fn: &ItemFn,
    public_callables: &BTreeMap<String, String>,
) -> Result<DependencyConcreteSignature, String> {
    if !signature_shape_allows_dependency_concrete_import(&item_fn.sig) {
        return Err(format!(
            "dependency concrete function `{alias}::{local_name}` has an unsupported signature shape for import"
        ));
    }

    let return_ty = match &item_fn.sig.output {
        syn::ReturnType::Type(_, ty) => {
            if is_reference_type(ty) {
                return Err(format!(
                    "dependency concrete function `{alias}::{local_name}` has unsupported reference return type"
                ));
            }
            type_from_syn(ty)
        }
        syn::ReturnType::Default => TrustVcType::Unit,
    };
    if return_ty.contains_opaque() {
        return Err(format!(
            "dependency concrete function `{alias}::{local_name}` has unsupported return type `{}`",
            return_ty.to_type_string()
        ));
    }

    let mut params = Vec::new();
    for input in &item_fn.sig.inputs {
        let syn::FnArg::Typed(pat_type) = input else {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` must not take self"
            ));
        };
        let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` has unsupported parameter pattern"
            ));
        };
        if is_reference_type(&pat_type.ty) {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` has unsupported reference parameter `{}`",
                pat_ident.ident
            ));
        }
        let ty = type_from_syn(&pat_type.ty);
        if ty.contains_opaque() {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` has unsupported parameter type `{}` for `{}`",
                ty.to_type_string(),
                pat_ident.ident
            ));
        }
        params.push((pat_ident.ident.to_string(), ty));
    }

    let contract = dependency_concrete_contract_from_attrs(
        alias,
        local_name,
        &item_fn.attrs,
        public_callables,
    )?;
    if params
        .iter()
        .any(|(param_name, _)| param_name == &contract.return_binding)
    {
        return Err(format!(
            "dependency concrete function `{alias}::{local_name}` return binding `{}` conflicts with a parameter name",
            contract.return_binding
        ));
    }

    Ok(DependencyConcreteSignature {
        name: format!("{alias}::{local_name}"),
        return_ty,
        params,
        contract,
    })
}

fn signature_shape_allows_dependency_concrete_import(sig: &syn::Signature) -> bool {
    sig.constness.is_none()
        && sig.asyncness.is_none()
        && sig.unsafety.is_none()
        && sig.abi.is_none()
        && sig.variadic.is_none()
        && sig.generics.params.is_empty()
        && sig.generics.where_clause.is_none()
}

fn is_reference_type(ty: &syn::Type) -> bool {
    matches!(ty, syn::Type::Reference(_))
}

struct DependencyContractClause {
    name: syn::Ident,
    args: Vec<Expr>,
}

impl Parse for DependencyContractClause {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name: syn::Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args = Punctuated::<Expr, Token![,]>::parse_terminated(&content)?;
        Ok(Self {
            name,
            args: args.into_iter().collect(),
        })
    }
}

fn dependency_concrete_contract_from_attrs(
    alias: &str,
    local_name: &str,
    attrs: &[syn::Attribute],
    public_callables: &BTreeMap<String, String>,
) -> Result<DependencyConcreteContract, String> {
    let mut contract = DependencyConcreteContract {
        return_binding: "result".to_string(),
        return_binding_set: false,
        requires: Vec::new(),
        ensures: Vec::new(),
        referenced_calls: BTreeSet::new(),
    };

    for attr in attrs {
        let Some(last) = attr
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
        else {
            continue;
        };
        match last.as_str() {
            "requires" => {
                let expr = attr.parse_args::<Expr>().map_err(|source| {
                    format!(
                        "failed to parse dependency concrete function `{alias}::{local_name}` requires clause: {source}"
                    )
                })?;
                push_dependency_contract_expr(
                    alias,
                    local_name,
                    "requires",
                    expr,
                    public_callables,
                    &mut contract.requires,
                    &mut contract.referenced_calls,
                )?;
            }
            "ensures" => {
                let expr = attr.parse_args::<Expr>().map_err(|source| {
                    format!(
                        "failed to parse dependency concrete function `{alias}::{local_name}` ensures clause: {source}"
                    )
                })?;
                push_dependency_contract_expr(
                    alias,
                    local_name,
                    "ensures",
                    expr,
                    public_callables,
                    &mut contract.ensures,
                    &mut contract.referenced_calls,
                )?;
            }
            "returns" => {
                let expr = attr.parse_args::<Expr>().map_err(|source| {
                    format!(
                        "failed to parse dependency concrete function `{alias}::{local_name}` returns clause: {source}"
                    )
                })?;
                apply_dependency_returns_clause(
                    alias,
                    local_name,
                    expr,
                    public_callables,
                    &mut contract,
                )?;
            }
            "contract" => {
                let clauses = attr
                    .parse_args_with(
                        Punctuated::<DependencyContractClause, Token![,]>::parse_terminated,
                    )
                    .map_err(|source| {
                        format!(
                            "failed to parse dependency concrete function `{alias}::{local_name}` contract: {source}"
                        )
                    })?;
                for clause in clauses {
                    apply_dependency_contract_clause(
                        alias,
                        local_name,
                        clause,
                        public_callables,
                        &mut contract,
                    )?;
                }
            }
            "recommends" => {
                return Err(format!(
                    "dependency concrete function `{alias}::{local_name}` has recommendation attributes, but TrustVc does not import dependency concrete recommendations"
                ));
            }
            _ => {}
        }
    }

    Ok(contract)
}

fn apply_dependency_contract_clause(
    alias: &str,
    local_name: &str,
    clause: DependencyContractClause,
    public_callables: &BTreeMap<String, String>,
    contract: &mut DependencyConcreteContract,
) -> Result<(), String> {
    let clause_name = clause.name.to_string();
    match clause_name.as_str() {
        "requires" => {
            ensure_dependency_contract_clause_nonempty(alias, local_name, &clause)?;
            for expr in clause.args {
                push_dependency_contract_expr(
                    alias,
                    local_name,
                    "requires",
                    expr,
                    public_callables,
                    &mut contract.requires,
                    &mut contract.referenced_calls,
                )?;
            }
        }
        "ensures" => {
            ensure_dependency_contract_clause_nonempty(alias, local_name, &clause)?;
            for expr in clause.args {
                push_dependency_contract_expr(
                    alias,
                    local_name,
                    "ensures",
                    expr,
                    public_callables,
                    &mut contract.ensures,
                    &mut contract.referenced_calls,
                )?;
            }
        }
        "returns" => {
            if clause.args.len() != 1 {
                return Err(format!(
                    "dependency concrete function `{alias}::{local_name}` returns() clause must take exactly one argument"
                ));
            }
            let expr = clause.args.into_iter().next().ok_or_else(|| {
                format!(
                    "dependency concrete function `{alias}::{local_name}` returns() clause is missing its return expression"
                )
            })?;
            apply_dependency_returns_clause(alias, local_name, expr, public_callables, contract)?;
        }
        "recommends" => {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` has recommendation attributes, but TrustVc does not import dependency concrete recommendations"
            ));
        }
        "decreases" => {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` has decreases clauses, but TrustVc does not import dependency concrete termination contracts"
            ));
        }
        other => {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` has unsupported contract clause `{other}`"
            ));
        }
    }
    Ok(())
}

fn ensure_dependency_contract_clause_nonempty(
    alias: &str,
    local_name: &str,
    clause: &DependencyContractClause,
) -> Result<(), String> {
    if clause.args.is_empty() {
        return Err(format!(
            "dependency concrete function `{alias}::{local_name}` has empty {}() clause",
            clause.name
        ));
    }
    Ok(())
}

fn apply_dependency_returns_clause(
    alias: &str,
    local_name: &str,
    expr: Expr,
    public_callables: &BTreeMap<String, String>,
    contract: &mut DependencyConcreteContract,
) -> Result<(), String> {
    if let Some(binding) = returns_expr_ident_opt(&expr) {
        if contract.return_binding_set {
            return Err(format!(
                "dependency concrete function `{alias}::{local_name}` has duplicate returns bindings"
            ));
        }
        contract.return_binding = binding;
        contract.return_binding_set = true;
        return Ok(());
    }
    if tuple_return_names_expr(&expr) {
        return Err(format!(
            "dependency concrete function `{alias}::{local_name}` has unsupported tuple returns binding"
        ));
    }

    let direct_return = syn::parse_str::<Expr>(&format!("result == ({})", quote!(#expr)))
        .map_err(|source| {
            format!(
                "failed to build dependency concrete function `{alias}::{local_name}` direct returns clause: {source}"
            )
        })?;
    push_dependency_contract_expr(
        alias,
        local_name,
        "returns",
        direct_return,
        public_callables,
        &mut contract.ensures,
        &mut contract.referenced_calls,
    )
}

fn push_dependency_contract_expr(
    alias: &str,
    local_name: &str,
    clause_name: &str,
    mut expr: Expr,
    public_callables: &BTreeMap<String, String>,
    out: &mut Vec<String>,
    referenced_calls: &mut BTreeSet<String>,
) -> Result<(), String> {
    let calls = qualify_dependency_contract_calls(
        alias,
        local_name,
        clause_name,
        &mut expr,
        public_callables,
    )?;
    referenced_calls.extend(calls);
    out.push(expr.to_token_stream().to_string());
    Ok(())
}

fn returns_expr_ident_opt(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(expr_path) if expr_path.qself.is_none() => {
            expr_path.path.get_ident().map(ToString::to_string)
        }
        _ => None,
    }
}

fn tuple_return_names_expr(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Tuple(tuple)
            if !tuple.elems.is_empty() && tuple.elems.iter().all(|elem| {
                returns_expr_ident_opt(elem).is_some()
            })
    )
}

fn qualify_dependency_contract_calls(
    alias: &str,
    local_name: &str,
    clause_name: &str,
    expr: &mut Expr,
    public_callables: &BTreeMap<String, String>,
) -> Result<BTreeSet<String>, String> {
    let mut qualifier = DependencyContractCallQualifier {
        alias,
        local_name,
        clause_name,
        public_callables,
        error: None,
    };
    qualifier.visit_expr_mut(expr);
    if let Some(error) = qualifier.error {
        return Err(error);
    }

    let mut collector = CallPathCollector::default();
    collector.visit_expr(expr);
    Ok(collector.paths)
}

struct DependencyContractCallQualifier<'a> {
    alias: &'a str,
    local_name: &'a str,
    clause_name: &'a str,
    public_callables: &'a BTreeMap<String, String>,
    error: Option<String>,
}

impl VisitMut for DependencyContractCallQualifier<'_> {
    fn visit_expr_call_mut(&mut self, call: &mut syn::ExprCall) {
        if self.error.is_some() {
            return;
        }

        if let Expr::Path(func_path) = &mut *call.func {
            if func_path
                .path
                .segments
                .iter()
                .any(|segment| !matches!(segment.arguments, syn::PathArguments::None))
            {
                self.error = Some(format!(
                    "dependency concrete function `{}::{}` has unsupported generic call in {} clause",
                    self.alias, self.local_name, self.clause_name
                ));
                return;
            }

            if let Some(local_path) = dependency_relative_call_path(&func_path.path) {
                let Some(qualified) = self.public_callables.get(&local_path) else {
                    self.error = Some(format!(
                        "dependency concrete function `{}::{}` {} clause calls unsupported dependency function `{local_path}`",
                        self.alias, self.local_name, self.clause_name
                    ));
                    return;
                };
                match syn::parse_str::<syn::Path>(qualified) {
                    Ok(path) => func_path.path = path,
                    Err(source) => {
                        self.error = Some(format!(
                            "failed to qualify dependency concrete function `{}::{}` {} clause call `{local_path}`: {source}",
                            self.alias, self.local_name, self.clause_name
                        ));
                        return;
                    }
                }
            }
        }

        syn::visit_mut::visit_expr_call_mut(self, call);
    }
}

fn dependency_relative_call_path(path: &syn::Path) -> Option<String> {
    if path.leading_colon.is_some() {
        return None;
    }
    let mut segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    if segments.is_empty() {
        return None;
    }
    if matches!(segments.first().map(String::as_str), Some("crate" | "self")) {
        segments.remove(0);
    }
    if segments.is_empty() || segments.first().is_some_and(|segment| segment == "super") {
        return None;
    }
    Some(segments.join("::"))
}

fn body_axiom_from_spec(
    alias: &str,
    local_name: &str,
    item_fn: &ItemFn,
    return_ty: &TrustVcType,
    params: &[(String, TrustVcType)],
    used_bound_names: &mut BTreeSet<String>,
) -> Result<Option<DependencySpecBodyAxiom>, String> {
    if !signature_shape_allows_body_axiom(&item_fn.sig) {
        return Ok(None);
    }

    // An `#[trust_vc::opaque]` dependency spec still gets its body axiom imported,
    // but registered suppressed-until-reveal (see `import_body_axiom`). The body
    // must still be one we can faithfully lower; if it is not, we DO NOT fabricate
    // an axiom — an opaque spec with an unlowerable body stays uninterpreted
    // forever (fail closed), so `reveal!` cannot disclose a body we never built
    // and a false goal can never pass. A non-opaque spec with an unlowerable body
    // remains a hard import error, exactly as before. Part of #2778.
    let is_opaque = has_opaque_attr(&item_fn.attrs);

    let param_names = params
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<BTreeSet<_>>();
    let support = SupportedBody::check(&item_fn.block, &param_names);
    if let Some(reason) = support.unsupported_reason {
        if is_opaque {
            return Ok(None);
        }
        return Err(format!(
            "dependency spec function `{alias}::{local_name}` has an unsupported body for import: {reason}"
        ));
    }

    let full_name = format!("{alias}::{local_name}");
    let mut rename_map = HashMap::new();
    let mut bound_vars = Vec::with_capacity(params.len());
    for (param_name, param_ty) in params {
        let bound_name = fresh_bound_name(used_bound_names, alias, local_name, param_name);
        rename_map.insert(param_name.clone(), bound_name.clone());
        bound_vars.push((bound_name, param_ty.clone()));
    }

    let mut renamed_block = (*item_fn.block).clone();
    IdentRenamer { rename_map }.visit_block_mut(&mut renamed_block);

    let call_args = bound_vars
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    let trigger = format!("{full_name}({call_args})");
    let body = quote!(#renamed_block).to_string();
    let condition = format!("{trigger} == {body}");

    if return_ty.contains_opaque() {
        return Ok(None);
    }

    Ok(Some(DependencySpecBodyAxiom {
        condition,
        trigger,
        bound_vars,
        is_opaque,
    }))
}

fn signature_shape_allows_body_axiom(sig: &syn::Signature) -> bool {
    sig.constness.is_none()
        && sig.asyncness.is_none()
        && sig.unsafety.is_none()
        && sig.abi.is_none()
        && sig.variadic.is_none()
        && sig.generics.params.is_empty()
        && sig.generics.where_clause.is_none()
}

fn fresh_bound_name(
    used_names: &mut BTreeSet<String>,
    alias: &str,
    local_name: &str,
    param_name: &str,
) -> String {
    let base = format!(
        "__trust_vc_dep_{}_{}_{}",
        sanitize_ident(alias),
        sanitize_ident(local_name),
        sanitize_ident(param_name)
    );
    if used_names.insert(base.clone()) {
        return base;
    }

    for i in 1.. {
        let candidate = format!("{base}_{i}");
        if used_names.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("unbounded suffix search must find a fresh name")
}

fn sanitize_ident(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn type_from_syn(ty: &syn::Type) -> TrustVcType {
    match ty {
        syn::Type::Path(type_path) => TrustVcType::parse_or_opaque(
            &quote!(#type_path)
                .to_string()
                .split_whitespace()
                .collect::<String>(),
        ),
        syn::Type::Reference(type_ref) => type_from_syn(&type_ref.elem),
        _ => TrustVcType::parse_or_opaque(
            &quote!(#ty)
                .to_string()
                .split_whitespace()
                .collect::<String>(),
        ),
    }
}

fn qualified_name(module_path: &str, name: &str) -> String {
    if module_path.is_empty() {
        name.to_string()
    } else {
        format!("{module_path}::{name}")
    }
}

fn is_public(vis: &syn::Visibility) -> bool {
    matches!(vis, syn::Visibility::Public(_))
}

fn has_spec_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "spec")
    })
}

fn has_dependency_contract_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().segments.last().is_some_and(|segment| {
            matches!(
                segment.ident.to_string().as_str(),
                "requires" | "ensures" | "recommends" | "returns" | "contract"
            )
        })
    })
}

fn has_opaque_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "opaque")
    })
}

#[derive(Default)]
struct SupportedBody {
    unsupported_reason: Option<String>,
}

impl SupportedBody {
    fn check(block: &syn::Block, param_names: &BTreeSet<&str>) -> Self {
        let mut checker = Self::default();
        checker.visit_block_with_params(block, param_names);
        checker
    }

    fn visit_block_with_params(&mut self, block: &syn::Block, param_names: &BTreeSet<&str>) {
        if self.unsupported_reason.is_some() {
            return;
        }
        if block.stmts.len() != 1 {
            self.unsupported(format!(
                "expected a single expression statement, found {} statements",
                block.stmts.len()
            ));
            return;
        }
        match &block.stmts[0] {
            syn::Stmt::Expr(expr, None) => self.visit_expr_with_params(expr, param_names),
            syn::Stmt::Expr(_, Some(_)) => {
                self.unsupported("body expression must not end in a semicolon");
            }
            syn::Stmt::Local(_) => self.unsupported("local let bindings are not supported"),
            syn::Stmt::Item(_) => self.unsupported("nested items are not supported"),
            syn::Stmt::Macro(_) => self.unsupported("macros are not supported"),
        }
    }

    fn visit_expr_with_params(&mut self, expr: &Expr, param_names: &BTreeSet<&str>) {
        if self.unsupported_reason.is_some() {
            return;
        }
        match expr {
            Expr::Binary(binary) => {
                if !is_supported_binary_op(&binary.op) {
                    self.unsupported("unsupported binary operator");
                    return;
                }
                self.visit_expr_with_params(&binary.left, param_names);
                self.visit_expr_with_params(&binary.right, param_names);
            }
            Expr::Block(block) => self.visit_block_with_params(&block.block, param_names),
            Expr::Cast(cast) => {
                let ty = type_from_syn(&cast.ty);
                if ty.contains_opaque() {
                    self.unsupported(format!(
                        "unsupported cast target type `{}`",
                        ty.to_type_string()
                    ));
                    return;
                }
                self.visit_expr_with_params(&cast.expr, param_names);
            }
            Expr::Group(group) => self.visit_expr_with_params(&group.expr, param_names),
            Expr::Lit(lit) => match &lit.lit {
                syn::Lit::Bool(_) | syn::Lit::Int(_) => {}
                _ => self.unsupported("only boolean and integer literals are supported"),
            },
            Expr::Paren(paren) => self.visit_expr_with_params(&paren.expr, param_names),
            Expr::Path(path) => {
                let path_is_param = path.qself.is_none() && path.path.segments.len() == 1 && {
                    let ident = path.path.segments[0].ident.to_string();
                    param_names.contains(ident.as_str())
                };
                if !path_is_param {
                    self.unsupported("body paths must refer directly to spec parameters");
                }
            }
            Expr::Tuple(tuple) if tuple.elems.is_empty() => {}
            Expr::Unary(unary) => {
                if !matches!(unary.op, syn::UnOp::Neg(_) | syn::UnOp::Not(_)) {
                    self.unsupported("unsupported unary operator");
                    return;
                }
                self.visit_expr_with_params(&unary.expr, param_names);
            }
            _ => self.unsupported(
                "only call-free literal, path, cast, unary, and binary expressions are supported",
            ),
        }
    }

    fn unsupported(&mut self, reason: impl Into<String>) {
        if self.unsupported_reason.is_none() {
            self.unsupported_reason = Some(reason.into());
        }
    }
}

fn is_supported_binary_op(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::Add(_)
            | syn::BinOp::Sub(_)
            | syn::BinOp::Mul(_)
            | syn::BinOp::Div(_)
            | syn::BinOp::Rem(_)
            | syn::BinOp::And(_)
            | syn::BinOp::Or(_)
            | syn::BinOp::Eq(_)
            | syn::BinOp::Lt(_)
            | syn::BinOp::Le(_)
            | syn::BinOp::Ne(_)
            | syn::BinOp::Ge(_)
            | syn::BinOp::Gt(_)
    )
}

struct IdentRenamer {
    rename_map: HashMap<String, String>,
}

impl VisitMut for IdentRenamer {
    fn visit_expr_path_mut(&mut self, path: &mut syn::ExprPath) {
        if path.qself.is_none() && path.path.segments.len() == 1 {
            let segment = &mut path.path.segments[0];
            if let Some(replacement) = self.rename_map.get(&segment.ident.to_string()) {
                segment.ident = syn::Ident::new(replacement, Span::call_site());
            }
        }
        syn::visit_mut::visit_expr_path_mut(self, path);
    }
}

fn referenced_call_paths(func: &ItemFn) -> BTreeSet<String> {
    let mut paths = referenced_body_call_paths(func);
    paths.extend(referenced_contract_call_paths(func));
    paths
}

fn referenced_body_call_paths(func: &ItemFn) -> BTreeSet<String> {
    let mut collector = CallPathCollector::default();
    collector.visit_block(&func.block);
    collector.paths
}

fn referenced_contract_call_paths(func: &ItemFn) -> BTreeSet<String> {
    let mut collector = CallPathCollector::default();
    for attr in &func.attrs {
        collector.visit_contract_attr(attr);
    }
    collector.paths
}

fn dependency_body_call_sites(func: &ItemFn, alias: &str) -> Vec<DependencyCallSite> {
    let mut collector = DependencyCallSiteCollector {
        alias,
        local_binding_scopes: Vec::new(),
        call_sites: Vec::new(),
    };
    collector.visit_block(&func.block);
    collector.call_sites
}

struct DependencyCallSiteCollector<'a> {
    alias: &'a str,
    local_binding_scopes: Vec<BTreeMap<String, Option<String>>>,
    call_sites: Vec<DependencyCallSite>,
}

impl<'ast> Visit<'ast> for DependencyCallSiteCollector<'_> {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.local_binding_scopes.push(BTreeMap::new());
        visit::visit_block(self, block);
        self.local_binding_scopes.pop();
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        visit::visit_local(self, local);
        let binding_names = pat_binding_names(&local.pat);
        let Some(scope) = self.local_binding_scopes.last_mut() else {
            return;
        };
        for name in &binding_names {
            scope.insert(name.clone(), None);
        }

        let syn::Pat::Ident(pat_ident) = &local.pat else {
            return;
        };
        if pat_ident.mutability.is_some() || pat_ident.by_ref.is_some() {
            return;
        };
        let Some(init) = &local.init else {
            return;
        };
        if let Some(scope) = self.local_binding_scopes.last_mut() {
            scope.insert(
                pat_ident.ident.to_string(),
                Some(init.expr.to_token_stream().to_string()),
            );
        }
    }

    fn visit_expr_assign(&mut self, assign: &'ast syn::ExprAssign) {
        visit::visit_expr_assign(self, assign);
        self.invalidate_assigned_expr(&assign.left);
    }

    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let Expr::Path(path) = &*call.func {
            let callee = path_to_string(&path.path);
            let prefix = format!("{}::", self.alias);
            if callee.starts_with(&prefix) {
                let args = call
                    .args
                    .iter()
                    .map(|arg| self.call_arg_expr(arg))
                    .collect::<Vec<_>>();
                self.call_sites.push(DependencyCallSite {
                    call_expr: format!("{callee}({})", args.join(", ")),
                    callee,
                    args,
                });
            }
        }
        visit::visit_expr_call(self, call);
    }
}

impl DependencyCallSiteCollector<'_> {
    fn invalidate_assigned_expr(&mut self, expr: &Expr) {
        let Expr::Path(path) = expr else {
            return;
        };
        if path.qself.is_some() || path.path.segments.len() != 1 {
            return;
        }
        let ident = path.path.segments[0].ident.to_string();
        for scope in self.local_binding_scopes.iter_mut().rev() {
            if let Some(binding) = scope.get_mut(&ident) {
                *binding = None;
                return;
            }
        }
    }

    fn call_arg_expr(&self, arg: &Expr) -> String {
        let Expr::Path(path) = arg else {
            return arg.to_token_stream().to_string();
        };
        if path.qself.is_some() || path.path.segments.len() != 1 {
            return arg.to_token_stream().to_string();
        }
        let ident = path.path.segments[0].ident.to_string();
        for scope in self.local_binding_scopes.iter().rev() {
            if let Some(binding) = scope.get(&ident) {
                return binding
                    .clone()
                    .unwrap_or_else(|| arg.to_token_stream().to_string());
            }
        }
        arg.to_token_stream().to_string()
    }
}

struct PatBindingNameCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for PatBindingNameCollector {
    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        self.names.push(pat.ident.to_string());
        visit::visit_pat_ident(self, pat);
    }
}

fn pat_binding_names(pat: &syn::Pat) -> Vec<String> {
    let mut collector = PatBindingNameCollector { names: Vec::new() };
    collector.visit_pat(pat);
    collector.names
}

#[derive(Default)]
struct CallPathCollector {
    paths: BTreeSet<String>,
}

impl CallPathCollector {
    fn visit_contract_attr(&mut self, attr: &syn::Attribute) {
        let Some(last) = attr
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
        else {
            return;
        };
        match last.as_str() {
            "requires" | "ensures" | "recommends" => {
                if let Ok(expr) = attr.parse_args::<Expr>() {
                    self.visit_expr(&expr);
                }
            }
            "contract" => self.visit_contract_clauses(attr),
            _ => {}
        }
    }

    fn visit_contract_clauses(&mut self, attr: &syn::Attribute) {
        let syn::Meta::List(meta_list) = &attr.meta else {
            return;
        };
        let parser = Punctuated::<syn::Meta, Token![,]>::parse_terminated;
        let Ok(clauses) = parser.parse2(meta_list.tokens.clone()) else {
            return;
        };
        for clause in clauses {
            let syn::Meta::List(list) = clause else {
                continue;
            };
            let Some(name) = list
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string())
            else {
                continue;
            };
            if !matches!(
                name.as_str(),
                "requires" | "ensures" | "recommends" | "returns"
            ) {
                continue;
            }
            if let Ok(expr) = syn::parse2::<Expr>(list.tokens) {
                self.visit_expr(&expr);
            }
        }
    }
}

impl<'ast> Visit<'ast> for CallPathCollector {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path) = &*call.func {
            self.paths.insert(path_to_string(&path.path));
        }
        visit::visit_expr_call(self, call);
    }
}

fn path_to_string(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_test_dependency_package(
        root: &Path,
        package_name: &str,
        dependencies: &str,
        source: &str,
    ) -> PathBuf {
        fs::create_dir_all(root.join("src")).expect("test dependency src dir should be created");
        let dependency_section = if dependencies.trim().is_empty() {
            String::new()
        } else {
            format!("\n[dependencies]\n{dependencies}\n")
        };
        fs::write(
            root.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{package_name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n{dependency_section}"
            ),
        )
        .expect("test dependency manifest should be written");
        fs::write(root.join("src/lib.rs"), source)
            .expect("test dependency source should be written");
        root.join("Cargo.toml")
    }

    #[test]
    fn manifest_parser_reads_renamed_path_dependencies() {
        let temp = std::env::temp_dir().join("trust_vc_dependency_spec_manifest_test");
        let _ = fs::remove_dir_all(&temp);
        fs::create_dir_all(&temp).expect("temp dir should be created");
        fs::write(
            temp.join("Cargo.toml"),
            r#"
[package]
name = "root"
version = "0.1.0"

[dependencies]
spec_def = { path = "../cargo_spec_def" }
spec_def2 = { path = "../cargo_spec_def2", package = "spec_def" }
trust-vc-core = { path = "../../../../crates/trust-vc-core" }
"#,
        )
        .expect("manifest should be written");

        let deps = read_path_dependencies(&temp.join("Cargo.toml"))
            .expect("path dependencies should parse");
        let mut aliases = deps
            .iter()
            .map(|dep| dep.alias.as_str())
            .collect::<Vec<_>>();
        aliases.sort_unstable();
        assert_eq!(aliases, vec!["spec_def", "spec_def2", "trust_vc_core"]);
    }

    #[test]
    fn referenced_call_paths_include_contract_clauses() {
        let func = syn::parse_quote! {
            #[trust_vc::contract(
                requires(spec_def::double(x) < 100i128),
                ensures(spec_def2::double(x) == spec_def::double(x) + 1i128),
                returns(result),
            )]
            pub fn f(x: u16) -> u16 {
                spec_def::concrete_a(x)
            }
        };

        let paths = referenced_call_paths(&func);
        assert!(paths.contains("spec_def::double"));
        assert!(paths.contains("spec_def2::double"));
        assert!(paths.contains("spec_def::concrete_a"));
    }

    #[test]
    fn dependency_spec_signatures_reject_unimported_contracts() {
        let item: ItemFn = syn::parse_quote! {
            #[trust_vc::spec]
            #[trust_vc::recommends(x < 10u8)]
            pub fn limited(x: u8) -> u8 {
                x
            }
        };

        let mut used_bound_names = BTreeSet::new();
        let error = signature_from_spec("spec_def", "limited", &item, &mut used_bound_names)
            .expect_err("dependency spec recommendations must fail closed");
        assert!(
            error.contains("does not import dependency spec contracts"),
            "error should explain dependency contract import limitation: {error}"
        );
    }

    #[test]
    fn dependency_spec_imports_supported_body_axiom() {
        let item: ItemFn = syn::parse_quote! {
            #[trust_vc::spec]
            pub fn double(x: u16) -> int {
                (x as int) + (x as int)
            }
        };

        let mut used_bound_names = BTreeSet::new();
        let spec = signature_from_spec("spec_def", "double", &item, &mut used_bound_names)
            .expect("simple public spec body should import");
        let axiom = spec
            .body_axiom
            .expect("call-free arithmetic body should produce a body axiom");

        assert_eq!(spec.name, "spec_def::double");
        assert_eq!(axiom.bound_vars.len(), 1);
        assert_eq!(axiom.bound_vars[0].0, "__trust_vc_dep_spec_def_double_x");
        assert_eq!(axiom.bound_vars[0].1.to_type_string(), "u16");
        assert_eq!(
            axiom.trigger,
            "spec_def::double(__trust_vc_dep_spec_def_double_x)"
        );
        assert!(
            axiom
                .condition
                .contains("spec_def::double(__trust_vc_dep_spec_def_double_x) == {")
                && axiom
                    .condition
                    .contains("__trust_vc_dep_spec_def_double_x as int"),
            "body axiom should alpha-rename the dependency spec body: {}",
            axiom.condition
        );
    }

    #[test]
    fn dependency_spec_body_import_rejects_calls() {
        let item: ItemFn = syn::parse_quote! {
            #[trust_vc::spec]
            pub fn wrapper(x: u16) -> int {
                helper(x)
            }
        };

        let mut used_bound_names = BTreeSet::new();
        let error = signature_from_spec("spec_def", "wrapper", &item, &mut used_bound_names)
            .expect_err("dependency spec body calls should fail closed");
        assert!(
            error.contains("unsupported body for import"),
            "error should explain that the body axiom was refused: {error}"
        );
    }

    #[test]
    fn dependency_concrete_signatures_import_reexported_contracts() {
        let file: syn::File = syn::parse_quote! {
            #[trust_vc::spec]
            pub fn double(x: u16) -> int {
                (x as int) + (x as int)
            }

            #[trust_vc::contract(
                requires(double(x) < 100i128),
                ensures(result == x),
                returns(result),
            )]
            pub fn lib(x: u16) -> u16 {
                x
            }

            pub use lib as concrete_a;
        };
        let functions = collect_public_function_map(&file.items);
        let reexports = collect_public_reexports(&file.items);
        let callables = public_dependency_callables("spec_def", &functions, &reexports);
        let referenced_calls = BTreeSet::from(["spec_def::concrete_a".to_string()]);

        let concrete = collect_public_concrete_signatures(
            "spec_def",
            &referenced_calls,
            &functions,
            &reexports,
            &callables,
        )
        .expect("supported reexported concrete contract should import");

        assert_eq!(concrete.len(), 1);
        let signature = &concrete[0];
        assert_eq!(signature.name, "spec_def::concrete_a");
        assert_eq!(signature.return_ty.to_type_string(), "u16");
        assert_eq!(signature.params[0].0, "x");
        assert_eq!(signature.params[0].1.to_type_string(), "u16");
        assert_eq!(signature.contract.return_binding, "result");
        assert_eq!(signature.contract.requires.len(), 1);
        assert!(
            signature.contract.requires[0].contains("spec_def :: double"),
            "dependency-local spec calls should be qualified in imported concrete requires: {}",
            signature.contract.requires[0]
        );
        assert_eq!(signature.contract.ensures, vec!["result == x"]);
        assert!(signature
            .contract
            .referenced_calls
            .contains("spec_def::double"));
    }

    #[test]
    fn dependency_concrete_call_contracts_emit_call_site_requires_obligations() {
        let file: syn::File = syn::parse_quote! {
            #[trust_vc::spec]
            pub fn double(x: u16) -> int {
                (x as int) + (x as int)
            }

            #[trust_vc::contract(
                requires(double(x) < 100i128),
                returns(result),
            )]
            pub fn lib(x: u16) -> u16 {
                x
            }

            pub use lib as concrete_a;
        };
        let functions = collect_public_function_map(&file.items);
        let reexports = collect_public_reexports(&file.items);
        let callables = public_dependency_callables("spec_def", &functions, &reexports);
        let referenced_calls = BTreeSet::from(["spec_def::concrete_a".to_string()]);
        let concrete = collect_public_concrete_signatures(
            "spec_def",
            &referenced_calls,
            &functions,
            &reexports,
            &callables,
        )
        .expect("supported reexported concrete contract should import")
        .remove(0);
        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                spec_def::concrete_a(x)
            }
        };
        let call_sites = dependency_body_call_sites(&target, "spec_def");
        let mut ctx = VerificationContext::new();

        import_concrete_call_contracts(&concrete, &call_sites, &mut ctx)
            .expect("supported concrete call contract should import");

        let requires = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.name().starts_with("__call_requires_"))
            .expect("requires clause should become a call-site assertion");
        assert!(
            requires.condition().contains("spec_def :: double")
                && requires.condition().contains("< 100i128"),
            "requires obligation should substitute call arguments: {}",
            requires.condition()
        );
        assert!(
            !ctx.obligations()
                .iter()
                .any(|obligation| obligation.name().starts_with("__call_ensures_")),
            "dependency concrete postconditions must not be assumed without proof artifacts"
        );
    }

    #[test]
    fn dependency_concrete_call_contracts_inline_let_bound_dependency_call_arguments() {
        let concrete: DependencyConcreteSignature = DependencyConcreteSignature {
            name: "spec_def::concrete_b".to_string(),
            return_ty: TrustVcType::Uint { width: 16 },
            params: vec![("value".to_string(), TrustVcType::Uint { width: 16 })],
            contract: DependencyConcreteContract {
                return_binding: "result".to_string(),
                return_binding_set: true,
                requires: vec!["value == x".to_string()],
                ensures: Vec::new(),
                referenced_calls: BTreeSet::new(),
            },
        };
        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                let y = spec_def::concrete_a(x);
                spec_def::concrete_b(y)
            }
        };
        let call_sites = dependency_body_call_sites(&target, "spec_def");
        let mut ctx = VerificationContext::new();

        import_concrete_call_contracts(&concrete, &call_sites, &mut ctx)
            .expect("supported concrete call contract should import");

        let requires = ctx
            .obligations()
            .iter()
            .find(|obligation| obligation.name().starts_with("__call_requires_"))
            .expect("requires clause should become a call-site assertion");
        assert!(
            requires
                .condition()
                .contains("spec_def :: concrete_a (x) == x"),
            "requires obligation should inline the let-bound dependency call argument: {}",
            requires.condition()
        );
    }

    #[test]
    fn dependency_concrete_call_contract_let_inlining_respects_block_scope_shadowing() {
        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                let y = x;
                {
                    let y = spec_def::concrete_a(x);
                }
                spec_def::concrete_b(y)
            }
        };

        let call_sites = dependency_body_call_sites(&target, "spec_def");
        let concrete_b = call_sites
            .iter()
            .find(|call_site| call_site.callee == "spec_def::concrete_b")
            .expect("outer dependency call should be collected");
        assert_eq!(concrete_b.args, vec!["x"]);
    }

    #[test]
    fn dependency_concrete_call_contract_let_inlining_skips_mutated_locals() {
        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                let mut y = spec_def::concrete_a(x);
                y = x;
                spec_def::concrete_b(y)
            }
        };

        let call_sites = dependency_body_call_sites(&target, "spec_def");
        let concrete_b = call_sites
            .iter()
            .find(|call_site| call_site.callee == "spec_def::concrete_b")
            .expect("dependency call should be collected");
        assert_eq!(
            concrete_b.args,
            vec!["y"],
            "mutable locals must not be substituted with stale initializer expressions"
        );
    }

    #[test]
    fn dependency_concrete_call_contract_let_inlining_respects_pattern_shadowing() {
        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                let y = x;
                {
                    let (y, _) = (spec_def::concrete_a(x), 0u16);
                    spec_def::concrete_b(y)
                }
            }
        };

        let call_sites = dependency_body_call_sites(&target, "spec_def");
        let concrete_b = call_sites
            .iter()
            .find(|call_site| call_site.callee == "spec_def::concrete_b")
            .expect("dependency call should be collected");
        assert_eq!(
            concrete_b.args,
            vec!["y"],
            "non-ident patterns shadow outer bindings but are not safe to inline"
        );
    }

    #[test]
    fn dependency_concrete_contracts_import_transitive_public_spec_calls() {
        let root = std::env::temp_dir().join(format!(
            "trust_vc_dependency_specs_transitive_spec_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        let spec_def_root = root.join("spec_def");
        let spec_use_root = root.join("spec_use");
        write_test_dependency_package(
            &spec_def_root,
            "spec_def",
            "",
            r#"
#[trust_vc::spec]
pub fn double(x: u16) -> i128 {
    (x as i128) + (x as i128)
}
"#,
        );
        let spec_use_manifest = write_test_dependency_package(
            &spec_use_root,
            "spec_use",
            r#"spec_def = { path = "../spec_def" }"#,
            r#"
#[trust_vc::contract(
    requires(spec_def::double(x) < 100i128),
    returns(result),
)]
pub fn concrete_b(x: u16) -> u16 {
    x
}
"#,
        );
        let dep = PathDependency {
            alias: "spec_use".to_string(),
            manifest_path: spec_use_manifest,
        };
        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                spec_use::concrete_b(x)
            }
        };
        let referenced_body_calls = BTreeSet::from(["spec_use::concrete_b".to_string()]);
        let mut ctx = VerificationContext::new();

        import_dependency_specs(
            &dep,
            &referenced_body_calls,
            &referenced_body_calls,
            &BTreeSet::new(),
            &target,
            &mut ctx,
        )
        .expect("transitive public spec calls in dependency concrete contracts should import");

        assert!(
            ctx.obligations().iter().any(|obligation| {
                obligation.name().starts_with("__call_requires_")
                    && obligation.condition().contains("spec_def :: double")
                    && obligation.condition().contains("< 100i128")
            }),
            "dependency concrete requires clause should keep the transitive spec call: {:?}",
            ctx.obligations()
        );
        assert!(
            ctx.obligations().iter().any(|obligation| {
                obligation.name() == "__body_axiom_spec_def__double_dependency_spec"
                    && obligation
                        .condition()
                        .contains("spec_def::double(__trust_vc_dep_spec_def_double_x) ==")
            }),
            "referenced transitive public spec should import its body axiom: {:?}",
            ctx.obligations()
        );

        fs::remove_dir_all(root).ok();
    }

    #[test]
    fn dependency_concrete_contracts_reject_transitive_public_concrete_calls() {
        let root = std::env::temp_dir().join(format!(
            "trust_vc_dependency_specs_transitive_concrete_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        let spec_def_root = root.join("spec_def");
        let spec_use_root = root.join("spec_use");
        write_test_dependency_package(
            &spec_def_root,
            "spec_def",
            "",
            r#"
pub fn concrete_a(x: u16) -> u16 {
    x
}
"#,
        );
        let spec_use_manifest = write_test_dependency_package(
            &spec_use_root,
            "spec_use",
            r#"spec_def = { path = "../spec_def" }"#,
            r#"
#[trust_vc::contract(
    requires(spec_def::concrete_a(x) == x),
    returns(result),
)]
pub fn concrete_b(x: u16) -> u16 {
    x
}
"#,
        );
        let dep = PathDependency {
            alias: "spec_use".to_string(),
            manifest_path: spec_use_manifest,
        };
        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                spec_use::concrete_b(x)
            }
        };
        let referenced_body_calls = BTreeSet::from(["spec_use::concrete_b".to_string()]);

        let error = import_dependency_specs(
            &dep,
            &referenced_body_calls,
            &referenced_body_calls,
            &BTreeSet::new(),
            &target,
            &mut VerificationContext::new(),
        )
        .expect_err(
            "transitive concrete calls in dependency concrete contracts should stay blocked",
        );
        assert!(
            error.contains(
                "requires clause calls unsupported dependency function `spec_def::concrete_a`"
            ),
            "error should identify the rejected transitive concrete call: {error}"
        );

        fs::remove_dir_all(root).ok();
    }

    #[test]
    fn dependency_concrete_postconditions_fail_closed_without_semantic_artifact() {
        let item: ItemFn = syn::parse_quote! {
            #[trust_vc::contract(
                ensures(result == x),
                returns(result),
            )]
            pub fn lib(x: u16) -> u16 {
                x
            }
        };

        let concrete = signature_from_concrete("spec_def", "concrete_a", &item, &BTreeMap::new())
            .expect("supported concrete signature should parse");
        let error = ensure_dependency_concrete_contract_import_supported(
            &PathDependency {
                alias: "spec_def".to_string(),
                manifest_path: PathBuf::from("Cargo.toml"),
            },
            &concrete,
            &BTreeSet::from(["spec_def::concrete_a".to_string()]),
            &BTreeSet::new(),
            &[],
        )
        .expect_err("dependency concrete postconditions require semantic proof artifacts");
        assert!(
            error.contains("matching semantic proof artifact"),
            "error should explain the semantic-artifact blocker: {error}"
        );
    }

    #[test]
    fn dependency_concrete_postconditions_import_with_matching_semantic_artifact() {
        let root = std::env::temp_dir().join(format!(
            "trust_vc_dependency_specs_artifact_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&root).expect("temp root should be creatable");
        let manifest_path = root.join("Cargo.toml");
        std::fs::write(
            &manifest_path,
            "[package]\nname = \"spec_def\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("manifest should be writable");
        let lib_path = root.join("src/lib.rs");
        std::fs::create_dir_all(lib_path.parent().expect("lib path should have parent"))
            .expect("dependency src dir should be creatable");
        std::fs::write(
            &lib_path,
            r#"
#[trust_vc::contract(
    ensures(result == x),
    returns(result),
)]
pub fn lib(x: u16) -> u16 {
    x
}
"#,
        )
        .expect("dependency source should be writable");
        let (source_len, source_sha256) =
            dependency_source_digest(&lib_path).expect("source digest should compute");

        let item: ItemFn = syn::parse_quote! {
            #[trust_vc::contract(
                ensures(result == x),
                returns(result),
            )]
            pub fn lib(x: u16) -> u16 {
                x
            }
        };
        let concrete = signature_from_concrete("spec_def", "concrete_a", &item, &BTreeMap::new())
            .expect("supported concrete signature should parse");
        let dep = PathDependency {
            alias: "spec_def".to_string(),
            manifest_path: manifest_path.clone(),
        };
        let artifact = DependencySemanticArtifact {
            crate_name: "spec_def".to_string(),
            package_name: "spec_def".to_string(),
            package_version: "0.1.0".to_string(),
            package_env_id: package_env_id_from_manifest_path("spec_def", "0.1.0", &manifest_path),
            manifest_path: canonical_manifest_path_for_hash(&manifest_path),
            source_path: Some(canonical_manifest_path_for_hash(&lib_path)),
            source_len: Some(source_len),
            source_sha256: Some(source_sha256),
            semantic_payload: DependencySemanticPayload {
                kind: TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND.to_string(),
                proof_facts_exported: true,
                concrete_functions: vec![DependencyConcreteFact {
                    name: "concrete_a".to_string(),
                    return_type: "u16".to_string(),
                    params: vec![DependencyConcreteParamFact {
                        name: "x".to_string(),
                        ty: "u16".to_string(),
                    }],
                    return_binding: "result".to_string(),
                    requires: Vec::new(),
                    ensures: vec!["result == x".to_string()],
                }],
            },
        };

        ensure_dependency_concrete_contract_import_supported(
            &dep,
            &concrete,
            &BTreeSet::from(["spec_def::concrete_a".to_string()]),
            &BTreeSet::new(),
            std::slice::from_ref(&artifact),
        )
        .expect("matching semantic artifact should allow postcondition import");

        let target: ItemFn = syn::parse_quote! {
            pub fn caller(x: u16) -> u16 {
                spec_def::concrete_a(x)
            }
        };
        let call_sites = dependency_body_call_sites(&target, "spec_def");
        let mut ctx = VerificationContext::new();
        import_concrete_call_contracts(&concrete, &call_sites, &mut ctx)
            .expect("artifact-authorized concrete postcondition should import");
        assert!(
            ctx.obligations()
                .iter()
                .any(|obligation| obligation.name().starts_with("__call_ensures_")
                    && obligation.condition().contains("spec_def :: concrete_a (x) == x")),
            "dependency concrete postcondition should be substituted into a call-site assumption: {:?}",
            ctx.obligations()
        );

        std::fs::write(
            &lib_path,
            r#"
#[trust_vc::contract(
    ensures(result == x),
    returns(result),
)]
pub fn lib(x: u16) -> u16 {
    0
}
"#,
        )
        .expect("dependency source should be rewritable");
        let error = ensure_dependency_concrete_contract_import_supported(
            &dep,
            &concrete,
            &BTreeSet::from(["spec_def::concrete_a".to_string()]),
            &BTreeSet::new(),
            &[artifact],
        )
        .expect_err("source-tampered semantic artifact should fail closed");
        assert!(
            error.contains("source hash mismatch"),
            "error should identify dependency source binding mismatch: {error}"
        );

        std::fs::remove_dir_all(root).ok();
    }

    #[test]
    fn dependency_semantic_artifacts_match_renamed_same_package_dependency_by_manifest_identity() {
        let root = std::env::temp_dir().join(format!(
            "trust_vc_dependency_specs_renamed_artifact_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        let package_root = root.join("cargo_spec_def2");
        std::fs::create_dir_all(package_root.join("src")).expect("temp package should be created");
        let manifest_path = package_root.join("Cargo.toml");
        std::fs::write(
            &manifest_path,
            "[package]\nname = \"spec_def\"\nversion = \"0.2.0\"\nedition = \"2021\"\n",
        )
        .expect("manifest should be writable");
        let lib_path = package_root.join("src/lib.rs");
        std::fs::write(
            &lib_path,
            r#"
#[trust_vc::contract(
    ensures(result == x),
    returns(result),
)]
pub fn lib(x: u16) -> u16 {
    x
}

pub use lib as concrete_a;
"#,
        )
        .expect("dependency source should be writable");
        let (source_len, source_sha256) =
            dependency_source_digest(&lib_path).expect("source digest should compute");
        let dep = PathDependency {
            alias: "spec_def2".to_string(),
            manifest_path: manifest_path.clone(),
        };
        let artifact = DependencySemanticArtifact {
            crate_name: "spec_def".to_string(),
            package_name: "spec_def".to_string(),
            package_version: "0.2.0".to_string(),
            package_env_id: package_env_id_from_manifest_path("spec_def", "0.2.0", &manifest_path),
            manifest_path: canonical_manifest_path_for_hash(&manifest_path),
            source_path: Some(canonical_manifest_path_for_hash(&lib_path)),
            source_len: Some(source_len),
            source_sha256: Some(source_sha256),
            semantic_payload: DependencySemanticPayload {
                kind: TRUST_VC_RUSTC_WRAPPER_SEMANTIC_FACTS_PAYLOAD_KIND.to_string(),
                proof_facts_exported: true,
                concrete_functions: Vec::new(),
            },
        };

        let artifacts = [artifact];
        let matched = matching_dependency_semantic_artifact(&dep, &artifacts)
            .expect("semantic artifact match should not error")
            .expect("renamed dependency should match by package identity and manifest path");
        assert_eq!(matched.crate_name, "spec_def");
        assert_eq!(matched.package_version, "0.2.0");

        std::fs::remove_dir_all(root).ok();
    }

    #[test]
    fn dependency_concrete_contracts_reject_recommendations() {
        let item: ItemFn = syn::parse_quote! {
            #[trust_vc::contract(
                recommends(x < 10u8),
                returns(result),
            )]
            pub fn limited(x: u8) -> u8 {
                x
            }
        };

        let error = signature_from_concrete("spec_def", "limited", &item, &BTreeMap::new())
            .expect_err("dependency concrete recommendations must fail closed");
        assert!(
            error.contains("does not import dependency concrete recommendations"),
            "error should explain dependency concrete recommendation limitation: {error}"
        );
    }
}
