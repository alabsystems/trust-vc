// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Versioned MergeBundle boundary for trust-vc, the proof backend of Trust
//! (the rustc fork). This contract hands verification state across trust-vc's
//! capabilities (trust_mc/trust_wp/trust_vc are capabilities integrated within
//! Trust, not a standalone end-product). Verus parity is the benchmark; the
//! destination is Trust's proof calculus on the pure-Rust `ay` solver.
//! See `design-trust-proof-backend.md`.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use thiserror::Error;

pub mod api_surface;
pub mod fixtures;
mod types;

pub use types::{
    BroadcastLemmaMeta, DecreasesClause, FuelAxiomMeta, FuncDeclMeta, SortMeta, TriggerGroup,
    TypedExpr, VarDecl,
};

/// Current supported merge bundle schema version.
pub const MERGE_BUNDLE_VERSION: u32 = 4;

/// Explicit expression format marker for cross-repo execution contracts.
///
/// v3 bundles must declare the grammar of `TypedExpr.expr` strings so consumers
/// can parse them without guessing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ExpressionFormat {
    /// Canonical SMT-LIB2 term text (not script-level, just terms).
    SmtLib2TermV1,
}

/// Stable, versioned handoff artifact from trust_vc to trust_mc (sibling
/// proof/model-checking capabilities within Trust).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MergeBundle {
    bundle_version: u32,
    /// Expression format for `TypedExpr.expr` strings.  Required for v3+.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    expression_format: Option<ExpressionFormat>,
    source_id: String,
    variables: Vec<VarDecl>,
    assumptions: Vec<TypedExpr>,
    assertions: Vec<TypedExpr>,
    decreases: Vec<DecreasesClause>,
    triggers: Vec<TriggerGroup>,
    metadata: BTreeMap<String, String>,
    // --- v4 additions ---
    /// Uninterpreted function declarations referenced by assumptions/assertions.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    func_decls: Vec<FuncDeclMeta>,
    /// Defining axioms for recursive functions (`forall x. {f(x)} f(x) == body(x)`).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    fuel_axioms: Vec<FuelAxiomMeta>,
    /// Auto-applied quantified lemmas with triggers and optional guards.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    broadcast_lemmas: Vec<BroadcastLemmaMeta>,
}

impl MergeBundle {
    /// Construct an empty bundle at the current [`MERGE_BUNDLE_VERSION`].
    #[must_use]
    pub fn new(source_id: impl Into<String>) -> Self {
        Self {
            bundle_version: MERGE_BUNDLE_VERSION,
            expression_format: Some(ExpressionFormat::SmtLib2TermV1),
            source_id: source_id.into(),
            variables: Vec::new(),
            assumptions: Vec::new(),
            assertions: Vec::new(),
            decreases: Vec::new(),
            triggers: Vec::new(),
            metadata: BTreeMap::new(),
            func_decls: Vec::new(),
            fuel_axioms: Vec::new(),
            broadcast_lemmas: Vec::new(),
        }
    }

    #[must_use]
    pub fn bundle_version(&self) -> u32 {
        self.bundle_version
    }

    #[must_use]
    pub fn expression_format(&self) -> Option<ExpressionFormat> {
        self.expression_format
    }

    #[must_use]
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    #[must_use]
    pub fn variables(&self) -> &[VarDecl] {
        &self.variables
    }

    #[must_use]
    pub fn assumptions(&self) -> &[TypedExpr] {
        &self.assumptions
    }

    #[must_use]
    pub fn assertions(&self) -> &[TypedExpr] {
        &self.assertions
    }

    #[must_use]
    pub fn decreases(&self) -> &[DecreasesClause] {
        &self.decreases
    }

    #[must_use]
    pub fn triggers(&self) -> &[TriggerGroup] {
        &self.triggers
    }

    #[must_use]
    pub fn metadata(&self) -> &BTreeMap<String, String> {
        &self.metadata
    }

    #[must_use]
    pub fn func_decls(&self) -> &[FuncDeclMeta] {
        &self.func_decls
    }

    #[must_use]
    pub fn fuel_axioms(&self) -> &[FuelAxiomMeta] {
        &self.fuel_axioms
    }

    #[must_use]
    pub fn broadcast_lemmas(&self) -> &[BroadcastLemmaMeta] {
        &self.broadcast_lemmas
    }

    #[must_use]
    pub fn with_bundle_version(mut self, version: u32) -> Self {
        self.bundle_version = version;
        self
    }

    #[must_use]
    pub fn with_expression_format(mut self, fmt: Option<ExpressionFormat>) -> Self {
        self.expression_format = fmt;
        self
    }

    #[must_use]
    pub fn with_variables(mut self, variables: Vec<VarDecl>) -> Self {
        self.variables = variables;
        self
    }

    #[must_use]
    pub fn with_assumptions(mut self, assumptions: Vec<TypedExpr>) -> Self {
        self.assumptions = assumptions;
        self
    }

    #[must_use]
    pub fn with_assertions(mut self, assertions: Vec<TypedExpr>) -> Self {
        self.assertions = assertions;
        self
    }

    #[must_use]
    pub fn with_decreases(mut self, decreases: Vec<DecreasesClause>) -> Self {
        self.decreases = decreases;
        self
    }

    #[must_use]
    pub fn with_triggers(mut self, triggers: Vec<TriggerGroup>) -> Self {
        self.triggers = triggers;
        self
    }

    #[must_use]
    pub fn with_metadata(mut self, metadata: BTreeMap<String, String>) -> Self {
        self.metadata = metadata;
        self
    }

    #[must_use]
    pub fn with_func_decls(mut self, decls: Vec<FuncDeclMeta>) -> Self {
        self.func_decls = decls;
        self
    }

    #[must_use]
    pub fn with_fuel_axioms(mut self, axioms: Vec<FuelAxiomMeta>) -> Self {
        self.fuel_axioms = axioms;
        self
    }

    #[must_use]
    pub fn with_broadcast_lemmas(mut self, lemmas: Vec<BroadcastLemmaMeta>) -> Self {
        self.broadcast_lemmas = lemmas;
        self
    }

    #[must_use]
    pub fn insert_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Reject unsupported bundle versions with a hard error.
    ///
    /// Accepts any version from 1 through [`MERGE_BUNDLE_VERSION`] (inclusive).
    pub fn enforce_supported_version(&self) -> Result<(), MergeBundleError> {
        if !(1..=MERGE_BUNDLE_VERSION).contains(&self.bundle_version) {
            return Err(MergeBundleError::UnsupportedBundleVersion {
                found: self.bundle_version,
                max_supported: MERGE_BUNDLE_VERSION,
            });
        }
        Ok(())
    }

    /// Parse JSON and enforce hard-fail semantics for unsupported versions.
    pub fn from_json_str(payload: &str) -> Result<Self, MergeBundleError> {
        let bundle: Self = serde_json::from_str(payload).map_err(MergeBundleError::Deserialize)?;
        bundle.enforce_supported_version()?;
        Ok(bundle)
    }

    /// Serialize JSON only for supported bundle versions.
    pub fn to_pretty_json(&self) -> Result<String, MergeBundleError> {
        self.enforce_supported_version()?;
        serde_json::to_string_pretty(self).map_err(MergeBundleError::Serialize)
    }
}

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MergeBundleError {
    #[error(
        "unsupported MergeBundle version {found}; this crate supports versions 1–{max_supported}"
    )]
    UnsupportedBundleVersion { found: u32, max_supported: u32 },
    #[error("failed to deserialize MergeBundle JSON: {0}")]
    Deserialize(#[source] serde_json::Error),
    #[error("failed to serialize MergeBundle JSON: {0}")]
    Serialize(#[source] serde_json::Error),
}

#[cfg(test)]
mod tests {
    use super::{fixtures, MergeBundle, MergeBundleError, MERGE_BUNDLE_VERSION};

    #[test]
    fn rejects_unknown_bundle_versions() {
        let bundle =
            fixtures::representative_bundle().with_bundle_version(MERGE_BUNDLE_VERSION + 1);
        let payload = serde_json::to_string(&bundle).expect("representative bundle serializes");

        let err = MergeBundle::from_json_str(&payload).expect_err("unsupported version rejected");
        match err {
            MergeBundleError::UnsupportedBundleVersion {
                found,
                max_supported,
            } => {
                assert_eq!(found, MERGE_BUNDLE_VERSION + 1, "wrong rejected version");
                assert_eq!(max_supported, MERGE_BUNDLE_VERSION, "wrong max supported");
            }
            other => panic!("expected UnsupportedBundleVersion, got: {other:?}"),
        }
    }

    #[test]
    fn accepts_v1_bundles() {
        let bundle = fixtures::representative_bundle()
            .with_bundle_version(1)
            .with_expression_format(None);
        let payload = serde_json::to_string(&bundle).expect("v1 bundle serializes");
        let parsed = MergeBundle::from_json_str(&payload).expect("v1 bundle should be accepted");
        parsed
            .enforce_supported_version()
            .expect("v1 should pass version check");
    }

    #[test]
    fn checked_in_fixture_round_trips_through_parser() {
        let fixture = fixtures::read_checked_in_representative_fixture()
            .expect("checked-in representative fixture should read");
        let bundle = MergeBundle::from_json_str(&fixture).expect("checked-in fixture should parse");
        bundle
            .enforce_supported_version()
            .expect("checked-in fixture should be supported");
    }

    #[test]
    fn version_constant_is_4() {
        assert_eq!(MERGE_BUNDLE_VERSION, 4);
    }

    #[test]
    fn enforce_accepts_versions_1_through_4() {
        for v in 1..=4 {
            let bundle = fixtures::representative_bundle().with_bundle_version(v);
            bundle
                .enforce_supported_version()
                .unwrap_or_else(|_| panic!("version {v} should be accepted"));
        }
    }

    #[test]
    fn enforce_rejects_version_5() {
        let bundle = fixtures::representative_bundle().with_bundle_version(5);
        assert!(bundle.enforce_supported_version().is_err());
    }
}
