//! Structural candidates for a Keep/Erase declaration join.
//!
//! These types describe observations, not authenticated import permissions.
//! The compiler/staging producer must bind source anchors and both views to
//! actual files and artifacts before using a candidate. In particular, no
//! caller-supplied observation can mint a header, mode, body or proof receipt.
//! Native keys identify declarations *within* a view; display paths and equal
//! native hashes never establish correspondence between views.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};

pub mod observation;
pub mod source_bindings;

/// SHA256 of actual input bytes, supplied by the staging producer.
pub type Digest = [u8; 32];

/// One actual compiler declaration key, scoped to the selected artifact/view.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NativeKey {
    pub stable_crate_id: u64,
    pub def_path_hash: u128,
}

impl NativeKey {
    fn is_well_formed(self) -> bool {
        u64::try_from(self.def_path_hash >> 64).ok() == Some(self.stable_crate_id)
    }
}

/// Original-file byte coordinates, never normalized or Debug span strings.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AuthoredSpan {
    /// Canonical source-manifest-relative path, not a display path.
    pub relative_file: String,
    pub file_sha256: Digest,
    pub original_file_len: u32,
    pub bytes: (u32, u32),
}

impl AuthoredSpan {
    fn is_well_formed(&self) -> bool {
        !self.relative_file.is_empty()
            && !self.relative_file.starts_with('/')
            && !self.relative_file.contains('\\')
            && self
                .relative_file
                .split('/')
                .all(|part| !matches!(part, "" | "." | ".."))
            && self.bytes.0 < self.bytes.1
            && self.bytes.1 <= self.original_file_len
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceAnchor {
    /// Name token supplied by the compiler's actual identifier span.
    pub identifier: AuthoredSpan,
    /// Authored module/impl anchors, outermost first. An out-of-line module
    /// may be in a different file. Missing/synthetic anchors stay Unknown.
    pub enclosing_declarations: Vec<AuthoredSpan>,
}

impl SourceAnchor {
    fn is_well_formed(&self) -> bool {
        self.identifier.is_well_formed()
            && self
                .enclosing_declarations
                .iter()
                .all(AuthoredSpan::is_well_formed)
    }
}

/// An actual type-parameter declaration, not a chosen generic argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParameter {
    pub index: u32,
    pub has_default: bool,
    pub synthetic: bool,
    pub pure_wrt_drop: bool,
}

/// Generic scopes from the declaration outward, preserving native flattened
/// indices. The first codec represents only ordinary type parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericScope {
    pub parent_count: u32,
    pub own_type_parameters: Vec<TypeParameter>,
    pub has_self: bool,
}

/// Nominal identity from another, exactly selected dependency artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalType {
    pub artifact_sha256: Digest,
    pub key: NativeKey,
    pub type_parameters: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntegerWidth {
    Fixed(u16),
    Pointer,
}

/// A structural declaration type. Unsupported aliases, binders, references,
/// lifetime/const arguments and inference variables are not silently erased.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclarationType {
    Bool,
    Integer {
        signed: bool,
        width: IntegerWidth,
    },
    Parameter(u32),
    Tuple(Vec<Self>),
    LocalNominal {
        declaration: NativeKey,
        arguments: Vec<Self>,
    },
    ExternalNominal {
        declaration: ExternalType,
        arguments: Vec<Self>,
    },
}

/// Source kind is a structural check; it is not a private field/layout query.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NominalKind {
    Struct,
    Enum,
    Union,
}

/// Function origin independently of spelling or impl disambiguators.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionOrigin {
    Free,
    Inherent { self_type: DeclarationType },
}

/// The bounded shape which both compiler passes must actually describe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclarationShape {
    Nominal {
        kind: NominalKind,
    },
    Function {
        origin: FunctionOrigin,
        inputs: Vec<DeclarationType>,
        output: Box<DeclarationType>,
    },
}

/// A missing structural or authored-source fact is an explicit refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Observation<T> {
    Observed(T),
    Unknown(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    pub key: NativeKey,
    pub source: Observation<SourceAnchor>,
    pub generics: Observation<Vec<GenericScope>>,
    pub shape: Observation<DeclarationShape>,
}

/// Inputs common to the two actual compiler projections. Full pass cfgs and
/// selected Erase metadata bytes are retained separately, not equated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommonInputs {
    /// Bytes of the actual compiler image used by both views. A separate
    /// staging executable is recorded as producer identity, not substituted.
    pub compiler_sha256: Digest,
    /// The complete checked source identity, including an explicit unmodified
    /// state or both the compatibility recipe and patch.
    pub source: source_bindings::SourceIdentity,
    pub builtin_artifacts: BTreeSet<Digest>,
    /// Every actual selected dependency artifact, including std/alloc and
    /// the builtin cohort. A lookalike key from other bytes is not imported.
    pub dependency_artifacts: BTreeSet<Digest>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct View {
    pub common: CommonInputs,
    pub cfg_sha256: Digest,
    pub stable_crate_id: u64,
    /// None for pre-MIR Keep observation; Some for the actual selected Erase
    /// rmeta. A local Keep SVH is not requested or invented.
    pub selected_rmeta_sha256: Option<Digest>,
    pub declarations: Vec<Declaration>,
}

/// A unique source/structural correlation. Header and mode authority are not
/// fields of this value, and it cannot be consumed as an import capability.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    pub keep: NativeKey,
    pub erase: NativeKey,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    pub keep: NativeKey,
    pub reason: &'static str,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Candidates {
    pub matches: Vec<Candidate>,
    pub refused: Vec<Refusal>,
}

fn inventory(view: &View) -> Result<BTreeMap<&SourceAnchor, Vec<&Declaration>>, &'static str> {
    let mut keys = BTreeSet::new();
    let mut anchors: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for declaration in &view.declarations {
        if !declaration.key.is_well_formed()
            || declaration.key.stable_crate_id != view.stable_crate_id
            || !keys.insert(declaration.key)
        {
            return Err("declaration keys are duplicated or outside the selected crate");
        }
        if let Observation::Observed(generics) = &declaration.generics {
            if generic_count(generics).is_none() {
                return Err("generic scope indices or parent counts are malformed");
            }
        }
        if let Observation::Observed(anchor) = &declaration.source {
            if !anchor.is_well_formed() {
                return Err("an authored source anchor is malformed");
            }
            anchors.entry(anchor).or_default().push(declaration);
        }
    }
    Ok(anchors)
}

fn generic_count(scopes: &[GenericScope]) -> Option<u32> {
    let mut parent = 0;
    for scope in scopes.iter().rev() {
        if scope.parent_count != parent {
            return None;
        }
        for (offset, parameter) in scope.own_type_parameters.iter().enumerate() {
            if parameter.index != parent.checked_add(u32::try_from(offset).ok()?)? {
                return None;
            }
        }
        parent = parent.checked_add(u32::try_from(scope.own_type_parameters.len()).ok()?)?;
    }
    Some(parent)
}

fn type_is_well_formed(
    ty: &DeclarationType,
    parameters: u32,
    nominals: &BTreeMap<NativeKey, u32>,
    dependencies: &BTreeSet<Digest>,
    depth: u32,
) -> bool {
    if depth > 64 {
        return false;
    }
    let arguments_valid = |arguments: &[DeclarationType], count: u32| {
        usize::try_from(count).ok() == Some(arguments.len())
            && arguments.iter().all(|argument| {
                type_is_well_formed(argument, parameters, nominals, dependencies, depth + 1)
            })
    };
    match ty {
        DeclarationType::Bool => true,
        DeclarationType::Integer {
            width: IntegerWidth::Fixed(width),
            ..
        } => matches!(width, 8 | 16 | 32 | 64 | 128),
        DeclarationType::Integer {
            width: IntegerWidth::Pointer,
            ..
        } => true,
        DeclarationType::Parameter(index) => *index < parameters,
        DeclarationType::Tuple(elements) => elements.iter().all(|element| {
            type_is_well_formed(element, parameters, nominals, dependencies, depth + 1)
        }),
        DeclarationType::LocalNominal {
            declaration,
            arguments,
        } => nominals
            .get(declaration)
            .is_some_and(|count| arguments_valid(arguments, *count)),
        DeclarationType::ExternalNominal {
            declaration,
            arguments,
        } => {
            declaration.key.is_well_formed()
                && dependencies.contains(&declaration.artifact_sha256)
                && arguments_valid(arguments, declaration.type_parameters)
        }
    }
}

fn structure_is_well_formed(
    declaration: &Declaration,
    nominals: &BTreeMap<NativeKey, u32>,
    dependencies: &BTreeSet<Digest>,
) -> bool {
    let (Observation::Observed(generics), Observation::Observed(shape)) =
        (&declaration.generics, &declaration.shape)
    else {
        return false;
    };
    let Some(parameters) = generic_count(generics) else {
        return false;
    };
    // Default type expressions and synthetic binders need their own faithful
    // codec. Their flags are retained and never mistaken for ordinary slots.
    if generics
        .iter()
        .flat_map(|scope| &scope.own_type_parameters)
        .any(|parameter| parameter.has_default || parameter.synthetic)
    {
        return false;
    }
    match shape {
        DeclarationShape::Nominal { .. } => true,
        DeclarationShape::Function {
            origin,
            inputs,
            output,
        } => {
            let origin_valid = match origin {
                FunctionOrigin::Free => true,
                FunctionOrigin::Inherent { self_type } => {
                    type_is_well_formed(self_type, parameters, nominals, dependencies, 0)
                }
            };
            origin_valid
                && inputs
                    .iter()
                    .chain(std::iter::once(output.as_ref()))
                    .all(|ty| type_is_well_formed(ty, parameters, nominals, dependencies, 0))
        }
    }
}

fn types_equal(
    keep: &DeclarationType,
    erase: &DeclarationType,
    nominals: &BTreeMap<NativeKey, NativeKey>,
    depth: u32,
) -> bool {
    if depth > 64 {
        return false;
    }
    let arguments_equal = |a: &[DeclarationType], b: &[DeclarationType]| {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(a, b)| types_equal(a, b, nominals, depth + 1))
    };
    match (keep, erase) {
        (DeclarationType::Bool, DeclarationType::Bool) => true,
        (
            DeclarationType::Integer {
                signed: a,
                width: aw,
            },
            DeclarationType::Integer {
                signed: b,
                width: bw,
            },
        ) => a == b && aw == bw,
        (DeclarationType::Parameter(a), DeclarationType::Parameter(b)) => a == b,
        (DeclarationType::Tuple(a), DeclarationType::Tuple(b)) => arguments_equal(a, b),
        (
            DeclarationType::LocalNominal {
                declaration: a,
                arguments: aa,
            },
            DeclarationType::LocalNominal {
                declaration: b,
                arguments: ba,
            },
        ) => nominals.get(a) == Some(b) && arguments_equal(aa, ba),
        (
            DeclarationType::ExternalNominal {
                declaration: a,
                arguments: aa,
            },
            DeclarationType::ExternalNominal {
                declaration: b,
                arguments: ba,
            },
        ) => a == b && arguments_equal(aa, ba),
        _ => false,
    }
}

fn shapes_equal(
    keep: &DeclarationShape,
    erase: &DeclarationShape,
    nominals: &BTreeMap<NativeKey, NativeKey>,
) -> bool {
    match (keep, erase) {
        (DeclarationShape::Nominal { kind: a }, DeclarationShape::Nominal { kind: b }) => a == b,
        (
            DeclarationShape::Function {
                origin: ko,
                inputs: ki,
                output: kr,
            },
            DeclarationShape::Function {
                origin: eo,
                inputs: ei,
                output: er,
            },
        ) => {
            let origin_equal = match (ko, eo) {
                (FunctionOrigin::Free, FunctionOrigin::Free) => true,
                (
                    FunctionOrigin::Inherent { self_type: a },
                    FunctionOrigin::Inherent { self_type: b },
                ) => types_equal(a, b, nominals, 0),
                _ => false,
            };
            origin_equal
                && ki.len() == ei.len()
                && ki
                    .iter()
                    .zip(ei)
                    .all(|(a, b)| types_equal(a, b, nominals, 0))
                && types_equal(kr, er, nominals, 0)
        }
        _ => false,
    }
}

/// Compute candidates across the entire observed inventory. A source anchor
/// must occur exactly once in each view. Type declarations are related first,
/// so a function never equates unrelated native nominal keys by coincidence.
///
/// Even a complete result says nothing about contracts, predicates, mode or
/// body validity. Unknown prerequisites still prohibit all product imports.
pub fn compare(keep: &View, erase: &View) -> Result<Candidates, &'static str> {
    if keep.common != erase.common
        || !keep
            .common
            .builtin_artifacts
            .is_subset(&keep.common.dependency_artifacts)
        || keep.selected_rmeta_sha256.is_some()
        || erase.selected_rmeta_sha256.is_none()
    {
        return Err("Keep/Erase input cohorts or projection roles do not match");
    }
    let keep_anchors = inventory(keep)?;
    let erase_anchors = inventory(erase)?;
    let nominal_counts = |view: &View| {
        view.declarations
            .iter()
            .filter_map(|declaration| {
                if let (
                    Observation::Observed(DeclarationShape::Nominal { .. }),
                    Observation::Observed(generics),
                ) = (&declaration.shape, &declaration.generics)
                {
                    generic_count(generics).map(|count| (declaration.key, count))
                } else {
                    None
                }
            })
            .collect::<BTreeMap<_, _>>()
    };
    let keep_nominals = nominal_counts(keep);
    let erase_nominals = nominal_counts(erase);
    let mut pairs = Vec::new();
    let mut out = Candidates::default();
    for declaration in &keep.declarations {
        let other = match &declaration.source {
            Observation::Observed(anchor) => {
                match (keep_anchors.get(anchor), erase_anchors.get(anchor)) {
                    (Some(a), Some(b)) if a.len() == 1 && b.len() == 1 => Some(b[0]),
                    _ => None,
                }
            }
            Observation::Unknown(_) => None,
        };
        if let Some(other) = other {
            pairs.push((declaration, other));
        } else {
            out.refused.push(Refusal {
                keep: declaration.key,
                reason: "no unique authored-source counterpart",
            });
        }
    }
    let mut nominals = BTreeMap::new();
    for (a, b) in &pairs {
        if let (
            Observation::Observed(DeclarationShape::Nominal { kind: ak }),
            Observation::Observed(DeclarationShape::Nominal { kind: bk }),
            Observation::Observed(ag),
            Observation::Observed(bg),
        ) = (&a.shape, &b.shape, &a.generics, &b.generics)
        {
            if ak == bk
                && ag == bg
                && structure_is_well_formed(a, &keep_nominals, &keep.common.dependency_artifacts)
                && structure_is_well_formed(b, &erase_nominals, &erase.common.dependency_artifacts)
            {
                nominals.insert(a.key, b.key);
            }
        }
    }
    for (a, b) in pairs {
        let equal = match (&a.generics, &b.generics, &a.shape, &b.shape) {
            (
                Observation::Observed(ag),
                Observation::Observed(bg),
                Observation::Observed(ash),
                Observation::Observed(bsh),
            ) => {
                ag == bg
                    && structure_is_well_formed(
                        a,
                        &keep_nominals,
                        &keep.common.dependency_artifacts,
                    )
                    && structure_is_well_formed(
                        b,
                        &erase_nominals,
                        &erase.common.dependency_artifacts,
                    )
                    && shapes_equal(ash, bsh, &nominals)
            }
            _ => false,
        };
        if equal {
            out.matches.push(Candidate {
                keep: a.key,
                erase: b.key,
            });
        } else {
            out.refused.push(Refusal {
                keep: a.key,
                reason: "unsupported or unequal declaration structure",
            });
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(krate: u64, local: u64) -> NativeKey {
        NativeKey {
            stable_crate_id: krate,
            def_path_hash: (u128::from(krate) << 64) | u128::from(local),
        }
    }

    fn anchor(lo: u32) -> Observation<SourceAnchor> {
        Observation::Observed(SourceAnchor {
            identifier: AuthoredSpan {
                relative_file: "source/vstd/set.rs".into(),
                file_sha256: [5; 32],
                original_file_len: 300,
                bytes: (lo, lo + 3),
            },
            enclosing_declarations: vec![AuthoredSpan {
                relative_file: "source/vstd/set.rs".into(),
                file_sha256: [5; 32],
                original_file_len: 300,
                bytes: (1, 200),
            }],
        })
    }

    fn views() -> (View, View) {
        let common = CommonInputs {
            compiler_sha256: [1; 32],
            source: source_bindings::SourceIdentity {
                manifest_sha256: [2; 32],
                compatibility: source_bindings::SourceCompatibility::Applied {
                    recipe_sha256: [14; 32],
                    patch_sha256: [3; 32],
                },
            },
            builtin_artifacts: BTreeSet::from([[4; 32]]),
            dependency_artifacts: BTreeSet::from([[4; 32]]),
        };
        let parameter = || TypeParameter {
            index: 0,
            has_default: false,
            synthetic: false,
            pure_wrt_drop: false,
        };
        let make = |krate| {
            let carrier = DeclarationType::LocalNominal {
                declaration: key(krate, 1),
                arguments: vec![DeclarationType::Parameter(0)],
            };
            vec![
                Declaration {
                    key: key(krate, 1),
                    source: anchor(10),
                    generics: Observation::Observed(vec![GenericScope {
                        parent_count: 0,
                        own_type_parameters: vec![parameter()],
                        has_self: false,
                    }]),
                    shape: Observation::Observed(DeclarationShape::Nominal {
                        kind: NominalKind::Struct,
                    }),
                },
                Declaration {
                    key: key(krate, 2),
                    source: anchor(50),
                    generics: Observation::Observed(vec![
                        GenericScope {
                            parent_count: 1,
                            own_type_parameters: vec![],
                            has_self: false,
                        },
                        GenericScope {
                            parent_count: 0,
                            own_type_parameters: vec![parameter()],
                            has_self: false,
                        },
                    ]),
                    shape: Observation::Observed(DeclarationShape::Function {
                        origin: FunctionOrigin::Inherent {
                            self_type: carrier.clone(),
                        },
                        inputs: vec![carrier],
                        output: Box::new(DeclarationType::ExternalNominal {
                            declaration: ExternalType {
                                artifact_sha256: [4; 32],
                                key: key(8, 3),
                                type_parameters: 0,
                            },
                            arguments: vec![],
                        }),
                    }),
                },
            ]
        };
        (
            View {
                common: common.clone(),
                cfg_sha256: [6; 32],
                stable_crate_id: 7,
                selected_rmeta_sha256: None,
                declarations: make(7),
            },
            View {
                common,
                cfg_sha256: [9; 32],
                stable_crate_id: 9,
                selected_rmeta_sha256: Some([10; 32]),
                declarations: make(9),
            },
        )
    }

    #[test]
    fn generic_nominal_keys_are_related_by_source_and_structure() {
        let (keep, erase) = views();
        let out = compare(&keep, &erase).unwrap();
        assert_eq!(
            out.matches,
            vec![
                Candidate {
                    keep: key(7, 1),
                    erase: key(9, 1)
                },
                Candidate {
                    keep: key(7, 2),
                    erase: key(9, 2)
                }
            ]
        );
        assert!(out.refused.is_empty());
    }

    #[test]
    fn equal_native_keys_cannot_replace_source_correspondence() {
        let (keep, mut erase) = views();
        erase.stable_crate_id = 7;
        erase.declarations = keep.declarations.clone();
        for declaration in &mut erase.declarations {
            if let Observation::Observed(anchor) = &mut declaration.source {
                anchor.identifier.file_sha256 = [11; 32];
            }
        }
        let out = compare(&keep, &erase).unwrap();
        assert!(out.matches.is_empty());
        assert_eq!(out.refused.len(), 2);
    }

    #[test]
    fn source_collision_is_unknown_instead_of_first_match() {
        let (keep, mut erase) = views();
        let mut duplicate = erase.declarations[1].clone();
        duplicate.key = key(9, 4);
        erase.declarations.push(duplicate);
        let out = compare(&keep, &erase).unwrap();
        assert_eq!(out.matches.len(), 1);
        assert_eq!(out.refused[0].keep, key(7, 2));
    }

    #[test]
    fn changed_generic_indices_are_not_alpha_renamed_into_agreement() {
        let (keep, mut erase) = views();
        if let Observation::Observed(scopes) = &mut erase.declarations[1].generics {
            scopes[1].own_type_parameters[0].index = 1;
        }
        assert!(compare(&keep, &erase).is_err());
    }

    #[test]
    fn a_different_builtin_cohort_refuses_the_entire_join() {
        let (keep, mut erase) = views();
        erase.common.builtin_artifacts = BTreeSet::from([[12; 32]]);
        assert!(compare(&keep, &erase).is_err());
    }

    #[test]
    fn source_graph_and_complete_compatibility_policy_must_match() {
        use source_bindings::{SourceCompatibility, SourceIdentity};
        let (mut keep, mut erase) = views();
        let original = keep.common.source;
        for changed in [
            SourceIdentity {
                manifest_sha256: [15; 32],
                ..original
            },
            SourceIdentity {
                compatibility: SourceCompatibility::Unmodified,
                ..original
            },
            SourceIdentity {
                compatibility: SourceCompatibility::Applied {
                    recipe_sha256: [16; 32],
                    patch_sha256: [3; 32],
                },
                ..original
            },
            SourceIdentity {
                compatibility: SourceCompatibility::Applied {
                    recipe_sha256: [14; 32],
                    patch_sha256: [17; 32],
                },
                ..original
            },
        ] {
            erase.common.source = changed;
            assert!(compare(&keep, &erase).is_err());
        }
        // A known unmodified graph can match; no invented patch is required.
        keep.common.source.compatibility = SourceCompatibility::Unmodified;
        erase.common.source = keep.common.source;
        assert_eq!(compare(&keep, &erase).unwrap().matches.len(), 2);
    }

    #[test]
    fn same_external_native_key_in_a_different_artifact_is_not_the_same_type() {
        let (keep, mut erase) = views();
        let Observation::Observed(DeclarationShape::Function { output, .. }) =
            &mut erase.declarations[1].shape
        else {
            panic!("expected the observed function");
        };
        let DeclarationType::ExternalNominal { declaration, .. } = output.as_mut() else {
            panic!("expected the external codomain");
        };
        declaration.artifact_sha256 = [13; 32];
        let out = compare(&keep, &erase).unwrap();
        assert_eq!(out.matches.len(), 1);
        assert_eq!(out.refused.len(), 1);
    }

    #[test]
    fn out_of_scope_type_arguments_do_not_match_even_in_both_views() {
        let (mut keep, mut erase) = views();
        for view in [&mut keep, &mut erase] {
            if let Observation::Observed(DeclarationShape::Function { inputs, .. }) =
                &mut view.declarations[1].shape
            {
                inputs[0] = DeclarationType::Parameter(1);
            }
        }
        let out = compare(&keep, &erase).unwrap();
        assert_eq!(out.matches.len(), 1);
        assert_eq!(out.refused.len(), 1);
    }

    #[test]
    fn missing_structural_facts_do_not_borrow_the_other_pass_facts() {
        let (keep, mut erase) = views();
        erase.declarations[1].shape = Observation::Unknown("normalization failed".into());
        let out = compare(&keep, &erase).unwrap();
        assert_eq!(out.matches.len(), 1);
        assert_eq!(out.refused.len(), 1);
    }

    #[test]
    fn duplicate_or_out_of_crate_native_keys_are_rejected() {
        let (keep, mut erase) = views();
        erase.declarations[1].key = erase.declarations[0].key;
        assert!(compare(&keep, &erase).is_err());
        let (keep, mut erase) = views();
        erase.declarations[1].key = key(99, 2);
        assert!(compare(&keep, &erase).is_err());
    }

    #[test]
    fn default_and_synthetic_slots_require_their_missing_type_codec() {
        for synthetic in [false, true] {
            let (mut keep, mut erase) = views();
            for view in [&mut keep, &mut erase] {
                for declaration in &mut view.declarations {
                    if let Observation::Observed(scopes) = &mut declaration.generics {
                        let parameter = &mut scopes.last_mut().unwrap().own_type_parameters[0];
                        parameter.synthetic = synthetic;
                        parameter.has_default = !synthetic;
                    }
                }
            }
            let out = compare(&keep, &erase).unwrap();
            assert!(out.matches.is_empty());
            assert_eq!(out.refused.len(), 2);
        }
    }
}
