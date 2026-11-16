//! Private companion observations for trait declarations and explicit impls.
//!
//! This does not widen the public signature-only declaration/import language.
//! Native keys are related by unique original source anchors and the complete
//! represented signature, scope, trait arguments and native clause vectors.

extern crate rustc_abi;

use rustc_hir::def_id::{CrateNum, DefIndex};

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Anchor {
    Named(SourceAnchor),
    Implementation(AuthoredSpan),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Reference {
    key: NativeKey,
    artifact: Option<alignment::Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Bound {
    scope: Reference,
    declaration: Reference,
    arguments: Vec<DeclarationType>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Origin {
    Free,
    Inherent {
        implementation: NativeKey,
        self_type: DeclarationType,
    },
    Trait(NativeKey),
    ExplicitImpl {
        implementation: NativeKey,
        declaration: NativeKey,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    Trait,
    Implementation {
        declaration: Reference,
        arguments: Vec<DeclarationType>,
    },
    InherentImplementation {
        self_type: DeclarationType,
    },
    Function {
        origin: Origin,
        inputs: Vec<DeclarationType>,
        output: DeclarationType,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    anchor: Anchor,
    generics: Vec<GenericScope>,
    clauses: Vec<Bound>,
    shape: Shape,
}

/// Only direct native capture creates this private companion view. Unknown
/// entries are retained; an absent observation never establishes equality.
pub(in crate::reader::declaration_staging) struct View {
    entries: BTreeMap<NativeKey, Observation<Entry>>,
}

struct Capture<'a, 'tcx> {
    types: declaration_native::Types<'tcx, 'a>,
    inputs: &'a Inputs,
}

impl<'tcx> Capture<'_, 'tcx> {
    fn reference(&self, definition: DefId) -> Result<Reference, String> {
        Ok(Reference {
            key: declaration_native::key(self.types.tcx, definition),
            artifact: (definition.krate != self.types.library)
                .then(|| {
                    declaration_native::selected(
                        self.types.tcx,
                        definition.krate,
                        self.types.dependencies,
                    )
                })
                .transpose()?,
        })
    }

    fn arguments(&self, args: ty::GenericArgs<'tcx>) -> Result<Vec<DeclarationType>, String> {
        if args.len() > 256 {
            return Err("Spec companion generic arity exceeds its bound".into());
        }
        args.iter()
            .map(|arg| match arg.kind() {
                ty::GenericArgKind::Type(value) => self.types.encode(value, 0),
                _ => Err("Spec companion lifetime/const arguments need a typed codec".into()),
            })
            .collect()
    }

    fn clauses(&self, definition: DefId) -> Result<Vec<Bound>, String> {
        let tcx = self.types.tcx;
        let env = ty::TypingEnv::non_body_analysis(tcx, definition);
        let args = ty::GenericArgs::identity_for_item(tcx, definition);
        dispatch::clauses(tcx, definition, args, env)?
            .into_iter()
            .map(|clause| {
                let Some(ty::ClauseKind::Trait(predicate)) = clause.clause.kind().no_bound_vars()
                else {
                    return Err(
                        "Spec companion higher-ranked/nontrait native clauses need a typed codec"
                            .into(),
                    );
                };
                if predicate.polarity != ty::ClausePolarity::Positive {
                    return Err("Spec companion negative native clauses are unsupported".into());
                }
                Ok(Bound {
                    scope: self.reference(clause.scope)?,
                    declaration: self.reference(predicate.def_id())?,
                    arguments: self.arguments(predicate.trait_ref.args)?,
                })
            })
            .collect()
    }

    fn entry(&self, definition: DefId) -> Result<Entry, String> {
        let tcx = self.types.tcx;
        let env = ty::TypingEnv::non_body_analysis(tcx, definition);
        let kind = tcx.def_kind(definition);
        let anchor = if matches!(kind, DefKind::Impl { .. }) {
            Anchor::Implementation(declaration_native::span(
                tcx,
                &self.inputs.sources,
                tcx.def_span(definition),
            )?)
        } else {
            Anchor::Named(declaration_native::source(
                tcx,
                definition,
                &self.inputs.sources,
            )?)
        };
        let shape = match kind {
            DefKind::Trait => Shape::Trait,
            DefKind::Impl { of_trait: true } => {
                let native = tcx
                    .try_normalize_erasing_regions(
                        env,
                        tcx.impl_trait_ref(definition).instantiate_identity(),
                    )
                    .map_err(
                        |_| "Spec companion native impl trait reference cannot be normalized",
                    )?;
                Shape::Implementation {
                    declaration: self.reference(native.def_id)?,
                    arguments: self.arguments(native.args)?,
                }
            }
            DefKind::Impl { of_trait: false } => {
                let self_type = tcx
                    .try_normalize_erasing_regions(
                        env,
                        tcx.type_of(definition).instantiate_identity(),
                    )
                    .map_err(|_| "Spec companion inherent impl Self normalization failed")?;
                Shape::InherentImplementation {
                    self_type: self.types.encode(self_type, 0)?,
                }
            }
            DefKind::Fn | DefKind::AssocFn => {
                let parent = tcx
                    .opt_parent(definition)
                    .ok_or("a Spec companion function lacks a parent")?;
                let origin = match tcx.def_kind(parent) {
                    DefKind::Mod => Origin::Free,
                    DefKind::Trait => Origin::Trait(declaration_native::key(tcx, parent)),
                    DefKind::Impl { of_trait: false } => {
                        let self_type = tcx
                            .try_normalize_erasing_regions(
                                ty::TypingEnv::non_body_analysis(tcx, parent),
                                tcx.type_of(parent).instantiate_identity(),
                            )
                            .map_err(|_| "Spec companion inherent Self normalization failed")?;
                        Origin::Inherent {
                            implementation: declaration_native::key(tcx, parent),
                            self_type: self.types.encode(self_type, 0)?,
                        }
                    }
                    DefKind::Impl { of_trait: true } => {
                        let item = tcx.associated_item(definition);
                        let declaration = item.trait_item_def_id().ok_or(
                            "a Spec companion impl member has no native trait declaration",
                        )?;
                        if tcx.trait_impl_of_assoc(definition) != Some(parent) {
                            return Err("a Spec companion associated impl owner changed".into());
                        }
                        Origin::ExplicitImpl {
                            implementation: declaration_native::key(tcx, parent),
                            declaration: declaration_native::key(tcx, declaration),
                        }
                    }
                    _ => {
                        return Err("a Spec companion function has unsupported native origin".into());
                    }
                };
                let native = tcx
                    .try_normalize_erasing_regions(
                        env,
                        tcx.fn_sig(definition).instantiate_identity(),
                    )
                    .map_err(|_| "Spec companion native signature normalization failed")?;
                let signature = native
                    .no_bound_vars()
                    .ok_or("a Spec companion signature has higher-ranked binders")?;
                if signature.abi() != rustc_abi::ExternAbi::Rust
                    || !signature.safety().is_safe()
                    || signature.c_variadic()
                    || signature.splatted().is_some()
                {
                    return Err("a Spec companion signature has unsupported native ABI".into());
                }
                if signature.inputs().len() > 256 {
                    return Err("a Spec companion signature exceeds its input bound".into());
                }
                Shape::Function {
                    origin,
                    inputs: signature
                        .inputs()
                        .iter()
                        .map(|value| self.types.encode(*value, 0))
                        .collect::<Result<_, _>>()?,
                    output: self.types.encode(signature.output(), 0)?,
                }
            }
            _ => return Err("unsupported Spec companion declaration kind".into()),
        };
        Ok(Entry {
            anchor,
            generics: declaration_native::scopes(tcx, definition)?,
            clauses: self.clauses(definition)?,
            shape,
        })
    }
}

impl View {
    pub(in crate::reader::declaration_staging) fn capture(
        tcx: TyCtxt<'_>,
        library: CrateNum,
        inputs: &Inputs,
        metadata: &Metadata,
    ) -> Result<Self, String> {
        diagnostics(tcx)?;
        let definitions = if library == LOCAL_CRATE {
            tcx.hir_crate_items(())
                .owners()
                .map(|owner| owner.def_id.to_def_id())
                .collect::<Vec<_>>()
        } else {
            (0..tcx.num_extern_def_ids(library))
                .map(|index| DefId {
                    krate: library,
                    index: DefIndex::from_usize(index),
                })
                .collect()
        };
        if definitions.len() > MAX_WORK {
            return Err("Spec companion inventory exceeds its bound".into());
        }
        let capture = Capture {
            types: declaration_native::Types {
                tcx,
                library,
                dependencies: metadata,
            },
            inputs,
        };
        let mut entries = BTreeMap::new();
        for definition in definitions {
            if !matches!(
                tcx.def_kind(definition),
                DefKind::Trait | DefKind::Fn | DefKind::AssocFn | DefKind::Impl { .. }
            ) {
                continue;
            }
            let value = match capture.entry(definition) {
                Ok(value) => Observation::Observed(value),
                Err(reason) => Observation::Unknown(reason),
            };
            if entries
                .insert(declaration_native::key(tcx, definition), value)
                .is_some()
            {
                return Err("Spec companion inventory repeats a native key".into());
            }
        }
        Ok(Self { entries })
    }
}

pub(in crate::reader::declaration_staging) fn roundtrip(
    local: &View,
    loaded: &View,
) -> BTreeSet<NativeKey> {
    local
        .entries
        .keys()
        .chain(loaded.entries.keys())
        .filter(|key| {
            !matches!((local.entries.get(key), loaded.entries.get(key)),
            (Some(Observation::Observed(a)), Some(Observation::Observed(b))) if a == b)
        })
        .copied()
        .collect()
}

/// Private, native-view-bound correspondence, still without body permission.
#[derive(PartialEq, Eq)]
pub(in crate::reader::declaration_staging) struct Pairs {
    pairs: BTreeMap<NativeKey, NativeKey>,
}

impl Pairs {
    pub(in crate::reader::declaration_staging) fn erase(
        &self,
        keep: NativeKey,
    ) -> Option<&NativeKey> {
        self.pairs.get(&keep)
    }

    pub(in crate::reader::declaration_staging) fn compare(
        keep: &View,
        erase: &View,
        unavailable: &BTreeSet<NativeKey>,
        nominals: BTreeMap<NativeKey, NativeKey>,
    ) -> Result<Self, String> {
        let index = |view: &View| {
            let mut out: BTreeMap<Anchor, Vec<NativeKey>> = BTreeMap::new();
            for (key, entry) in &view.entries {
                if let Observation::Observed(entry) = entry {
                    out.entry(entry.anchor.clone()).or_default().push(*key);
                }
            }
            out
        };
        let ki = index(keep);
        let ei = index(erase);
        let mut pairs = BTreeMap::new();
        for (anchor, keys) in ki {
            if let ([key], Some(others)) = (keys.as_slice(), ei.get(&anchor)) {
                if let [other] = others.as_slice() {
                    if !unavailable.contains(other) {
                        pairs.insert(*key, *other);
                    }
                }
            }
        }
        // Remove unsupported pairs to a fixed point. A member cannot retain
        // correspondence after its referenced trait or explicit impl failed.
        let mut remaining = MAX_WORK;
        loop {
            remaining = remaining
                .checked_sub(pairs.len())
                .ok_or("Spec companion comparison work bound exhausted")?;
            let invalid = pairs
                .iter()
                .filter_map(|(key, other)| {
                    let (Some(Observation::Observed(a)), Some(Observation::Observed(b))) =
                        (keep.entries.get(key), erase.entries.get(other))
                    else {
                        return Some(*key);
                    };
                    (!equal(a, b, &pairs, &nominals)).then_some(*key)
                })
                .collect::<Vec<_>>();
            if invalid.is_empty() {
                break;
            }
            for key in invalid {
                pairs.remove(&key);
            }
        }
        Ok(Self { pairs })
    }
}

#[cfg(test)]
mod tests;

fn equal(
    a: &Entry,
    b: &Entry,
    pairs: &BTreeMap<NativeKey, NativeKey>,
    nominals: &BTreeMap<NativeKey, NativeKey>,
) -> bool {
    let reference = |a: &Reference, b: &Reference| match (a.artifact, b.artifact) {
        (None, None) => pairs.get(&a.key) == Some(&b.key),
        (Some(_), Some(_)) => a == b,
        _ => false,
    };
    let types = |a: &[DeclarationType], b: &[DeclarationType]| {
        a.len() == b.len() && a.iter().zip(b).all(|(a, b)| type_equal(a, b, nominals, 0))
    };
    let shape = match (&a.shape, &b.shape) {
        (Shape::Trait, Shape::Trait) => true,
        (
            Shape::InherentImplementation { self_type: a },
            Shape::InherentImplementation { self_type: b },
        ) => type_equal(a, b, nominals, 0),
        (
            Shape::Implementation {
                declaration: ad,
                arguments: aa,
            },
            Shape::Implementation {
                declaration: bd,
                arguments: ba,
            },
        ) => reference(ad, bd) && types(aa, ba),
        (
            Shape::Function {
                origin: ao,
                inputs: ai,
                output: ar,
            },
            Shape::Function {
                origin: bo,
                inputs: bi,
                output: br,
            },
        ) => {
            let origin = match (ao, bo) {
                (Origin::Free, Origin::Free) => true,
                (
                    Origin::Inherent {
                        implementation: ai,
                        self_type: a,
                    },
                    Origin::Inherent {
                        implementation: bi,
                        self_type: b,
                    },
                ) => pairs.get(ai) == Some(bi) && type_equal(a, b, nominals, 0),
                (Origin::Trait(a), Origin::Trait(b)) => pairs.get(a) == Some(b),
                (
                    Origin::ExplicitImpl {
                        implementation: ai,
                        declaration: ad,
                    },
                    Origin::ExplicitImpl {
                        implementation: bi,
                        declaration: bd,
                    },
                ) => pairs.get(ai) == Some(bi) && pairs.get(ad) == Some(bd),
                _ => false,
            };
            origin && types(ai, bi) && type_equal(ar, br, nominals, 0)
        }
        _ => false,
    };
    a.anchor == b.anchor
        && a.generics == b.generics
        && shape
        && a.clauses.len() == b.clauses.len()
        && a.clauses.iter().zip(&b.clauses).all(|(a, b)| {
            reference(&a.scope, &b.scope)
                && reference(&a.declaration, &b.declaration)
                && types(&a.arguments, &b.arguments)
        })
}

fn type_equal(
    a: &DeclarationType,
    b: &DeclarationType,
    nominals: &BTreeMap<NativeKey, NativeKey>,
    depth: usize,
) -> bool {
    if depth > 64 {
        return false;
    }
    let args = |a: &[DeclarationType], b: &[DeclarationType]| {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(a, b)| type_equal(a, b, nominals, depth + 1))
    };
    match (a, b) {
        (
            DeclarationType::LocalNominal {
                declaration: ad,
                arguments: aa,
            },
            DeclarationType::LocalNominal {
                declaration: bd,
                arguments: ba,
            },
        ) => nominals.get(ad) == Some(bd) && args(aa, ba),
        (
            DeclarationType::ExternalNominal {
                declaration: ad,
                arguments: aa,
            },
            DeclarationType::ExternalNominal {
                declaration: bd,
                arguments: ba,
            },
        ) => ad == bd && args(aa, ba),
        (DeclarationType::Tuple(a), DeclarationType::Tuple(b)) => args(a, b),
        _ => a == b,
    }
}
