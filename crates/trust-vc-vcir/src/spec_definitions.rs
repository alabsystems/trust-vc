//! Checked semantic definitions carried separately from imported signatures.
//!
//! This collection checks VcIR semantics, not native provenance. A native
//! producer must retain its own live source, correspondence and client join.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    bitvector::Architecture, AdtId, AdtKind, Body, Expr, ExprKind, FnDecl, FnId, FnKind, FnRole,
    Mode, SpanId, Ty, VcCrate, WfClass, WfError,
};

/// Strictly checked, acyclic scalar Spec definitions in their own local scopes.
///
/// Imported declarations remain bodyless. Neither an imported role nor a
/// successful construction here establishes that a native producer owns a body.
#[derive(Debug, Clone, Default)]
pub struct CheckedSpecDefinitions {
    definitions: BTreeMap<FnId, FnDecl>,
    bodyless_recommendations: BTreeMap<FnId, FnDecl>,
    signatures: BTreeMap<FnId, Signature>,
    opaque_nominals: BTreeMap<AdtId, usize>,
    architecture: Option<(Architecture, u32)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Signature {
    mode: Mode,
    kind: FnKind,
    type_parameters: usize,
    parameters: Vec<(Ty, Mode, bool)>,
    result: (Ty, Mode, bool),
    opaque: bool,
    prophetic: bool,
}

impl Signature {
    fn of(declaration: &FnDecl) -> Option<Self> {
        let parameters = declaration
            .params
            .iter()
            .map(|id| {
                let local = declaration.local(*id)?;
                Some((local.ty.clone(), local.mode, local.mutable))
            })
            .collect::<Option<Vec<_>>>()?;
        let result = declaration.local(declaration.ret)?;
        Some(Self {
            mode: declaration.mode,
            kind: declaration.kind,
            type_parameters: declaration.type_params.len(),
            parameters,
            result: (result.ty.clone(), result.mode, result.mutable),
            opaque: declaration.attrs.opaque,
            prophetic: declaration.attrs.prophetic,
        })
    }
}

fn error(function: Option<FnId>, span: SpanId, message: impl Into<String>) -> WfError {
    WfError {
        class: WfClass::Malformed,
        function,
        span,
        message: message.into(),
    }
}

fn scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int(_) | Ty::Unit)
}

fn walk(expression: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expression);
    expression.for_each_child(&mut |child| walk(child, visit));
}

fn recommendation_type(ty: &Ty, source: &VcCrate, nominals: &mut BTreeMap<AdtId, usize>) -> bool {
    match ty {
        Ty::Bool | Ty::Int(_) | Ty::Unit | Ty::Param(_) => true,
        Ty::Adt(owner, arguments) => {
            let Some(declaration) = source.adts.iter().find(|adt| adt.id == *owner) else {
                return false;
            };
            if declaration.kind != AdtKind::Opaque
                || declaration.type_params.len() != arguments.len()
            {
                return false;
            }
            nominals.insert(*owner, arguments.len());
            arguments
                .iter()
                .all(|argument| recommendation_type(argument, source, nominals))
        }
        _ => false,
    }
}

fn recommendation_expression(expression: &Expr) -> bool {
    match &expression.kind {
        ExprKind::Read(place) => place.projections.is_empty(),
        ExprKind::Lit(_)
        | ExprKind::IntegerConstant(_)
        | ExprKind::Unary { check: None, .. }
        | ExprKind::Binary { check: None, .. }
        | ExprKind::If { .. }
        | ExprKind::Let { .. }
        | ExprKind::Call { .. }
        | ExprKind::Cast { .. } => true,
        _ => false,
    }
}

impl CheckedSpecDefinitions {
    /// Check the complete semantic source before retaining the selected owners.
    ///
    /// `source` uses genuine source declarations with their own local tables;
    /// it is not the client's bodyless imported-signature crate. Producers must
    /// first remap item/type/span identities into the intended client namespace.
    /// The initial fragment excludes recursion, contracts, explicit inline
    /// bodies and non-scalar types. Recommendations are checked and retained,
    /// but never become assumptions or guards on the definition.
    pub fn from_crate(source: &VcCrate, owners: &[FnId]) -> Result<Self, Vec<WfError>> {
        Self::from_crate_with_bodyless_recommendations(source, owners, &[])
    }

    /// Retain checked recommendations of additional uninterpreted source
    /// declarations without retaining any defining body or equation for them.
    ///
    /// This checks semantic syntax and exact signature joins only. A native
    /// producer must separately authenticate the original ordered headers,
    /// modes, binders, nominal policy and current source/metadata ownership.
    /// Generic values remain abstract parameters or opaque nominals; field,
    /// reference, constructor and execution semantics are outside this slice.
    pub fn from_crate_with_bodyless_recommendations(
        source: &VcCrate,
        owners: &[FnId],
        recommendation_owners: &[FnId],
    ) -> Result<Self, Vec<WfError>> {
        let mut errors = crate::check_crate(source);
        if !errors.is_empty() {
            return Err(errors);
        }
        let selected: BTreeSet<_> = owners.iter().copied().collect();
        if selected.len() != owners.len() {
            errors.push(error(
                None,
                SpanId(0),
                "duplicate checked Spec definition owner",
            ));
        }
        let mut definitions = BTreeMap::new();
        let mut bodyless_recommendations = BTreeMap::new();
        let mut signatures = BTreeMap::new();
        let mut opaque_nominals = BTreeMap::new();
        let mut calls = BTreeMap::<FnId, BTreeSet<FnId>>::new();
        for owner in selected.iter().copied() {
            let Some(declaration) = source.fn_decl(owner) else {
                errors.push(error(
                    Some(owner),
                    SpanId(0),
                    "missing checked Spec definition owner",
                ));
                continue;
            };
            let Body::Spec(body) = &declaration.body else {
                errors.push(error(
                    Some(owner),
                    declaration.span,
                    "a checked Spec definition requires its source Spec body",
                ));
                continue;
            };
            if declaration.role != FnRole::Item
                || declaration.mode != Mode::Spec
                || declaration.kind != FnKind::Function
                || !declaration.type_params.is_empty()
                || declaration
                    .locals
                    .iter()
                    .any(|local| !scalar(&local.ty) || local.mode != Mode::Spec || local.mutable)
                || declaration.attrs.inline
                || declaration.attrs.opaque
                || declaration.attrs.external_body
                || declaration.attrs.exec_allows_no_decreases
                || declaration.attrs.is_decreases_by
                || declaration.attrs.is_trait_method_impl
                || declaration.attrs.instance.is_some()
                || !declaration.requires.is_empty()
                || !declaration.ensures.is_empty()
                || declaration.unwind.is_some()
                || !declaration.decreases.is_empty()
                || declaration.decreases_when.is_some()
                || declaration.decreases_by.is_some()
                || source.rec_group(owner).is_some()
            {
                errors.push(error(
                    Some(owner),
                    declaration.span,
                    "unsupported checked Spec definition shape",
                ));
                continue;
            }
            let mut callees = BTreeSet::new();
            walk(body, &mut |expression| {
                if !scalar(&expression.ty) || matches!(expression.kind, ExprKind::ProofInSpec(_)) {
                    errors.push(error(
                        Some(owner),
                        expression.span,
                        "a checked scalar Spec definition contains an unsupported expression",
                    ));
                }
                if let ExprKind::Call { callee, .. } = &expression.kind {
                    callees.insert(*callee);
                }
            });
            let body_callees = callees.clone();
            // Recommendations are ordinary checked source expressions. Their
            // dependencies still require a real matching native signature.
            for clause in &declaration.recommends {
                walk(&clause.expr, &mut |expression| {
                    if let ExprKind::Call { callee, .. } = &expression.kind {
                        callees.insert(*callee);
                    }
                });
            }
            for callee in &callees {
                let Some(target) = source.fn_decl(*callee) else {
                    // The strict whole-source check above normally owns this.
                    errors.push(error(
                        Some(owner),
                        declaration.span,
                        "a checked Spec dependency has no source signature",
                    ));
                    continue;
                };
                if body_callees.contains(callee)
                    && !matches!(target.body, Body::None)
                    && !selected.contains(callee)
                {
                    errors.push(error(
                        Some(owner),
                        declaration.span,
                        "a checked Spec definition omits a source-body dependency",
                    ));
                }
                if let Some(signature) = Signature::of(target) {
                    signatures.insert(*callee, signature);
                }
            }
            calls.insert(owner, body_callees);
            if let Some(signature) = Signature::of(declaration) {
                signatures.insert(owner, signature);
            }
            definitions.insert(owner, declaration.clone());
        }
        let recommendation_selected = recommendation_owners
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if recommendation_selected.len() != recommendation_owners.len()
            || !recommendation_selected.is_disjoint(&selected)
        {
            errors.push(error(
                None,
                SpanId(0),
                "duplicate checked recommendation owner",
            ));
        }
        for owner in recommendation_selected {
            let Some(declaration) = source.fn_decl(owner) else {
                errors.push(error(
                    Some(owner),
                    SpanId(0),
                    "missing checked recommendation owner",
                ));
                continue;
            };
            if declaration.role != FnRole::Item
                || declaration.mode != Mode::Spec
                || declaration.kind != FnKind::Function
                || !matches!(declaration.body, Body::None)
                || declaration.recommends.is_empty()
                || declaration.locals.iter().any(|local| {
                    local.mode != Mode::Spec
                        || local.mutable
                        || !recommendation_type(&local.ty, source, &mut opaque_nominals)
                })
                || declaration.attrs.inline
                || declaration.attrs.opaque
                || declaration.attrs.exec_allows_no_decreases
                || declaration.attrs.is_decreases_by
                || declaration.attrs.is_trait_method_impl
                || declaration.attrs.instance.is_some()
                || declaration.attrs.broadcast_triggers.is_some()
                || !declaration.requires.is_empty()
                || !declaration.ensures.is_empty()
                || declaration.unwind.is_some()
                || !declaration.decreases.is_empty()
                || declaration.decreases_when.is_some()
                || declaration.decreases_by.is_some()
                || source.rec_group(owner).is_some()
            {
                errors.push(error(
                    Some(owner),
                    declaration.span,
                    "unsupported bodyless recommendation shape",
                ));
                continue;
            }
            let mut callees = BTreeSet::from([owner]);
            for clause in &declaration.recommends {
                walk(&clause.expr, &mut |expression| {
                    if !recommendation_expression(expression)
                        || !recommendation_type(&expression.ty, source, &mut opaque_nominals)
                        || matches!(&expression.kind, ExprKind::Read(place) if place.local == declaration.ret)
                    {
                        errors.push(error(
                            Some(owner),
                            expression.span,
                            "unsupported bodyless recommendation expression",
                        ));
                    }
                    if let ExprKind::Call {
                        callee, type_args, ..
                    } = &expression.kind
                    {
                        if type_args
                            .iter()
                            .any(|ty| !recommendation_type(ty, source, &mut opaque_nominals))
                        {
                            errors.push(error(
                                Some(owner),
                                expression.span,
                                "unsupported bodyless recommendation type argument",
                            ));
                        }
                        callees.insert(*callee);
                    }
                });
            }
            for callee in callees {
                let Some(target) = source.fn_decl(callee) else {
                    errors.push(error(
                        Some(owner),
                        declaration.span,
                        "a checked recommendation dependency has no source signature",
                    ));
                    continue;
                };
                if target.mode != Mode::Spec
                    || target.locals.iter().any(|local| {
                        local.mode != Mode::Spec
                            || local.mutable
                            || !recommendation_type(&local.ty, source, &mut opaque_nominals)
                    })
                {
                    errors.push(error(
                        Some(owner),
                        declaration.span,
                        "unsupported bodyless recommendation dependency",
                    ));
                }
                if let Some(signature) = Signature::of(target) {
                    signatures.insert(callee, signature);
                }
            }
            bodyless_recommendations.insert(owner, declaration.clone());
        }
        // Strict WF checks declared groups; this additional walk excludes
        // uncovered cycles too, before any definition can become usable.
        for owner in definitions.keys().copied() {
            let mut pending = calls
                .get(&owner)
                .into_iter()
                .flatten()
                .copied()
                .collect::<Vec<_>>();
            let mut visited = BTreeSet::new();
            while let Some(callee) = pending.pop() {
                if callee == owner {
                    errors.push(error(
                        Some(owner),
                        definitions[&owner].span,
                        "recursive checked Spec definitions are not supported",
                    ));
                    break;
                }
                if visited.insert(callee) {
                    pending.extend(calls.get(&callee).into_iter().flatten().copied());
                }
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(Self {
            architecture: (!signatures.is_empty())
                .then_some((source.architecture, source.pointer_width)),
            definitions,
            bodyless_recommendations,
            signatures,
            opaque_nominals,
        })
    }

    /// Retain finite inline forwarders separately from general definition
    /// admission. Each actual body must call one uninterpreted Spec function
    /// with precisely its original parameters and identity type arguments.
    ///
    /// This checks semantic bodies, never their native origin. Native callers
    /// must separately retain the exact original body/header, binders, nominal
    /// policy, source correspondence and current metadata signature joins.
    pub fn from_crate_with_forwarders(
        source: &VcCrate,
        owners: &[FnId],
        recommendation_owners: &[FnId],
        forwarder_owners: &[FnId],
    ) -> Result<Self, Vec<WfError>> {
        let mut checked =
            Self::from_crate_with_bodyless_recommendations(source, owners, recommendation_owners)?;
        let selected = forwarder_owners.iter().copied().collect::<BTreeSet<_>>();
        let mut errors = Vec::new();
        if selected.len() != forwarder_owners.len()
            || selected
                .iter()
                .any(|owner| owners.contains(owner) || recommendation_owners.contains(owner))
        {
            errors.push(error(None, SpanId(0), "duplicate checked forwarder owner"));
        }
        for owner in selected {
            let Some(declaration) = source.fn_decl(owner) else {
                errors.push(error(
                    Some(owner),
                    SpanId(0),
                    "missing checked forwarder owner",
                ));
                continue;
            };
            let Body::Spec(body) = &declaration.body else {
                errors.push(error(
                    Some(owner),
                    declaration.span,
                    "a checked forwarder requires its actual Spec body",
                ));
                continue;
            };
            let ExprKind::Call {
                callee,
                type_args,
                args,
            } = &body.kind
            else {
                errors.push(error(
                    Some(owner),
                    body.span,
                    "a checked forwarder body must be one direct Spec call",
                ));
                continue;
            };
            let Some(target) = source.fn_decl(*callee) else {
                errors.push(error(
                    Some(owner),
                    body.span,
                    "a checked forwarder target has no source declaration",
                ));
                continue;
            };
            let parameters = (0..declaration.type_params.len())
                .map(|index| u32::try_from(index).map(Ty::Param))
                .collect::<Result<Vec<_>, _>>();
            let Ok(parameters) = parameters else {
                errors.push(error(
                    Some(owner),
                    declaration.span,
                    "checked forwarder type parameter index overflow",
                ));
                continue;
            };
            if declaration.role != FnRole::Item
                || declaration.mode != Mode::Spec
                || declaration.kind != FnKind::Function
                || !declaration.attrs.inline
                || declaration.attrs.opaque
                || declaration.attrs.external_body
                || declaration.attrs.prophetic
                || declaration.attrs.exec_allows_no_decreases
                || declaration.attrs.is_decreases_by
                || declaration.attrs.is_trait_method_impl
                || declaration.attrs.instance.is_some()
                || declaration.attrs.broadcast_triggers.is_some()
                || !declaration.requires.is_empty()
                || !declaration.ensures.is_empty()
                || declaration.unwind.is_some()
                || !declaration.decreases.is_empty()
                || declaration.decreases_when.is_some()
                || declaration.decreases_by.is_some()
                || source.rec_group(owner).is_some()
                || declaration.locals.len() != declaration.params.len() + 1
                || declaration.locals.iter().any(|local| local.mode != Mode::Spec || local.mutable
                    || local.prophecy != crate::DeclProphecy::Default
                    || !recommendation_type(&local.ty, source, &mut checked.opaque_nominals))
                || target.role != FnRole::Item
                || target.mode != Mode::Spec
                || target.kind != FnKind::Function
                || !matches!(target.body, Body::None)
                || target.attrs.inline
                || target.attrs.prophetic
                || target.type_params.len() != declaration.type_params.len()
                || target.params.len() != declaration.params.len()
                || type_args.as_slice() != parameters.as_slice()
                || args.len() != declaration.params.len()
                || args.iter().zip(&declaration.params).any(|(argument, parameter)| {
                    !matches!(&argument.kind, ExprKind::Read(place) if place.local == *parameter && place.projections.is_empty())
                })
                || target.locals.iter().any(|local| local.mode != Mode::Spec || local.mutable
                    || local.prophecy != crate::DeclProphecy::Default
                    || !recommendation_type(&local.ty, source, &mut checked.opaque_nominals))
            {
                errors.push(error(Some(owner), declaration.span, "unsupported checked forwarder shape"));
                continue;
            }
            let mut callees = BTreeSet::from([owner, *callee]);
            for clause in &declaration.recommends {
                walk(&clause.expr, &mut |expression| {
                    if !recommendation_expression(expression)
                        || !recommendation_type(
                            &expression.ty,
                            source,
                            &mut checked.opaque_nominals,
                        )
                        || matches!(&expression.kind, ExprKind::Read(place) if place.local == declaration.ret)
                    {
                        errors.push(error(
                            Some(owner),
                            expression.span,
                            "unsupported checked forwarder recommendation",
                        ));
                    }
                    if let ExprKind::Call {
                        callee, type_args, ..
                    } = &expression.kind
                    {
                        if type_args.iter().any(|ty| {
                            !recommendation_type(ty, source, &mut checked.opaque_nominals)
                        }) {
                            errors.push(error(
                                Some(owner),
                                expression.span,
                                "unsupported checked forwarder recommendation type argument",
                            ));
                        }
                        callees.insert(*callee);
                    }
                });
            }
            for callee in callees {
                let Some(target) = source.fn_decl(callee) else {
                    errors.push(error(
                        Some(owner),
                        declaration.span,
                        "a checked forwarder dependency has no source signature",
                    ));
                    continue;
                };
                if target.mode != Mode::Spec
                    || target.locals.iter().any(|local| {
                        local.mode != Mode::Spec
                            || local.mutable
                            || !recommendation_type(&local.ty, source, &mut checked.opaque_nominals)
                    })
                {
                    errors.push(error(
                        Some(owner),
                        declaration.span,
                        "unsupported checked forwarder dependency",
                    ));
                }
                if let Some(signature) = Signature::of(target) {
                    checked.signatures.insert(callee, signature);
                }
            }
            checked.definitions.insert(owner, declaration.clone());
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        if !checked.signatures.is_empty() {
            checked.architecture = Some((source.architecture, source.pointer_width));
        }
        Ok(checked)
    }

    /// The retained definitions, with their complete independent local scopes.
    pub fn definitions(&self) -> impl Iterator<Item = &FnDecl> {
        self.definitions.values()
    }

    pub(crate) fn recommendation_declarations(&self) -> impl Iterator<Item = &FnDecl> {
        self.definitions
            .values()
            .chain(self.bodyless_recommendations.values())
            .filter(|declaration| !declaration.recommends.is_empty())
    }

    /// Number of retained defining bodies.
    #[must_use]
    pub fn len(&self) -> usize {
        self.definitions.len()
    }

    /// Whether this collection supplies no defining equations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    /// Strictly join every retained owner and dependency to the current client.
    /// Names and local indices are intentionally not signature identities.
    pub fn validate_for_crate(&self, client: &VcCrate) -> Result<(), Vec<WfError>> {
        if self.signatures.is_empty() {
            return Ok(());
        }
        let mut errors = crate::check_crate(client);
        for (owner, arity) in &self.opaque_nominals {
            if client
                .adts
                .iter()
                .find(|adt| adt.id == *owner)
                .is_none_or(|adt| adt.kind != AdtKind::Opaque || adt.type_params.len() != *arity)
            {
                errors.push(error(
                    None,
                    SpanId(0),
                    "a checked recommendation opaque nominal differs from its client declaration",
                ));
            }
        }
        if self.architecture != Some((client.architecture, client.pointer_width)) {
            errors.push(error(
                None,
                SpanId(0),
                "checked Spec definition architecture changed",
            ));
        }
        for (owner, signature) in &self.signatures {
            let Some(declaration) = client.fn_decl(*owner) else {
                errors.push(error(
                    Some(*owner),
                    SpanId(0),
                    "a checked Spec definition or dependency has no client signature",
                ));
                continue;
            };
            if declaration.role != FnRole::Imported
                || declaration.imported_problem().is_some()
                || Signature::of(declaration).as_ref() != Some(signature)
            {
                errors.push(error(Some(*owner), declaration.span, "a checked Spec definition or dependency differs from its bodyless client signature"));
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub(crate) fn get(&self, owner: FnId) -> Option<&FnDecl> {
        self.definitions.get(&owner)
    }
}
