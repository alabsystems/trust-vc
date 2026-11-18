//! Checked native `when_used_as_spec` declaration and call selections.
//!
//! The attribute requests a different callee in ghost code. It neither proves
//! an equation about the executable body nor changes that body's native mode.
//! Names locate a sibling candidate; current native identities and complete
//! declaration/signature checks establish the mapping before any mode walk.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

extern crate rustc_abi;

use std::collections::HashMap;

use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt, TypeckResults};
use rustc_span::Span;
use trust_vc_vcir::{FnKind, Mode};

use super::{attrs, declaration_modes, is_external, Cx, Refusal, UserError};
use crate::messages::Phase;

mod rejections;

pub(super) fn external_directive_ignored(cx: &Cx<'_>, source: LocalDefId) -> bool {
    rejections::external_directive_ignored(cx, source)
}

pub(super) fn ignored_external_call<'tcx>(
    cx: &Cx<'tcx>,
    caller: LocalDefId,
    body_owner: LocalDefId,
    typeck: &'tcx TypeckResults<'tcx>,
    expression: &'tcx hir::Expr<'tcx>,
    callee: DefId,
) -> Option<UserError> {
    rejections::ignored_external_call(cx, caller, body_owner, typeck, expression, callee)
}

#[derive(Default)]
pub(super) struct Registry<'tcx> {
    pairs: HashMap<DefId, Pair<'tcx>>,
    // Only first-phase declaration errors issued by this current reader.
    // These are rejection observations, never mode or ownership evidence.
    rejected_sources: HashMap<LocalDefId, UserError>,
}

struct Pair<'tcx> {
    source: LocalDefId,
    native_source: LocalDefId,
    target: LocalDefId,
    source_attrs: Vec<(attrs::VerusAttr, Span)>,
    target_attrs: Vec<(attrs::VerusAttr, Span)>,
    source_body: &'tcx hir::Body<'tcx>,
    target_body: &'tcx hir::Body<'tcx>,
    source_typeck: &'tcx TypeckResults<'tcx>,
    target_typeck: &'tcx TypeckResults<'tcx>,
}

/// A call observation retained only by the completed original mode walk.
#[derive(Clone)]
pub(super) struct Call<'tcx> {
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    expression: &'tcx hir::Expr<'tcx>,
    pub(super) original: DefId,
    pub(super) original_args: ty::GenericArgs<'tcx>,
    pub(super) declaration: LocalDefId,
    constant: Option<super::constants::Use<'tcx>>,
    pub(super) target: LocalDefId,
    pub(super) args: ty::GenericArgs<'tcx>,
}

impl std::fmt::Debug for Call<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AutospecCall")
            .field("caller", &self.caller)
            .field("expression", &self.expression.hir_id)
            .field("original", &self.original)
            .field("target", &self.target)
            .finish_non_exhaustive()
    }
}

impl<'tcx> Call<'tcx> {
    pub(super) fn same_selection(&self, other: &Self) -> bool {
        std::ptr::eq(*self.tcx, *other.tcx)
            && self.caller == other.caller
            && std::ptr::eq(self.body, other.body)
            && std::ptr::eq(self.typeck, other.typeck)
            && std::ptr::eq(self.expression, other.expression)
            && self.original == other.original
            && self.original_args == other.original_args
            && self.declaration == other.declaration
            && match (&self.constant, &other.constant) {
                (Some(left), Some(right)) => left.same_selection(right),
                (None, None) => true,
                _ => false,
            }
            && self.target == other.target
            && self.args == other.args
    }

    /// Both packets must describe the same original native occurrence. An
    /// ordinary autospec call has no constant role; only a current ConstFunction
    /// source may join the two independently selected observations.
    pub(super) fn matches_constant(&self, selected: Option<&super::constants::Use<'tcx>>) -> bool {
        match (&self.constant, selected) {
            (Some(expected), Some(actual)) => {
                actual.kind == FnKind::ConstFunction
                    && actual.original == self.original
                    && actual.declaration == self.declaration
                    && actual.arguments == self.original_args
                    && expected.same_selection(actual)
            }
            (None, None) => true,
            _ => false,
        }
    }
}

fn ready(tcx: TyCtxt<'_>, owner: LocalDefId) -> bool {
    tcx.dcx().has_errors().is_none()
        && declaration_modes::original_body_available(tcx, owner)
        && !super::function_identity_observer::body_is_quarantined(tcx.sess, owner)
        && !is_external(tcx, owner)
}

/// Native function shape is insufficient: constants have function-shaped
/// unerased proxies whose canonical Verus identity is their REAL declaration.
/// The ordinary-function slice must not expose a proxy spelling as a second
/// logical declaration. An ordinary function with that spelling remains valid.
fn ordinary_function(cx: &Cx<'_>, definition: LocalDefId) -> bool {
    matches!(cx.tcx.def_kind(definition), DefKind::Fn | DefKind::AssocFn)
        && cx.constants.kind(definition) == FnKind::Function
        && cx.constants.real(definition).is_none()
        && cx.constants.proxy(definition).is_none()
}

/// A40 gives a const function's logical declaration its canonical real path.
/// The sealed native pair supplies that identity; its spelling grants nothing.
/// Constants/statics and generated proxies remain ineligible Spec targets.
fn source_function(cx: &Cx<'_>, declaration: LocalDefId) -> Option<LocalDefId> {
    if ordinary_function(cx, declaration) {
        return Some(declaration);
    }
    let real = cx.constants.real(declaration)?;
    (cx.constants.kind(declaration) == FnKind::ConstFunction
        && cx.constants.proxy(real) == Some(declaration)
        && cx.constants.current_pair(cx.tcx, declaration))
    .then_some(real)
}

fn error(tcx: TyCtxt<'_>, source: LocalDefId, message: impl Into<String>) -> UserError {
    let mut problem = UserError::new(Phase::WellFormed, tcx.def_span(source), message);
    problem.function = Some(source);
    problem
}

impl<'tcx> Registry<'tcx> {
    /// Close just a declaration A40 rejects before reading its body. Recheck
    /// its current native source; a stale/unknown observation closes nothing.
    pub(super) fn rejected_source(&self, cx: &Cx<'tcx>, source: LocalDefId) -> Option<&UserError> {
        let expected = self.rejected_sources.get(&source)?;
        let current = rejections::mutable_parameter_error(cx, source)?;
        (expected.function == current.function
            && expected.phase == current.phase
            && expected.span == current.span
            && expected.message == current.message)
            .then_some(expected)
    }

    /// Whole-declaration validation precedes Modes, including unused sources.
    /// Foreign/trait/constant redirection is not inferred from this registry.
    pub(super) fn collect(cx: &Cx<'tcx>, ordinary: bool) -> (Self, Vec<UserError>, Vec<Refusal>) {
        let tcx = cx.tcx;
        let mut result = Self::default();
        let mut errors = Vec::new();
        let mut refusals = Vec::new();
        let mut definitions = cx
            .fns
            .keys()
            .filter_map(|def| def.as_local())
            .collect::<Vec<_>>();
        definitions.sort_by_key(|def| tcx.def_span(*def).lo());
        for source in &definitions {
            let source = *source;
            let source_attrs = cx.declaration_attrs(source);
            let Some((name, span)) = &source_attrs.autospec else {
                continue;
            };
            let refuse = |reason| Refusal::new("autospec", reason, *span);
            if ordinary {
                if let Some(problem) = rejections::mutable_parameter_error(cx, source) {
                    result.rejected_sources.insert(source, problem);
                    continue;
                }
                if rejections::missing_trait_sibling(cx, source, name) {
                    errors.push(error(
                        tcx,
                        source,
                        format!("cannot find function referred to in when_used_as_spec: {name}"),
                    ));
                    continue;
                }
            }
            if !ordinary || !ready(tcx, source) || !source_attrs.verus_macro {
                refusals.push(refuse(
                    "redirection needs an original local Verus function in the ordinary reader",
                ));
                continue;
            }
            if source_attrs
                .unsupported
                .iter()
                .any(|(name, _)| name == "verifier::allow_in_spec")
            {
                // Declaration validation already reported the contradictory
                // directives, including on unused functions. Do not issue a
                // redirection pair or a duplicate error.
                continue;
            }
            let parent = tcx.local_parent(source);
            let native_source = source_function(cx, source);
            if tcx.trait_of_assoc(source.to_def_id()).is_some()
                || native_source.is_none()
                || !matches!(
                    tcx.def_kind(parent),
                    DefKind::Mod | DefKind::Impl { of_trait: false }
                )
            {
                refusals.push(refuse("trait, default-method and constant redirection need their own complete native selection"));
                continue;
            }
            let Some(native_source) = native_source else {
                continue;
            };
            if !source_attrs.unsupported.is_empty() {
                refusals.push(refuse("the source has unrepresented declaration semantics"));
                continue;
            }
            // A40 replaces the last canonical path segment. No reexport,
            // diagnostic rename or source-level shadowing changes this owner.
            let targets = definitions
                .iter()
                .copied()
                .filter(|target| {
                    tcx.local_parent(*target) == parent
                        && ordinary_function(cx, *target)
                        && tcx.item_name(target.to_def_id()).as_str() == name.as_str()
                })
                .collect::<Vec<_>>();
            let [target] = targets.as_slice() else {
                errors.push(error(
                    tcx,
                    source,
                    format!("cannot find function referred to in when_used_as_spec: {name}"),
                ));
                continue;
            };
            let target = *target;
            let target_attrs = cx.declaration_attrs(target);
            if !ready(tcx, target)
                || !target_attrs.verus_macro
                || !target_attrs.unsupported.is_empty()
            {
                refusals.push(refuse(
                    "the specification target lacks its current original native declaration",
                ));
                continue;
            }
            if cx.fns[&source.to_def_id()].mode != Mode::Exec
                || cx.fns[&target.to_def_id()].mode != Mode::Spec
            {
                errors.push(error(
                    tcx,
                    source,
                    "when_used_as_spec must point from an exec function to a spec function",
                ));
                continue;
            }
            let wide = tcx.visibility(target);
            let visible = match tcx.visibility(source) {
                ty::Visibility::Public => wide.is_public(),
                ty::Visibility::Restricted(module) => wide.is_accessible_from(module, tcx),
            };
            if !visible {
                errors.push(error(
                    tcx,
                    source,
                    "when_used_as_spec refers to function which is more private",
                ));
                continue;
            }
            match signatures(cx, source, target) {
                Ok(()) => {}
                Err(SignatureProblem::Error(message)) => {
                    errors.push(error(tcx, source, message));
                    continue;
                }
                Err(SignatureProblem::Unknown(message)) => {
                    refusals.push(refuse(message));
                    continue;
                }
            }
            let source_body = tcx.hir_body_owned_by(source);
            let target_body = tcx.hir_body_owned_by(target);
            let source_typeck = tcx.typeck(source);
            let target_typeck = tcx.typeck(target);
            if source_typeck.tainted_by_errors.is_some()
                || target_typeck.tainted_by_errors.is_some()
                || !ready(tcx, source)
                || !ready(tcx, target)
            {
                refusals.push(refuse(
                    "native diagnostics or quarantine revoked the declaration pair",
                ));
                continue;
            }
            result.pairs.insert(
                native_source.to_def_id(),
                Pair {
                    source,
                    native_source,
                    target,
                    source_attrs: attrs::verus_attrs(
                        tcx.hir_attrs(tcx.local_def_id_to_hir_id(source)),
                    ),
                    target_attrs: attrs::verus_attrs(
                        tcx.hir_attrs(tcx.local_def_id_to_hir_id(target)),
                    ),
                    source_body,
                    target_body,
                    source_typeck,
                    target_typeck,
                },
            );
        }
        (result, errors, refusals)
    }

    /// The caller decides the real ghost context. This method never changes
    /// an executable call merely because its declaration has an attribute.
    pub(super) fn call(
        &self,
        cx: &Cx<'tcx>,
        caller: LocalDefId,
        typeck: &'tcx TypeckResults<'tcx>,
        expression: &'tcx hir::Expr<'tcx>,
    ) -> Result<Option<Call<'tcx>>, Refusal> {
        if self.pairs.is_empty() {
            return Ok(None);
        }
        let tcx = cx.tcx;
        let refuse = |reason| Refusal::new("autospec-call", reason, expression.span);
        if !ready(tcx, caller)
            || !std::ptr::eq(typeck, tcx.typeck(caller))
            || expression.hir_id.owner.def_id != caller
            || !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
        {
            return Err(refuse(
                "the call lacks its original clean caller, native HIR or type-check results",
            ));
        }
        let (original, args) = match expression.kind {
            hir::ExprKind::MethodCall(..) => {
                let Some(def) = typeck.type_dependent_def_id(expression.hir_id) else {
                    return Ok(None);
                };
                (def, typeck.node_args(expression.hir_id))
            }
            hir::ExprKind::Call(function, _) => {
                let hir::ExprKind::Path(ref path) = function.kind else {
                    return Ok(None);
                };
                let Res::Def(DefKind::Fn | DefKind::AssocFn, def) =
                    typeck.qpath_res(path, function.hir_id)
                else {
                    return Ok(None);
                };
                (def, typeck.node_args(function.hir_id))
            }
            _ => return Ok(None),
        };
        let Some(pair) = self.pairs.get(&original) else {
            return Ok(None);
        };
        if !pair.current(cx) {
            return Err(refuse("the original declaration pair is no longer current"));
        }
        let constant = cx
            .constants
            .select(tcx, caller, typeck, expression)
            .map_err(|_| refuse("the source lost its original constant-function selection"))?;
        match &constant {
            Some(selected)
                if pair.source != pair.native_source
                    && selected.kind == FnKind::ConstFunction
                    && selected.original == original
                    && selected.declaration == pair.source
                    && selected.arguments == args => {}
            None if pair.source == pair.native_source => {}
            _ => return Err(refuse("the redirection and native constant-function roles differ")),
        }
        check_call_arguments(cx, original, args, caller, expression.span)?;
        if pair.source != pair.native_source {
            check_call_arguments(cx, pair.source.to_def_id(), args, caller, expression.span)?;
        }
        check_call_arguments(cx, pair.target.to_def_id(), args, caller, expression.span)?;
        if !pair.current(cx) || !ready(tcx, caller) {
            return Err(refuse(
                "native diagnostics revoked this call's selected declaration pair",
            ));
        }
        Ok(Some(Call {
            tcx,
            caller,
            body: tcx.hir_body_owned_by(caller),
            typeck,
            expression,
            original,
            original_args: args,
            declaration: pair.source,
            constant,
            target: pair.target,
            args,
        }))
    }
}

impl<'tcx> Pair<'tcx> {
    fn current(&self, cx: &Cx<'tcx>) -> bool {
        let tcx = cx.tcx;
        ready(tcx, self.source)
            && ready(tcx, self.target)
            && source_function(cx, self.source) == Some(self.native_source)
            && ordinary_function(cx, self.target)
            && attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(self.source)))
                == self.source_attrs
            && attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(self.target)))
                == self.target_attrs
            && cx
                .fns
                .get(&self.source.to_def_id())
                .is_some_and(|info| info.mode == Mode::Exec)
            && cx
                .fns
                .get(&self.target.to_def_id())
                .is_some_and(|info| info.mode == Mode::Spec)
            && std::ptr::eq(tcx.hir_body_owned_by(self.source), self.source_body)
            && std::ptr::eq(tcx.hir_body_owned_by(self.target), self.target_body)
            && std::ptr::eq(tcx.typeck(self.source), self.source_typeck)
            && std::ptr::eq(tcx.typeck(self.target), self.target_typeck)
            && self.source_typeck.tainted_by_errors.is_none()
            && self.target_typeck.tainted_by_errors.is_none()
            && tcx.dcx().has_errors().is_none()
    }
}

enum SignatureProblem {
    Error(&'static str),
    Unknown(&'static str),
}

fn signatures(cx: &Cx<'_>, source: LocalDefId, target: LocalDefId) -> Result<(), SignatureProblem> {
    use SignatureProblem::{Error, Unknown};
    let tcx = cx.tcx;
    let left_generics = tcx.generics_of(source);
    let right_generics = tcx.generics_of(target);
    let type_parameters = |generics: &ty::Generics| {
        generics
            .own_params
            .iter()
            .filter(|parameter| !matches!(parameter.kind, ty::GenericParamDefKind::Lifetime))
            .count()
    };
    if type_parameters(left_generics) != type_parameters(right_generics) {
        return Err(Error(
            "when_used_as_spec function should have the same type parameters",
        ));
    }
    if left_generics.parent != right_generics.parent
        || left_generics.count() != right_generics.count()
        || left_generics.own_params.len() != right_generics.own_params.len()
    {
        return Err(Unknown(
            "the native lifetime/generic tables need a distinct complete redirection mapping",
        ));
    }
    for (left, right) in left_generics
        .own_params
        .iter()
        .zip(&right_generics.own_params)
    {
        match (&left.kind, &right.kind) {
            (ty::GenericParamDefKind::Lifetime, ty::GenericParamDefKind::Lifetime) => {}
            (
                ty::GenericParamDefKind::Type {
                    has_default: a,
                    synthetic: b,
                },
                ty::GenericParamDefKind::Type {
                    has_default: c,
                    synthetic: d,
                },
            ) if a == c && b == d => {
                // Explicit pinned A40 WF rule: typ_params are user identifiers
                // and check_functions_match compares that list exactly.
                if left.name != right.name {
                    return Err(Error(
                        "when_used_as_spec function should have the same type bounds",
                    ));
                }
            }
            (ty::GenericParamDefKind::Const { .. }, _)
            | (_, ty::GenericParamDefKind::Const { .. }) => {
                return Err(Unknown(
                    "const-generic autospec declarations are not represented",
                ))
            }
            _ => {
                return Err(Error(
                    "when_used_as_spec function should have the same type parameters",
                ))
            }
        }
    }
    let args = ty::GenericArgs::identity_for_item(tcx, source.to_def_id());
    if !tcx.check_args_compatible(target.to_def_id(), args) {
        return Err(Unknown(
            "the target has no compatible native generic argument table",
        ));
    }
    // Anonymization preserves bound-variable/region relationships. Erasing
    // regions here would wrongly equate independent and tied references.
    let left = tcx.anonymize_bound_vars(
        tcx.fn_sig(source)
            .instantiate(tcx, args)
            .skip_normalization(),
    );
    let right = tcx.anonymize_bound_vars(
        tcx.fn_sig(target)
            .instantiate(tcx, args)
            .skip_normalization(),
    );
    if left.skip_binder().safety().is_unsafe()
        || right.skip_binder().safety().is_unsafe()
        || left.skip_binder().abi() != rustc_abi::ExternAbi::Rust
        || right.skip_binder().abi() != rustc_abi::ExternAbi::Rust
        || left.skip_binder().c_variadic()
        || right.skip_binder().c_variadic()
    {
        return Err(Unknown(
            "unsafe, foreign-ABI or variadic redirection is unsupported",
        ));
    }
    let parameters = args
        .types()
        .enumerate()
        .filter_map(|(index, value)| {
            if let ty::Param(parameter) = value.kind() {
                u32::try_from(index)
                    .ok()
                    .map(|index| (parameter.index, index))
            } else {
                None
            }
        })
        .collect::<HashMap<_, _>>();
    let convert = |value| {
        cx.vc_ty_with(value, &|parameter| {
            parameters.get(&parameter.index).copied()
        })
    };
    let left_inputs = left
        .skip_binder()
        .inputs()
        .iter()
        .map(|value| convert(*value))
        .collect::<Option<Vec<_>>>()
        .ok_or(Unknown(
            "an autospec parameter has no complete represented native type",
        ))?;
    let right_inputs = right
        .skip_binder()
        .inputs()
        .iter()
        .map(|value| convert(*value))
        .collect::<Option<Vec<_>>>()
        .ok_or(Unknown(
            "an autospec target parameter has no complete represented native type",
        ))?;
    if left_inputs != right_inputs {
        return Err(Error(
            "when_used_as_spec function should have the same parameters",
        ));
    }
    let left_output = convert(left.skip_binder().output()).ok_or(Unknown(
        "the autospec result has no complete represented native type",
    ))?;
    let right_output = convert(right.skip_binder().output()).ok_or(Unknown(
        "the autospec target result has no complete represented native type",
    ))?;
    if left_output != right_output {
        return Err(Error(
            "when_used_as_spec function should have the same return types",
        ));
    }
    if left != right {
        return Err(Unknown(
            "the native autospec signature changes its binder or region relationships",
        ));
    }
    if left
        .skip_binder()
        .inputs()
        .iter()
        .any(|ty| matches!(ty.kind(), ty::Ref(_, _, mutability) if mutability.is_mut()))
    {
        return Err(Unknown(
            "when_used_as_spec with a mutable-reference parameter is unsupported",
        ));
    }
    let left = tcx.clauses_of(source).instantiate(tcx, args);
    let right = tcx.clauses_of(target).instantiate(tcx, args);
    if left.clauses.len() != right.clauses.len()
        || left.clauses.iter().zip(&right.clauses).any(|(a, b)| {
            tcx.anonymize_bound_vars(a.skip_normalization().kind())
                != tcx.anonymize_bound_vars(b.skip_normalization().kind())
        })
    {
        // A40's generic-bound comparison is region-insensitive. Never report
        // a native region-only difference as its type-bound error, and never
        // erase the difference to admit the pair. Regionless trait clauses
        // retain exactly the declaration/type-argument identities A40 compares.
        let regionless_trait = |clause: &ty::Unnormalized<'_, ty::Clause<'_>>| {
            let ty::ClauseKind::Trait(predicate) = clause.skip_normalization().kind().skip_binder()
            else {
                return false;
            };
            predicate
                .trait_ref
                .args
                .iter()
                .all(|argument| match argument.kind() {
                    ty::GenericArgKind::Type(value) => value.walk().all(|part| {
                        !matches!(part.kind(), ty::GenericArgKind::Lifetime(_))
                            && !part
                                .as_type()
                                .is_some_and(|value| matches!(value.kind(), ty::Ref(..)))
                    }),
                    _ => false,
                })
        };
        if left
            .clauses
            .iter()
            .chain(&right.clauses)
            .all(regionless_trait)
        {
            return Err(Error(
                "when_used_as_spec function should have the same type bounds",
            ));
        }
        return Err(Unknown("the native autospec predicates differ outside the represented regionless trait comparison"));
    }
    Ok(())
}

/// Retain the original native call obligations even when its logical target
/// changes. Called again at the reader's concrete instance arguments.
pub(super) fn check_call_arguments<'tcx>(
    cx: &Cx<'tcx>,
    definition: DefId,
    args: ty::GenericArgs<'tcx>,
    caller: LocalDefId,
    span: Span,
) -> Result<(), Refusal> {
    let refuse = |reason| Refusal::new("autospec-call", reason, span);
    if args.has_infer()
        || args.has_placeholders()
        || args.has_opaque_types()
        || args.has_escaping_bound_vars()
        || args.references_error()
        || args.iter().any(|argument| argument.as_const().is_some())
        || !cx.tcx.check_args_compatible(definition, args)
    {
        return Err(refuse(
            "the original native call arguments are unsupported or incompatible",
        ));
    }
    for argument in args.iter() {
        if cx
            .verus_arg_problem(argument, caller.to_def_id())?
            .is_some()
        {
            return Err(refuse(
                "an original native type argument is outside the represented Verus fragment",
            ));
        }
    }
    if cx
        .verus_bounds_problem(definition, args, caller.to_def_id())?
        .is_some()
    {
        return Err(refuse(
            "the original native call bounds are not represented",
        ));
    }
    for argument in args.types() {
        if cx.verus_wf_problem(argument, caller.to_def_id())?.is_some() {
            return Err(refuse(
                "the original native call argument is not well formed",
            ));
        }
    }
    if !ready(cx.tcx, caller) {
        return Err(refuse(
            "native diagnostics revoked the caller after argument validation",
        ));
    }
    Ok(())
}
