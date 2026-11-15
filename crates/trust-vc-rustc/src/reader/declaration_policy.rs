//! Native generic clauses and authored nominal parameter policy.
//!
//! These sealed facts describe this declaration in this compiler context.
//! They do not authenticate macro/build provenance, prove a datatype's private
//! representation positive or well founded, or grant import/body authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::{self as hir, OwnerNode};
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json, Value};
use trust_vc_vcir::Mode;

use crate::declaration_alignment::NativeKey;

mod attributes;
pub(super) mod local_directives;
use attributes::{Context, Directives};

#[cfg(test)]
mod tests;

const MAX_SCOPES: usize = 64;
const MAX_PARAMETERS: usize = 256;
const MAX_CLAUSES: usize = 1_024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SizedTrait {
    Sized,
    MetaSized,
    PointeeSized,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Recursion {
    Reject,
    RejectInGround,
    Accept,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RecursionOrigin {
    ItemAttribute,
    ParameterAttribute,
    VerusDefault,
}

/// Complete native flattened index, including the scope that introduced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Parameter {
    pub(super) definition: NativeKey,
    pub(super) scope: NativeKey,
    pub(super) index: u32,
    pub(super) has_default: bool,
}

/// One actual positive native clause. The three sizedness traits are distinct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SizedClause {
    pub(super) scope: NativeKey,
    pub(super) parameter: u32,
    pub(super) trait_definition: NativeKey,
    pub(super) kind: SizedTrait,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ParameterRecursion {
    pub(super) parameter: u32,
    pub(super) policy: Recursion,
    pub(super) origin: RecursionOrigin,
}

/// No representation is exported. A true Sized result comes from the native
/// query under the declaration's genuine environment, never empty variants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Nominal {
    mode: Mode,
    known_sized: bool,
    external_body: bool,
    ext_equal_declared: bool,
    recursion: Vec<ParameterRecursion>,
}

impl Nominal {
    pub(super) fn mode(&self) -> Mode {
        self.mode
    }
    pub(super) fn known_sized(&self) -> bool {
        self.known_sized
    }
    pub(super) fn external_body(&self) -> bool {
        self.external_body
    }
    pub(super) fn ext_equal_declared(&self) -> bool {
        self.ext_equal_declared
    }
    pub(super) fn recursion(&self) -> &[ParameterRecursion] {
        &self.recursion
    }
}

/// Owned, sealed output of the native check. A staging callback may retain
/// it after the TyCtxt ends, then bind its native key to the actual artifact.
/// File hashes alone cannot construct this value or authenticate that build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct OwnedPolicy {
    owner: NativeKey,
    parameters: Vec<Parameter>,
    clauses: Vec<SizedClause>,
    nominal: Option<Nominal>,
}

impl OwnedPolicy {
    pub(super) fn owner(&self) -> NativeKey {
        self.owner
    }
    pub(super) fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }
    pub(super) fn clauses(&self) -> &[SizedClause] {
        &self.clauses
    }
    pub(super) fn nominal(&self) -> Option<&Nominal> {
        self.nominal.as_ref()
    }
}

pub(super) struct CheckedPolicy<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    facts: Result<OwnedPolicy, String>,
}

impl<'tcx> CheckedPolicy<'tcx> {
    pub(super) fn for_owner(&self, tcx: TyCtxt<'tcx>, owner: DefId) -> Option<&OwnedPolicy> {
        if self.owner != owner
            || !std::ptr::eq(*self.tcx, *tcx)
            || !original_owner_available(tcx, owner)
            || tcx.dcx().has_errors().is_some()
        {
            return None;
        }
        self.facts.as_ref().ok()
    }

    pub(super) fn owned_for(&self, tcx: TyCtxt<'tcx>, owner: DefId) -> Option<OwnedPolicy> {
        self.for_owner(tcx, owner).cloned()
    }

    pub(super) fn observation(&self) -> Value {
        let Some(facts) = self.for_owner(self.tcx, self.owner) else {
            return json!({"state": "Unknown", "reason": self.facts.as_ref().err()
                .map(String::as_str).unwrap_or("native owner/context is no longer established"),
                "import_authorized": false});
        };
        json!({
            "state": "CheckedNativeGenericPolicy",
            "owner": key_json(facts.owner),
            "parameters": facts.parameters.iter().map(|parameter| json!({
                "definition": key_json(parameter.definition), "scope": key_json(parameter.scope),
                "native_index": parameter.index, "has_default": parameter.has_default,
            })).collect::<Vec<_>>(),
            "clauses": facts.clauses.iter().map(|clause| json!({
                "scope": key_json(clause.scope), "native_parameter_index": clause.parameter,
                "trait_definition": key_json(clause.trait_definition), "kind": format!("{:?}", clause.kind),
            })).collect::<Vec<_>>(),
            "nominal": facts.nominal.as_ref().map(|nominal| json!({
                "mode": format!("{:?}", nominal.mode),
                "known_sized": nominal.known_sized, "external_body": nominal.external_body,
                "ext_equal_declared": nominal.ext_equal_declared,
                "parameter_recursion": nominal.recursion.iter().map(|parameter| json!({
                    "native_parameter_index": parameter.parameter,
                    "policy": format!("{:?}", parameter.policy), "origin": format!("{:?}", parameter.origin),
                })).collect::<Vec<_>>(),
                "positive_and_well_founded_representation": "Unknown; separate source validation required",
            })),
            "macro_and_build_provenance": "Unknown; a native policy check is not build authentication",
            "import_authorized": false,
        })
    }
}

fn key_json(key: NativeKey) -> Value {
    json!({"stable_crate_id": format!("{:016x}", key.stable_crate_id),
        "def_path_hash": format!("{:032x}", key.def_path_hash)})
}

fn key(tcx: TyCtxt<'_>, owner: DefId) -> NativeKey {
    let (high, low) = tcx.def_path_hash(owner).0.split();
    NativeKey {
        stable_crate_id: tcx.stable_crate_id(owner.krate).as_u64(),
        def_path_hash: (u128::from(high.as_u64()) << 64) | u128::from(low.as_u64()),
    }
}

fn original_owner_available(tcx: TyCtxt<'_>, owner: DefId) -> bool {
    let Some(local) = owner.as_local() else {
        return false;
    };
    let Some(original) = tcx.lower_to_hir(local).as_owner() else {
        return false;
    };
    match (original.node(), tcx.hir_node_by_def_id(local)) {
        (OwnerNode::Item(a), hir::Node::Item(b)) => std::ptr::eq(a, b),
        (OwnerNode::ImplItem(a), hir::Node::ImplItem(b)) => std::ptr::eq(a, b),
        _ => false,
    }
}

fn collect<'tcx>(tcx: TyCtxt<'tcx>, owner: DefId) -> Result<OwnedPolicy, String> {
    if tcx.dcx().has_errors().is_some() || !original_owner_available(tcx, owner) {
        return Err("no error-free original local declaration is established".into());
    }
    let local = owner
        .as_local()
        .ok_or("foreign attributes need their genuine local producer")?;
    let nominal = matches!(tcx.def_kind(owner), DefKind::Struct | DefKind::Enum);
    if !nominal && !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn) {
        return Err("this declaration kind has no supported generic policy producer".into());
    }
    if !nominal && matches!(tcx.constness(owner), hir::Constness::Const { .. }) {
        return Err("const function policy needs a separate native producer".into());
    }
    let parent = tcx.def_kind(tcx.local_parent(local));
    if !(parent == DefKind::Mod || (!nominal && parent == DefKind::Impl { of_trait: false }))
        || (!nominal && tcx.trait_impl_of_assoc(owner).is_some())
    {
        return Err(
            "trait/default/inherited or nested declaration policy is outside this producer".into(),
        );
    }
    let context = if nominal {
        Context::Nominal
    } else {
        Context::Function
    };
    let directives = attributes::read(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)), context)?;
    if !directives.verus_macro {
        return Err("the declaration has no Verus-origin marker".into());
    }

    let mut scopes = Vec::new();
    let mut seen = HashSet::new();
    let mut current = Some(owner);
    while let Some(scope) = current {
        if scopes.len() >= MAX_SCOPES || !seen.insert(scope) {
            return Err("generic parent scopes exceed their bound or cycle".into());
        }
        scopes.push(scope);
        current = tcx.generics_of(scope).parent;
    }
    scopes.reverse();
    let mut parameters = Vec::new();
    let mut native_parameters = Vec::new();
    let mut clauses = Vec::new();
    for scope in scopes {
        if tcx.is_conditionally_const(scope) {
            return Err("conditional const clauses need a separate native policy producer".into());
        }
        // Native generics omit late-bound lifetimes. Inspect the original
        // declaration too so a lifetime binder cannot disappear from this
        // deliberately type-parameter-only policy fragment.
        let local_scope = scope
            .as_local()
            .ok_or("a generic policy scope is not local")?;
        let authored = tcx
            .hir_node_by_def_id(local_scope)
            .generics()
            .ok_or("a native policy scope has no authored generic declaration")?;
        if authored.params.len() > MAX_PARAMETERS {
            return Err("authored generic parameter inventory exceeds its bound".into());
        }
        if authored
            .params
            .iter()
            .any(|parameter| !matches!(parameter.kind, hir::GenericParamKind::Type { .. }))
        {
            return Err("authored lifetime or const binders need another policy producer".into());
        }
        if scope != owner {
            let local = scope
                .as_local()
                .ok_or("an inherited generic scope is not local")?;
            if tcx.def_kind(scope) != (DefKind::Impl { of_trait: false }) {
                return Err("an inherited generic scope is not an inherent implementation".into());
            }
            attributes::read(
                tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
                Context::Implementation,
            )?;
            if !original_owner_available(tcx, scope) {
                return Err("an inherited implementation is not its original native owner".into());
            }
        }
        let generics = tcx.generics_of(scope);
        if authored.params.len() != generics.own_params.len()
            || authored
                .params
                .iter()
                .zip(&generics.own_params)
                .any(|(authored, native)| authored.def_id.to_def_id() != native.def_id)
        {
            return Err("authored and native own type-parameter inventories differ".into());
        }
        if generics.has_self || generics.parent_count != parameters.len() {
            return Err("generic Self or parent binder correspondence is unsupported".into());
        }
        if parameters.len().saturating_add(generics.own_params.len()) > MAX_PARAMETERS {
            return Err("native generic parameter inventory exceeds its bound".into());
        }
        for parameter in &generics.own_params {
            let ty::GenericParamDefKind::Type {
                has_default,
                synthetic: false,
            } = parameter.kind
            else {
                return Err(
                    "lifetime, const or synthetic generic parameters need another policy producer"
                        .into(),
                );
            };
            if parameter.pure_wrt_drop || parameter.index as usize != parameters.len() {
                return Err("native generic parameter index/drop policy is unsupported".into());
            }
            let local = parameter
                .def_id
                .as_local()
                .ok_or("a generic parameter is not local")?;
            let parameter_directives = attributes::read(
                tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
                Context::Parameter,
            )?;
            if !nominal && parameter_directives.has_recursion() {
                return Err(
                    "a recursion policy on a function/implementation parameter is unsupported"
                        .into(),
                );
            }
            parameters.push(Parameter {
                definition: key(tcx, parameter.def_id),
                scope: key(tcx, scope),
                index: parameter.index,
                has_default,
            });
            native_parameters.push(parameter);
        }
        let native = tcx.clauses_of(scope);
        if native.parent != generics.parent
            || clauses.len().saturating_add(native.clauses.len()) > MAX_CLAUSES
        {
            return Err("native clause parent/inventory differs from its generic scope".into());
        }
        for (clause, _) in native.instantiate_own_identity() {
            let Some(ty::ClauseKind::Trait(predicate)) =
                clause.skip_normalization().kind().no_bound_vars()
            else {
                return Err(
                    "higher-ranked, region, projection, const or other generic clauses are Unknown"
                        .into(),
                );
            };
            if predicate.polarity != ty::ClausePolarity::Positive
                || predicate.trait_ref.args.len() != 1
            {
                return Err(
                    "a nonpositive or nonunary trait clause needs another policy producer".into(),
                );
            }
            let lang = tcx.lang_items();
            let trait_id = predicate.def_id();
            let kind = if Some(trait_id) == lang.sized_trait() {
                SizedTrait::Sized
            } else if Some(trait_id) == lang.meta_sized_trait() {
                SizedTrait::MetaSized
            } else if Some(trait_id) == lang.pointee_sized_trait() {
                SizedTrait::PointeeSized
            } else {
                return Err(
                    "a generic trait clause is not a recognized native sizedness lang item".into(),
                );
            };
            let ty::Param(parameter) = predicate.self_ty().kind() else {
                return Err(
                    "a sizedness clause subject is not a native type-parameter index".into(),
                );
            };
            if !parameters
                .iter()
                .any(|candidate| candidate.index == parameter.index)
            {
                return Err("a sizedness clause refers to an unknown native parameter".into());
            }
            clauses.push(SizedClause {
                scope: key(tcx, scope),
                parameter: parameter.index,
                trait_definition: key(tcx, trait_id),
                kind,
            });
        }
    }
    let nominal = if nominal {
        let recursion = recursion_policy(tcx, &native_parameters, &directives)?;
        // Same first query as pinned Verus get_sized_constraint. Unsupported
        // lifetime/projection clauses were refused before this region-erased query.
        let environment = ty::TypingEnv::post_analysis(tcx, owner);
        let native = tcx
            .type_of(owner)
            .instantiate_identity()
            .skip_normalization();
        Some(Nominal {
            mode: directives.nominal_mode.unwrap_or(Mode::Exec),
            known_sized: native.is_sized(tcx, environment),
            external_body: directives.external_body,
            ext_equal_declared: directives.ext_equal,
            recursion,
        })
    } else {
        None
    };
    if tcx.dcx().has_errors().is_some() || !original_owner_available(tcx, owner) {
        return Err("native policy checking emitted errors or changed the original owner".into());
    }
    Ok(OwnedPolicy {
        owner: key(tcx, owner),
        parameters,
        clauses,
        nominal,
    })
}

fn recursion_policy(
    tcx: TyCtxt<'_>,
    parameters: &[&ty::GenericParamDef],
    directives: &Directives,
) -> Result<Vec<ParameterRecursion>, String> {
    let mut selected = Vec::new();
    for parameter in parameters {
        let local = parameter
            .def_id
            .as_local()
            .ok_or("a nominal type parameter is not local")?;
        let attrs = attributes::read(
            tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
            Context::Parameter,
        )?;
        selected.push(
            attrs
                .bare_policy()
                .map(|policy| (policy, RecursionOrigin::ParameterAttribute)),
        );
    }
    for (name, policy) in &directives.named {
        let Some(index) = parameters
            .iter()
            .position(|parameter| parameter.name.as_str() == name)
        else {
            return Err("a recursion directive names no actual native type parameter".into());
        };
        if selected[index].is_some() {
            return Err("duplicate recursion policy for a native type parameter".into());
        }
        selected[index] = Some((*policy, RecursionOrigin::ItemAttribute));
    }
    parameters
        .iter()
        .zip(selected)
        .map(|(parameter, selected)| {
            let (policy, origin) =
                match selected {
                    Some(selected) => selected,
                    None if directives.external_body => return Err(
                        "external_body needs an explicit recursion policy for every type parameter"
                            .into(),
                    ),
                    None => (Recursion::RejectInGround, RecursionOrigin::VerusDefault),
                };
            Ok(ParameterRecursion {
                parameter: parameter.index,
                policy,
                origin,
            })
        })
        .collect()
}

pub(super) fn check<'tcx>(tcx: TyCtxt<'tcx>, owner: DefId) -> CheckedPolicy<'tcx> {
    CheckedPolicy {
        tcx,
        owner,
        facts: collect(tcx, owner),
    }
}
