//! Bounded native field type-language admission after nominal WF checking.

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt};
use rustc_span::Symbol;

use super::super::declaration_policy;
use super::super::declaration_wf::{BuiltinRole, CheckedWf, OwnedWf};
use super::{attributes, key, proxy, ExternalMapping};

const MAX_VARIANTS: usize = 1_024;
const MAX_FIELDS: usize = 4_096;
const MAX_TYPE_WORK: usize = 16_384;

pub(super) struct Captured {
    pub(super) proxies: Vec<DefId>,
    pub(super) mappings: Vec<ExternalMapping>,
}

struct Check<'facts, 'tcx> {
    tcx: TyCtxt<'tcx>,
    declarations: HashSet<DefId>,
    wf: &'facts OwnedWf,
    captured: Captured,
    type_work: usize,
}

impl<'tcx> Check<'_, 'tcx> {
    fn builtin(&self, owner: DefId) -> Option<BuiltinRole> {
        for (name, role) in [
            ("verus::verus_builtin::FnSpec", BuiltinRole::SpecFunction),
            (
                "verus::verus_builtin::int",
                BuiltinRole::MathematicalInteger,
            ),
            ("verus::verus_builtin::nat", BuiltinRole::NaturalNumber),
        ] {
            if self.tcx.get_diagnostic_item(Symbol::intern(name)) == Some(owner) {
                return Some(role);
            }
        }
        (self.tcx.lang_items().owned_box() == Some(owner)).then_some(BuiltinRole::OwnedBox)
    }

    fn require_builtin(&self, owner: DefId, role: BuiltinRole) -> Result<(), String> {
        if owner.is_local()
            || self.tcx.def_kind(owner) != DefKind::Struct
            || !self.wf.builtin_requirements().iter().any(|requirement| {
                requirement.role == role
                    && requirement.definition == key(self.tcx, owner)
                    && requirement.crate_svh == self.tcx.crate_hash(owner.krate).as_u128()
            })
        {
            return Err(
                "field builtin identity is not covered by the sealed native WF check".into(),
            );
        }
        Ok(())
    }

    fn arguments(&self, owner: DefId, args: GenericArgsRef<'tcx>) -> Result<Vec<Ty<'tcx>>, String> {
        let generics = self.tcx.generics_of(owner);
        if args.len() > self.type_work
            || generics.parent.is_some()
            || generics.own_params.len() != args.len()
            || generics.own_params.iter().any(|parameter| {
                !matches!(
                    parameter.kind,
                    ty::GenericParamDefKind::Type {
                        synthetic: false,
                        ..
                    }
                )
            })
        {
            return Err("field type argument shape needs unsupported binders or arity".into());
        }
        args.iter()
            .map(|argument| match argument.kind() {
                ty::GenericArgKind::Type(value) => Ok(value),
                _ => Err("field type lifetime/const argument admission is not represented".into()),
            })
            .collect()
    }

    fn allocator(&mut self, target: Ty<'tcx>) -> Result<(), String> {
        let ty::Adt(adt, _) = target.kind() else {
            return Err("default allocator is not a nominal type".into());
        };
        if self
            .captured
            .mappings
            .iter()
            .any(|mapping| mapping.target == key(self.tcx, adt.did()))
        {
            return Ok(());
        }
        let (proxy, mapping) = proxy::find(self.tcx, target)?;
        self.captured.proxies.push(proxy);
        self.captured.mappings.push(mapping);
        Ok(())
    }

    fn ty(&mut self, value: Ty<'tcx>, parameters: usize, depth: usize) -> Result<(), String> {
        self.type_work = self
            .type_work
            .checked_sub(1)
            .ok_or("field type work exceeds its bound")?;
        if depth > 64 {
            return Err("field type depth exceeds its bound".into());
        }
        match value.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => Ok(()),
            ty::Param(parameter) if (parameter.index as usize) < parameters => Ok(()),
            ty::Tuple(values) => {
                if values.len() > self.type_work {
                    return Err("field tuple exceeds its work bound".into());
                }
                for value in values.iter() {
                    self.ty(value, parameters, depth + 1)?;
                }
                Ok(())
            }
            ty::Ref(_, inner, mutability) if !mutability.is_mut() => {
                self.ty(*inner, parameters, depth + 1)
            }
            ty::Adt(adt, args) => {
                let definition = adt.did();
                let arguments = self.arguments(definition, args)?;
                match self.builtin(definition) {
                    Some(
                        role @ (BuiltinRole::MathematicalInteger | BuiltinRole::NaturalNumber),
                    ) => {
                        if !arguments.is_empty() {
                            return Err("field numeric builtin has unexpected arguments".into());
                        }
                        self.require_builtin(definition, role)
                    }
                    Some(BuiltinRole::SpecFunction) => {
                        let [inputs, output] = arguments.as_slice() else {
                            return Err("field spec-function has unexpected arity".into());
                        };
                        if !matches!(inputs.kind(), ty::Tuple(_)) {
                            return Err("field spec-function arguments are not a tuple".into());
                        }
                        self.require_builtin(definition, BuiltinRole::SpecFunction)?;
                        self.ty(*inputs, parameters, depth + 1)?;
                        self.ty(*output, parameters, depth + 1)
                    }
                    Some(BuiltinRole::OwnedBox) => {
                        let [inner, allocator] = arguments.as_slice() else {
                            return Err("field Box has unexpected arity".into());
                        };
                        let parameter = &self.tcx.generics_of(definition).own_params[1];
                        if !matches!(
                            parameter.kind,
                            ty::GenericParamDefKind::Type {
                                has_default: true,
                                ..
                            }
                        ) || self
                            .tcx
                            .type_of(parameter.def_id)
                            .instantiate(self.tcx, args)
                            .skip_normalization()
                            != *allocator
                        {
                            return Err("field Box allocator is outside the native declared-default fragment".into());
                        }
                        self.require_builtin(definition, BuiltinRole::OwnedBox)?;
                        self.ty(*inner, parameters, depth + 1)?;
                        // Verus translates ALL Box arguments, even though the
                        // positivity pass erases the allocator decoration.
                        self.type_work = self
                            .type_work
                            .checked_sub(1)
                            .ok_or("allocator type work exceeds its bound")?;
                        self.allocator(*allocator)
                    }
                    None if self.declarations.contains(&definition) => {
                        for argument in arguments {
                            self.ty(argument, parameters, depth + 1)?;
                        }
                        Ok(())
                    }
                    None => Err(
                        "field nominal type is outside the checked local declaration inventory"
                            .into(),
                    ),
                }
            }
            _ => Err("field type-language validation needs an unsupported native type form".into()),
        }
    }
}

pub(super) fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    wf: &CheckedWf<'_, 'tcx>,
) -> Result<Captured, String> {
    let facts = wf
        .for_owner(tcx, owner)
        .ok_or("no matching native WF fact for field admission")?;
    let owners = wf
        .local_owners(tcx, owner)
        .ok_or("no matching native owner inventory")?;
    let mut check = Check {
        tcx,
        declarations: owners.iter().copied().collect(),
        wf: facts,
        captured: Captured {
            proxies: vec![],
            mappings: vec![],
        },
        type_work: MAX_TYPE_WORK,
    };
    let mut variants = 0usize;
    let mut fields = 0usize;
    for declaration in owners {
        let policy = declaration_policy::check(tcx, *declaration);
        let policy = policy
            .for_owner(tcx, *declaration)
            .ok_or("a field owner lost its original native policy")?;
        let nominal = policy.nominal().ok_or("a field owner is not nominal")?;
        let local = declaration
            .as_local()
            .ok_or("foreign field owners are not inspected")?;
        let _ = attributes::mode(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)))?;
        let adt = tcx.adt_def(*declaration);
        if adt.is_struct() && nominal.external_body() {
            continue;
        }
        if !adt.is_struct() && !adt.is_enum() {
            return Err("field owner must be a struct or enum".into());
        }
        variants = variants
            .checked_add(adt.variants().len())
            .filter(|count| *count <= MAX_VARIANTS)
            .ok_or("field variant inventory exceeds its bound")?;
        for variant in adt.variants().iter() {
            fields = fields
                .checked_add(variant.fields.len())
                .filter(|count| *count <= MAX_FIELDS)
                .ok_or("field inventory exceeds its bound")?;
            for field in &variant.fields {
                let local = field
                    .did
                    .as_local()
                    .ok_or("foreign private fields are not field admission inputs")?;
                let _ = attributes::mode(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)))?;
                check.ty(
                    tcx.type_of(field.did)
                        .instantiate_identity()
                        .skip_normalization(),
                    policy.parameters().len(),
                    0,
                )?;
            }
        }
    }
    Ok(check.captured)
}
