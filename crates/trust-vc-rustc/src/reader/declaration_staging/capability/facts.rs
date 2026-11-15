//! Join sealed native facts within one actual producer batch.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// The indices are the complete native flattened binder, including parent
/// implementation parameters. Display names are never its authority.
pub(super) fn parameters(
    declaration: &alignment::Declaration,
    policy: &declaration_policy::OwnedPolicy,
) -> Result<Vec<u32>, String> {
    if declaration.key != policy.owner() {
        return Err("the native generic policy belongs to another declaration".into());
    }
    let Observation::Observed(scopes) = &declaration.generics else {
        return Err("the complete declaration binder is Unknown".into());
    };
    let indices = binder_indices(scopes)?;
    if policy.parameters().len() != indices.len()
        || policy
            .parameters()
            .iter()
            .zip(&indices)
            .any(|(parameter, index)| parameter.index != *index || parameter.has_default)
    {
        return Err("the checked native policy does not cover the full flattened binder".into());
    }
    Ok(indices)
}

fn binder_indices(scopes: &[alignment::GenericScope]) -> Result<Vec<u32>, String> {
    let mut indices = Vec::new();
    for scope in scopes.iter().rev() {
        if scope.has_self || scope.parent_count as usize != indices.len() {
            return Err("the declaration binder has unsupported Self or parent indices".into());
        }
        for parameter in &scope.own_type_parameters {
            if indices.len() >= 256
                || parameter.index as usize != indices.len()
                || parameter.has_default
                || parameter.synthetic
                || parameter.pure_wrt_drop
            {
                return Err("the declaration binder is incomplete or unsupported".into());
            }
            indices.push(parameter.index);
        }
    }
    Ok(indices)
}

fn declaration(view: &View, key: NativeKey) -> Result<&alignment::Declaration, String> {
    view.declarations
        .iter()
        .find(|declaration| declaration.key == key)
        .ok_or_else(|| "the native declaration is absent".into())
}

pub(super) fn correspondence(
    library: &StagedLibrary,
    keep: NativeKey,
) -> Result<(&alignment::Declaration, &alignment::Declaration), String> {
    let candidate = library
        .prepared
        .candidates
        .matches
        .iter()
        .find(|candidate| candidate.keep == keep)
        .ok_or("the declaration has no unique checked Keep/Erase correspondence")?;
    if library
        .prepared
        .erase
        .roundtrip_unknown
        .contains_key(&candidate.erase)
    {
        return Err(
            "the emitted declaration did not survive the actual metadata round trip".into(),
        );
    }
    let keep = declaration(&library.prepared.keep_view, candidate.keep)?;
    let erase = declaration(&library.prepared.erase.view, candidate.erase)?;
    for declaration in [keep, erase] {
        let Observation::Observed(anchor) = &declaration.source else {
            return Err("the declaration's original source identity is Unknown".into());
        };
        library.inputs.sources.validate_anchor(&anchor.identifier)?;
        for enclosing in &anchor.enclosing_declarations {
            library.inputs.sources.validate_anchor(enclosing)?;
        }
    }
    Ok((keep, erase))
}

/// Retain the original per-parameter recursion rule beside the abstract
/// carrier. Empty exported variants never stand in for representation WF.
pub(super) struct NominalFacts<'library> {
    pub(super) erase: &'library alignment::Declaration,
    pub(super) policy: &'library declaration_policy::OwnedPolicy,
    pub(super) parameters: Vec<u32>,
}

pub(super) fn nominal(library: &StagedLibrary, key: NativeKey) -> Result<NominalFacts<'_>, String> {
    let (keep, erase) = correspondence(library, key)?;
    if !matches!(
        keep.shape,
        Observation::Observed(alignment::DeclarationShape::Nominal {
            kind: alignment::NominalKind::Struct | alignment::NominalKind::Enum
        })
    ) {
        return Err("the declaration is not a supported native nominal kind".into());
    }
    let policy = library
        .prepared
        .nominal_policies
        .get(&key)
        .ok_or("the native nominal policy is Unknown")?;
    let nominal = policy
        .nominal()
        .filter(|nominal| nominal.known_sized())
        .ok_or("the abstract nominal carrier lacks an actual Sized declaration")?;
    if nominal.mode() != trust_vc_vcir::Mode::Exec {
        return Err(
            "a ghost/tracked nominal needs its datatype-mode consumer before registration".into(),
        );
    }
    let parameters = parameters(keep, policy)?;
    if nominal.recursion().len() != parameters.len()
        || nominal
            .recursion()
            .iter()
            .zip(&parameters)
            .any(|(rule, index)| rule.parameter != *index)
    {
        return Err("the nominal recursion policy does not cover the complete binder".into());
    }
    let wf = library
        .prepared
        .nominal_wf
        .get(&key)
        .ok_or("the original nominal positivity/base-case facts are Unknown")?;
    let fields = library
        .prepared
        .nominal_fields
        .get(&key)
        .ok_or("the original field-language facts are Unknown")?;
    let helpers = library
        .prepared
        .nominal_helpers
        .get(&key)
        .ok_or("the original nominal helper-language closure is Unknown")?;
    helpers.revalidate(&library.inputs, &library.prepared.common)?;
    let expected = wf
        .local_declarations()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let actual = fields
        .local_declarations()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if wf.owner() != key
        || fields.owner() != key
        || helpers.owner() != key
        || expected.len() != wf.local_declarations().len()
        || actual.len() != fields.local_declarations().len()
        || expected != actual
        || !expected.contains(&key)
        || helpers.local_declarations() != wf.local_declarations()
    {
        return Err(
            "the native nominal facts have different owners or local dependency sets".into(),
        );
    }
    Ok(NominalFacts {
        erase,
        policy,
        parameters,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_binder_keeps_inherited_indices_and_refuses_missing_scopes() {
        let scope = |parent_count, indices: &[u32]| alignment::GenericScope {
            parent_count,
            has_self: false,
            own_type_parameters: indices
                .iter()
                .map(|index| alignment::TypeParameter {
                    index: *index,
                    has_default: false,
                    synthetic: false,
                    pure_wrt_drop: false,
                })
                .collect(),
        };
        // len's own binder is empty, but its impl's A is still parameter 0.
        let inherited = [scope(1, &[]), scope(0, &[0])];
        assert_eq!(binder_indices(&inherited).unwrap(), vec![0]);
        assert!(binder_indices(&inherited[..1]).is_err());
        assert!(binder_indices(&[scope(1, &[0]), scope(0, &[0])]).is_err());
        let mut unsupported = inherited.clone();
        unsupported[1].own_type_parameters[0].synthetic = true;
        assert!(binder_indices(&unsupported).is_err());
    }
}
