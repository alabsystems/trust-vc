//! Current-session field meaning for already represented LOCAL enum values.
//!
//! This uses the ordinary reader's admitted builtin TCB. It cannot be used as
//! the fresh build-owner permission for an imported representation or body.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_abi;

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Symbol;
use sha2::{Digest as _, Sha256};
use trust_vc_vcir::AdtDecl;

use crate::declaration_alignment::source_bindings::PinnedFile;

const FIELD: &str = "verus::verus_builtin::get_variant_field";
const ERASED: &str = "verus::verus_builtin::erased_ghost_value";
const TEST: &str = "verus::verus_builtin::is_variant";

#[derive(Clone, Copy)]
enum Kind {
    Field,
    Test,
}

/// No constructor accepts a diagnostic label, artifact hash, or role from a
/// caller. The exact current CStore selection and full native signature are
/// read here. Native IDs and permissions never escape this compiler context.
pub(super) struct Local<'tcx> {
    tcx: TyCtxt<'tcx>,
    intrinsic: DefId,
    test: DefId,
    erased: DefId,
    stable_crate: u64,
    svh: u128,
    file: PinnedFile,
    nominals: HashSet<DefId>,
}

fn signature(tcx: TyCtxt<'_>, definition: DefId, kind: Kind) -> Result<(), String> {
    let parameters = match kind {
        Kind::Field => 2,
        Kind::Test => 1,
    };
    let metadata = match kind {
        Kind::Field => 2,
        Kind::Test => 1,
    };
    let generics = tcx.generics_of(definition);
    if generics.parent.is_some()
        || generics.parent_count != 0
        || generics.has_self
        || generics.own_params.len() != parameters
        || generics
            .own_params
            .iter()
            .enumerate()
            .any(|(index, parameter)| {
                parameter.index as usize != index
                    || parameter.pure_wrt_drop
                    || !matches!(
                        parameter.kind,
                        ty::GenericParamDefKind::Type {
                            has_default: false,
                            synthetic: false
                        }
                    )
            })
    {
        return Err("the local field intrinsic has another native generic binder".into());
    }
    let env = ty::TypingEnv::non_body_analysis(tcx, definition);
    let clauses = tcx.clauses_of(definition);
    if clauses.parent.is_some() || clauses.clauses.len() > 16 {
        return Err("the local field intrinsic has another native clause scope".into());
    }
    let mut sized = vec![false; parameters];
    for (clause, _) in clauses.instantiate_own_identity() {
        let clause = tcx
            .try_normalize_erasing_regions(env, clause)
            .map_err(|_| "the local field intrinsic clauses cannot be normalized")?;
        let Some(ty::ClauseKind::Trait(predicate)) = clause.kind().no_bound_vars() else {
            return Err("the local field intrinsic has an unsupported native clause".into());
        };
        let language = tcx.lang_items();
        let trait_id = predicate.def_id();
        if predicate.polarity != ty::ClausePolarity::Positive
            || predicate.trait_ref.args.len() != 1
            || ![
                language.sized_trait(),
                language.meta_sized_trait(),
                language.pointee_sized_trait(),
            ]
            .into_iter()
            .any(|item| item == Some(trait_id))
        {
            return Err("the local field intrinsic has another native bound".into());
        }
        let ty::Param(parameter) = predicate.self_ty().kind() else {
            return Err("the local field intrinsic bound has another native subject".into());
        };
        let Some(slot) = sized.get_mut(parameter.index as usize) else {
            return Err("the local field intrinsic bound refers to another generic slot".into());
        };
        if Some(trait_id) == language.sized_trait() {
            *slot = true;
        }
    }
    if sized.iter().any(|value| !value) {
        return Err("the local field intrinsic omits its native Sized bounds".into());
    }
    let native = tcx
        .try_normalize_erasing_regions(env, tcx.fn_sig(definition).instantiate_identity())
        .map_err(|_| "the local field intrinsic signature cannot be normalized")?;
    if native.bound_vars().len() != metadata
        || native
            .bound_vars()
            .iter()
            .any(|variable| !matches!(variable, ty::BoundVariableKind::Region(_)))
    {
        return Err("the local field intrinsic has another native region binder".into());
    }
    // The binder is inspected only after its full variable kind/count check.
    // No normalization or generic substitution is skipped.
    let sig = native.skip_binder();
    if sig.abi() != rustc_abi::ExternAbi::Rust
        || !sig.safety().is_safe()
        || sig.c_variadic()
        || sig.splatted().is_some()
        || sig.inputs().len() != metadata + 1
        || !matches!(sig.inputs()[0].kind(), ty::Param(value) if value.index == 0)
        || !match kind {
            Kind::Field => matches!(sig.output().kind(), ty::Param(value) if value.index == 1),
            Kind::Test => matches!(sig.output().kind(), ty::Bool),
        }
    {
        return Err("the local field intrinsic has another native function signature".into());
    }
    for (index, input) in sig.inputs()[1..].iter().enumerate() {
        let ty::Ref(region, target, rustc_hir::Mutability::Not) = input.kind() else {
            return Err(
                "the local field intrinsic metadata arguments are not shared references".into(),
            );
        };
        if !matches!(target.kind(), ty::Str)
            || !matches!(region.kind(), ty::ReBound(ty::BoundVarIndexKind::Bound(depth), bound)
                if depth == ty::INNERMOST && bound.var.as_u32() as usize == index)
        {
            return Err("the local field intrinsic has another string/region argument".into());
        }
    }
    Ok(())
}

impl<'tcx> Local<'tcx> {
    pub(super) fn capture(
        tcx: TyCtxt<'tcx>,
        declarations: &[(LocalDefId, AdtDecl)],
    ) -> Result<Option<Self>, String> {
        let nominals = declarations
            .iter()
            .filter_map(|(owner, _)| {
                (tcx.def_kind(*owner) == DefKind::Enum).then_some(owner.to_def_id())
            })
            .collect::<HashSet<_>>();
        if nominals.is_empty() {
            return Ok(None);
        }
        let intrinsic = tcx
            .get_diagnostic_item(Symbol::intern(FIELD))
            .ok_or("the admitted local enum builtin cohort has no field intrinsic")?;
        let erased = tcx
            .get_diagnostic_item(Symbol::intern(ERASED))
            .ok_or("the ordinary reader has no admitted erasure builtin cohort")?;
        let test = tcx
            .get_diagnostic_item(Symbol::intern(TEST))
            .ok_or("the admitted local enum builtin cohort has no variant test")?;
        if intrinsic.is_local()
            || erased.is_local()
            || test.is_local()
            || intrinsic.krate != erased.krate
            || test.krate != intrinsic.krate
            || tcx.def_kind(intrinsic) != DefKind::Fn
            || tcx.def_kind(test) != DefKind::Fn
            || tcx.dcx().has_errors().is_some()
        {
            return Err(
                "the local field intrinsic is outside the actual foreign builtin cohort".into(),
            );
        }
        signature(tcx, intrinsic, Kind::Field)?;
        signature(tcx, test, Kind::Test)?;
        let source = tcx.used_crate_source(intrinsic.krate);
        let path = source
            .rmeta
            .as_ref()
            .or(source.rlib.as_ref())
            .or(source.dylib.as_ref())
            .ok_or("the local field intrinsic has no actual CStore artifact")?
            .canonicalize()
            .map_err(|error| error.to_string())?;
        let bytes = std::fs::read(&path).map_err(|error| error.to_string())?;
        let file = PinnedFile {
            path,
            sha256: Sha256::digest(bytes).into(),
        };
        file.read()?;
        let result = Self {
            tcx,
            intrinsic,
            test,
            erased,
            stable_crate: tcx.stable_crate_id(intrinsic.krate).as_u64(),
            svh: tcx.crate_hash(intrinsic.krate).as_u128(),
            file,
            nominals,
        };
        result.revalidate(tcx)?;
        Ok(Some(result))
    }

    fn current(&self, tcx: TyCtxt<'tcx>) -> bool {
        std::ptr::eq(*tcx, *self.tcx)
            && tcx.dcx().has_errors().is_none()
            && tcx.get_diagnostic_item(Symbol::intern(FIELD)) == Some(self.intrinsic)
            && tcx.get_diagnostic_item(Symbol::intern(ERASED)) == Some(self.erased)
            && tcx.get_diagnostic_item(Symbol::intern(TEST)) == Some(self.test)
            && tcx.stable_crate_id(self.intrinsic.krate).as_u64() == self.stable_crate
            && tcx.crate_hash(self.intrinsic.krate).as_u128() == self.svh
    }

    pub(super) fn intrinsic(&self, tcx: TyCtxt<'tcx>) -> Option<DefId> {
        self.current(tcx).then_some(self.intrinsic)
    }

    pub(super) fn test_intrinsic(&self, tcx: TyCtxt<'tcx>) -> Option<DefId> {
        self.current(tcx).then_some(self.test)
    }

    pub(super) fn permits(&self, tcx: TyCtxt<'tcx>, definition: DefId) -> bool {
        self.current(tcx) && definition.is_local() && self.nominals.contains(&definition)
    }

    pub(super) fn revalidate(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        if !self.current(tcx) {
            return Err("the local field intrinsic left its original native context".into());
        }
        let source = tcx.used_crate_source(self.intrinsic.krate);
        let path = source
            .rmeta
            .as_ref()
            .or(source.rlib.as_ref())
            .or(source.dylib.as_ref())
            .ok_or("the local field intrinsic lost its native artifact")?
            .canonicalize()
            .map_err(|error| error.to_string())?;
        if path != self.file.path {
            return Err("the local field intrinsic CStore artifact changed".into());
        }
        self.file.read()?;
        Ok(())
    }
}
