//! Function declaration invariants and declaration-local lookup helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

impl FnDecl {
    /// Every source trigger hint attached to this declaration's broadcast.
    pub fn broadcast_hints(&self) -> impl Iterator<Item = &Expr> {
        self.attrs.broadcast_triggers.iter().flatten().flatten()
    }

    pub(crate) fn broadcast_problem(&self) -> Option<&'static str> {
        self.attrs.broadcast_triggers.as_ref()?;
        if self.role != FnRole::Item
            || self.kind != FnKind::Function
            || self.mode != Mode::Proof
            || !self.type_params.is_empty()
            || self.attrs.instance.is_some()
            || self.attrs.is_trait_method_impl
            || self.ret_ty() != Some(&Ty::Unit)
        {
            return Some("a broadcast outside the local monomorphic proof fragment");
        }
        if self.params.iter().any(|id| {
            self.local(*id).is_none_or(|local| {
                local.mode != Mode::Spec
                    || local.mutable
                    || matches!(local.ty, Ty::MutRef(_) | Ty::Ref { mutable: true, .. })
            })
        }) {
            return Some("a broadcast requires immutable spec parameter values");
        }
        None
    }

    /// The effective unwind promise, without copying a condition's AST.
    #[must_use]
    pub fn unwind_spec(&self) -> &UnwindSpec {
        const MAY: UnwindSpec = UnwindSpec::MayUnwind;
        const NO: UnwindSpec = UnwindSpec::NoUnwind;
        self.unwind.as_ref().unwrap_or(match self.mode {
            Mode::Exec => &MAY,
            Mode::Spec | Mode::Proof => &NO,
        })
    }

    /// The initial imported fragment carries only a specification signature.
    /// Body visibility and resource metadata grant no definition or queries.
    pub(crate) fn imported_problem(&self) -> Option<&'static str> {
        if self.role != FnRole::Imported {
            return None;
        }
        if self.mode != Mode::Spec || self.kind != FnKind::Function || self.body != Body::None {
            return Some("an imported declaration requires an ordinary bodyless spec function");
        }
        if !self.requires.is_empty()
            || self.unwind.is_some()
            || !self.ensures.is_empty()
            || !self.recommends.is_empty()
            || !self.decreases.is_empty()
            || self.decreases_when.is_some()
            || self.decreases_by.is_some()
        {
            return Some("an imported declaration cannot carry contract or termination clauses");
        }
        if self.attrs.inline
            || self.attrs.broadcast_triggers.is_some()
            || self.attrs.external_body
            || self.attrs.exec_allows_no_decreases
            || self.attrs.is_decreases_by
            || self.attrs.is_trait_method_impl
            || self.attrs.instance.is_some()
        {
            return Some("an imported declaration cannot carry body or instance authority");
        }
        if self.locals.len() != self.params.len() + 1
            || self.locals.iter().any(|local| {
                local.mode != Mode::Spec
                    || local.mutable
                    || !matches!(local.kind, LocalKind::Param | LocalKind::Return)
            })
        {
            return Some(
                "an imported signature requires only immutable spec parameters and result",
            );
        }
        None
    }

    /// The declaration of `local`, if it exists.
    #[must_use]
    pub fn local(&self, local: LocalId) -> Option<&LocalDecl> {
        self.locals.get(local.index())
    }

    /// The return type.
    #[must_use]
    pub fn ret_ty(&self) -> Option<&Ty> {
        self.local(self.ret).map(|decl| &decl.ty)
    }
}
