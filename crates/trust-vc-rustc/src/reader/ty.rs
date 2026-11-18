//! rustc types as VcIR types, and as Verus prints them.
//!
//! [`Cx::vc_ty_with`] gives the VcIR type of a rustc type, or `None` when VcIR
//! cannot represent it (the caller refuses). [`Cx::v_typ`] gives the
//! [`VTyp`] Verus would name in a diagnostic, or `None` when this reader does
//! not know Verus's spelling for it.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArgKind, Ty};
use rustc_span::sym;

use trust_vc_vcir::{IntRange, Ty as VcTy};

use super::Cx;
use crate::verus_items::VerusItem;
use crate::vtyp::{Decoration, VTyp};

impl<'tcx> Cx<'tcx> {
    /// The integer range of a rustc type, including Verus's `int` and `nat`.
    pub(crate) fn int_range(&self, ty: Ty<'tcx>) -> Option<IntRange> {
        match ty.kind() {
            ty::Int(int_ty) => Some(match int_ty.bit_width() {
                Some(bits) => IntRange::I(u32::try_from(bits).ok()?),
                None => IntRange::ISize,
            }),
            ty::Uint(uint_ty) => Some(match uint_ty.bit_width() {
                Some(bits) => IntRange::U(u32::try_from(bits).ok()?),
                None => IntRange::USize,
            }),
            ty::Char => Some(IntRange::Char),
            ty::Adt(adt, _) => match self.verus_item(adt.did()) {
                Some(VerusItem::Int) => Some(IntRange::Int),
                Some(VerusItem::Nat) => Some(IntRange::Nat),
                _ => None,
            },
            _ => None,
        }
    }

    /// The VcIR type of `ty`, or `None` when VcIR has no such type; `param`
    /// gives the VcIR index of each type parameter in scope.
    pub(crate) fn vc_ty_with(
        &self,
        ty: Ty<'tcx>,
        param: &dyn Fn(ty::ParamTy) -> Option<u32>,
    ) -> Option<VcTy> {
        if let Some(range) = self.int_range(ty) {
            // Retain source identity. The complete architecture contexts
            // choose mathematical bounds, never a host-dependent type alias.
            return Some(VcTy::Int(range));
        }
        match ty.kind() {
            ty::Bool => Some(VcTy::Bool),
            ty::Tuple(elems) if elems.is_empty() => Some(VcTy::Unit),
            ty::Tuple(elems) => elems
                .iter()
                .map(|elem| self.vc_ty_with(elem, param))
                .collect::<Option<Vec<_>>>()
                .map(VcTy::Tuple),
            ty::Adt(adt, args) => {
                let id = self.adt_id(adt.did())?;
                let mut type_args = Vec::new();
                for arg in args.iter() {
                    match arg.kind() {
                        GenericArgKind::Lifetime(_) => {}
                        GenericArgKind::Type(t) => {
                            // Legacy mutable parameters are transparent and
                            // cannot be stored in a datatype. The new mode
                            // retains an opaque carrier at every nesting level.
                            if !self.opts.new_mut_ref
                                && t.walk().any(|a| {
                                    a.as_type().is_some_and(
                                        |t| matches!(t.kind(), ty::Ref(_, _, m) if m.is_mut()),
                                    )
                                })
                            {
                                return None;
                            }
                            type_args.push(self.vc_ty_with(t, param)?);
                        }
                        GenericArgKind::Const(_) => return None,
                    }
                }
                Some(VcTy::Adt(id, type_args))
            }
            ty::Ref(_, inner, mutability) if self.opts.new_mut_ref && mutability.is_mut() => {
                Some(VcTy::MutRef(Box::new(self.vc_ty_with(*inner, param)?)))
            }
            ty::Ref(_, inner, mutability) => Some(VcTy::Ref {
                mutable: mutability.is_mut(),
                inner: Box::new(self.vc_ty_with(*inner, param)?),
            }),
            ty::Param(p) => param(*p).map(VcTy::Param),
            ty::Alias(..) => super::projection_types::lower(self, ty, param),
            _ => None,
        }
    }

    /// The type as Verus names it in diagnostics, or `None` when the reader
    /// does not know Verus's spelling.
    pub(crate) fn v_typ(&self, ty: Ty<'tcx>) -> Option<VTyp> {
        if let Some(range) = self.int_range(ty) {
            return Some(VTyp::Int(range));
        }
        let tcx = self.tcx;
        match ty.kind() {
            ty::Bool => Some(VTyp::Bool),
            ty::Never => Some(VTyp::Never),
            ty::Tuple(elems) => elems
                .iter()
                .map(|elem| self.v_typ(elem))
                .collect::<Option<Vec<_>>>()
                .map(VTyp::Tuple),
            ty::Ref(_, inner, mutability) => {
                let decoration = if mutability.is_mut() {
                    Decoration::MutRef
                } else {
                    Decoration::Ref
                };
                Some(VTyp::Decorate(decoration, Box::new(self.v_typ(*inner)?)))
            }
            ty::Param(param) => Some(VTyp::Param(param.name.to_string())),
            ty::Adt(adt, args) => {
                let did = adt.did();
                let type_args: Vec<Ty<'tcx>> = args
                    .iter()
                    .filter_map(|arg| match arg.kind() {
                        GenericArgKind::Type(t) => Some(t),
                        _ => None,
                    })
                    .collect();
                let decoration = if adt.is_box() {
                    Some(Decoration::Box)
                } else if tcx.is_diagnostic_item(sym::Rc, did) {
                    Some(Decoration::Rc)
                } else if tcx.is_diagnostic_item(sym::Arc, did) {
                    Some(Decoration::Arc)
                } else {
                    match self.verus_item(did) {
                        Some(VerusItem::Ghost) => Some(Decoration::Ghost),
                        Some(VerusItem::Tracked) => Some(Decoration::Tracked),
                        _ => None,
                    }
                };
                if let Some(decoration) = decoration {
                    // The allocator argument of Box/Rc/Arc is not part of
                    // Verus's comparison when it is the default one; the
                    // reader only handles that case.
                    let inner = *type_args.first()?;
                    return Some(VTyp::Decorate(decoration, Box::new(self.v_typ(inner)?)));
                }
                if self.verus_item(did) == Some(VerusItem::FnSpec) {
                    // FnSpec<(A, B, ..), R> prints as spec_fn(A, B, ..) -> R.
                    let [params, ret] = type_args.as_slice() else {
                        return None;
                    };
                    let ty::Tuple(param_tys) = params.kind() else {
                        return None;
                    };
                    let params = param_tys
                        .iter()
                        .map(|p| self.v_typ(p))
                        .collect::<Option<Vec<_>>>()?;
                    return Some(VTyp::SpecFn(params, Box::new(self.v_typ(*ret)?)));
                }
                if self.verus_item(did).is_some() {
                    return None;
                }
                let args = type_args
                    .iter()
                    .map(|t| self.v_typ(*t))
                    .collect::<Option<Vec<_>>>()?;
                Some(VTyp::Datatype {
                    path: self.friendly_path(did),
                    args,
                })
            }
            ty::Closure(def_id, args) => {
                // Verus's `AnonymousClosure` type (`rust_to_vir_base.rs`,
                // `TyKind::Closure`): the signature's single tuple parameter
                // is spread into the parameter list.
                let closure = args.as_closure();
                let sig = closure.sig().skip_binder();
                let [params] = sig.inputs() else {
                    return None;
                };
                let ty::Tuple(params) = params.kind() else {
                    return None;
                };
                let params = params
                    .iter()
                    .map(|p| self.v_typ(p))
                    .collect::<Option<Vec<_>>>()?;
                let ret = self.v_typ(sig.output())?;
                let kind = match closure.kind() {
                    ty::ClosureKind::Fn => "Fn",
                    ty::ClosureKind::FnMut => "FnMut",
                    ty::ClosureKind::FnOnce => "FnOnce",
                };
                Some(VTyp::AnonymousClosure {
                    kind,
                    args: params,
                    ret: Box::new(ret),
                    id: def_id.as_local()?.local_def_index.as_u32(),
                })
            }
            ty::Alias(_, alias) => match alias.kind {
                ty::AliasTyKind::Projection { def_id } => {
                    let def_id: DefId = def_id;
                    let trait_id = tcx.parent(def_id);
                    let mut types = alias.args.iter().filter_map(|arg| match arg.kind() {
                        GenericArgKind::Type(t) => Some(t),
                        _ => None,
                    });
                    let self_ty = self.v_typ(types.next()?)?;
                    let trait_args = types.map(|t| self.v_typ(t)).collect::<Option<Vec<_>>>()?;
                    Some(VTyp::Projection {
                        self_ty: Box::new(self_ty),
                        trait_path: self.friendly_path(trait_id),
                        trait_args,
                        name: tcx.item_name(def_id).to_string(),
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// A function's path as Verus writes it in messages
    /// (`rust_to_vir_base.rs`, `register_friendly_path_as_rust_name`):
    /// `crate::module::f`, and `crate::module::Type::f` for a method of an
    /// impl whose self type is a named type.
    pub(crate) fn friendly_fn_path(&self, did: DefId) -> String {
        let tcx = self.tcx;
        if let Some(real) = did.as_local().and_then(|local| self.constants.real(local)) {
            return self.friendly_path(real.to_def_id());
        }
        let parent = tcx.parent(did);
        if matches!(tcx.def_kind(parent), DefKind::Impl { .. }) {
            if let ty::Adt(adt, _) = tcx.type_of(parent).skip_binder().kind() {
                return format!("{}::{}", self.friendly_path(adt.did()), tcx.item_name(did));
            }
        }
        self.friendly_path(did)
    }

    /// `crate::module::Name`, the way Verus writes paths in messages: the
    /// defining crate's name followed by every named path segment.
    pub(crate) fn friendly_path(&self, did: DefId) -> String {
        let tcx = self.tcx;
        let mut parts = vec![tcx.crate_name(did.krate).to_string()];
        for component in tcx.def_path(did).data {
            if let Some(name) = component.data.get_opt_name() {
                parts.push(name.to_string());
            }
        }
        parts.join("::")
    }
}
